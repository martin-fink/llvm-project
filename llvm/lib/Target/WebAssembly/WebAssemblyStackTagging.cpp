//===- WebAssemblyStackTagging.cpp - Stack tagging in IR --===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//===----------------------------------------------------------------------===//

#include "WebAssembly.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/StackSafetyAnalysis.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/CodeGen/LiveRegUnits.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineOperand.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IntrinsicsWebAssembly.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/ValueHandle.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/MemoryTaggingSupport.h"
#include <algorithm>
#include <cassert>
#include <memory>

using namespace llvm;

#define DEBUG_TYPE "wasm-stack-tagging"

namespace {

class WebAssemblyStackTagging : public FunctionPass {

public:
  static char ID;

  WebAssemblyStackTagging() : FunctionPass(ID) {
    initializeWebAssemblyStackTaggingPass(*PassRegistry::getPassRegistry());
  }

  bool runOnFunction(Function &F) override;

  StringRef getPassName() const override { return "WebAssembly Stack Tagging"; }

private:
  // Function *F = nullptr;
  // Function *NewSegmentStackFunc = nullptr;
  // const DataLayout *DL = nullptr;
  // // AAResults *AA = nullptr;
  // const StackSafetyGlobalInfo *SSI = nullptr;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    // AU.addRequired<StackSafetyGlobalInfoWrapperPass>();
    // if (MergeInit)
    // AU.addRequired<AAResultsWrapperPass>();
  }
};

bool WebAssemblyStackTagging::runOnFunction(Function &F) {
  if (!F.hasFnAttribute(Attribute::SanitizeWasmMemSafety))
    return false;

  DataLayout DL = F.getParent()->getDataLayout();

  SmallVector<AllocaInst *, 8> AllocaInsts;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *Alloca = dyn_cast<AllocaInst>(&I)) {
        LLVM_DEBUG(dbgs() << "Checking alloca: " << *Alloca << "\n");

        // TODO: check which allocas we actually need to protect and which we
        // don't We cannot use Alloca->isArrayAllocation(), as it returns true
        // for [i8 x 16] and some more cases
        AllocaInsts.emplace_back(Alloca);
      }
    }
  }

  auto *NewSegmentStackFunc = Intrinsic::getDeclaration(
      F.getParent(), Intrinsic::wasm_segment_stack_new,
      {Type::getInt32Ty(F.getContext())});

  for (auto *Alloca : AllocaInsts) {
    auto *AllocSize = Alloca->getOperand(0);

    Alloca->setAlignment(std::max(Alloca->getAlign(), Align(16)));
    if (auto *Const = dyn_cast<ConstantInt>(AllocSize)) {
      auto ZextValue = Const->getZExtValue();
      auto AlignedValue = (ZextValue + 15) & ~0xF;
      Alloca->setOperand(0, ConstantInt::get(Const->getType(), AlignedValue));
    } else {
      auto *AddVal = BinaryOperator::CreateAdd(
          AllocSize, ConstantInt::get(AllocSize->getType(), 15));
      AddVal->insertBefore(Alloca);
      auto *AndVal = BinaryOperator::CreateAnd(
          AddVal, ConstantInt::get(AllocSize->getType(), 15), "extended");
      AndVal->insertBefore(Alloca);
      Alloca->setOperand(0, AndVal);
    }

    auto *NewStackSegmentInst =
        CallInst::Create(NewSegmentStackFunc, {Alloca, Alloca->getOperand(0)});
    NewStackSegmentInst->insertAfter(Alloca);

    Alloca->replaceUsesWithIf(NewStackSegmentInst, [&](Use &U) {
      return U.getUser() != NewStackSegmentInst;
    });
  }

  auto *FreeSegmentFunc =
      Intrinsic::getDeclaration(F.getParent(), Intrinsic::wasm_segment_free,
                                {Type::getInt32Ty(F.getContext())});

  for (auto &BB : F) {
    auto *Terminator = BB.getTerminator();

    for (auto *Alloca : AllocaInsts) {
      auto *AllocSize = Alloca->getOperand(0);

      auto *FreeSegmentInst =
          CallInst::Create(FreeSegmentFunc, {Alloca, AllocSize});
      FreeSegmentInst->insertBefore(Terminator);
    }
  }

  return true;
}

} // namespace

char WebAssemblyStackTagging::ID = 0;

INITIALIZE_PASS_BEGIN(WebAssemblyStackTagging, DEBUG_TYPE,
                      "WebAssembly Stack Tagging", false, false)
// INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
// INITIALIZE_PASS_DEPENDENCY(StackSafetyGlobalInfoWrapperPass)
INITIALIZE_PASS_END(WebAssemblyStackTagging, DEBUG_TYPE,
                    "WebAssembly Stack Tagging", false, false)

FunctionPass *llvm::createWebAssemblyStackTaggingPass(bool IsOptNone) {
  return new WebAssemblyStackTagging();
}

#undef DEBUG_TYPE
