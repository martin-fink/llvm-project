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
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IntrinsicsWebAssembly.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/ValueHandle.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/MemoryTaggingSupport.h"
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
  Function *F = nullptr;
  Function *NewSegmentStackFunc = nullptr;
  const DataLayout *DL = nullptr;
  // AAResults *AA = nullptr;
  const StackSafetyGlobalInfo *SSI = nullptr;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    // if (UseStackSafety)
    AU.addRequired<StackSafetyGlobalInfoWrapperPass>();
    // if (MergeInit)
    // AU.addRequired<AAResultsWrapperPass>();
  }
};

bool WebAssemblyStackTagging::runOnFunction(Function &F) {
  if (!F.hasFnAttribute(Attribute::SanitizeWasmMemSafety))
    return false;

  // only do this if we use stack safety
  SSI = &getAnalysis<StackSafetyGlobalInfoWrapperPass>().getResult();
  this->F = &F;
  this->DL = &F.getParent()->getDataLayout();

  memtag::StackInfoBuilder SIB(SSI);
  for (Instruction &I : instructions(F))
    SIB.visit(I);
  memtag::StackInfo &SInfo = SIB.get();

  if (SInfo.AllocasToInstrument.empty())
    return false;

  std::unique_ptr<DominatorTree> DeleteDT;
  DominatorTree *DT = nullptr;
  if (auto *P = getAnalysisIfAvailable<DominatorTreeWrapperPass>())
    DT = &P->getDomTree();

  if (DT == nullptr) {
    DeleteDT = std::make_unique<DominatorTree>(F);
    DT = DeleteDT.get();
  }

  std::unique_ptr<PostDominatorTree> DeletePDT;
  PostDominatorTree *PDT = nullptr;
  if (auto *P = getAnalysisIfAvailable<PostDominatorTreeWrapperPass>())
    PDT = &P->getPostDomTree();

  if (PDT == nullptr) {
    DeletePDT = std::make_unique<PostDominatorTree>(F);
    PDT = DeletePDT.get();
  }

  std::unique_ptr<LoopInfo> DeleteLI;
  LoopInfo *LI = nullptr;
  if (auto *LIWP = getAnalysisIfAvailable<LoopInfoWrapperPass>()) {
    LI = &LIWP->getLoopInfo();
  } else {
    DeleteLI = std::make_unique<LoopInfo>(*DT);
    LI = DeleteLI.get();
  }

  NewSegmentStackFunc = Intrinsic::getDeclaration(
      F.getParent(), Intrinsic::wasm_segment_stack_sp);

  BasicBlock *PrologueBB = nullptr;
  for (auto Alloca : SInfo.AllocasToInstrument) {
    const memtag::AllocaInfo &Info = Alloca.second;
    AllocaInst *AI = Info.AI;

    if (!PrologueBB) {
      PrologueBB = AI->getParent();
      continue;
    }
    PrologueBB = DT->findNearestCommonDominator(PrologueBB, AI->getParent());
  }
  assert(PrologueBB);

  IRBuilder<> IRB(&PrologueBB->front());

  for (auto Alloca : SInfo.AllocasToInstrument) {
    auto AllocSize =
        Alloca.second.AI->getAllocationSize(F.getParent()->getDataLayout());
    if (!AllocSize) {
      errs() << "AllocSize not known:";
      Alloca.second.AI->dump();
      continue;
    }

    Instruction *NewStackSegmentInst = IRB.CreateCall(
        NewSegmentStackFunc,
        {Constant::getIntegerValue(
            IRB.getInt64Ty(), APInt(64, AllocSize->getFixedValue(), false))});
    Alloca.second.AI->replaceAllUsesWith(NewStackSegmentInst);

    // TODO: insert free as well
  }

  return true;
}

} // namespace

char WebAssemblyStackTagging::ID = 0;

INITIALIZE_PASS_BEGIN(WebAssemblyStackTagging, DEBUG_TYPE,
                      "WebAssembly Stack Tagging", false, false)
// INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
INITIALIZE_PASS_DEPENDENCY(StackSafetyGlobalInfoWrapperPass)
INITIALIZE_PASS_END(WebAssemblyStackTagging, DEBUG_TYPE,
                    "WebAssembly Stack Tagging", false, false)

FunctionPass *llvm::createWebAssemblyStackTaggingPass(bool IsOptNone) {
  return new WebAssemblyStackTagging();
}

#undef DEBUG_TYPE
