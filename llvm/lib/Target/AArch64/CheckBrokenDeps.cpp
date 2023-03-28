#include "AArch64.h"
#include "AArch64InstrInfo.h"
#include "AArch64RegisterInfo.h"
#include "MCTargetDesc/AArch64MCTargetDesc.h"
#include "llvm-c/DebugInfo.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/CodeGen/CallingConvLower.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineInstrBundle.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineOperand.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/Register.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/InitializePasses.h"
#include "llvm/MC/MCRegister.h"
#include "llvm/MC/MCRegisterInfo.h"
#include "llvm/Pass.h"
#include "llvm/PassRegistry.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Errc.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <iterator>
#include <list>
#include <memory>
#include <optional>
#include <ostream>
#include <queue>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>

// TODO: remove this
#define MFDEBUG_ENABLED 0
#define PRINT_BROKEN_BY_MIDDLE_END 1

#if MFDEBUG_ENABLED
#define MFDEBUG(X)                                                             \
  do {                                                                         \
    X                                                                          \
  } while (0)
#else
#define MFDEBUG(X)
#endif

using namespace llvm;
// Avoid the std:: qualifier if possible
using std::list;
using std::make_shared;
using std::pair;
using std::shared_ptr;
using std::string;
using std::to_string;
using std::unordered_map;
using std::unordered_set;

namespace llvm {
string getArgRegName(MCRegister Reg) {
  switch (Reg) {
  case AArch64::X0:
  case AArch64::W0:
    return "X0";
  case AArch64::X1:
  case AArch64::W1:
    return "X1";
  case AArch64::X2:
  case AArch64::W2:
    return "X2";
  case AArch64::X3:
  case AArch64::W3:
    return "X3";
  case AArch64::X4:
  case AArch64::W4:
    return "X4";
  case AArch64::X5:
  case AArch64::W5:
    return "X5";
  case AArch64::X6:
  case AArch64::W6:
    return "X6";
  case AArch64::X7:
  case AArch64::W7:
    return "X7";
  default:
    return "unknown";
  }
}

class MachineValue {
private:
  enum Kind {
    Instruction,
    RegisterArgument,
  } Kind;
  union U {
    const MachineInstr *MI;
    MCRegister Reg;

    U(const MachineInstr *MI) : MI(MI) {}
    U(MCRegister Reg) : Reg(Reg) {}
  } U;

public:
  MachineValue(const MachineInstr *MI) : Kind(Instruction), U(MI) {}
  MachineValue(MCRegister Reg) : Kind(RegisterArgument), U(Reg) {}
  ~MachineValue() {}

  void dump() const;

  bool isInstr() const { return this->Kind == Instruction; }
  bool isRegArg() const { return this->Kind == RegisterArgument; }

  const MachineInstr *getMI() const {
    assert(isInstr() && "Called getMI on non-instruction value");
    return U.MI;
  }

  friend raw_ostream &operator<<(raw_ostream &Os, const MachineValue &Val);

  bool operator==(const MachineValue &Other) const {
    if (this->Kind != Other.Kind)
      return false;

    switch (this->Kind) {
    case Instruction:
      return this->U.MI == Other.U.MI;
    case RegisterArgument:
      return this->U.Reg == Other.U.Reg;
    }
    llvm_unreachable("Invalid MachineValue kind");
  }

  bool operator<(const MachineValue &Other) const { return false; }

  size_t hash() const {
    size_t KindHash = std::hash<size_t>()(static_cast<std::size_t>(Kind));
    size_t ValHash = 0;
    switch (Kind) {
    case Instruction:
      ValHash = std::hash<const MachineInstr *>()(U.MI);
      break;
    case RegisterArgument:
      ValHash = std::hash<unsigned>()(U.Reg);
      break;
    }

    return KindHash ^ (ValHash << 1);
  }

  struct HashFunction {
    size_t operator()(const MachineValue &Other) const { return Other.hash(); }
  };
};

void MachineValue::dump() const {
  switch (this->Kind) {
  case Instruction:
    this->U.MI->dump();
    return;
  case RegisterArgument:
    errs() << "  register: " << getArgRegName(this->U.Reg) << "\n";
    return;
  }

  llvm_unreachable("Invalid MachineValue kind");
}

raw_ostream &operator<<(raw_ostream &Os, const MachineValue &Val) {
  switch (Val.Kind) {
  case MachineValue::Kind::Instruction:
    Os << *Val.U.MI;
    break;
  case MachineValue::Kind::RegisterArgument:
    Os << "register: " << getArgRegName(Val.U.Reg) << "\n";
    break;
  }
  return Os;
}

template <> struct DenseMapInfo<MachineValue> {
  static constexpr uintptr_t Log2MaxAlign = 12;

  static inline MachineValue getEmptyKey() {
    uintptr_t Val = static_cast<uintptr_t>(-1);
    Val <<= Log2MaxAlign;
    return MachineValue(reinterpret_cast<MachineInstr *>(Val));
  }

  static inline MachineValue getTombstoneKey() {
    uintptr_t Val = static_cast<uintptr_t>(-2);
    Val <<= Log2MaxAlign;
    return MachineValue(reinterpret_cast<MachineInstr *>(Val));
  }

  static unsigned getHashValue(const MachineValue Val) { return Val.hash(); }

  static bool isEqual(const MachineValue LHS, const MachineValue RHS) {
    return LHS == RHS;
  }
};

using IDReMap = unordered_map<string, unordered_set<string>>;

// Represents a map of IDs to (potential) dependency halfs.
template <typename T> using DepHalfMap = unordered_map<string, T>;

/// Every dep chain link has a DCLevel. The level tracks whether the pointer
/// itself or the pointed-to value, the pointee, is part of the dependency
/// chain.
///
/// PTR   -> we're interested in the pointer itself.  PTE -> we're
/// interested in the pointed-to value.
///
/// BOTH  -> matches PTR __AND__ PTE.
///
/// NORET -> Dep chain doesn't get returned, but calling function should still
/// be made aware of its existence. The calling function then knows that the
/// beginning has been seen, but its dependency chain might have been broken.
///
/// EMPTY -> Empty.
enum class BackendDCLevel { PTR, PTE, BOTH, NORET, EMPTY };

/// Represents a dependency chain link. A dep chain link consists of an IR
/// value and the corresponding dep chain level.
struct BackendDCLink {
  BackendDCLink(MachineValue Val, BackendDCLevel Lvl) : Val(Val), Lvl(Lvl) {}
  MachineValue Val;
  BackendDCLevel Lvl;

  bool operator==(const BackendDCLink &Other) const {
    return Val == Other.Val && Lvl == Other.Lvl;
  }
};

template <> struct DenseMapInfo<BackendDCLink> {
  static inline BackendDCLink getEmptyKey() {
    return BackendDCLink(DenseMapInfo<MachineValue>::getEmptyKey(),
                         BackendDCLevel::EMPTY);
  }

  static inline BackendDCLink getTombstoneKey() {
    return BackendDCLink(DenseMapInfo<MachineValue>::getTombstoneKey(),
                         BackendDCLevel::EMPTY);
  }

  static unsigned getHashValue(const BackendDCLink &Link) {
    return hash_combine(Link.Val.hash(), Link.Lvl);
  }

  static bool isEqual(const BackendDCLink &LHS, const BackendDCLink &RHS) {
    return LHS == RHS;
  }
};
} // namespace llvm

namespace {
static const std::array<MCRegister, 8> AArch64ArgRegs = {
    AArch64::X0, AArch64::X1, AArch64::X2, AArch64::X3,
    AArch64::X4, AArch64::X5, AArch64::X6, AArch64::X7};

#define DEBUG_TYPE "lkmm-dep-checker-backend"

using MachineValueSet = unordered_set<MachineValue, MachineValue::HashFunction>;

using DepChain = SetVector<BackendDCLink>;

using DepChainMap = MapVector<MachineBasicBlock *, DepChain>;

using VerIDSet = unordered_set<string>;

using CallPathStack = list<MachineInstr *>;

using BBtoBBSetMap =
    unordered_map<MachineBasicBlock *, unordered_set<MachineBasicBlock *>>;

SmallVector<StringRef, 5> getLKMMAnnotations(MachineInstr *MI) {
  SmallVector<StringRef, 5> Annotations{};
  MDNode *MDN = MI->getPCSections();
  if (!MDN) {
    return Annotations;
  }

  for (const MDOperand &MDO : MDN->operands()) {
    if (auto *MD = dyn_cast<MDString>(MDO.get())) {
      Annotations.push_back(MD->getString());
    }
  }

  return Annotations;
}

string getInstLocString(MachineValue Val, bool ViaFile = false) {
  if (!Val.isInstr()) {
    return "no location";
  }

  auto *MI = Val.getMI();
  const llvm::DebugLoc &InstDebugLoc = MI->getDebugLoc();

  if (!InstDebugLoc) {
    return "no location";
  }

  auto LAndC = "::" + to_string(InstDebugLoc.getLine()) + ":" +
               to_string(InstDebugLoc.getCol());

  if (ViaFile) {
    return InstDebugLoc.get()->getFilename().str() + LAndC;
  }

  return MI->getParent()->getParent()->getName().str() + LAndC;
}

std::optional<MachineFunction *>
getMachineFunctionFromCall(const MachineInstr *MI) {
  assert(
      MI->isCall() &&
      "Expected getMachineFunctionFromCall to be called on a call instruction");

  auto *MF = MI->getParent()->getParent();
  auto &FunctionOperand = MI->getOperand(0);

  // ignore calls to non-global functions
  // we need to check if ignoring these might be a problem
  if (!FunctionOperand.isGlobal()) {
    return {};
  }

  auto &MMI = MF->getMMI();
  auto *CalledF = MF->getFunction().getParent()->getFunction(
      FunctionOperand.getGlobal()->getName());

  if (CalledF == nullptr) {
    // errs() << "Found no function for call\n";
    // MI->dump();
    return {};
  }

  return &MMI.getOrCreateMachineFunction(*CalledF);
}

string getCalledFunctionName(MachineInstr *MI) {
  if (!MI->isCall()) {
    errs() << "getCalledFunctionName called on non call instruction\n";
    return "";
  }

  auto &FunctionOperand = MI->getOperand(0);
  if (!FunctionOperand.isGlobal()) {
    errs() << "getCalledFunctionName called on invalid call instruction\n";
    return "";
  }

  return FunctionOperand.getGlobal()->getName().str();
}

bool shouldIgnoreInstruction(const MachineInstr *MI) {
  switch (MI->getOpcode()) {
  case AArch64::HINT:
    return true;
  default:
    return false;
  }
}

class RegisterValueMapping {
public:
  RegisterValueMapping(const MachineFunction *MF)
      : RegistersMap(), WorkingSet() {
    if (MF->getFunction().getNumOperands() > AArch64ArgRegs.size()) {
      llvm_unreachable(
          "Unable to handle functions that pass arguments on the stack");
    }

    for (unsigned I = 0; I < MF->getFunction().arg_size(); ++I) {
      auto Reg = AArch64ArgRegs[I];
      WorkingSet[Reg] = {Reg};
    }
  }

  MachineValueSet getValuesForRegisters(MachineInstr *MI);

  MachineValueSet getValuesForRegister(MCRegister Reg, MachineInstr *MI);

  void enterBlock(const MachineBasicBlock *MBB);

  void exitBlock(const MachineBasicBlock *MBB);

  void visitInstruction(const MachineInstr *MI);

  MachineValueSet getPointerOperands(MachineInstr *MI);

  MachineValueSet getValueOperands(MachineInstr *MI);

private:
  std::map<const MachineBasicBlock *, std::map<MCRegister, MachineValueSet>>
      RegistersMap;

  std::map<MCRegister, MachineValueSet> WorkingSet;

  MachineValueSet
  getValuesForRegister(MachineBasicBlock *MBB, MCRegister Reg,
                       MachineInstr *StartBefore = nullptr) const;

  // if map[reg] is not empty, it will be cleared
  void
  getValuesForInstruction(const MachineInstr *MI,
                          std::map<MCRegister, MachineValueSet> &Result) const;

  void getOutgoingValuesForUnvisitedBlock(const MachineBasicBlock *MBB);

  MCRegister getSuperRegister(MCRegister Reg,
                              const TargetRegisterInfo *TRI) const {
    // convert 32 bit registers (W0-W30) to 64 bit registers (X0-X30)
    if (Reg >= AArch64::W0 && Reg <= AArch64::W30) {
      return Reg + (AArch64::X0 - AArch64::W0);
    }

    if (Reg == AArch64::WZR) {
      return AArch64::XZR;
    }

    // don't handle other registers
    return Reg;
  }
};

void RegisterValueMapping::enterBlock(const MachineBasicBlock *MBB) {
  // Make sure RegistersMap[MBB] is initialized so
  // getOutgoingValuesForUnvisitedBlock does not visit it
  RegistersMap[MBB];

  // union of all predecessor values
  for (auto *Pred : MBB->predecessors()) {
    auto OutgoingRegisters = RegistersMap.find(Pred);
    if (OutgoingRegisters == RegistersMap.end()) {
      getOutgoingValuesForUnvisitedBlock(Pred);
      OutgoingRegisters = RegistersMap.find(Pred);
    }
    assert(OutgoingRegisters != RegistersMap.end());

    // copy incoming values
    for (auto &[Reg, Values] : OutgoingRegisters->second) {
      WorkingSet[Reg].insert(Values.begin(), Values.end());
    }
  }
}

void RegisterValueMapping::exitBlock(const MachineBasicBlock *MBB) {
  // TODO: check if we really need to clear or if we can just return if the
  // registers map has already been populated
  RegistersMap[MBB].clear();

  for (auto &[Reg, Vals] : WorkingSet) {
    RegistersMap[MBB][Reg].insert(Vals.begin(), Vals.end());
  }

  WorkingSet.clear();
}

void RegisterValueMapping::getOutgoingValuesForUnvisitedBlock(
    const MachineBasicBlock *MBB) {
  if (RegistersMap.find(MBB) != RegistersMap.end()) {
    return;
  }

  // initialize current block
  RegistersMap[MBB];

  // find values defined in this block
  std::map<MCRegister, MachineValueSet> InBlockDefinedVals{};
  for (auto Iter = MBB->begin(); Iter != MBB->end(); ++Iter) {
    getValuesForInstruction(&*Iter, InBlockDefinedVals);
  }

  // since there might be a path that runs through this block, registers defined
  // in this block also need to be considered as possible incoming values.
  for (auto &[Reg, Vals] : InBlockDefinedVals) {
    RegistersMap[MBB][Reg].insert(Vals.begin(), Vals.end());
  }

  for (auto *Pred : MBB->predecessors()) {
    getOutgoingValuesForUnvisitedBlock(Pred);

    auto PrevVals = RegistersMap.find(Pred);
    assert(PrevVals != RegistersMap.end());

    for (auto &[Reg, Vals] : PrevVals->second) {
      RegistersMap[MBB][Reg].insert(Vals.begin(), Vals.end());
    }
  }

  // handle registers defined in this block, as they overwrite incoming values
  for (auto &[Reg, Vals] : InBlockDefinedVals) {
    RegistersMap[MBB][Reg].clear();
    RegistersMap[MBB][Reg].insert(Vals.begin(), Vals.end());
  }
}

void RegisterValueMapping::getValuesForInstruction(
    const MachineInstr *MI,
    std::map<MCRegister, MachineValueSet> &Result) const {
  auto *TRI = MI->getParent()->getParent()->getSubtarget().getRegisterInfo();

  auto InsertVals = [&](MCRegister Reg, std::optional<MachineValue> Value) {
    auto SuperReg = getSuperRegister(Reg, TRI);

    if (SuperReg == AArch64::XZR) {
      return;
    }

    Result[SuperReg].clear();
    if (Value.has_value()) {
      Result[SuperReg].insert(Value.value());
    }
  };

  /*const AArch64InstrInfo *TII = dyn_cast<AArch64InstrInfo>(
      MI->getParent()->getParent()->getSubtarget().getInstrInfo());

  if (TII->isGPRZero(*MI)) {
    // TODO: check if this works
    for (auto &Op : MI->operands()) {
      if (!Op.isReg() || !Op.isDef()) {
        continue;
      }

      InsertVals(Op.getReg(), {});
    }
  } else */
  if (MI->isCall()) {
    // TODO: handle registers that have been overwritten by function calls
    // (callee-saved)
    auto CalledMFOptional = getMachineFunctionFromCall(MI);
    if (CalledMFOptional.has_value()) {
      auto *CalledMF = *CalledMFOptional;
      auto &CalledF = CalledMF->getFunction();

      auto *RetTy = CalledF.getReturnType();

      if (RetTy->isIntOrPtrTy()) {
        InsertVals(AArch64::X0, MachineValue(AArch64::X0));
      } else if (RetTy->isArrayTy()) {
        if (RetTy->getArrayNumElements() > 2 ||
            !RetTy->getArrayElementType()->isIntOrPtrTy()) {
          errs() << "Unsupported array type: " << *RetTy << "for function"
                 << CalledF.getName().str() << "\n";
          llvm_unreachable("Unsupported array return type");
        }

        for (unsigned I = 0; I < RetTy->getArrayNumElements(); ++I) {
          InsertVals(AArch64::X0 + I, MachineValue(AArch64::X0 + I));
        }
      } else if (!RetTy->isVoidTy()) {
        errs() << "Unsupported return type: " << *RetTy << "for function"
               << CalledF.getName().str() << "\n";
        llvm_unreachable("Unsupported return type");
      }
    }
  } else {
    for (auto &Op : MI->operands()) {
      if (!Op.isReg() || !Op.isDef()) {
        continue;
      }

      InsertVals(Op.getReg(), MI);
    }
  }
}

void RegisterValueMapping::visitInstruction(const MachineInstr *MI) {
  getValuesForInstruction(MI, WorkingSet);
}

MachineValueSet RegisterValueMapping::getValuesForRegister(
    MachineBasicBlock *MBB, MCRegister Reg, MachineInstr *StartBefore) const {
  assert((StartBefore == nullptr || MBB == StartBefore->getParent()) &&
         "StartAt->getParent and passed MBB do not match");

  auto *TRI = MBB->getParent()->getSubtarget().getRegisterInfo();
  Reg = getSuperRegister(Reg, TRI);

  if (auto Vals = WorkingSet.find(Reg); Vals != WorkingSet.end()) {
    return Vals->second;
  }

  return {};
}

MachineValueSet RegisterValueMapping::getValuesForRegisters(MachineInstr *MI) {
  MachineValueSet Deps{};
  for (auto Op : MI->operands()) {
    if (Op.isReg() && MI->readsRegister(Op.getReg())) {
      auto DepsForReg = getValuesForRegister(MI->getParent(), Op.getReg(), MI);
      Deps.insert(DepsForReg.begin(), DepsForReg.end());
    }
  }

  return Deps;
}

MachineValueSet RegisterValueMapping::getValuesForRegister(MCRegister Reg,
                                                           MachineInstr *MI) {
  return getValuesForRegister(MI->getParent(), Reg, MI);
}

MachineValueSet RegisterValueMapping::getValueOperands(MachineInstr *MI) {
  MachineValueSet ValueOperands{};

  switch (MI->getOpcode()) {
  case AArch64::STPDi:
  case AArch64::STPDpost:
  case AArch64::STPDpre:
  case AArch64::STPQi:
  case AArch64::STPQpost:
  case AArch64::STPQpre:
  case AArch64::STPSi:
  case AArch64::STPSpost:
  case AArch64::STPSpre:
  case AArch64::STPWi:
  case AArch64::STPWpost:
  case AArch64::STPWpre:
  case AArch64::STPXi:
  case AArch64::STPXpost:
  case AArch64::STPXpre:
  case AArch64::STRBBpost:
  case AArch64::STRBBpre:
  case AArch64::STRBBroW:
  case AArch64::STRBBroX:
  case AArch64::STRBBui:
  case AArch64::STRBpost:
  case AArch64::STRBpre:
  case AArch64::STRBroW:
  case AArch64::STRBroX:
  case AArch64::STRBui:
  case AArch64::STRDpost:
  case AArch64::STRDpre:
  case AArch64::STRDroW:
  case AArch64::STRDroX:
  case AArch64::STRDui:
  case AArch64::STRHHpost:
  case AArch64::STRHHpre:
  case AArch64::STRHHroW:
  case AArch64::STRHHroX:
  case AArch64::STRHHui:
  case AArch64::STRHpost:
  case AArch64::STRHpre:
  case AArch64::STRHroW:
  case AArch64::STRHroX:
  case AArch64::STRHui:
  case AArch64::STRQpost:
  case AArch64::STRQpre:
  case AArch64::STRQroW:
  case AArch64::STRQroX:
  case AArch64::STRQui:
  case AArch64::STRSpost:
  case AArch64::STRSpre:
  case AArch64::STRSroW:
  case AArch64::STRSroX:
  case AArch64::STRSui:
  case AArch64::STRWpost:
  case AArch64::STRWpre:
  case AArch64::STRWroW:
  case AArch64::STRWroX:
  case AArch64::STRWui:
  case AArch64::STRXpost:
  case AArch64::STRXpre:
  case AArch64::STRXroW:
  case AArch64::STRXroX:
  case AArch64::STRXui:
  case AArch64::STURBBi:
  case AArch64::STURBi:
  case AArch64::STURDi:
  case AArch64::STURHHi:
  case AArch64::STURHi:
  case AArch64::STURQi:
  case AArch64::STURSi:
  case AArch64::STURWi:
  case AArch64::STURXi: {
    auto *TII = static_cast<const AArch64InstrInfo *>(
        MI->getParent()->getParent()->getSubtarget().getInstrInfo());

    unsigned NStoreOperands = TII->isPairedLdSt(*MI) ? 2 : 1;

    for (unsigned I = 0; I < NStoreOperands; ++I) {
      auto Op = MI->getOperand(I + MI->getNumDefs());
      if (Op.isReg()) {
        auto ValsForReg = getValuesForRegister(Op.getReg(), MI);

        ValueOperands.insert(ValsForReg.begin(), ValsForReg.end());
      }
    }

    break;
  }
  }

  return ValueOperands;
}

MachineValueSet RegisterValueMapping::getPointerOperands(MachineInstr *MI) {
  MachineValueSet PointerOperands{};
  switch (MI->getOpcode()) {
  case AArch64::STPDi:
  case AArch64::STPDpost:
  case AArch64::STPDpre:
  case AArch64::STPQi:
  case AArch64::STPQpost:
  case AArch64::STPQpre:
  case AArch64::STPSi:
  case AArch64::STPSpost:
  case AArch64::STPSpre:
  case AArch64::STPWi:
  case AArch64::STPWpost:
  case AArch64::STPWpre:
  case AArch64::STPXi:
  case AArch64::STPXpost:
  case AArch64::STPXpre:
  case AArch64::STRBBpost:
  case AArch64::STRBBpre:
  case AArch64::STRBBroW:
  case AArch64::STRBBroX:
  case AArch64::STRBBui:
  case AArch64::STRBpost:
  case AArch64::STRBpre:
  case AArch64::STRBroW:
  case AArch64::STRBroX:
  case AArch64::STRBui:
  case AArch64::STRDpost:
  case AArch64::STRDpre:
  case AArch64::STRDroW:
  case AArch64::STRDroX:
  case AArch64::STRDui:
  case AArch64::STRHHpost:
  case AArch64::STRHHpre:
  case AArch64::STRHHroW:
  case AArch64::STRHHroX:
  case AArch64::STRHHui:
  case AArch64::STRHpost:
  case AArch64::STRHpre:
  case AArch64::STRHroW:
  case AArch64::STRHroX:
  case AArch64::STRHui:
  case AArch64::STRQpost:
  case AArch64::STRQpre:
  case AArch64::STRQroW:
  case AArch64::STRQroX:
  case AArch64::STRQui:
  case AArch64::STRSpost:
  case AArch64::STRSpre:
  case AArch64::STRSroW:
  case AArch64::STRSroX:
  case AArch64::STRSui:
  case AArch64::STRWpost:
  case AArch64::STRWpre:
  case AArch64::STRWroW:
  case AArch64::STRWroX:
  case AArch64::STRWui:
  case AArch64::STRXpost:
  case AArch64::STRXpre:
  case AArch64::STRXroW:
  case AArch64::STRXroX:
  case AArch64::STRXui:
  case AArch64::STURBBi:
  case AArch64::STURBi:
  case AArch64::STURDi:
  case AArch64::STURHHi:
  case AArch64::STURHi:
  case AArch64::STURQi:
  case AArch64::STURSi:
  case AArch64::STURWi:
  case AArch64::STURXi: {
    auto *TII = static_cast<const AArch64InstrInfo *>(
        MI->getParent()->getParent()->getSubtarget().getInstrInfo());

    unsigned NStoreOperands = TII->isPairedLdSt(*MI) ? 2 : 1;

    for (unsigned I = NStoreOperands + MI->getNumDefs();
         I < MI->getNumOperands(); ++I) {
      auto Op = MI->getOperand(I);
      if (Op.isReg()) {
        auto ValsForReg = getValuesForRegister(Op.getReg(), MI);

        PointerOperands.insert(ValsForReg.begin(), ValsForReg.end());
      }
    }
    break;
  }
  case AArch64::LDPDi:
  case AArch64::LDPDpost:
  case AArch64::LDPDpre:
  case AArch64::LDPQi:
  case AArch64::LDPQpost:
  case AArch64::LDPQpre:
  case AArch64::LDPSWi:
  case AArch64::LDPSWpost:
  case AArch64::LDPSWpre:
  case AArch64::LDPSi:
  case AArch64::LDPSpost:
  case AArch64::LDPSpre:
  case AArch64::LDPWi:
  case AArch64::LDPWpost:
  case AArch64::LDPWpre:
  case AArch64::LDPXi:
  case AArch64::LDPXpost:
  case AArch64::LDPXpre:
  case AArch64::LDRAAindexed:
  case AArch64::LDRAAwriteback:
  case AArch64::LDRABindexed:
  case AArch64::LDRABwriteback:
  case AArch64::LDRBBpost:
  case AArch64::LDRBBpre:
  case AArch64::LDRBBroW:
  case AArch64::LDRBBroX:
  case AArch64::LDRBBui:
  case AArch64::LDRBpost:
  case AArch64::LDRBpre:
  case AArch64::LDRBroW:
  case AArch64::LDRBroX:
  case AArch64::LDRBui:
  case AArch64::LDRDl:
  case AArch64::LDRDpost:
  case AArch64::LDRDpre:
  case AArch64::LDRDroW:
  case AArch64::LDRDroX:
  case AArch64::LDRDui:
  case AArch64::LDRHHpost:
  case AArch64::LDRHHpre:
  case AArch64::LDRHHroW:
  case AArch64::LDRHHroX:
  case AArch64::LDRHHui:
  case AArch64::LDRHpost:
  case AArch64::LDRHpre:
  case AArch64::LDRHroW:
  case AArch64::LDRHroX:
  case AArch64::LDRHui:
  case AArch64::LDRQl:
  case AArch64::LDRQpost:
  case AArch64::LDRQpre:
  case AArch64::LDRQroW:
  case AArch64::LDRQroX:
  case AArch64::LDRQui:
  case AArch64::LDRSBWpost:
  case AArch64::LDRSBWpre:
  case AArch64::LDRSBWroW:
  case AArch64::LDRSBWroX:
  case AArch64::LDRSBWui:
  case AArch64::LDRSBXpost:
  case AArch64::LDRSBXpre:
  case AArch64::LDRSBXroW:
  case AArch64::LDRSBXroX:
  case AArch64::LDRSBXui:
  case AArch64::LDRSHWpost:
  case AArch64::LDRSHWpre:
  case AArch64::LDRSHWroW:
  case AArch64::LDRSHWroX:
  case AArch64::LDRSHWui:
  case AArch64::LDRSHXpost:
  case AArch64::LDRSHXpre:
  case AArch64::LDRSHXroW:
  case AArch64::LDRSHXroX:
  case AArch64::LDRSHXui:
  case AArch64::LDRSWl:
  case AArch64::LDRSWpost:
  case AArch64::LDRSWpre:
  case AArch64::LDRSWroW:
  case AArch64::LDRSWroX:
  case AArch64::LDRSWui:
  case AArch64::LDRSl:
  case AArch64::LDRSpost:
  case AArch64::LDRSpre:
  case AArch64::LDRSroW:
  case AArch64::LDRSroX:
  case AArch64::LDRSui:
  case AArch64::LDRWl:
  case AArch64::LDRWpost:
  case AArch64::LDRWpre:
  case AArch64::LDRWroW:
  case AArch64::LDRWroX:
  case AArch64::LDRWui:
  case AArch64::LDRXl:
  case AArch64::LDRXpost:
  case AArch64::LDRXpre:
  case AArch64::LDRXroW:
  case AArch64::LDRXroX:
  case AArch64::LDRXui:
  case AArch64::LDR_PXI:
  case AArch64::LDR_ZA:
  case AArch64::LDR_ZXI:
  case AArch64::LDURBBi:
  case AArch64::LDURBi:
  case AArch64::LDURDi:
  case AArch64::LDURHHi:
  case AArch64::LDURHi:
  case AArch64::LDURQi:
  case AArch64::LDURSBWi:
  case AArch64::LDURSBXi:
  case AArch64::LDURSHWi:
  case AArch64::LDURSHXi:
  case AArch64::LDURSWi:
  case AArch64::LDURSi:
  case AArch64::LDURWi:
  case AArch64::LDURXi: {
    auto Vals = getValuesForRegisters(MI);
    PointerOperands.insert(Vals.begin(), Vals.end());
    break;
  }
  case AArch64::HINT:
  case AArch64::INLINEASM:
  case AArch64::INLINEASM_BR:
    break;
  default:
    errs() << "unhandled instruction:";
    MI->dump();
    llvm_unreachable("Unhandled load/store instruction");
  }

  return PointerOperands;
}

class DepHalf {
public:
  enum DepKind {
    DK_AddrBeg,
    DK_VerAddrBeg,
    DK_VerAddrEnd,
  };

  string getID() const;

  string getPathToViaFiles() const { return PathToViaFiles; }

  string getPathFrom() const { return PathFrom; }

  void setPathFrom(string P) { PathFrom = P; }

  void addStepToPathFrom(MachineInstr *FCall, bool R = false) {
    auto CalledF = getMachineFunctionFromCall(FCall);

    if (CalledF.has_value())
      PathFrom += (getInstLocString(FCall) + (R ? "<-" : "->") +
                   CalledF.value()->getName().str() + "()\n");
  }

  void resetPathFromTo(MachineInstr *MI) {
    auto Ind = PathFrom.find(getInstLocString(MI));

    if (Ind != string::npos)
      PathFrom.erase(Ind);
  }

  DepKind getKind() const { return Kind; }

  bool isBrokenByMiddleEnd() const { return BrokenByMiddleEnd; }

protected:
  MachineInstr *const MI;

  const string ID;

  const string PathToViaFiles;

  string PathFrom;

  bool BrokenByMiddleEnd;

  DepHalf(MachineInstr *MI, string ID, string PathToViaFiles, DepKind Kind,
          bool BrokenByMiddleEnd)
      : MI(MI), ID(ID), PathToViaFiles(PathToViaFiles), PathFrom("\n"),
        BrokenByMiddleEnd(BrokenByMiddleEnd), Kind(Kind){};

  virtual ~DepHalf() {}

private:
  DepKind Kind;
};

class PotAddrDepBeg : public DepHalf {
public:
  PotAddrDepBeg(MachineInstr *MI, string ID, string PathToViaFiles, DepChain DC,
                bool BrokenByMiddleEnd, MachineBasicBlock *MBB)
      : DepHalf(MI, ID, PathToViaFiles, DK_AddrBeg, BrokenByMiddleEnd), DCM{} {
    DCM.insert(pair{MBB, DC});
  }

  /// Checks whether a DepChainPair is currently at a given BB.
  ///
  /// \param BB the BB to be checked.
  ///
  /// \returns true if the PotAddrDepBeg has dep chains at \p BB.
  bool isAt(MachineBasicBlock *MBB) const { return DCM.find(MBB) != DCM.end(); }

  DepChain *getDCsAt(MachineBasicBlock *MBB) {
    if (isAt(MBB))
      return &DCM[MBB];

    return nullptr;
  }

  /// Removes a dep chain link in all dep chains at a given BB.
  ///
  /// \param BB the BB in question.
  void removeLinkFromDCs(MachineBasicBlock *MBB, BackendDCLink DCL) {
    if (!isAt(MBB))
      return;

    DCM[MBB].remove(DCL);
  }

  /// Checks whether this PotAddrDepBeg begins at a given instruction.
  ///
  /// \param I the instruction to be checked.
  ///
  /// \returns true if \p this begins at \p I.
  bool beginsAt(MachineInstr *MI) const { return MI == this->MI; }

  /// Checks whether all DepChains of this PotAddrDepBeg are at a given
  /// BasicBlock. Useful for interprocedural analysis as it helps determine
  /// whether this PotAddrDepBeg can be completed as a full dependency in a
  /// called function.
  ///
  /// \param BB the BB to be checked.
  ///
  /// \returns true if all DepChains are at \p BB.
  bool areAllDepChainsAt(MachineBasicBlock *MBB) {
    if (!isAt(MBB))
      return false;

    return DCM.find(MBB) != DCM.end() && DCM.size() == 1;
  };

  /// Updates the dep chain map after the BFS has visitied a given BB with a
  /// given succeeding BB.
  ///
  /// \param BB the BB the BFS just visited.
  /// \param SBB one of BB's successors.
  /// \param BEDsForBB the back edge destination map.
  void progressDCPaths(MachineBasicBlock *MBB, MachineBasicBlock *SMBB,
                       BBtoBBSetMap &BEDsForBB);

  /// Tries to delete DepChains if possible. Needed for a), keeping track of
  /// how
  /// many DepChains are still valid, and b), saving space.
  ///
  /// \param BB the BB the BFS just visited.
  /// \param BEDsForBB the back edge destination for \p BB.
  void deleteDCsAt(MachineBasicBlock *MBB,
                   unordered_set<MachineBasicBlock *> &BEDs);

  /// Tries to add a value to the union of all dep chains at \p BB.
  ///
  /// \param BB the BB to whose dep chain union \p V should be added.
  /// \param V the value to be added.
  void addToDCUnion(MachineBasicBlock *MBB, BackendDCLink DCL);

  /// Tries to continue the DepChain with a new value.
  ///
  /// \param I the instruction which is currently being checked.
  /// \param ValCmp the value which might or might not be part of a DepChain.
  /// \param ValAdd the value to add if \p ValCmp is part of a DepChain.
  void tryAddValueToDepChains(RegisterValueMapping &RegisterValueMap,
                              MachineInstr *MI, BackendDCLink DCLAdd,
                              BackendDCLink DCLCmp);

  /// Checks if a value is part of any dep chain of an addr dep beginning.
  ///
  /// \param BB the BB the BFS is currently at.
  /// \param VCmp the value which might or might not be part of a dep chain.
  ///
  /// \returns true if \p VCmp belongs to at least one of the beginning's dep
  ///  chains.
  bool belongsToDepChain(MachineBasicBlock *MBB, BackendDCLink DCLCmp);

  /// Annotates an address dependency from a given ending to this beginning.
  ///
  /// \param ID2 the ID of the ending.
  /// \param I2 the instruction where the address dependency ends.
  /// \param FDep set to true if this is a full address
  ///  dependency.
  // void addAddrDep(string ID2, string PathToViaFiles2,
  //                 MachineInstr *MI2, bool FDep) const;

  /// Resets the dep chain map completely, i.e. clear it, or to a given BB.
  ///
  /// \param ToBB optional BB to which the dep chain map should be reset.
  void resetDCM(MachineBasicBlock *ToBB = nullptr) {
    DCM.clear();

    if (ToBB)
      DCM.insert({ToBB, DepChain{}});
  }

  /// Returns true if the DepChainMap is completely empty. This is useful for
  /// determining whether a dependency has started in the current function or
  /// was carried over from a previous function where its dependency chain
  /// didn't run into any of the function call's arguments, in which case its
  /// DepChainMap will be completely empty.
  ///
  /// \Returns true if the DepChainMap is completely empty.
  bool isDepChainMapEmpty() { return DCM.empty(); }

  static bool classof(const DepHalf *VDH) {
    return VDH->getKind() == DK_AddrBeg;
  }

  void printDepChainAt(MachineBasicBlock *MBB) {
    auto BBIt = DCM.find(MBB);

    if (BBIt == DCM.end())
      return;

    auto &DCU = BBIt->second;

    errs() << "printing DCUnion\n";
    for (auto &DCL : DCU) {
      errs() << DCL.Val;
      errs() << (DCL.Lvl == BackendDCLevel::PTE ? " PTE " : " PTR ") << "\n";
    }
  }

private:
  DepChainMap DCM;

  friend class PotCtrlDepBeg;

  /// Helper function for progressDCPaths(). Used for computing an
  /// intersection
  /// of dep chains.
  ///
  /// \param DCs the list of (BasicBlock, DepChain) pairs wheere the DCs
  /// might
  ///  all contain \p V
  /// \param V the value to be checked.
  ///
  /// \returns true if \p V is present in all of \p DCs' dep chains.
  bool depChainsShareLink(list<pair<MachineBasicBlock *, DepChain *>> &DCs,
                          const BackendDCLink &DCL) const;
};

void PotAddrDepBeg::progressDCPaths(MachineBasicBlock *BB,
                                    MachineBasicBlock *SBB,
                                    BBtoBBSetMap &BEDsForBB) {
  if (!isAt(BB)) {
    return;
  }

  if (!isAt(SBB)) {
    DCM.insert(pair{SBB, DepChain{}});
  }

  auto &SDC = DCM[SBB];

  // BB might not be the only predecessor of SBB. Build a list of
  // all preceeding dep chains.
  list<pair<MachineBasicBlock *, DepChain *>> PDCs;

  // Populate PDCs and DCUnion.
  for (auto *Pred : SBB->predecessors()) {
    // If Pred is connected to SBB via a back edge, skip.
    if (BEDsForBB.at(Pred).find(SBB) != BEDsForBB.at(Pred).end())
      continue;

    // If the DepChain don't run through Pred, skip.
    if (!isAt(Pred))
      continue;

    // Previous, i.e. Pred's, DepChain.
    auto &PDC = DCM[Pred];

    // Insert preceeding DCunion into succeeding DCUnion.
    // => union of all preceeding unions.
    SDC.insert(PDC.begin(), PDC.end());
  }

  // If PDCs is empty, we are at the function entry:
  if (PDCs.empty()) {
    // 1. Intiialise PDCs with current DCUnion.
    SDC.insert(DCM[BB].begin(), DCM[BB].end());

    // 2. Initialise SDCP's DCUnion with the current DCUnion.
    PDCs.emplace_back(BB, &DCM[BB]);
  }
}

void PotAddrDepBeg::deleteDCsAt(MachineBasicBlock *MBB,
                                unordered_set<MachineBasicBlock *> &BEDs) {
  if (!isAt(MBB)) {
    return;
  }

  // get first terminator
  // TODO: check if this terminator check works
  auto TerminatorInst = MBB->getFirstInstrTerminator();
  if (!BEDs.empty() ||
      (!TerminatorInst.isEnd() && TerminatorInst->isReturn())) {
    // Keep the entry in DCM to account for 'dead' DepChain, but clear
    // them to save space.
    DCM[MBB].clear();
  } else {
    // If there's no dead DepChain, erase the DCM entry for the current BB.
    DCM.erase(MBB);
  }
}

void PotAddrDepBeg::addToDCUnion(llvm::MachineBasicBlock *MBB,
                                 BackendDCLink DCL) {
  if (!isAt(MBB)) {
    return;
  }

  DCM[MBB].insert(DCL);
}

void PotAddrDepBeg::tryAddValueToDepChains(
    RegisterValueMapping &RegisterValueMap, MachineInstr *MI,
    BackendDCLink DCLAdd, BackendDCLink DCLCmp) {
  // FIXME: How can this check be made redundant?
  assert(DCLAdd.Lvl != BackendDCLevel::BOTH &&
         "Called tryAddLinkToDepChains() with invalid level for DCAdd.");

  if (DCLCmp.Lvl == BackendDCLevel::BOTH) {
    // FIXME: Check DCAdd's level here?
    tryAddValueToDepChains(RegisterValueMap, MI, DCLAdd,
                           BackendDCLink{DCLCmp.Val, BackendDCLevel::PTR});
    tryAddValueToDepChains(RegisterValueMap, MI, DCLAdd,
                           BackendDCLink{DCLCmp.Val, BackendDCLevel::PTE});
    return;
  }

  if (!isAt(MI->getParent())) {
    return;
  }

  auto &DC = DCM[MI->getParent()];

  if (DC.contains(DCLCmp))
    DC.insert(DCLAdd);
}

bool PotAddrDepBeg::belongsToDepChain(llvm::MachineBasicBlock *MBB,
                                      BackendDCLink DCLCmp) {
  // FIXME: How can we make this redundant?
  assert(DCLCmp.Lvl != BackendDCLevel::BOTH &&
         "Called belongsToDepChain() with DCLevel::BOTH.");

  if (!isAt(MBB))
    return false;

  auto &DC = DCM[MBB];

  return DC.contains(DCLCmp);
}

bool PotAddrDepBeg::depChainsShareLink(
    list<pair<MachineBasicBlock *, DepChain *>> &DCs,
    const BackendDCLink &DCL) const {
  for (auto &DCP : DCs)
    if (DCP.second->contains(DCL))
      return false;

  return true;
}

class VerDepHalf : public DepHalf {
public:
  enum BrokenByType { BrokenDC, ParToFull };

  void setBrokenBy(BrokenByType BB) { BrokenBy = BB; }

  string getBrokenBy() {
    switch (BrokenBy) {
    case BrokenDC:
      return "by breaking the dependency chain";
    case ParToFull:
      return "by converting a partial dependency to a full dependency";
    }
  }

  string const &getParsedDepHalfID() const { return ParsedDepHalfID; }

  string const &getParsedpathTOViaFiles() const { return ParsedPathToViaFiles; }

  MachineInstr *const &getInst() const { return MI; };

  virtual ~VerDepHalf(){};

  static bool classof(const DepHalf *VDH) {
    return VDH->getKind() >= DK_VerAddrBeg && VDH->getKind() <= DK_VerAddrEnd;
  }

  string const &getParsedID() const { return ParsedID; }

protected:
  VerDepHalf(MachineInstr *MI, string ParsedID, string DepHalfID,
             string PathToViaFiles, string ParsedDepHalfID,
             string ParsedPathToViaFiles, DepKind Kind, bool BrokenByMiddleEnd)
      : DepHalf(MI, DepHalfID, PathToViaFiles, Kind, BrokenByMiddleEnd),
        ParsedID(ParsedID),
        ParsedDepHalfID(ParsedDepHalfID), ParsedPathToViaFiles{
                                              ParsedPathToViaFiles} {}

private:
  // Shows how this dependency got broken
  BrokenByType BrokenBy;

  // The ID which identifies the two metadata annotations for this dependency.
  const string ParsedID;

  // The PathTo which was attached to the metadata annotation, i.e. the
  // path to I in unoptimised IR.
  const string ParsedDepHalfID;

  const string ParsedPathToViaFiles;
};

class VerAddrDepBeg : public VerDepHalf {
public:
  VerAddrDepBeg(MachineInstr *MI, string ParsedID, string DepHalfID,
                string PathToViaFiles, string ParsedPathTo,
                string ParsedPathToViaFiles, bool BrokenByMiddleEnd)
      : VerDepHalf(MI, ParsedID, DepHalfID, PathToViaFiles, ParsedPathTo,
                   ParsedPathToViaFiles, DK_VerAddrBeg, BrokenByMiddleEnd) {}

  static bool classof(const DepHalf *VDH) {
    return VDH->getKind() == DK_VerAddrBeg;
  }

  void setDCP(DepChain DC) { this->DC = DC; }
  DepChain &getDC() { return DC; }

private:
  DepChain DC;
};

string DepHalf::getID() const {
  if (isa<PotAddrDepBeg>(this))
    return ID;
  if (const auto *VDH = dyn_cast<VerDepHalf>(this))
    return VDH->getParsedID();
  llvm_unreachable("unhandled case in getID");
}

void findMachineFunctionBackedges(
    const MachineFunction &MF,
    SmallVectorImpl<pair<const MachineBasicBlock *, const MachineBasicBlock *>>
        &Result) {
  const MachineBasicBlock *MBB = &*MF.begin();
  if (MBB->succ_empty()) {
    return;
  }

  SmallPtrSet<const MachineBasicBlock *, 8> Visited;
  SmallVector<
      pair<const MachineBasicBlock *, MachineBasicBlock::const_succ_iterator>,
      8>
      VisitStack;
  SmallPtrSet<const MachineBasicBlock *, 8> InStack;

  Visited.insert(MBB);
  VisitStack.push_back(std::make_pair(MBB, MBB->succ_begin()));
  InStack.insert(MBB);
  do {
    pair<const MachineBasicBlock *, MachineBasicBlock::const_succ_iterator>
        &Top = VisitStack.back();
    const MachineBasicBlock *ParentMBB = Top.first;
    MachineBasicBlock::const_succ_iterator &Iter = Top.second;

    bool FoundNew = false;
    while (Iter != ParentMBB->succ_end()) {
      MBB = *Iter++;
      if (Visited.insert(MBB).second) {
        FoundNew = true;
        break;
      }
      // Successor is in VisitStack, it's a back edge.
      if (InStack.count(MBB)) {
        Result.push_back(std::make_pair(ParentMBB, MBB));
      }
    }

    if (FoundNew) {
      // Go down one level if there is a unvisited successor.
      InStack.insert(MBB);
      VisitStack.push_back(std::make_pair(MBB, MBB->succ_begin()));
    } else {
      // Go up one level.
      InStack.erase(VisitStack.pop_back_val().first);
    }

  } while (!VisitStack.empty());
}

class VerAddrDepEnd : public VerDepHalf {
public:
  VerAddrDepEnd(MachineInstr *MI, string ParsedID, string DepHalfID,
                string PathToViaFiles, string ParsedDepHalfID,
                string ParsedPathToViaFiles, bool BrokenByMiddleEnd)
      : VerDepHalf(MI, ParsedID, DepHalfID, PathToViaFiles, ParsedDepHalfID,
                   ParsedPathToViaFiles, DK_VerAddrEnd, BrokenByMiddleEnd) {}

  static bool classof(const DepHalf *VDH) {
    return VDH->getKind() == DK_VerAddrEnd;
  }
};

struct BFSBBInfo {
  // The BB the two fields below relate to.
  MachineBasicBlock *MBB;

  // Denotes the amount of predeceessors which must be visited before the BFS
  // can look at 'BB'.
  unsigned MaxHits;

  // Denotes the amount of predecessors the BFS has already seen (or how many
  // times 'BB' has been 'hit' by an edge from a predecessor).
  unsigned CurrentHits;

  BFSBBInfo(MachineBasicBlock *MBB, unsigned MaxHits)
      : MBB(MBB), MaxHits(MaxHits), CurrentHits(0) {}
};

struct InterprocRetAddrDep {
  /// Discriminator for LLVM-style RTTI (dyn_cast<> et al.)
  enum IRADBKind { IRADBKind_Overwritten, IRADBKind_Returned };

  PotAddrDepBeg ADB;

  InterprocRetAddrDep(PotAddrDepBeg &ADB, IRADBKind Kind)
      : ADB(ADB), Kind(Kind) {}

  IRADBKind getKind() const { return Kind; }

private:
  const IRADBKind Kind;
};

struct ReturnedADB : InterprocRetAddrDep {
  BackendDCLevel Lvl;
  bool DiscoveredInInterproc;

  ReturnedADB(PotAddrDepBeg ADB, BackendDCLevel Lvl, bool DiscoveredInInterproc)
      : InterprocRetAddrDep(ADB, IRADBKind_Returned), Lvl(Lvl),
        DiscoveredInInterproc(DiscoveredInInterproc) {}

  static bool classof(const InterprocRetAddrDep *IRADB) {
    return IRADB->getKind() == IRADBKind_Returned;
  }
};

struct OverwrittenADB : InterprocRetAddrDep {
  OverwrittenADB(PotAddrDepBeg &ADB)
      : InterprocRetAddrDep(ADB, IRADBKind_Overwritten) {}

  static bool classof(const InterprocRetAddrDep *IRADB) {
    return IRADB->getKind() == IRADBKind_Overwritten;
  }
};

// FIXME: Make this a unique_ptr. Requires at least a custom copy constructor
// for BFSCtx (Rule of X).
using InterprocBFSRes = list<shared_ptr<InterprocRetAddrDep>>;

class BFSCtx {
public:
  // TODO: make sure MBB is always the first basic block
  BFSCtx(MachineBasicBlock *MBB,
         shared_ptr<DepHalfMap<VerAddrDepBeg>> BrokenADBs,
         shared_ptr<DepHalfMap<VerAddrDepEnd>> BrokenADEs,
         shared_ptr<IDReMap> RemappedIDs, shared_ptr<VerIDSet> VerifiedIDs)
      : MBB(MBB), ADBs(), ADBsToBeReturned(), CallPath(CallPathStack()),
        InheritedADBs(), RegisterValueMap(MBB->getParent()),
        BrokenADBs(BrokenADBs), BrokenADEs(BrokenADEs),
        RemappedIDs(RemappedIDs), VerifiedIDs(VerifiedIDs), OutsideIDs() {}

  BFSCtx(BFSCtx &Ctx, MachineBasicBlock *MBB, MachineInstr *CallInstr)
      : BFSCtx(Ctx) {
    ADBsToBeReturned.clear();

    prepareInterproc(MBB, CallInstr);

    this->MBB = MBB;
  }

  void runBFS();

private:
  MachineBasicBlock *MBB;

  DepHalfMap<PotAddrDepBeg> ADBs;

  // Potential beginnings where the return value is part of the DepChain.
  InterprocBFSRes ADBsToBeReturned;

  CallPathStack CallPath;

  unordered_set<string> InheritedADBs;

  RegisterValueMapping RegisterValueMap;

  void buildBackEdgeMap(BBtoBBSetMap *BEDsForBB, MachineFunction *MF);

  void buildBFSInfo(unordered_map<MachineBasicBlock *, BFSBBInfo> *BFSInfo,
                    BBtoBBSetMap *BEDsForBB, MachineFunction *MF);

  void removeBackEdgesFromSuccessors(
      MachineBasicBlock *MBB, unordered_set<MachineBasicBlock *> *BEDs,
      unordered_set<MachineBasicBlock *> *SuccessorsWOBackEdges);

  bool bfsCanVisit(MachineBasicBlock *MBB,
                   unordered_map<MachineBasicBlock *, BFSBBInfo> &BFSInfo,
                   unordered_set<MachineBasicBlock *> &BEDs);

  void progressAddrDepDCPaths(MachineBasicBlock *MBB, MachineBasicBlock *SBB,
                              BBtoBBSetMap &BEDsForBB);

  void deleteAddrDepDCsAt(MachineBasicBlock *MBB,
                          unordered_set<MachineBasicBlock *> &BEDs);

  void visitBasicBlock(MachineBasicBlock *MBB);

  void visitInstruction(MachineInstr *MI);

  void handleCallInst(MachineInstr *MI);

  void handleLoadStoreInst(MachineInstr *MI);

  void handleBranchInst(MachineInstr *MI);

  void handleReturnInst(MachineInstr *MI);

  void handleInlineAsmInst(MachineInstr *MI);

  void handleInstruction(MachineInstr *MI);

  void handleDependentFunctionArgs(MachineInstr *CallInstr,
                                   MachineBasicBlock *MBB);

  void prepareInterproc(MachineBasicBlock *MBB, MachineInstr *CallInstr);

  InterprocBFSRes runInterprocBFS(MachineBasicBlock *FirstMBB,
                                  MachineInstr *CallInstr);

  /// Helper function for handleDependentFunctionArgs(). Finds all args which
  /// are part of the dep chains of \p ADB.
  ///
  /// \param ADB the PotAddrDepBeg in question.
  /// \param CallI the call instruction whose arguments should be checked
  ///  against \p ADB's dep chains.
  /// \param DepArgsDCUnion the set which will contain all dependent function
  ///  arguments on return.
  void
  findDependentArgs(PotAddrDepBeg &ADB, MachineInstr *CallB,
                    SmallVectorImpl<pair<int, BackendDCLevel>> *DepArgsDCUnion);

  // verification methods and properties

  // Contains all unverified address dependency beginning annotations.
  shared_ptr<DepHalfMap<VerAddrDepBeg>> BrokenADBs;
  // Contains all unverified address dependency ending annotations.
  shared_ptr<DepHalfMap<VerAddrDepEnd>> BrokenADEs;

  // All remapped IDs which were discovered from the current root function.
  shared_ptr<IDReMap> RemappedIDs;

  // Contains all IDs which have been verified in the current module.
  shared_ptr<VerIDSet> VerifiedIDs;

  /// IDs of PotAddrDepBeg's which have been visited, but don't run into the
  /// current function.
  unordered_set<string> OutsideIDs;

  void handleDepAnnotations(MachineInstr *MI,
                            SmallVector<StringRef, 5> Annotations);

  bool parseDepHalfString(StringRef Annot, SmallVectorImpl<string> &AnnotData);

  // bool handleAddrDepID(string const &ID, MachineInstr *MI,
  //                      string &ParsedDepHalfID,
  //                      string &ParsedPathToViaFiles, bool
  //                      ParsedFullDep);

  void updateID(string &ID) {
    if (RemappedIDs->find(ID) == RemappedIDs->end()) {
      RemappedIDs->emplace(ID, unordered_set<string>{ID + "-#1"});
      ID = ID + "-#1";
    } else {
      auto S = RemappedIDs->at(ID).size();
      RemappedIDs->at(ID).insert(ID + "-#" + to_string(S + 1));
      ID = ID + "-#" + to_string(S + 1);
    }
  }

  void markIDAsVerified(const string &ParsedID) {
    BrokenADBs->erase(ParsedID);
    BrokenADEs->erase(ParsedID);

    if (auto IDs = this->RemappedIDs->find(ParsedID);
        IDs != this->RemappedIDs->end()) {
      for (auto const &RemappedID : IDs->second) {
        BrokenADBs->erase(RemappedID);
        BrokenADEs->erase(RemappedID);
      }
    }

    VerifiedIDs->insert(ParsedID);
    RemappedIDs->erase(ParsedID);
  }

  void addToOutsideIDs(string ID) { OutsideIDs.insert(ID); }

  void addBrokenEnding(VerAddrDepBeg VADB, VerAddrDepEnd VADE, DepChain DC,
                       VerDepHalf::BrokenByType BrokenBy) {
    VADB.setDCP(DC);

    VADE.setBrokenBy(BrokenBy);

    BrokenADEs->emplace(VADB.getID(), std::move(VADE));
  }

  bool isADBBroken(string const &ID, MachineInstr *MI, string &ParsedPathTo,
                   string &ParsedPathToViaFiles);

  /// Shared functionality for dep chains running through instructions.
  ///
  /// \param MI the instruction to be handled.
  /// \param DCLAdd the new link which would be added to the dependency chain.
  /// \param DCLCmps the links which adding DCLAdd to the dep chain depends on.
  void depChainThroughInst(MachineInstr *MI, BackendDCLink DCLAdd,
                           SmallVector<BackendDCLink, 6> DCLCmps) {
    for (auto &ADBP : ADBs) {
      auto &ADB = ADBP.second;

      // Check whether all cmp links are part of the dep chains in ADB.
      for (auto DCLCmp : DCLCmps)
        ADB.tryAddValueToDepChains(RegisterValueMap, MI, DCLAdd, DCLCmp);
    }
  }

  bool storeOverwritesDCValue(MachineInstr *MI, PotAddrDepBeg &ADB);

  // helper methods

  unsigned recLevel() { return CallPath.size(); }

  constexpr unsigned recLimit() const { return 4; }

  string getFullPath(MachineInstr *MI, bool ViaFiles = false) {
    return convertPathToString(ViaFiles) + getInstLocString(MI, ViaFiles);
  }

  string getFullPathViaFiles(MachineInstr *MI) {
    return convertPathToString() + getInstLocString(MI);
  }

  string convertPathToString(bool ViaFiles = false) {
    string PathStr{""};

    for (auto &CallI : CallPath)
      PathStr += (getInstLocString(CallI, ViaFiles) + "  ");

    return PathStr;
  }

  string buildInlineString(MachineInstr *MI);

  void addToInheritedADBs(string ID) { InheritedADBs.emplace(ID); }
};

void BFSCtx::runBFS() {
  // MBB might be null when runBFS gets called for a function with external
  // linkage for example
  if (!MBB)
    return;

  LLVM_DEBUG(dbgs() << "Running BFS on machine function "
                    << MBB->getParent()->getName().str() << "\n";);

  BBtoBBSetMap BEDsForBB;

  buildBackEdgeMap(&BEDsForBB, MBB->getParent());

  unordered_map<MachineBasicBlock *, BFSBBInfo> BFSInfo;

  buildBFSInfo(&BFSInfo, &BEDsForBB, MBB->getParent());

  std::queue<MachineBasicBlock *> BFSQueue = {};

  BFSQueue.push(MBB);

  while (!BFSQueue.empty()) {
    auto &MBB = BFSQueue.front();

    visitBasicBlock(MBB);

    unordered_set<MachineBasicBlock *> SuccessorsWOBackEdges{};

    removeBackEdgesFromSuccessors(MBB, &BEDsForBB.at(MBB),
                                  &SuccessorsWOBackEdges);

    for (auto &SBB : SuccessorsWOBackEdges) {
      if (bfsCanVisit(SBB, BFSInfo, BEDsForBB.at(SBB))) {
        BFSQueue.push(SBB);
      }

      progressAddrDepDCPaths(MBB, SBB, BEDsForBB);
    }

    deleteAddrDepDCsAt(MBB, BEDsForBB.at(MBB));

    BFSQueue.pop();
  }
}

void BFSCtx::handleDependentFunctionArgs(MachineInstr *CallInstr,
                                         MachineBasicBlock *FirstBB) {
  SmallVector<pair<int, BackendDCLevel>, 12> DepArgIndices;
  auto CalledMF = getMachineFunctionFromCall(CallInstr);
  if (!CalledMF)
    return;

  Function &CalledF = CalledMF.value()->getFunction();
  if (CalledF.arg_size() > AArch64ArgRegs.size()) {
    errs() << "Unable to handle function with arguments passed on stack\n";
    return;
  }

  for (auto It = ADBs.begin(); It != ADBs.end();) {
    auto &ID = It->first;
    auto &ADB = It->second;

    findDependentArgs(ADB, CallInstr, &DepArgIndices);

    // FIXME: Make this nicer
    if (!DepArgIndices.empty()) {
      if (FirstBB) {
        ADB.addStepToPathFrom(CallInstr);

        ADB.resetDCM(FirstBB);

        for (auto &[Index, Level] : DepArgIndices)
          ADB.addToDCUnion(
              FirstBB,
              BackendDCLink(MachineValue(AArch64ArgRegs[Index]), Level));

        addToInheritedADBs(ID);
        ++It;
      } else {
        // Mark dependencies through external or empty functions as trivially
        // verified in VerCtx
        markIDAsVerified(ID);
        ++It;
      }
    } else {
      // FIXME: Are we using outsideIDs?
      // If we don't have any dependent arguments, we can remove the ADB
      addToOutsideIDs(ID);

      // All PotAddrDepBeg's which don't run into the function are removed from
      // ADBs
      auto Del = It++;
      ADBs.erase(Del);
    }

    DepArgIndices.clear();
  }
}

void BFSCtx::prepareInterproc(MachineBasicBlock *MBB, MachineInstr *CallInstr) {
  handleDependentFunctionArgs(CallInstr, MBB);

  CallPath.push_back(CallInstr);

  if (MBB != nullptr) {
    this->RegisterValueMap = RegisterValueMapping(MBB->getParent());
  }
}

InterprocBFSRes BFSCtx::runInterprocBFS(MachineBasicBlock *FirstMBB,
                                        MachineInstr *CallInstr) {
  BFSCtx InterprocCtx = BFSCtx(*this, FirstMBB, CallInstr);
  InterprocCtx.runBFS();
  return InterprocBFSRes(std::move(InterprocCtx.ADBsToBeReturned));
}

void BFSCtx::visitBasicBlock(MachineBasicBlock *MBB) {
  MFDEBUG(errs() << "\nBlock " << MBB->getParent()->getName() << "::bb."
                 << MBB->getNumber() << "." << MBB->getName() << "\n";);

  this->MBB = MBB;
  RegisterValueMap.enterBlock(MBB);

  for (auto &MI : *MBB) {
    if (!MI.isDebugInstr() && !shouldIgnoreInstruction(&MI)) {
      visitInstruction(&MI);
    }
  }

  RegisterValueMap.exitBlock(MBB);
}

void BFSCtx::visitInstruction(MachineInstr *MI) {
  if (MBB->getParent()->getName() == "rwsem_spin_on_owner") {
    auto &DebugLoc = MI->getDebugLoc();
    if (!DebugLoc) {
      MFDEBUG(errs() << "unknown:0:0: ";);
    } else {
      MFDEBUG(errs() << DebugLoc->getFilename() << ":" << DebugLoc->getLine()
                     << ":" << DebugLoc->getColumn() << ": ";);
    }
    MFDEBUG(errs() << *MI;);
  }

  if (MI->isInlineAsm()) {
    handleInlineAsmInst(MI);
    handleInstruction(MI);
  } else if (MI->isCall()) {
    handleCallInst(MI);
  } else if (MI->mayLoadOrStore()) {
    handleLoadStoreInst(MI);
  } else if (MI->isBranch()) {
    handleBranchInst(MI);
  } else if (MI->isReturn()) {
    handleReturnInst(MI);
  } else {
    handleInstruction(MI);
  }

  RegisterValueMap.visitInstruction(MI);
}

void BFSCtx::handleCallInst(MachineInstr *MI) {
  auto CalledMFOptional = getMachineFunctionFromCall(MI);
  if (!CalledMFOptional.has_value()) {
    LLVM_DEBUG(dbgs() << "Got no machine function from call instruction: "
                      << *MI << "\n");
    return;
  }
  auto *CalledMF = *CalledMFOptional;
  auto &CalledF = CalledMF->getFunction();

  if (recLevel() > recLimit()) {
    return;
  }

  // FirstBB being nullptr implies that the function should be skipped, but
  // the call's arguments should still be looked at. For example, if this is a
  // call to a function with external linkage, the analysis won't be able to
  // follow the call, but the call's arguments should still be checked against
  // current dep chains. If they are part of any dep chain, the corresponding
  // dependency is marked as trivially verified as we want to avoid false
  // positives here. Similarly for calls to intrinsics or indirect calls.
  MachineBasicBlock *FirstBB;

  // Here, we operate under the assumption that void intrinsics will not
  // overwrite any function arguments passed to them. They therefore do not hold
  // the potential to break dep chains and can be safely skipped. Per our
  // assumption, the same does not apply to non-void intrinsics, simply for the
  // reason that they might return a dep chain value which the analysis cannot
  // cach. They are therefore treated like external functions (see below) unless
  // their function attribute denote that they only read from memory (or don't
  // access memory at all).

  // FIXME: CallI.isIndirectCall() == !CalledF ?
  if (!CalledMF || CalledF.hasExternalLinkage() || CalledF.isIntrinsic() ||
      CalledF.isVarArg() || CalledMF->empty() || MI->isIndirectBranch() ||
      CalledF.arg_size() > AArch64ArgRegs.size()) {
    FirstBB = nullptr;
  } else if (CalledF.hasExternalLinkage() || CalledF.isIntrinsic() ||
             CalledF.isVarArg() || CalledF.empty()) {
    // TODO: check if this mirrors what is done in the frontend checker
    if (CalledF.onlyReadsMemory() || (CalledF.getReturnType()->isVoidTy())) {
      return;
    }
    FirstBB = nullptr;
  } else {
    FirstBB = &*CalledMF->begin();
  }

  // Contains new beginnings whose dep chain(s) run through the function
  // return
  //
  // AND
  //
  // Contains existing beginnings whoes dep chain(s) run into and out of the
  // interprocedural context.
  InterprocBFSRes RADBsFromCall = runInterprocBFS(FirstBB, MI);

  auto *VAdd = MI;

  // Handle returned addr deps.
  for (auto &IRetAD : RADBsFromCall) {
    auto ID = IRetAD->ADB.getID();

    if (auto *OvwrADB = dyn_cast<OverwrittenADB>(IRetAD.get())) {
      assert(ADBs.find(ID) != ADBs.end() &&
             "Overwritten ADB not present in calling function!");

      auto &ADB = ADBs.at(ID);

      ADB.addStepToPathFrom(MI);

      ADB.addStepToPathFrom(MI, true);

      if (InheritedADBs.find(ID) != InheritedADBs.end())
        ADBsToBeReturned.push_back(std::move(IRetAD));

      ADBs.erase(ID);
    } else if (auto *RADB = dyn_cast<ReturnedADB>(IRetAD.get())) {
      auto &Lvl = RADB->Lvl;
      if (Lvl != BackendDCLevel::NORET) {
        if (RADB->DiscoveredInInterproc ||
            (ADBs.find(ID) == ADBs.end() &&
             InheritedADBs.find(ID) != InheritedADBs.end())) {
          ADBs.emplace(ID, std::move(RADB->ADB));
          ADBs.at(ID).resetDCM(MBB);
        }

        assert(ADBs.find(ID) != ADBs.end() &&
               "returned ADB which wasn't discovered in function call not "
               "present in calling function's ADBs or InheritedADBs");

        auto &ADB = ADBs.at(ID);

        if (!RADB->DiscoveredInInterproc)
          ADB.addStepToPathFrom(MI);

        ADB.addStepToPathFrom(MI, true);

        // FIXME: Can this be made nicer?
        switch (Lvl) {
        case BackendDCLevel::PTR:
          ADB.addToDCUnion(MBB, BackendDCLink{VAdd, BackendDCLevel::PTR});
          break;
        case BackendDCLevel::PTE:
          ADB.addToDCUnion(MBB, BackendDCLink{VAdd, BackendDCLevel::PTE});
          break;
        case BackendDCLevel::BOTH:
          ADB.addToDCUnion(MBB, BackendDCLink{VAdd, BackendDCLevel::PTR});
          ADB.addToDCUnion(MBB, BackendDCLink{VAdd, BackendDCLevel::PTE});
          break;
        default:
          break;
        }
      } else {
        // A dep chain didn't get returned. We start tracking the ADB
        // if we are verifying and continue.
        addToOutsideIDs(RADB->ADB.getID());
        ADBsToBeReturned.push_back(std::move(IRetAD));
      }
    }
  }
}

bool BFSCtx::storeOverwritesDCValue(MachineInstr *MI, PotAddrDepBeg &ADB) {
  // TODO: check if this any check is correct
  for (auto PointerOperand : RegisterValueMap.getPointerOperands(MI)) {
    for (auto ValueOperand : RegisterValueMap.getValueOperands(MI)) {
      auto StoreSrcPTE = BackendDCLink(ValueOperand, BackendDCLevel::PTE);
      auto StoreSrcPTR = BackendDCLink(ValueOperand, BackendDCLevel::PTR);
      auto StoreDstPTE = BackendDCLink(PointerOperand, BackendDCLevel::PTE);

      // Overwrites iff we store non-dc value to a pointee value in a dep chain
      if (ADB.belongsToDepChain(MI->getParent(), StoreDstPTE) &&
          (!ADB.belongsToDepChain(MI->getParent(), StoreSrcPTR) &&
           !ADB.belongsToDepChain(MI->getParent(), StoreSrcPTE)))
        return true;
    }
  }

  return false;
}

void BFSCtx::handleLoadStoreInst(MachineInstr *MI) {
  if (MI->mayLoad() && MI->mayStore()) {
    MI->dump();
    llvm_unreachable("Unable to handle instruction that loads and stores");
  }

  auto Annotations = getLKMMAnnotations(MI);
  handleDepAnnotations(MI, Annotations);

  // MachineValueSet Dependencies = RegisterValueMap.getValuesForRegisters(MI);

  if (MI->mayLoad()) {
    for (auto PointerOperand : RegisterValueMap.getPointerOperands(MI)) {
      // Handle dep chains through this load instruction
      auto DCLCmp = BackendDCLink(PointerOperand, BackendDCLevel::BOTH);
      auto DCLEnd = BackendDCLink(PointerOperand, BackendDCLevel::PTR);
      auto DCLAdd = BackendDCLink(MI, BackendDCLevel::PTR);

      // TODO outsource into seperate functions
      depChainThroughInst(MI, DCLAdd, SmallVector<BackendDCLink>{DCLCmp});
    }
  } else if (MI->mayStore()) {
    // TODO: check if this is correct if we loop over all pointer and value
    // operands
    for (auto PointerOperand : RegisterValueMap.getPointerOperands(MI)) {
      for (auto ValueOperand : RegisterValueMap.getValueOperands(MI)) {
        // DCLCmp can only run at PTR level as we could otherwise prodcue a
        // 2nd-degree PTE-level value
        auto DCLCmp = BackendDCLink(ValueOperand, BackendDCLevel::PTR);
        auto DCLEnd = BackendDCLink(PointerOperand, BackendDCLevel::PTR);
        auto DCLAdd = BackendDCLink(PointerOperand, BackendDCLevel::PTE);

        for (auto &ADBP : ADBs) {
          auto &ID = ADBP.first;
          auto &ADB = ADBP.second;

          // *ptr_to_dep_chain_value = non_dep_chain_value;
          //
          // ========== ♫ Throoooow awaaaay your dependency chaaaa-aain ♫
          // ==========
          //
          // We make a deliberate overstimation here in the favour of preventing
          // false positives. If we see any PTE-level dep chain value being
          // overwritten, we either throw away the full dependency chain or
          // consider it preserved. This is a result of us not being able to
          // tell which value is being overwritten and to what other values the
          // pointer to the PTE-level value in question aliases.
          if (storeOverwritesDCValue(MI, ADB)) {
            // If this dep chain runs interprocedurally, we need to make the
            // calling function aware of the overwrite
            if (InheritedADBs.find(ID) != InheritedADBs.end())
              ADBsToBeReturned.push_back(make_shared<OverwrittenADB>(ADB));

            markIDAsVerified(ID);
            continue;
          }

          ADB.tryAddValueToDepChains(RegisterValueMap, MI, DCLAdd, DCLCmp);
        }
      }
    }
  }
}

void BFSCtx::handleBranchInst(MachineInstr *MI) {
  // only for ctrl dependencies at the moment
}

void BFSCtx::handleReturnInst(MachineInstr *MI) {
  // get values possibly stored in return register
  MachineValueSet ReturnDependencyVals =
      RegisterValueMap.getValuesForRegister(AArch64::X0, MI);

  if (recLevel() == 0) {
    return;
  }

  auto AddReturnADB = [&](MachineValue RetVal) {
    auto RetLinkPTR = BackendDCLink(RetVal, BackendDCLevel::PTR);
    auto RetLinkPTE = BackendDCLink(RetVal, BackendDCLevel::PTE);

    for (auto &[ID, ADB] : ADBs) {
      bool ADBDiscoverdInThisF = InheritedADBs.find(ID) == InheritedADBs.end();

      auto RADB = make_shared<ReturnedADB>(ADB, BackendDCLevel::NORET,
                                           ADBDiscoverdInThisF);

      auto RetAtPTR = ADB.belongsToDepChain(MBB, RetLinkPTR);
      auto RetAtPTE = ADB.belongsToDepChain(MBB, RetLinkPTE);

      // Set the appropriate level at which an ADB is being returned. If the dep
      // chain does not run into the return value and the ADB was not discovered
      // as part of the current interprocedural analysis, the calling function
      // must be aware of its existence and it must not be returned at all.
      if (RetAtPTR && RetAtPTE)
        RADB->Lvl = BackendDCLevel::BOTH;
      else if (RetAtPTR)
        RADB->Lvl = BackendDCLevel::PTR;
      else if (RetAtPTE)
        RADB->Lvl = BackendDCLevel::PTE;
      else if (!ADBDiscoverdInThisF)
        return;

      ADBsToBeReturned.push_back(std::move(RADB));
    }
  };

  if (ReturnDependencyVals.empty()) {
    AddReturnADB(nullptr);
  } else {
    for (auto RetVal : ReturnDependencyVals) {
      AddReturnADB(RetVal);
    }
  }
}

void BFSCtx::handleInlineAsmInst(MachineInstr *MI) {
  auto DependentVals = RegisterValueMap.getValuesForRegisters(MI);

  // TODO: we might need to handle dependency annotations on inline assembly
  // instructions. Not sure if they are actually attached to those.

  for (auto &[ID, ADB] : ADBs) {
    bool AnyBelongsToDepChain = false;
    for (auto Val : DependentVals) {
      AnyBelongsToDepChain |= ADB.belongsToDepChain(
          MI->getParent(), BackendDCLink(Val, BackendDCLevel::PTR));
      AnyBelongsToDepChain |= ADB.belongsToDepChain(
          MI->getParent(), BackendDCLink(Val, BackendDCLevel::PTE));
    }

    if (AnyBelongsToDepChain) {
      markIDAsVerified(ID);
    }
  }
}

// this function mirrors visitInstruction and visitPhiNode from the IR
// checker, as any instruction may function as a phi node in the backend.
void BFSCtx::handleInstruction(MachineInstr *MI) {
  SmallVector<BackendDCLink, 6> DCLCmpsPTR;

  for (auto Val : RegisterValueMap.getValuesForRegisters(MI)) {
    DCLCmpsPTR.emplace_back(BackendDCLink(Val, BackendDCLevel::PTR));
  }

  depChainThroughInst(MI, BackendDCLink(MI, BackendDCLevel::PTR), DCLCmpsPTR);
}

bool BFSCtx::parseDepHalfString(StringRef Annot,
                                SmallVectorImpl<string> &AnnotData) {
  bool BrokenByMiddleEnd = false;
  if (Annot.consume_back(";BrokenInMiddleEnd;")) {
    BrokenByMiddleEnd = true;
  } else if (Annot.consume_back(";")) {
    BrokenByMiddleEnd = false;
  } else {
    return false;
  }

  while (!Annot.empty()) {
    auto P = Annot.split(",");
    AnnotData.push_back(P.first.str());
    Annot = P.second;
  }

  return BrokenByMiddleEnd;
}

string BFSCtx::buildInlineString(MachineInstr *MI) {
  auto InstDebugLoc = MI->getDebugLoc();

  if (!InstDebugLoc)
    return "no debug loc when building inline string";

  string InlinePath = InstDebugLoc.get()->getFilename().str() +
                      "::" + to_string(InstDebugLoc.getLine()) + ":" +
                      to_string(InstDebugLoc.getCol());

  auto *InlinedAt = InstDebugLoc.getInlinedAt();

  while (InlinedAt) {
    // Column.
    InlinePath = ":" + to_string(InlinedAt->getColumn()) + "  " + InlinePath;
    // Line.
    InlinePath = "::" + to_string(InlinedAt->getLine()) + InlinePath;
    // File name.
    InlinePath = InlinedAt->getFilename().str() + InlinePath;

    // Move to next InlinedAt if it exists.
    InlinedAt = InlinedAt->getInlinedAt();
  }

  return InlinePath;
}

bool BFSCtx::isADBBroken(string const &ID, MachineInstr *MI,
                         string &ParsedDepHalfID,
                         string &ParsedPathToViaFiles) {

  // TODO: check if we actually need to check every pointer operand or just the
  // very first one, as that usually is the address, while the others just
  // calculate an address. This not only applies here, but also in other place

  auto CheckADBBroken = [&](MachineValue PointerOperand) {
    auto DCLCmp = BackendDCLink(PointerOperand, BackendDCLevel::PTR);

    auto PartOfADBs = ADBs.find(ID) != ADBs.end();
    auto PartOfOutsideIDs = OutsideIDs.find(ID) != OutsideIDs.end();

    // FIXME: formatting looks very uncomfortable here
    // We only add the current annotation as a broken ending if the current
    // BFS has seen the beginning ID. If we were to add unconditionally, we
    // might add endings which aren't actually reachable by the corresponding.
    // Such cases would then be false positivies.
    if (PartOfADBs || PartOfOutsideIDs) {
      // We have to account for the fact that annotations might get removed for
      // example and therefore we might not have seen the corresponding
      // beginning annotation.
      if (BrokenADBs->find(ID) == BrokenADBs->end())
        return false;

      auto &VADB = BrokenADBs->at(ID);
      auto BrokenBy = VerDepHalf::BrokenDC;

      if (PartOfADBs) {
        auto &ADB = ADBs.at(ID);
        // Check for fully broken dependency chain
        if (!ADB.belongsToDepChain(MBB, DCLCmp)) {
          DepChain DC = {};

          if (auto *DCU = ADB.getDCsAt(MBB))
            DC = *DCU;

          addBrokenEnding(VADB,
                          VerAddrDepEnd(MI, ID, getFullPath(MI),
                                        getFullPath(MI, true), ParsedDepHalfID,
                                        ParsedPathToViaFiles, false),
                          DC, BrokenBy);
        } else
          return true;
      }

      if (PartOfOutsideIDs) {
        addBrokenEnding(BrokenADBs->at(ID),
                        VerAddrDepEnd(MI, ID, getFullPath(MI),
                                      getFullPath(MI, true), ParsedDepHalfID,
                                      ParsedPathToViaFiles, false),
                        {}, BrokenBy);
      }
    }
    return false;
  };

  bool AnyBroken = false;
  auto PointerOperands = RegisterValueMap.getPointerOperands(MI);
  for (auto PointerOperand : PointerOperands) {
    AnyBroken |= CheckADBBroken(PointerOperand);
  }

  return AnyBroken;
}

void BFSCtx::handleDepAnnotations(MachineInstr *MI,
                                  SmallVector<StringRef, 5> Annotations) {
  unordered_set<int> AddedEndings;

  SmallVector<string, 5> AnnotData;

  for (auto &CurrentDepHalfStr : Annotations) {
    if (!CurrentDepHalfStr.contains("LKMMDep")) {
      continue;
    }

    AnnotData.clear();

    auto BrokenByMiddleEnd = parseDepHalfString(CurrentDepHalfStr, AnnotData);

    auto &ParsedDepHalfTypeStr = AnnotData[0];
    auto &ParsedID = AnnotData[1];

    if (VerifiedIDs->find(ParsedID) != VerifiedIDs->end()) {
      continue;
    }

    auto &ParsedDepHalfID = AnnotData[2];
    auto &ParsedPathToViaFiles = CurrentDepHalfStr.contains("ctrl dep begin")
                                     ? AnnotData[4]
                                     : AnnotData[3];

    // Figure out if this is the inst we originally attached the annotation to.
    // If it isn't, continue
    auto InlinePath = buildInlineString(MI);

    if (!InlinePath.empty() && !ParsedPathToViaFiles.empty()) {
      if ((InlinePath.length() > ParsedPathToViaFiles.length()) ||
          // Does ParsedPathTo end with InlinePath?
          ParsedPathToViaFiles.compare(ParsedPathToViaFiles.length() -
                                           InlinePath.length(),
                                       InlinePath.length(), InlinePath) != 0) {
        continue;
      }
    }

    // MFDEBUG(errs() << "- " << CurrentDepHalfStr.str() << "\n";);

    if (ParsedDepHalfTypeStr.find("begin") != string::npos) {
      if (ADBs.find(ParsedID) != ADBs.end()) {
        updateID(ParsedID);
      }

      DepChain DC;
      DC.insert(BackendDCLink(MI, BackendDCLevel::PTR));
      ADBs.emplace(ParsedID, PotAddrDepBeg(MI, ParsedID, getFullPath(MI, true),
                                           std::move(DC), BrokenByMiddleEnd,
                                           MI->getParent()));

      if (ParsedDepHalfTypeStr.find("address dep") != string::npos) {
        // Assume broken until proven wrong.
        // MFDEBUG(errs() << "-- assume broken\n";);
        BrokenADBs->emplace(
            ParsedID, VerAddrDepBeg(MI, ParsedID, getFullPath(MI),
                                    getFullPath(MI, true), ParsedDepHalfID,
                                    ParsedPathToViaFiles, BrokenByMiddleEnd));
      }
    } else if (ParsedDepHalfTypeStr.find("end") != string::npos) {
      // If we are able to verify one pair in
      // {ORIGINAL_ID} \cup REMAPPED_IDS.at(ORIGINAL_ID) x {ORIGINAL_ID}
      // We consider ORIGINAL_ID verified; there only exists one dependency
      // in unoptimised IR, hence we only look for one dependency in
      // optimised IR.
      if (ParsedDepHalfTypeStr.find("address dep") != string::npos) {
        if (isADBBroken(ParsedID, MI, ParsedDepHalfID, ParsedPathToViaFiles)) {
          markIDAsVerified(ParsedID);
          continue;
        }

        if (RemappedIDs->find(ParsedID) != RemappedIDs->end()) {
          for (auto const &RemappedID : RemappedIDs->at(ParsedID)) {
            if (isADBBroken(RemappedID, MI, ParsedDepHalfID,
                            ParsedPathToViaFiles)) {
              markIDAsVerified(ParsedID);
              break;
            }
          }
        }
      }
    }
  }
}

void BFSCtx::buildBackEdgeMap(BBtoBBSetMap *BEDsForBB, MachineFunction *MF) {
  for (auto &MBB : *MF) {
    BEDsForBB->insert({&MBB, {}});
  }

  SmallVector<pair<const MachineBasicBlock *, const MachineBasicBlock *>>
      BackEdgeVector;
  findMachineFunctionBackedges(*MF, BackEdgeVector);

  for (auto &BackEdge : BackEdgeVector) {
    BEDsForBB->at(const_cast<MachineBasicBlock *>(BackEdge.first))
        .insert(const_cast<MachineBasicBlock *>(BackEdge.second));
  }
}

void BFSCtx::buildBFSInfo(
    unordered_map<MachineBasicBlock *, BFSBBInfo> *BFSInfo,
    BBtoBBSetMap *BEDsForBB, MachineFunction *MF) {
  for (auto &MBB : *MF) {
    unsigned MaxHits{MBB.pred_size()};

    for (auto *Pred : MBB.predecessors()) {
      if (BEDsForBB->at(Pred).find(&MBB) != BEDsForBB->at(Pred).end()) {
        --MaxHits;
      }
    }

    BFSInfo->emplace(&MBB, BFSBBInfo(&MBB, MaxHits));
  }
}

void BFSCtx::removeBackEdgesFromSuccessors(
    MachineBasicBlock *MBB, unordered_set<MachineBasicBlock *> *BEDs,
    unordered_set<MachineBasicBlock *> *SuccessorsWOBackEdges) {
  for (auto *SBB : MBB->successors()) {
    if (BEDs->find(SBB) == BEDs->end()) {
      SuccessorsWOBackEdges->insert(SBB);
    }
  }
}

void BFSCtx::findDependentArgs(
    PotAddrDepBeg &ADB, MachineInstr *MI,
    SmallVectorImpl<pair<int, BackendDCLevel>> *DepArgs) {
  auto CalledMFOptional = getMachineFunctionFromCall(MI);
  Function *CalledF = nullptr;
  if (CalledMFOptional) {
    auto *CalledMF = *CalledMFOptional;
    CalledF = &CalledMF->getFunction();
  }

  if (CalledF->arg_size() > AArch64ArgRegs.size()) {
    // TODO: handle functions that pass their arguments on the stack.
    // We could do the analysis for the arguments that ar epassed in registers
    // could be an option
    return;
  }

  for (unsigned Ind = 0; Ind < CalledF->arg_size(); ++Ind) {
    auto ArgReg = AArch64ArgRegs[Ind];
    auto ArgValues = RegisterValueMap.getValuesForRegister(ArgReg, MI);

    for (auto VCmp : ArgValues) {
      // FIXME: Can this be made nicer?
      if (ADB.belongsToDepChain(MBB, BackendDCLink(VCmp, BackendDCLevel::PTR)))
        if (CalledF)
          if (!CalledF->isVarArg())
            DepArgs->emplace_back(Ind, BackendDCLevel::PTR);

      // FIXME: Basically duplicate
      if (ADB.belongsToDepChain(MBB, BackendDCLink(VCmp, BackendDCLevel::PTE)))
        if (CalledF)
          if (!CalledF->isVarArg())
            DepArgs->emplace_back(Ind, BackendDCLevel::PTE);
    }
  }
}

bool BFSCtx::bfsCanVisit(MachineBasicBlock *MBB,
                         unordered_map<MachineBasicBlock *, BFSBBInfo> &BFSInfo,
                         unordered_set<MachineBasicBlock *> &BEDs) {
  auto &NextMaxHits{BFSInfo.at(MBB).MaxHits};
  auto &NextCurrentHits{BFSInfo.at(MBB).CurrentHits};

  if (NextMaxHits == 0 || ++NextCurrentHits == NextMaxHits) {
    return true;
  }

  return false;
}

void BFSCtx::progressAddrDepDCPaths(MachineBasicBlock *MBB,
                                    MachineBasicBlock *SBB,
                                    BBtoBBSetMap &BEDsForBB) {
  for (auto &ADBP : ADBs) {
    ADBP.second.progressDCPaths(MBB, SBB, BEDsForBB);
  }
}

void BFSCtx::deleteAddrDepDCsAt(MachineBasicBlock *MBB,
                                unordered_set<MachineBasicBlock *> &BEDs) {
  for (auto &ADBP : ADBs) {
    ADBP.second.deleteDCsAt(MBB, BEDs);
  }
}

class LKMMCheckDepsBackend : public MachineFunctionPass {
public:
  static char ID;
  LKMMCheckDepsBackend()
      : MachineFunctionPass(ID),
        BrokenADBs(make_shared<DepHalfMap<VerAddrDepBeg>>()),
        BrokenADEs(make_shared<DepHalfMap<VerAddrDepEnd>>()),
        RemappedIDs(make_shared<IDReMap>()),
        VerifiedIDs(make_shared<unordered_set<string>>()), PrintedBrokenIDs() {
    initializeLKMMCheckDepsBackendPass(*PassRegistry::getPassRegistry());
  }

  bool runOnMachineFunction(MachineFunction &MF) override;

  StringRef getPassName() const override { return "LKMMCheckDepsBackend"; }

private:
  // Contains all unverified address dependency beginning annotations.
  shared_ptr<DepHalfMap<VerAddrDepBeg>> BrokenADBs;

  shared_ptr<DepHalfMap<VerAddrDepEnd>> BrokenADEs;

  shared_ptr<IDReMap> RemappedIDs;

  shared_ptr<unordered_set<string>> VerifiedIDs;

  unordered_set<string> PrintedBrokenIDs;

  /// Maps the reduced IDs of the same beginning / ending to the shortest
  /// VerAddDepBeg with that ending plus the length of its ID.  An ID is
  /// reduced if it excludes the path from the beginning to the end and only
  /// contains the beginning location and the ending location.
  StringMap<pair<VerAddrDepBeg *, unsigned>> MinLengthPerBegEndPair;

  void printBrokenDeps();

  void printBrokenDep(VerDepHalf &Beg, VerDepHalf &End, const string &ID);

  void onlyPrintShortestDep() {
    for (auto VADBPIt = BrokenADBs->begin(); VADBPIt != BrokenADBs->end();) {
      auto RdcdID = VADBPIt->first;
      string OgID = VADBPIt->first;
      auto &VADB = VADBPIt->second;

      // Reduce ID
      auto F = RdcdID.find_first_of('\n', 2);
      auto L = RdcdID.find_last_of('\n', RdcdID.length() - 3);
      RdcdID.erase(F, L - F);

      // Check ID in ShortestLengthPerBegEndPair
      // FIXME: do I need to account for the increments here?
      if (MinLengthPerBegEndPair.find(RdcdID) == MinLengthPerBegEndPair.end()) {
        MinLengthPerBegEndPair.insert(
            pair<string, pair<VerAddrDepBeg *, unsigned>>{
                RdcdID, pair<VerAddrDepBeg *, unsigned>{&VADB, OgID.length()}});

        ++VADBPIt;
      } else if (MinLengthPerBegEndPair[RdcdID].second > OgID.length()) {
        auto OldID = MinLengthPerBegEndPair[RdcdID].first->getID();
        MinLengthPerBegEndPair[RdcdID] =
            pair<VerAddrDepBeg *, unsigned>{&VADB, OgID.length()};

        BrokenADBs->erase(OldID);

        if (BrokenADEs->find(OldID) != BrokenADEs->end())
          BrokenADEs->erase(OldID);

        ++VADBPIt;
      } else {
        auto Del = VADBPIt++;

        BrokenADBs->erase(Del);

        if (BrokenADEs->find(OgID) != BrokenADEs->end())
          BrokenADEs->erase(OgID);
      }
    }
  }
};

char LKMMCheckDepsBackend::ID = 0;

bool LKMMCheckDepsBackend::runOnMachineFunction(MachineFunction &MF) {
  if (!MFDEBUG_ENABLED || MF.getName().str() == "down_write") {
    MFDEBUG(dbgs() << "Checking deps for " << MF.getName() << "\n";);
    MFDEBUG(MF.dump(););
    MFDEBUG(MF.getFunction().dump(););

    BFSCtx BFSCtx(&*MF.begin(), BrokenADBs, BrokenADEs, RemappedIDs,
                  VerifiedIDs);
    BFSCtx.runBFS();

    onlyPrintShortestDep();

    printBrokenDeps();
  }

  return false;
}

void LKMMCheckDepsBackend::printBrokenDeps() {
  unsigned NotPrintedDeps = 0;

  for (auto &VADBP : *BrokenADBs) {
    auto ID = VADBP.first;
    // Exclude duplicate IDs by normalising them.
    // This means we only print one representative of each equivalence class.
    if (auto Pos = ID.find("-#"); Pos != string::npos) {
      ID = ID.substr(0, Pos);
    }

    auto &VDB = VADBP.second;

    auto VDEP = BrokenADEs->find(ID);
    if (VDEP == BrokenADEs->end()) {
      continue;
    }

    auto &VDE = VDEP->second;
    if (PrintedBrokenIDs.find(ID) != PrintedBrokenIDs.end()) {
      continue;
    }

    PrintedBrokenIDs.insert(ID);

    // broken by middle end, we don't need to print this dependency
    if (VDB.isBrokenByMiddleEnd() && !PRINT_BROKEN_BY_MIDDLE_END) {
      NotPrintedDeps++;
    } else {
      printBrokenDep(VDB, VDE, ID);
    }
  }

  if (NotPrintedDeps > 0) {
    dbgs() << "Not printing " << NotPrintedDeps
           << " broken deps which were already detected by the middle end\n";
  }
}

void LKMMCheckDepsBackend::printBrokenDep(VerDepHalf &Beg, VerDepHalf &End,
                                          const string &ID) {
  string DepKindStr{""};

  if (isa<VerAddrDepBeg>(Beg))
    DepKindStr = "Backend address dependency";
  else
    llvm_unreachable("Invalid beginning type when printing broken dependency.");

  errs() << "//===--------------------------Broken "
            "Dependency---------------------------===//\n";

  errs() << DepKindStr << " with ID: " << ID << "\n\n";

  errs() << "Dependency Beginning:\t" << Beg.getParsedDepHalfID() << "\n";
  errs() << "\nPath to (via files) from annotation: "
         << Beg.getParsedpathTOViaFiles() << "\n";

  errs() << "\nDependnecy Ending:\t" << End.getParsedDepHalfID() << "\n";
  errs() << "\nPath to (via files) from annotation: "
         << End.getParsedpathTOViaFiles() << "\n";

  errs() << "\nBroken " << End.getBrokenBy() << "\n\n";

  if (auto *VADB = dyn_cast<VerAddrDepBeg>(&Beg)) {
    auto &DCUnion = VADB->getDC();

    errs() << "Soure-level dep chains at " << getInstLocString(End.getInst())
           << "\n";

    errs() << "\nUnion of all dependency chains at the ending:\n";
    for (auto &DCL : DCUnion)
      errs() << getInstLocString(DCL.Val) << "\n";
  }

  errs() << "//"
            "===-----------------------------------------------------------"
            "----"
            "-------===//\n\n";
}

class LKMMRemoveDepAnnotation : public MachineFunctionPass {
public:
  static char ID;
  LKMMRemoveDepAnnotation() : MachineFunctionPass(ID) {}

  bool runOnMachineFunction(MachineFunction &MF) override;

  StringRef getPassName() const override {
    return "RemoveLKMMDepAnnotationPass";
  }
};

char LKMMRemoveDepAnnotation::ID = 0;

bool LKMMRemoveDepAnnotation::runOnMachineFunction(MachineFunction &MF) {

  for (auto &MBB : MF) {
    for (auto &MI : MBB) {
      MDNode *MDN = MI.getPCSections();
      if (!MDN) {
        continue;
      }

      // TODO: only remove pcsections inserted by us
      MI.setPCSections(MF, nullptr);

      // MDN->dump();

      // TODO: only remove the annotation if it is a LKMM annotation
      // SmallVector<StringRef, 5> Annotations{};
      // MDNode *MDN = MI->getPCSections();
      // if (!MDN) {
      //   return Annotations;
      // }

      // for (const MDOperand &MDO : MDN->operands()) {
      //   if (auto *MD = dyn_cast<MDString>(MDO.get())) {
      //     Annotations.push_back(MD->getString());
      //   }
      // }

      // return Annotations;

      // std::map<StringRef, SmallVector<Constant *>> SectionWithValues{};
      // StringRef SectionName;
      // for (const MDOperand &MDO : MDN->operands()) {
      //   if (auto *MD = dyn_cast<MDString>(MDO.get()); MD) {
      //     SectionName = MD->getString();
      //   }

      //   if (auto *MD = dyn_cast<ConstantAsMetadata>(MDO.get()); MD) {
      //     SectionWithValues[SectionName].push_back(MD->getValue());
      //   }
      // }

      // MDBuilder MDB(MF.getFunction().getContext());
      // SmallVector<MDBuilder::PCSection, 5> NewAnnotations{};
      // for (auto Section : SectionWithValues) {
      //   if (Section.first.startswith("LKMM")) {
      //     continue;
      //   }

      //   NewAnnotations.push_back({Section.first, Section.second});
      // }

      // if (NewAnnotations.empty()) {
      //   MI.setPCSections(MF, nullptr);
      //   errs() << "null\n";
      // } else {
      //   MI.setPCSections(MF, MDB.createPCSections(NewAnnotations));
      //   MI.getPCSections()->dump();
      // }
    }
  }

  return false;
}

} // namespace

INITIALIZE_PASS(LKMMCheckDepsBackend, DEBUG_TYPE, "Check broken dependencies",
                false, false)

#undef DEBUG_TYPE

FunctionPass *llvm::createLKMMCheckDepsBackendPass() {
  return new LKMMCheckDepsBackend();
}

FunctionPass *llvm::createLKMMRemoveDepAnnotationPass() {
  return new LKMMRemoveDepAnnotation();
}
