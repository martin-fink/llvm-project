#include "AArch64.h"
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
#include "llvm/IR/Instructions.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/InitializePasses.h"
#include "llvm/MC/MCRegister.h"
#include "llvm/MC/MCRegisterInfo.h"
#include "llvm/Pass.h"
#include "llvm/PassRegistry.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <array>
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
// #include "../Target/AArch64/AArch64.h"

using namespace llvm;

namespace {
class MachineValue {
private:
  enum Kind {
    Instruction,
    RegisterArgument,
  } Kind;
  union U {
    MachineInstr *MI;
    Register Reg;

    U(MachineInstr *MI) : MI(MI) {}
    U(Register Reg) : Reg(Reg) {}
  } U;

public:
  MachineValue(MachineInstr *MI) : Kind(Instruction), U(MI) {}
  MachineValue(Register Reg) : Kind(RegisterArgument), U(Reg) {}
  ~MachineValue() {}

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

  struct HashFunction {
    size_t operator()(const MachineValue &Other) const {
      size_t KindHash =
          std::hash<size_t>()(static_cast<std::size_t>(Other.Kind));
      size_t ValHash = 0;
      switch (Other.Kind) {
      case Instruction:
        ValHash = std::hash<MachineInstr *>()(Other.U.MI);
        break;
      case RegisterArgument:
        ValHash = std::hash<unsigned>()(Other.U.Reg);
        break;
      }

      return KindHash ^ (ValHash << 1);
    }
  };
};

raw_ostream &operator<<(raw_ostream &Os, const MachineValue &Val) {
  switch (Val.Kind) {
  case MachineValue::Kind::Instruction:
    Os << Val.U.MI;
    break;
  case MachineValue::Kind::RegisterArgument:
    // TODO: print register name
    Os << "Register argument: " << static_cast<unsigned>(Val.U.Reg);
    break;
  }
  return Os;
}

static const std::array<Register, 8> AArch64ArgRegs = {
    AArch64::X0, AArch64::X1, AArch64::X2, AArch64::X3,
    AArch64::X4, AArch64::X5, AArch64::X6, AArch64::X7};

#define DEBUG_TYPE "lkmm-dep-checker-backend"

using IDReMap =
    std::unordered_map<std::string, std::unordered_set<std::string>>;

// Represents a map of IDs to (potential) dependency halfs.
template <typename T> using DepHalfMap = std::unordered_map<std::string, T>;

using CallPathStack = std::list<MachineInstr *>;

using DepChain = std::unordered_set<MachineValue, MachineValue::HashFunction>;

using DepChainPair = std::pair<DepChain, DepChain>;

using DepChainMap = std::unordered_map<MachineBasicBlock *, DepChainPair>;

using VerIDSet = std::unordered_set<std::string>;

using BBtoBBSetMap =
    std::unordered_map<MachineBasicBlock *,
                       std::unordered_set<MachineBasicBlock *>>;

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

std::string getInstLocationString(MachineInstr *MI, bool ViaFile = false) {
  const llvm::DebugLoc &InstDebugLoc = MI->getDebugLoc();

  if (!InstDebugLoc) {
    return "no location";
  }

  auto LAndC = "::" + std::to_string(InstDebugLoc.getLine()) + ":" +
               std::to_string(InstDebugLoc.getCol());

  if (ViaFile) {
    return InstDebugLoc.get()->getFilename().str() + LAndC;
  }

  return MI->getParent()->getParent()->getName().str() + LAndC;
}

std::optional<MachineFunction *> getMachineFunctionFromCall(MachineInstr *MI) {
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

  return &MMI.getOrCreateMachineFunction(*CalledF);
}

std::string getCalledFunctionName(MachineInstr *MI) {
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

class RegisterValueMapping {
public:
  RegisterValueMapping() /*: RegisterValueMap()*/ {}

  std::set<MachineValue> getValuesForRegisters(MachineInstr *MI);

  std::set<MachineValue> getValuesForRegister(Register Reg, MachineInstr *MI);

private:
  // std::map<MachineBasicBlock *, std::map<Register, std::set<MachineInstr *>>>
  //     RegisterValueMap;

  std::set<MachineValue>
  getValuesForRegister(MachineBasicBlock *MBB, Register Reg,
                       std::set<MachineBasicBlock *> &Visited,
                       MachineInstr *StartBefore = nullptr);
};

std::set<MachineValue> RegisterValueMapping::getValuesForRegister(
    MachineBasicBlock *MBB, Register Reg,
    std::set<MachineBasicBlock *> &Visited, MachineInstr *StartBefore) {
  assert((StartBefore == nullptr || MBB == StartBefore->getParent()) &&
         "StartAt->getParent and passed MBB do not match");

  // if we are looking up values for the zero register, return an empty set
  if (Reg == AArch64::XZR || Reg == AArch64::WZR) {
    return {};
  }

  // already visited this basic block, return
  if (Visited.find(MBB) != Visited.end()) {
    return {};
  }

  Visited.insert(MBB);

  // for now, don't chache register values
  // this might be good idea for future optimizations
  // the problem is that we need to consider that there might be multiple
  // writes to a register in a basic block -- how do we handle this?

  // auto &RegMap = RegisterValueMap[MBB];
  // if (StartAt == nullptr) {
  //   // check if we already computed this
  //   if (auto Val = RegMap.find(Reg); Val != RegMap.end()) {
  //     return Val->second;
  //   }
  // }

  auto It = MBB->rbegin();
  if (StartBefore != nullptr) {
    // walk until we reach StartAt
    while (It != MBB->rend() && It != StartBefore) {
      ++It;
    }

    if (It != MBB->rend()) {
      // walk one further than StartAt
      ++It;
    }
  }

  for (; It != MBB->rend(); ++It) {
    // instruction defines register, it is the only instruction that should be
    // returned
    // TODO: handle subregisters

    auto *TRI = MBB->getParent()->getSubtarget().getRegisterInfo();

    for (MCSubRegIterator SubRegs(Reg, TRI, true); SubRegs.isValid();
         ++SubRegs) {
      if (It->definesRegister(*SubRegs)) {
        return {&*It};
      }
    }
  }

  // if we are in the entry block for this function, we also need to check if
  // the register is an argument register
  auto *MF = MBB->getParent();
  // TODO: check if we can compare blocks just by their number
  if (MF->front().getNumber() == MBB->getNumber() &&
      MF->getRegInfo().isArgumentRegister(*MF, Reg)) {
    const auto *ArgReg =
        std::find(AArch64ArgRegs.begin(), AArch64ArgRegs.end(), Reg);
    if (ArgReg != AArch64ArgRegs.end() &&
        std::distance(AArch64ArgRegs.begin(), ArgReg) <
            static_cast<long>(MF->getFunction().arg_size())) {
      // this is an argument register used for this function
      return {*ArgReg};
    }
  }

  // register was not defined in this, we need to look it up in the predecessors
  std::set<MachineValue> Result{};

  for (auto &Pred : MBB->predecessors()) {
    auto PredResult = getValuesForRegister(Pred, Reg, Visited);
    Result.insert(PredResult.begin(), PredResult.end());
  }
  // RegMap[Reg] = Result;

  return Result;
}

std::set<MachineValue>
RegisterValueMapping::getValuesForRegisters(MachineInstr *MI) {
  std::set<MachineValue> Deps{};
  for (auto Op : MI->operands()) {
    if (Op.isReg() && MI->readsRegister(Op.getReg())) {
      std::set<MachineBasicBlock *> Visited;
      auto DepsForReg =
          getValuesForRegister(MI->getParent(), Op.getReg(), Visited, MI);
      Deps.insert(DepsForReg.begin(), DepsForReg.end());
    }
  }

  return Deps;
}

std::set<MachineValue>
RegisterValueMapping::getValuesForRegister(Register Reg, MachineInstr *MI) {
  std::set<MachineBasicBlock *> Visited;
  return getValuesForRegister(MI->getParent(), Reg, Visited, MI);
}

class DepHalf {
public:
  enum DepKind {
    DK_AddrBeg,
    DK_CtrlBeg,
    DK_VerAddrBeg,
    DK_VerAddrEnd,
    DK_VerCtrlBeg,
    DK_VerCtrlEnd
  };

  std::string getID() const;

  std::string getPathToViaFiles() const { return PathToViaFiles; }

  std::string getPathFrom() const { return PathFrom; }

  void setPathFrom(std::string P) { PathFrom = P; }

  void addStepToPathFrom(MachineInstr *FCall, bool R = false) {
    PathFrom += (getInstLocationString(FCall) + (R ? "<-" : "->") +
                 getCalledFunctionName(FCall) + "()\n");
  }

  DepKind getKind() const { return Kind; }

protected:
  MachineInstr *const MI;

  const std::string ID;

  const std::string PathToViaFiles;

  std::string PathFrom;

  DepHalf(MachineInstr *MI, std::string ID, std::string PathToViaFiles,
          DepKind Kind)
      : MI(MI), ID(ID), PathToViaFiles(PathToViaFiles), PathFrom("\n"),
        Kind(Kind){};

  virtual ~DepHalf() {}

private:
  DepKind Kind;
};

class PotAddrDepBeg : public DepHalf {
public:
  PotAddrDepBeg(MachineInstr *MI, std::string ID, std::string PathToViaFiles,
                MachineValue InstID, bool FDep = true)
      : PotAddrDepBeg(MI, ID, PathToViaFiles, DepChain{InstID}, FDep,
                      MI->getParent()) {}

  PotAddrDepBeg(MachineInstr *MI, std::string ID, std::string PathToViaFiles,
                DepChain DC, bool FDep, MachineBasicBlock *MBB)
      : DepHalf(MI, ID, PathToViaFiles, DK_AddrBeg), DCM(), FDep(FDep) {
    DCM.emplace(MBB, DepChainPair{DC, DC});
  }

  // Copy constructor for copying a returned PotAddrDepBeg into the calling
  // context.
  PotAddrDepBeg(PotAddrDepBeg &ADB, MachineBasicBlock *MBB, DepChain DC)
      : PotAddrDepBeg(ADB) {
    DCM.clear();
    DCM.emplace(MBB, DepChainPair(DC, DC));
  }

  /// Checks whether a DepChainPair is currently at a given BB.
  ///
  /// \param BB the BB to be checked.
  ///
  /// \returns true if the PotAddrDepBeg has dep chains at \p BB.
  bool isAt(MachineBasicBlock *MBB) const { return DCM.find(MBB) != DCM.end(); }

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
                   std::unordered_set<MachineBasicBlock *> &BEDs);

  /// Tries to add a value to the intersection of all DepChains at \p BB.
  ///
  /// \param BB the BB to whose dep chain intersection \p V should be
  ///  added.
  /// \param V the value to be added.
  void addToDCInter(MachineBasicBlock *MBB, MachineValue InstID);

  /// Tries to add a value to the union of all dep chains at \p BB.
  ///
  /// \param BB the BB to whose dep chain union \p V should be added.
  /// \param V the value to be added.
  void addToDCUnion(MachineBasicBlock *MBB, MachineValue InstID);

  /// Checks if a counter-argument for this beginning being a full dependency
  /// has been found yet.
  ///
  /// \returns false if a counter-argument for this beginning being a full
  ///  dependency has been found.
  bool canBeFullDependency() const { return FDep; }

  /// This function is called when the BFS is able to prove that any
  /// instruction it encounters after this call is not able to complete a
  /// full
  /// dependency to this beginning. This might be the case when the BFS has
  /// just
  /// seen a DepChain running through a back edge.
  void cannotBeFullDependencyAnymore() { FDep = false; }

  /// Tries to continue the DepChain with a new value.
  ///
  /// \param I the instruction which is currently being checked.
  /// \param ValCmp the value which might or might not be part of a DepChain.
  /// \param ValAdd the value to add if \p ValCmp is part of a DepChain.
  bool tryAddValueToDepChains(RegisterValueMapping &RegisterValueMap,
                              MachineInstr *MI, MachineValue InstCmp,
                              MachineValue InstAdd);

  /// Checks if a value is part of all dep chains starting at this
  /// PotAddrDepBeg. Can be used for checking whether an address dependency
  /// ending marks a full dependency to this PotAddrDepBeg.
  ///
  /// \param BB the BB the BFS is currently visiting.
  /// \param VCmp the value which might or might not be part of all dep
  ///  chains.
  ///
  /// \returns true if \p VCmp is part of all of the beginning's dep chains.
  bool belongsToAllDepChains(MachineBasicBlock *MBB, MachineValue InstID) const;

  /// Checks if a value is part of any dep chain of an addr dep beginning.
  ///
  /// \param BB the BB the BFS is currently at.
  /// \param VCmp the value which might or might not be part of a dep chain.
  ///
  /// \returns true if \p VCmp belongs to at least one of the beginning's dep
  ///  chains.
  bool belongsToDepChain(MachineBasicBlock *MBB, MachineValue InstID) const;

  /// Checks if a value is part of some, but not all, dep chains, starting at
  /// this potential beginning. Can be used for checking whether an address
  /// dependency ending marks a partial dependency to this PotAddrDepBeg.
  ///
  /// \param BB the BB the BFS is currently at.
  /// \param VCmp the value which might or might not be part of all dep
  ///  chains.
  ///
  /// \returns true if \p VCmp belongs to at least one, but not all, of this
  ///  PotAddrDepBeg's DepChains.
  bool belongsToSomeNotAllDepChains(MachineBasicBlock *MBB,
                                    MachineValue InstID) const;

  /// Annotates an address dependency from a given ending to this beginning.
  ///
  /// \param ID2 the ID of the ending.
  /// \param I2 the instruction where the address dependency ends.
  /// \param FDep set to true if this is a full address
  ///  dependency.
  // void addAddrDep(std::string ID2, std::string PathToViaFiles2,
  //                 MachineInstr *MI2, bool FDep) const;

  /// Resets the DepChainMap to a new state and potentially alteres the
  /// possibility of this PotAddrDepBeg being the beginning of a full
  /// dependency. This functionality is required for interprocedural
  /// analysis,
  /// where a DepChain carries over, but should not be cluttered with values
  /// from previous function(s). In the case where not all DepChains of this
  /// PotAddrDepBeg carry over, this cannot mark the beginning of a full
  /// dependency in the called function anymore.
  ///
  /// \param BB The BB to reset the DepChainMap to.
  /// \param FDep The new \p FDep state.
  /// \param DC A DepChain to be used as initial value for the new
  /// DepChainPair
  /// at \p BB. In the interprocedural analysis case, \p DC will contain all
  /// function arguments which are part of a DepChain in the calling
  /// function.
  void resetDCMTo(MachineBasicBlock *MBB, bool FDep, DepChain &DC) {
    this->FDep = FDep;
    DCM.clear();
    DCM.emplace(MBB, DepChainPair(DC, DC));
  }

  /// Resets the DepChainMap
  void clearDCMap() { DCM.clear(); }

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
    errs() << "printing DCInter\n";
    for (auto &V : DCM.at(MBB).first) {
      // TODO: check if printing value like this makes sense
      errs() << V << "\n";
    }
  }

private:
  DepChainMap DCM;

  // Denotes whether a matching ending can be annotated as a full dependency.
  // Is
  // set to false if the algorithm encounters something on the way that makes
  // a
  // full dependency impossible, e.g. a backedge.
  bool FDep;

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
  bool depChainsShareValue(
      std::list<std::pair<MachineBasicBlock *, DepChain *>> &DCs,
      MachineValue InstID) const;
};

void PotAddrDepBeg::progressDCPaths(MachineBasicBlock *BB,
                                    MachineBasicBlock *SBB,
                                    BBtoBBSetMap &BEDsForBB) {
  if (!isAt(BB)) {
    return;
  }

  if (!isAt(SBB)) {
    DCM.insert({SBB, DepChainPair{}});
  }

  auto &SDCP = DCM.at(SBB);

  // BB might not be the only predecessor of SBB. Build a list of all
  // preceeding dep chains.
  std::list<std::pair<MachineBasicBlock *, DepChain *>> PDCs;

  // Populate PDCs and DCUnion.
  for (auto *Pred : SBB->predecessors()) {
    // If Pred is connected to SBB via a back edge, skip.
    if (BEDsForBB.at(Pred).find(SBB) != BEDsForBB.at(Pred).end()) {
      continue;
    }

    // If the DepChain don't run through Pred, skip.
    if (!isAt(Pred)) {
      continue;
    }

    // Previous, i.e. Pred's, DepChainPair.
    auto &PDCP = DCM.at(Pred);

    // Insert preceeding DCunion into succeeding DCUnion.
    SDCP.second.insert(PDCP.second.begin(), PDCP.second.end());

    // Save preceeding DepChain for intersection.
    PDCs.emplace_back(Pred, &PDCP.first);
  }

  // FIXME When this if doesn't fire, depChainsShareValue() will make one
  //  unneccesary loop iteration.

  // If PDCs is empty, we are at the function entry:
  if (PDCs.empty()) {
    // 1. Intiialise PDCs with current DCUnion.
    SDCP.second.insert(DCM.at(BB).second.begin(), DCM.at(BB).second.end());

    // 2. Initialise SDCP's DCUnion with the current DCUnion.
    PDCs.emplace_back(BB, &DCM.at(BB).first);
  }

  // Update DCInter. Only add a value if it's present in every
  // preceeding DepChain.
  DepChain FixedDC = *PDCs.begin()->second;

  // If SDCP's DCInter isn't empty. Intersect succeeding DCInter with
  // current DCInter.
  if (!SDCP.first.empty()) {
    FixedDC = SDCP.first;
    SDCP.first.clear();
  }

  // Compute intersection of all dep chains leading to SBB.
  for (auto &V : FixedDC) {
    // Add a value if it is present in all preceeding DepChains.
    if (depChainsShareValue(PDCs, V)) {
      SDCP.first.insert(V);
    }
  }
}

void PotAddrDepBeg::deleteDCsAt(MachineBasicBlock *MBB,
                                std::unordered_set<MachineBasicBlock *> &BEDs) {
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
    DCM.at(MBB).first.clear();
    DCM.at(MBB).second.clear();
  } else {
    // If there's no dead DepChain, erase the DCM entry for the current MBB.
    DCM.erase(MBB);
  }
}

void PotAddrDepBeg::addToDCInter(llvm::MachineBasicBlock *MBB,
                                 MachineValue InstID) {
  if (!isAt(MBB)) {
    return;
  }

  DCM.at(MBB).first.insert(InstID);
}

void PotAddrDepBeg::addToDCUnion(llvm::MachineBasicBlock *MBB,
                                 MachineValue InstID) {
  if (!isAt(MBB)) {
    return;
  }

  DCM.at(MBB).second.insert(InstID);
}

bool PotAddrDepBeg::tryAddValueToDepChains(
    RegisterValueMapping &RegisterValueMap, llvm::MachineInstr *MI,
    MachineValue InstCmp, MachineValue InstAdd) {
  if (!isAt(MI->getParent())) {
    return false;
  }

  // TODO: can remove check?
  //  if (isa<ConstantData>(InstAdd))
  //    return false;

  auto Ret = false;

  auto &DCP = DCM.at(MI->getParent());

  auto &DCInter = DCP.first;
  auto &DCUnion = DCP.second;

  // Add to DCinter and account for redefinition.
  if (DCInter.find(InstCmp) != DCInter.end()) {
    DCInter.insert(InstAdd);
    Ret = true;
  } else if (MI->mayStore()) {
    for (auto PotRedefOp : RegisterValueMap.getValuesForRegisters(MI)) {
      if (DCInter.find(PotRedefOp) != DCInter.end()) {
        DCInter.erase(PotRedefOp);
      }
    }
  }

  // Add to DCUnion and account for redefinition
  if (DCUnion.find(InstCmp) != DCUnion.end()) {
    DCUnion.insert(InstAdd);
    Ret = true;
  } else if (MI->mayStore()) {
    for (auto PotRedefOp : RegisterValueMap.getValuesForRegisters(MI)) {
      if (DCUnion.find(PotRedefOp) != DCUnion.end()) {
        DCUnion.erase(PotRedefOp);
      }
    }
  }

  return Ret;
}

bool PotAddrDepBeg::belongsToAllDepChains(llvm::MachineBasicBlock *MBB,
                                          MachineValue InstID) const {
  if (DCM.find(MBB) == DCM.end()) {
    return false;
  }
  auto &DCInter = DCM.at(MBB).first;

  return DCInter.find(InstID) != DCInter.end() && DCM.size() == 1;
}

bool PotAddrDepBeg::belongsToDepChain(llvm::MachineBasicBlock *MBB,
                                      MachineValue InstID) const {
  if (DCM.find(MBB) == DCM.end()) {
    return false;
  }

  auto &DCUnion = DCM.at(MBB).second;

  return DCUnion.find(InstID) != DCUnion.end();
}

bool PotAddrDepBeg::belongsToSomeNotAllDepChains(llvm::MachineBasicBlock *MBB,
                                                 MachineValue InstID) const {
  if (DCM.find(MBB) == DCM.end()) {
    return false;
  }

  return !belongsToAllDepChains(MBB, InstID) && belongsToDepChain(MBB, InstID);
}

bool PotAddrDepBeg::depChainsShareValue(
    std::list<std::pair<MachineBasicBlock *, DepChain *>> &DCs,
    MachineValue InstID) const {
  for (auto &DCP : DCs) {
    if (DCP.second->find(InstID) == DCP.second->end()) {
      return false;
    }
  }

  return true;
}

class VerDepHalf : public DepHalf {
public:
  enum BrokenByType { BrokenDC, ParToFull };

  void setBrokenBy(BrokenByType BB) { BrokenBy = BB; }

  std::string getBrokenBy() {
    switch (BrokenBy) {
    case BrokenDC:
      return "by breaking the dependency chain";
    case ParToFull:
      return "by converting a partial dependency to a full dependency";
    }
  }

  std::string const &getParsedDepHalfID() const { return ParsedDepHalfID; }

  std::string const &getParsedpathTOViaFiles() const {
    return ParsedPathToViaFiles;
  }

  MachineInstr *const &getInst() const { return MI; };

  virtual ~VerDepHalf(){};

  static bool classof(const DepHalf *VDH) {
    return VDH->getKind() >= DK_VerAddrBeg && VDH->getKind() <= DK_VerCtrlEnd;
  }

  std::string const &getParsedID() const { return ParsedID; }

protected:
  VerDepHalf(MachineInstr *MI, std::string ParsedID, std::string DepHalfID,
             std::string PathToViaFiles, std::string ParsedDepHalfID,
             std::string ParsedPathToViaFiles, DepKind Kind)
      : DepHalf(MI, DepHalfID, PathToViaFiles, Kind), ParsedID(ParsedID),
        ParsedDepHalfID(ParsedDepHalfID), ParsedPathToViaFiles{
                                              ParsedPathToViaFiles} {}

private:
  // Shows how this dependency got broken
  BrokenByType BrokenBy;

  // The ID which identifies the two metadata annotations for this dependency.
  const std::string ParsedID;

  // The PathTo which was attached to the metadata annotation, i.e. the
  // path to I in unoptimised IR.
  const std::string ParsedDepHalfID;

  const std::string ParsedPathToViaFiles;
};

class VerAddrDepBeg : public VerDepHalf {
public:
  VerAddrDepBeg(MachineInstr *MI, std::string ParsedID, std::string DepHalfID,
                std::string PathToViaFiles, std::string ParsedPathTo,
                std::string ParsedPathToViaFiles)
      : VerDepHalf(MI, ParsedID, DepHalfID, PathToViaFiles, ParsedPathTo,
                   ParsedPathToViaFiles, DK_VerAddrBeg) {}

  static bool classof(const DepHalf *VDH) {
    return VDH->getKind() == DK_VerAddrBeg;
  }
};

void findMachineFunctionBackedges(
    const MachineFunction &MF,
    SmallVectorImpl<std::pair<const MachineBasicBlock *,
                              const MachineBasicBlock *>> &Result) {
  const MachineBasicBlock *MBB = &*MF.begin();
  if (MBB->succ_empty()) {
    return;
  }

  SmallPtrSet<const MachineBasicBlock *, 8> Visited;
  SmallVector<std::pair<const MachineBasicBlock *,
                        MachineBasicBlock::const_succ_iterator>,
              8>
      VisitStack;
  SmallPtrSet<const MachineBasicBlock *, 8> InStack;

  Visited.insert(MBB);
  VisitStack.push_back(std::make_pair(MBB, MBB->succ_begin()));
  InStack.insert(MBB);
  do {
    std::pair<const MachineBasicBlock *, MachineBasicBlock::const_succ_iterator>
        &Top = VisitStack.back();
    const MachineBasicBlock *ParentMBB = Top.first;
    MachineBasicBlock::const_succ_iterator &MI = Top.second;

    bool FoundNew = false;
    while (MI != ParentMBB->succ_end()) {
      MBB = *MI++;
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
  VerAddrDepEnd(MachineInstr *MI, std::string ParsedID, std::string DepHalfID,
                std::string PathToViaFiles, std::string ParsedDepHalfID,
                std::string ParsedPathToViaFiles, bool ParsedFDep)
      : VerDepHalf(MI, ParsedID, DepHalfID, PathToViaFiles, ParsedDepHalfID,
                   ParsedPathToViaFiles, DK_VerAddrEnd),
        ParsedFDep(ParsedFDep) {}

  const bool &getParsedFullDep() const { return ParsedFDep; }

  static bool classof(const DepHalf *VDH) {
    return VDH->getKind() == DK_VerAddrEnd;
  }

private:
  // Denotes whether the address dependency was annotated as a full dependency
  // or a partial dependency. The value is obtained from the metadata
  // annotation.
  const bool ParsedFDep;
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

using InterprocBFSRes = DepHalfMap<PotAddrDepBeg>;

class BFSCtx {
public:
  BFSCtx(MachineBasicBlock *MBB,
         std::shared_ptr<DepHalfMap<VerAddrDepBeg>> BrokenADBs,
         std::shared_ptr<DepHalfMap<VerAddrDepEnd>> BrokenADEs,
         std::shared_ptr<IDReMap> RemappedIDs,
         std::shared_ptr<VerIDSet> VerifiedIDs)
      : MBB(MBB), ADBs(), ReturnedADBs(), CallPath(new CallPathStack()),
        RegisterValueMap(), BrokenADBs(BrokenADBs), BrokenADEs(BrokenADEs),
        RemappedIDs(RemappedIDs), VerifiedIDs(VerifiedIDs) {}

  BFSCtx(BFSCtx &Ctx, MachineBasicBlock *MBB, MachineInstr *CallInstr)
      : BFSCtx(Ctx) {
    prepareInterproc(MBB, CallInstr);
    ReturnedADBs.clear();
  }

  void runBFS();

private:
  MachineBasicBlock *MBB;

  DepHalfMap<PotAddrDepBeg> ADBs;

  // Potential beginnings where the return value is part of the DepChain.
  DepHalfMap<PotAddrDepBeg> ReturnedADBs;

  std::shared_ptr<CallPathStack> CallPath;

  RegisterValueMapping RegisterValueMap;

  void buildBackEdgeMap(BBtoBBSetMap *BEDsForBB, MachineFunction *MF);

  void buildBFSInfo(std::unordered_map<MachineBasicBlock *, BFSBBInfo> *BFSInfo,
                    BBtoBBSetMap *BEDsForBB, MachineFunction *MF);

  void removeBackEdgesFromSuccessors(
      MachineBasicBlock *MBB, std::unordered_set<MachineBasicBlock *> *BEDs,
      std::unordered_set<MachineBasicBlock *> *SuccessorsWOBackEdges);

  bool bfsCanVisit(MachineBasicBlock *MBB,
                   std::unordered_map<MachineBasicBlock *, BFSBBInfo> &BFSInfo,
                   std::unordered_set<MachineBasicBlock *> &BEDs);

  void progressAddrDepDCPaths(MachineBasicBlock *MBB, MachineBasicBlock *SBB,
                              BBtoBBSetMap &BEDsForBB);

  void deleteAddrDepDCsAt(MachineBasicBlock *MBB,
                          std::unordered_set<MachineBasicBlock *> &BEDs);

  void visitBasicBlock(MachineBasicBlock *MBB);

  void visitInstruction(MachineInstr *MI);

  void handleCallInst(MachineInstr *MI);

  void handleLoadStoreInst(MachineInstr *MI);

  void handleBranchInst(MachineInstr *MI);

  void handleReturnInst(MachineInstr *MI);

  void handleInstruction(MachineInstr *MI);

  bool allFunctionArgsPartOfAllDepChains(
      PotAddrDepBeg &ADB, MachineInstr *CallInstr,
      std::unordered_set<MachineValue, MachineValue::HashFunction>
          &DependentArgs);

  void handleDependentFunctionArgs(MachineInstr *CallInstr,
                                   MachineBasicBlock *MBB);

  void prepareInterproc(MachineBasicBlock *MBB, MachineInstr *CallInstr);

  InterprocBFSRes runInterprocBFS(MachineBasicBlock *FirstMBB,
                                  MachineInstr *CallInstr);

  // verification methods and properties

  // Contains all unverified address dependency beginning annotations.
  // TODO: can this be a reference?
  std::shared_ptr<DepHalfMap<VerAddrDepBeg>> BrokenADBs;
  // Contains all unverified address dependency ending annotations.
  std::shared_ptr<DepHalfMap<VerAddrDepEnd>> BrokenADEs;

  // All remapped IDs which were discovered from the current root function.
  std::shared_ptr<IDReMap> RemappedIDs;

  // Contains all IDs which have been verified in the current module.
  std::shared_ptr<VerIDSet> VerifiedIDs;

  void handleDepAnnotations(MachineInstr *MI,
                            SmallVector<StringRef, 5> Annotations);

  void parseDepHalfString(StringRef Annot,
                          SmallVectorImpl<std::string> &AnnotData);

  bool handleAddrDepID(std::string const &ID, MachineInstr *MI,
                       std::string &ParsedDepHalfID,
                       std::string &ParsedPathToViaFiles, bool ParsedFullDep);

  void updateID(std::string &ID) {
    if (RemappedIDs->find(ID) != RemappedIDs->end()) {
      RemappedIDs->emplace(ID, std::unordered_set<std::string>{ID + "-#1"});
      ID += "-#1";
    } else {
      auto S = RemappedIDs->at(ID).size();
      RemappedIDs->at(ID).insert(ID + "-#" + std::to_string(S + 1));
      ID += "-#" + std::to_string(S + 1);
    }
  }

  void markIDAsVerified(std::string &ParsedID) {
    auto DelID = [](auto &ID, auto &Bs, auto &Es, auto &RemappedIDs) {
      Bs->erase(ID);
      Es->erase(ID);

      if (RemappedIDs->find(ID) != RemappedIDs->end()) {
        for (auto const &RemappedID : RemappedIDs->at(ID)) {
          Bs->erase(RemappedID);
          Es->erase(RemappedID);
        }
      }
    };

    DelID(ParsedID, BrokenADBs, BrokenADEs, RemappedIDs);

    VerifiedIDs->insert(ParsedID);
    RemappedIDs->erase(ParsedID);
  }

  // helper methods

  unsigned recLevel() { return CallPath->size(); }

  constexpr unsigned recLimit() const { return 4; }

  std::string getFullPath(MachineInstr *MI, bool ViaFiles = false) {
    return convertPathToString(ViaFiles) + getInstLocationString(MI, ViaFiles);
  }

  std::string getFullPathViaFiles(MachineInstr *MI) {
    return convertPathToString() + getInstLocationString(MI);
  }

  std::string convertPathToString(bool ViaFiles = false) {
    std::string PathStr{""};

    for (auto &CallI : *CallPath)
      PathStr += (getInstLocationString(CallI, ViaFiles) + "  ");

    return PathStr;
  }

  std::string buildInlineString(MachineInstr *MI);
};

void BFSCtx::runBFS() {
  LLVM_DEBUG(dbgs() << "Running BFS on machine function "
                    << MBB->getParent()->getName().str() << "\n";);

  BBtoBBSetMap BEDsForBB;

  buildBackEdgeMap(&BEDsForBB, MBB->getParent());

  std::unordered_map<MachineBasicBlock *, BFSBBInfo> BFSInfo;

  buildBFSInfo(&BFSInfo, &BEDsForBB, MBB->getParent());

  std::queue<MachineBasicBlock *> BFSQueue = {};

  BFSQueue.push(MBB);

  while (!BFSQueue.empty()) {
    auto &MBB = BFSQueue.front();

    visitBasicBlock(MBB);

    std::unordered_set<MachineBasicBlock *> SuccessorsWOBackEdges{};

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

bool BFSCtx::allFunctionArgsPartOfAllDepChains(
    PotAddrDepBeg &ADB, MachineInstr *CallInstr,
    std::unordered_set<MachineValue, MachineValue::HashFunction>
        &DependentArgs) {
  bool FDep = ADB.canBeFullDependency();

  if (!ADB.areAllDepChainsAt(MBB)) {
    FDep = false;
  }

  auto CalledMFOptional = getMachineFunctionFromCall(CallInstr);
  if (!CalledMFOptional.has_value()) {
    errs() << "Got no machine function from call instruction.\n";
    // TODO: check if returning false is the correct response to this
    return false;
  }
  auto *CalledMF = *CalledMFOptional;
  auto &CalledF = CalledMF->getFunction();

  // TODO: this should be handled in the future
  if (CalledF.arg_size() > AArch64ArgRegs.size()) {
    errs() << "Cannot handle functions with arguments passed over the stack.\n";
    return false;
  }

  for (unsigned I = 0; I < CalledF.arg_size() && I < AArch64ArgRegs.size();
       ++I) {
    auto Reg = AArch64ArgRegs[I];
    auto Values = RegisterValueMap.getValuesForRegister(Reg, CallInstr);

    auto BelongsToDepChain =
        std::all_of(Values.begin(), Values.end(),
                    [&](auto &V) { return ADB.belongsToDepChain(MBB, V); });
    if (!BelongsToDepChain) {
      continue;
    }

    auto BelongsToAllDepChains =
        std::all_of(Values.begin(), Values.end(),
                    [&](auto &V) { return ADB.belongsToAllDepChains(MBB, V); });
    if (!BelongsToAllDepChains) {
      FDep = false;
    }

    DependentArgs.insert(Reg);
  }

  return FDep;
}

void BFSCtx::handleDependentFunctionArgs(MachineInstr *CallInstr,
                                         MachineBasicBlock *MBB) {
  DepChain DependentArgs{};

  for (auto &ADBP : ADBs) {
    auto &ADB = ADBP.second;

    bool FDep =
        allFunctionArgsPartOfAllDepChains(ADB, CallInstr, DependentArgs);

    // Instead of deleting an ADB if it doesn't run into a function, we keep it
    // with an empty DCM, thereby ensuring that no further items can be added to
    // the DepChain until control flow returns to this function, but still
    // allowing an ending to be mapped to it when verifying.
    if (DependentArgs.empty()) {
      ADB.clearDCMap();
    } else {
      ADB.resetDCMTo(MBB, FDep, DependentArgs);
      ADB.addStepToPathFrom(CallInstr);
    }

    DependentArgs.clear();
  }
}

void BFSCtx::prepareInterproc(MachineBasicBlock *MBB, MachineInstr *CallInstr) {
  handleDependentFunctionArgs(CallInstr, MBB);

  CallPath->push_back(CallInstr);

  this->MBB = MBB;
}

InterprocBFSRes BFSCtx::runInterprocBFS(MachineBasicBlock *FirstMBB,
                                        MachineInstr *CallInstr) {
  BFSCtx InterprocCtx = BFSCtx(*this, FirstMBB, CallInstr);
  InterprocCtx.runBFS();
  return InterprocBFSRes(std::move(InterprocCtx.ReturnedADBs));
}

void BFSCtx::visitBasicBlock(MachineBasicBlock *MBB) {
  LLVM_DEBUG(dbgs() << "Visiting machine basic block" << MBB->getNumber()
                    << "\n";);

  this->MBB = MBB;

  for (auto &MI : *MBB) {
    visitInstruction(&MI);
  }
}

void BFSCtx::visitInstruction(MachineInstr *MI) {
  LLVM_DEBUG(dbgs() << "Visiting instruction:\n"
                    << "isCall: " << MI->isCall() << ", mayLoad: "
                    << MI->mayLoad() << ", mayStore: " << MI->mayStore()
                    << ", isBranch: " << MI->isBranch()
                    << ", isReturn: " << MI->isReturn() << "\n"
                    << *MI << "\n");

  if (MI->isCall()) {
    handleCallInst(MI);
  }
  if (MI->mayLoadOrStore()) {
    handleLoadStoreInst(MI);
  }
  if (MI->isBranch()) {
    handleBranchInst(MI);
  }
  if (MI->isReturn()) {
    handleReturnInst(MI);
  }
  handleInstruction(MI);
}

void BFSCtx::handleCallInst(MachineInstr *MI) {
  auto CalledMFOptional = getMachineFunctionFromCall(MI);
  if (!CalledMFOptional.has_value()) {
    errs() << "Got no machine function from call instruction.\n";
    return;
  }
  auto *CalledMF = *CalledMFOptional;
  auto &CalledF = CalledMF->getFunction();

  if (CalledMF->empty() || CalledF.isVarArg()) {
    return;
  }

  if (this->recLevel() > this->recLimit()) {
    return;
  }

  // TODO: check if we can use CalledMF.front()
  InterprocBFSRes ReturnedADBsFromCall =
      runInterprocBFS(&*CalledMF->begin(), MI);

  // auto &ReturnedADBsFromCall = Ret;
  for (auto &[ID, ReturnedADB] : ReturnedADBsFromCall) {
    if (ADBs.find(ID) != ADBs.end()) {
      auto &ADB = ADBs.at(ID);

      if (ReturnedADB.isDepChainMapEmpty()) {
        continue;
      }

      ADB.addToDCUnion(MBB, MI);
      ADB.setPathFrom(ReturnedADB.getPathFrom());

      // If not all dep chains from the beginning got returned, FDep might
      // have changed.

      if (ReturnedADB.canBeFullDependency()) {
        ADB.addToDCInter(MBB, MI);
      } else {
        ADB.cannotBeFullDependencyAnymore();
      }

      ADBs.at(ID).addStepToPathFrom(MI, true);
    } else if (ReturnedADB.isDepChainMapEmpty()) {
      ADBs.emplace(ID, ReturnedADB);
    } else {
      ADBs.emplace(ID, PotAddrDepBeg(ReturnedADB, MBB, DepChain{MI}));
      ADBs.at(ID).addStepToPathFrom(MI, true);
    }
  }
}

void BFSCtx::handleLoadStoreInst(MachineInstr *MI) {
  // handle common load/store functionality
  handleDepAnnotations(MI, getLKMMAnnotations(MI));

  std::set<MachineValue> Dependencies =
      RegisterValueMap.getValuesForRegisters(MI);

  if (MI->mayStore()) {
    for (auto &ADBP : ADBs) {
      auto &ADB = ADBP.second;

      for (auto V : Dependencies) {
        ADB.tryAddValueToDepChains(RegisterValueMap, MI, V, V);
      }
    }
  }
  if (MI->mayLoad()) {
    for (auto &ADBP : ADBs) {
      auto &ADB = ADBP.second;

      for (auto V : Dependencies) {
        ADB.tryAddValueToDepChains(RegisterValueMap, MI, V, MI);
      }
    }
  }
}

void BFSCtx::handleBranchInst(MachineInstr *MI) {
  // only for ctrl dependencies at the moment
}

void BFSCtx::handleReturnInst(MachineInstr *MI) {
  // get values possibly stored in return register
  std::set<MachineInstr *> ReturnDependencyVals{};

  if (recLevel() == 0) {
    return;
  }

  for (auto &ADBP : ADBs) {
    auto &ADB = ADBP.second;
    bool AnyBelongToDepChain = false;
    for (auto *V : ReturnDependencyVals) {
      AnyBelongToDepChain |= ADB.belongsToDepChain(MBB, V);
    }

    if (ReturnDependencyVals.empty() || ADB.isDepChainMapEmpty() ||
        !ADB.isDepChainMapEmpty() || !AnyBelongToDepChain) {
      ReturnedADBs.emplace(ADBP.first, ADB);
      ReturnedADBs.at(ADBP.first).clearDCMap();
    } else {
      for (auto *V : ReturnDependencyVals) {
        // TODO: this needs to be reworked: what happens if one dep belongs to
        // all and next not?
        if (ADB.belongsToSomeNotAllDepChains(MBB, V)) {
          ADB.cannotBeFullDependencyAnymore();
        }
      }

      ReturnedADBs.emplace(ADBP.first, ADB);
    }
  }
}

// this function mirrors visitInstruction and visitPhiNode from the IR
// checker, as any instruction may function as a phi node in the backend.
void BFSCtx::handleInstruction(MachineInstr *MI) {
  for (auto &ADBP : ADBs) {
    auto DependentValues = RegisterValueMap.getValuesForRegisters(MI);
    for (auto &DependentInst : DependentValues) {
      if (!ADBP.second.tryAddValueToDepChains(RegisterValueMap, MI,
                                              DependentInst, MI)) {
        ADBP.second.cannotBeFullDependencyAnymore();
      }
    }
  }
}

void BFSCtx::parseDepHalfString(StringRef Annot,
                                SmallVectorImpl<std::string> &AnnotData) {
  if (!Annot.consume_back(";")) {
    return;
  }

  while (!Annot.empty()) {
    auto P = Annot.split(",");
    AnnotData.push_back(P.first.str());
    Annot = P.second;
  }
}

std::string BFSCtx::buildInlineString(MachineInstr *MI) {
  auto InstDebugLog = MI->getDebugLoc();

  if (!InstDebugLog) {
    return "no debug loc when building inline string";
  }

  std::string InlinePath = InstDebugLog.get()->getFilename().str() + "::" +
                           std::to_string(InstDebugLog.get()->getLine()) + ":" +
                           std::to_string(InstDebugLog.get()->getColumn());

  auto *InlinedAt = InstDebugLog->getInlinedAt();

  while (InlinedAt) {
    // InlinePath = ":" + std::to_string(InlinedAt->getColumn());
    InlinePath += InlinedAt->getFilename().str() +
                  "::" + std::to_string(InlinedAt->getLine()) + ":" +
                  std::to_string(InlinedAt->getColumn());

    InlinedAt = InlinedAt->getInlinedAt();
  }

  return InlinePath;
}

bool BFSCtx::handleAddrDepID(std::string const &ID, MachineInstr *MI,
                             std::string &ParsedDepHalfID,
                             std::string &ParsedPathToViaFiles,
                             bool ParsedFullDep) {

  auto Values = RegisterValueMap.getValuesForRegisters(MI);

  for (auto VCmp : Values) {
    if (ADBs.find(ID) != ADBs.end()) {
      auto &ADB = ADBs.at(ID);

      // FIXME condition can be shortened
      if ((ParsedFullDep && ADB.belongsToAllDepChains(MBB, VCmp)) ||
          ((!ParsedFullDep && ADB.belongsToDepChain(MBB, VCmp)))) {
        return true;
      }

      // We only add the current annotation as a broken ending if the current
      // BFS has seen the beginning ID. If we were to add unconditionally, we
      // might add endings which aren't actually reachable by the corresponding.
      // Such cases may be false positivies.
      BrokenADEs->emplace(ID,
                          VerAddrDepEnd(MI, ID, getFullPath(MI),
                                        getFullPath(MI, true), ParsedDepHalfID,
                                        ParsedPathToViaFiles, ParsedFullDep));

      // Identify how the dependency got broken
      if (!ParsedFullDep && ADB.belongsToAllDepChains(MBB, VCmp))
        BrokenADEs->at(ID).setBrokenBy(VerDepHalf::BrokenByType::ParToFull);
      else if (!ADB.belongsToDepChain(MBB, VCmp))
        BrokenADEs->at(ID).setBrokenBy(VerDepHalf::BrokenByType::BrokenDC);
    }
  }
  return false;
}

void BFSCtx::handleDepAnnotations(MachineInstr *MI,
                                  SmallVector<StringRef, 5> Annotations) {
  std::unordered_set<int> AddedEndings;

  SmallVector<std::string, 5> AnnotData;

  for (auto &CurrentDepHalfStr : Annotations) {
    if (!CurrentDepHalfStr.contains("LKMMDep")) {
      continue;
    }

    AnnotData.clear();

    parseDepHalfString(CurrentDepHalfStr, AnnotData);

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
      if (InlinePath.length() > ParsedPathToViaFiles.length() ||
          ParsedPathToViaFiles.compare(ParsedPathToViaFiles.length() -
                                           InlinePath.length(),
                                       InlinePath.length(), InlinePath) != 0) {
        continue;
      }

      if (ParsedDepHalfTypeStr.find("begin") != std::string::npos) {
        if (ADBs.find(ParsedID) != ADBs.end()) {
          updateID(ParsedID);
        }

        ADBs.emplace(ParsedID, PotAddrDepBeg(MI, getFullPath(MI),
                                             getFullPath(MI, true), MI));

        if (ParsedDepHalfTypeStr.find("address dep") != std::string::npos) {
          // Assume broken until proven wrong.
          BrokenADBs->emplace(
              ParsedID, VerAddrDepBeg(MI, ParsedID, getFullPath(MI),
                                      getFullPath(MI, true), ParsedDepHalfID,
                                      ParsedPathToViaFiles));
        }
      } else if (ParsedDepHalfTypeStr.find("end") != std::string::npos) {
        // If we are able to verify one pair in
        // {ORIGINAL_ID} \cup REMAPPED_IDS.at(ORIGINAL_ID) x {ORIGINAL_ID}
        // We consider ORIGINAL_ID verified; there only exists one dependency in
        // unoptimised IR, hence we only look for one dependency in optimised
        // IR.
        if (ParsedDepHalfTypeStr.find("address dep") != std::string::npos) {
          bool ParsedFullDep = std::stoi(AnnotData[4]);

          if (handleAddrDepID(ParsedID, MI, ParsedDepHalfID,
                              ParsedPathToViaFiles, ParsedFullDep)) {
            markIDAsVerified(ParsedID);
            continue;
          }

          if (RemappedIDs->find(ParsedID) != RemappedIDs->end()) {
            for (auto const &RemappedID : RemappedIDs->at(ParsedID)) {
              if (handleAddrDepID(RemappedID, MI, ParsedDepHalfID,
                                  ParsedPathToViaFiles, ParsedFullDep)) {
                markIDAsVerified(ParsedID);
                break;
              }
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

  SmallVector<std::pair<const MachineBasicBlock *, const MachineBasicBlock *>>
      BackEdgeVector;
  findMachineFunctionBackedges(*MF, BackEdgeVector);

  for (auto &BackEdge : BackEdgeVector) {
    BEDsForBB->at(const_cast<MachineBasicBlock *>(BackEdge.first))
        .insert(const_cast<MachineBasicBlock *>(BackEdge.second));
  }
}

void BFSCtx::buildBFSInfo(
    std::unordered_map<MachineBasicBlock *, BFSBBInfo> *BFSInfo,
    BBtoBBSetMap *BEDsForBB, MachineFunction *MF) {
  for (auto &MBB : *MF) {
    unsigned MaxHits(MBB.pred_size());

    for (auto *Pred : MBB.predecessors()) {
      if (BEDsForBB->at(Pred).find(&MBB) != BEDsForBB->at(Pred).end()) {
        --MaxHits;
      }
    }

    BFSInfo->emplace(&MBB, BFSBBInfo(&MBB, MaxHits));
  }
}

void BFSCtx::removeBackEdgesFromSuccessors(
    MachineBasicBlock *MBB, std::unordered_set<MachineBasicBlock *> *BEDs,
    std::unordered_set<MachineBasicBlock *> *SuccessorsWOBackEdges) {
  for (auto *SBB : MBB->successors()) {
    if (BEDs->find(SBB) == BEDs->end()) {
      SuccessorsWOBackEdges->insert(SBB);
    }
  }
}

bool BFSCtx::bfsCanVisit(
    MachineBasicBlock *MBB,
    std::unordered_map<MachineBasicBlock *, BFSBBInfo> &BFSInfo,
    std::unordered_set<MachineBasicBlock *> &BEDs) {
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
                                std::unordered_set<MachineBasicBlock *> &BEDs) {
  for (auto &ADBP : ADBs) {
    ADBP.second.deleteDCsAt(MBB, BEDs);
  }
}

class CheckDepsPass : public MachineFunctionPass {
public:
  static char ID;
  CheckDepsPass()
      : MachineFunctionPass(ID),
        BrokenADBs(std::make_shared<DepHalfMap<VerAddrDepBeg>>()),
        BrokenADEs(std::make_shared<DepHalfMap<VerAddrDepEnd>>()),
        RemappedIDs(std::make_shared<IDReMap>()),
        VerifiedIDs(std::make_shared<std::unordered_set<std::string>>()),
        PrintedBrokenIDs() {}

  bool runOnMachineFunction(MachineFunction &MF) override;

private:
  // Contains all unverified address dependency beginning annotations.
  std::shared_ptr<DepHalfMap<VerAddrDepBeg>> BrokenADBs;

  std::shared_ptr<DepHalfMap<VerAddrDepEnd>> BrokenADEs;

  std::shared_ptr<IDReMap> RemappedIDs;

  std::shared_ptr<std::unordered_set<std::string>> VerifiedIDs;

  std::unordered_set<std::string> PrintedBrokenIDs;

  // std::unordered_set<MachineModule *> PrintedModules;

  void printBrokenDeps();

  void printBrokenDep(VerDepHalf &Beg, VerDepHalf &End, const std::string &ID);
};

char CheckDepsPass::ID = 0;

bool CheckDepsPass::runOnMachineFunction(MachineFunction &MF) {
  // auto CalleeCC = MF.getFunction().getCallingConv();
  // SmallVector<CCValAssign, 16> ArgLocs;
  // CCState CCInfo(CalleeCC, MF.getFunction().isVarArg(), MF, ArgLocs,
  // MF.getFunction().getContext());

  // MF.getRegInfo().getTargetRegisterInfo().

  if (MF.getName().str() == "doitlk_rw_addr_dep_begin_call_beginning_helper" ||
      MF.getName().str() == "doitlk_rw_addr_dep_begin_call_dep_chain") {
    errs() << "just here to set a debug breakpoint\n";
  }

  LLVM_DEBUG(dbgs() << "Checking deps for " << MF.getName() << "\n");
  BFSCtx BFSCtx(&*MF.begin(), BrokenADBs, BrokenADEs, RemappedIDs, VerifiedIDs);
  BFSCtx.runBFS();

  printBrokenDeps();

  return false;
}

void CheckDepsPass::printBrokenDeps() {
  auto CheckDepPair = [this](auto &P, auto &E) {
    auto ID = P.first;

    // Exclude duplicate IDs by normalising them.
    // This means we only print one representative of each equivalence class.
    if (auto Pos = ID.find("-#"))
      ID = ID.substr(0, Pos);

    auto &VDB = P.second;

    auto VDEP = E->find(ID);

    if (VDEP == E->end())
      return;

    auto &VDE = VDEP->second;

    if (PrintedBrokenIDs.find(ID) != PrintedBrokenIDs.end())
      return;

    PrintedBrokenIDs.insert(ID);
    printBrokenDep(VDB, VDE, ID);
  };

  for (auto &VADBP : *BrokenADBs)
    CheckDepPair(VADBP, BrokenADEs);
}

void CheckDepsPass::printBrokenDep(VerDepHalf &Beg, VerDepHalf &End,
                                   const std::string &ID) {
  std::string DepKindStr{""};

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

  if (auto *VADE = dyn_cast<VerAddrDepEnd>(&End))
    errs() << "\nFull dependency: " << (VADE->getParsedFullDep() ? "yes" : "no")
           << "\n";

  errs() << "Broken " << End.getBrokenBy() << "\n";

  errs() << "//"
            "===---------------------------------------------------------------"
            "-------===//\n\n";
}
#undef DEBUG_TYPE
} // namespace

FunctionPass *llvm::createCheckDepsPass() { return new CheckDepsPass(); }
