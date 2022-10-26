#include "llvm/ADT/SmallVector.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineInstrBundle.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/PassRegistry.h"
#include <list>
#include <queue>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
using namespace llvm;

// // namespace {
using IDReMap =
    std::unordered_map<std::string, std::unordered_set<std::string>>;

// Represents a map of IDs to (potential) dependency halfs.
template <typename T> using DepHalfMap = std::unordered_map<std::string, T>;

using CallPathStack = std::list<MachineInstr *>;

using InstIdentifier = std::string;

using DepChain = std::unordered_set<InstIdentifier>;

using DepChainPair = std::pair<DepChain, DepChain>;

using DepChainMap = std::unordered_map<MachineBasicBlock *, DepChainPair>;

using VerIDSet = std::unordered_set<std::string>;

using BBtoBBSetMap =
    std::unordered_map<MachineBasicBlock *,
                       std::unordered_set<MachineBasicBlock *>>;

bool hasAnnotation(MachineInstr *MI, std::string &A) {
  MDNode *MDN = MI->getPCSections();
  if (!MDN) {
    return false;
  }

  MDN->dump();
  // TODO:
  return false;
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

// struct BFSBBInfo {
//   MachineBasicBlock *MBB;

//   unsigned MaxHits;

//   unsigned CurrentHits;

//   BFSBBInfo(MachineBasicBlock *MBB, unsigned MaxHits)
//       : MBB(MBB), MaxHits(MaxHits), CurrentHits(0) {}
// };

// // //<editor-fold desc="Dependency half classes">
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
                InstIdentifier InstID, bool FDep = true)
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
  void addToDCInter(MachineBasicBlock *MBB, InstIdentifier InstID);

  /// Tries to add a value to the union of all dep chains at \p BB.
  ///
  /// \param BB the BB to whose dep chain union \p V should be added.
  /// \param V the value to be added.
  void addToDCUnion(MachineBasicBlock *MBB, InstIdentifier InstID);

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
  bool tryAddValueToDepChains(MachineInstr *MI, InstIdentifier InstCmp,
                              InstIdentifier InstAdd);

  /// Checks if a value is part of all dep chains starting at this
  /// PotAddrDepBeg. Can be used for checking whether an address dependency
  /// ending marks a full dependency to this PotAddrDepBeg.
  ///
  /// \param BB the BB the BFS is currently visiting.
  /// \param VCmp the value which might or might not be part of all dep
  ///  chains.
  ///
  /// \returns true if \p VCmp is part of all of the beginning's dep chains.
  bool belongsToAllDepChains(MachineBasicBlock *MBB,
                             InstIdentifier InstID) const;

  /// Checks if a value is part of any dep chain of an addr dep beginning.
  ///
  /// \param BB the BB the BFS is currently at.
  /// \param VCmp the value which might or might not be part of a dep chain.
  ///
  /// \returns true if \p VCmp belongs to at least one of the beginning's dep
  ///  chains.
  bool belongsToDepChain(MachineBasicBlock *MBB, InstIdentifier InstID) const;

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
                                    InstIdentifier InstID) const;

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
      InstIdentifier InstID) const;
};

// class PotCtrlDepBeg : public DepHalf {
// public:
//   // Copy constructor for constructing a PotCtrlDep from a PotAddrDep. As
//   // PotCtrlDep require the existence of a DepChain to a READ_ONCE(), marking
//   // their beginning, there is no other way of constructing a PotCtrlDepBeg.
//   PotCtrlDepBeg(PotAddrDepBeg &ADB, std::string BranchID,
//                 bool Resolvable = true)
//       : PotCtrlDepBeg(ADB.MI, ADB.ID, ADB.PathToViaFiles, BranchID,
//                       Resolvable) {}

//   /// Checks whether this PotCtrlDepBeg was recently discovered,
//   /// i.e. if it doesn't maintain any paths yet.
//   ///
//   /// \returns true if this PotCtrlDepBeg was recently discovered.
//   bool recentlyDiscovered() const { return CtrlPaths.empty(); }

//   /// Updates the PotCtrlDepBeg to be unresolvable. This might be the case
//   when
//   /// not all ctrl paths carry over to a called function. Within the
//   context(s)
//   /// of the called function (and beyond), the PotCtrlDepBeg cannot be
//   resolved
//   /// as some CtrlPaths still reside in the calling function.
//   void setCannotResolve() { Resolvable = false; }

//   /// Checks if the PotCtrlDepBeg can be resolved right now.
//   ///
//   /// \returns true if it can be resolved.
//   bool canResolve() const { return Resolvable; }

//   /// Checks if this PotCtrlDepBeg has ctrl paths whose heads are at \p BB
//   right
//   /// now.
//   ///
//   /// \returns true if a ctrl path is at \p BB.
//   bool isAt(MachineBasicBlock *MBB) const {
//     return CtrlPaths.find(MBB) != CtrlPaths.end();
//   }

//   /// Returns a string representation of the location of the branch
//   instruction.
//   ///
//   /// \returns a string representation of location of the branch instruction.
//   std::string const &getBranchID() const { return BranchID; };

//   /// Maintains the ctrl paths at this PotCtrlDepBeg.
//   ///
//   /// \param BB the BB the BFS just ran on.
//   /// \param SuccessorsWOBackEdges all successors of BB which are not
//   ///  connected through back edges.
//   /// \param HasBackEdges denotes whether any back edges start at \p BB.
//   ///
//   /// \returns true if the scope of this PotCtrlDepBeg has ended.
//   bool progressCtrlPaths(
//       MachineBasicBlock *MBB,
//       std::unordered_set<MachineBasicBlock *> *SuccessorsWOBackEdges,
//       bool HasBackEdges);

//   /// Annotates a ctrl dependency from a given ending to this beginning.
//   ///
//   /// \param PathTo2 the path the annotation pass took to discover \p I2.
//   /// \param PathToViaFiles2 the path the annotation pass took to discover \p
//   /// I2. \param I2 the instruction where the ctrl dependency ends.
//   // void addCtrlDep(std::string ID2, std::string PathToViaFiles2,
//   //                 MachineInstr *MI2) const;

//   static bool classof(const DepHalf *VDH) {
//     return VDH->getKind() == DK_CtrlBeg;
//   }

// private:
//   /// A string representation of the branch instruction's location
//   const std::string BranchID;

//   // Set to true if this PotCtrlDepBeg cannot be resolved
//   // in the current function, e.g. because the branch inst is located in a
//   // function which calls the current function.
//   bool Resolvable;

//   // The set of paths which are induced by the branch instruction. Paths
//   // are represented by their 'head', i.e. the BB they are currently at as
//   per
//   // the BFS.
//   std::unordered_set<MachineBasicBlock *> CtrlPaths;

//   PotCtrlDepBeg(MachineInstr *MI, std::string BegID, std::string
//   PathToViaFiles,
//                 std::string BranchID, bool Resolvable = true)
//       : DepHalf(MI, BegID, PathToViaFiles, DK_CtrlBeg), BranchID{BranchID},
//         Resolvable{Resolvable}, CtrlPaths(){};
// };

// class VerDepHalf : public DepHalf {
// public:
//   enum BrokenByType { BrokenDC, PToF };

//   void setBrokenBy(BrokenByType BB) { BrokenBy = BB; }

//   std::string getBrokenBy() {
//     switch (BrokenBy) {
//     case BrokenDC:
//       return "by breaking the dependency chain";
//     case PToF:
//       return "by converting a partial dependency to a full dependency";
//     }
//   }

//   std::string const &getParsedDepHalfID() const { return ParsedDepHalfID; }

//   std::string const &getParsedpathTOViaFiles() const {
//     return ParsedPathToViaFiles;
//   }

//   MachineInstr *const &getInst() const { return MI; };

//   virtual ~VerDepHalf(){};

//   static bool classof(const DepHalf *VDH) {
//     return VDH->getKind() >= DK_VerAddrBeg && VDH->getKind() <=
//     DK_VerCtrlEnd;
//   }

//   std::string const &getParsedID() const { return ParsedID; }

// protected:
//   VerDepHalf(MachineInstr *MI, std::string ParsedID, std::string DepHalfID,
//              std::string PathToViaFiles, std::string ParsedDepHalfID,
//              std::string ParsedPathToViaFiles, DepKind Kind)
//       : DepHalf(MI, DepHalfID, PathToViaFiles, Kind), ParsedID(ParsedID),
//         ParsedDepHalfID(ParsedDepHalfID), ParsedPathToViaFiles{
//                                               ParsedPathToViaFiles} {}

// private:
//   // Shows how this dependency got broken
//   BrokenByType BrokenBy;

//   // The ID which identifies the two metadata annotations for this
//   dependency. const std::string ParsedID;

//   // The PathTo which was attached to the metadata annotation, i.e. the
//   // path to I in unoptimised IR.
//   const std::string ParsedDepHalfID;

//   const std::string ParsedPathToViaFiles;
// };

// class VerAddrDepBeg : public VerDepHalf {
// public:
//   VerAddrDepBeg(MachineInstr *MI, std::string ParsedID, std::string
//   DepHalfID,
//                 std::string PathToViaFiles, std::string ParsedPathTo,
//                 std::string ParsedPathToViaFiles)
//       : VerDepHalf(MI, ParsedID, DepHalfID, PathToViaFiles, ParsedPathTo,
//                    ParsedPathToViaFiles, DK_VerAddrBeg) {}

//   static bool classof(const DepHalf *VDH) {
//     return VDH->getKind() == DK_VerAddrBeg;
//   }
// };

// class VerCtrlDepBeg : public VerDepHalf {
// public:
//   VerCtrlDepBeg(MachineInstr *MI, std::string ParsedID, std::string
//   DepHalfID,
//                 std::string PathToViaFiles, std::string ParsedDepHalfID,
//                 std::string ParsedPathToViaFiles, std::string ParsedBranchID)
//       : VerDepHalf(MI, ParsedID, DepHalfID, PathToViaFiles, ParsedDepHalfID,
//                    ParsedPathToViaFiles, DK_VerCtrlBeg),
//         ParsedBranchID(ParsedBranchID) {}

//   const std::string &getParsedBranchID() const { return ParsedBranchID; }

//   static bool classof(const DepHalf *VDH) {
//     return VDH->getKind() == DK_VerCtrlBeg;
//   }

// private:
//   // A string representation of the path the BFS took in unoptimized IR to
//   // discover the branch instruction. Is retrived from the metadata
//   annotation. const std::string ParsedBranchID;
// };

// class VerAddrDepEnd : public VerDepHalf {
// public:
//   VerAddrDepEnd(MachineInstr *MI, std::string ParsedID, std::string
//   DepHalfID,
//                 std::string PathToViaFiles, std::string ParsedDepHalfID,
//                 std::string ParsedPathToViaFiles, bool ParsedFDep)
//       : VerDepHalf(MI, ParsedID, DepHalfID, PathToViaFiles, ParsedDepHalfID,
//                    ParsedPathToViaFiles, DK_VerAddrEnd),
//         ParsedFDep(ParsedFDep) {}

//   const bool &getParsedFullDep() const { return ParsedFDep; }

//   static bool classof(const DepHalf *VDH) {
//     return VDH->getKind() == DK_VerAddrEnd;
//   }

// private:
//   // Denotes whether the address dependency was annotated as a full
//   dependency
//   // or a partial dependency. The value is obtained from the metadata
//   // annotation.
//   const bool ParsedFDep;
// };

// class VerCtrlDepEnd : public VerDepHalf {
// public:
//   VerCtrlDepEnd(MachineInstr *MI, std::string ParsedID, std::string
//   DepHalfID,
//                 std::string PathToViaFiles, std::string ParsedDepHalfID,
//                 std::string ParsedPathToViaFiles)
//       : VerDepHalf(MI, ParsedID, DepHalfID, PathToViaFiles, ParsedDepHalfID,
//                    ParsedPathToViaFiles, DK_VerCtrlEnd) {}

//   static bool classof(const DepHalf *VDH) {
//     return VDH->getKind() == DK_VerCtrlEnd;
//   }
// };

// // //</editor-fold>
// using InterprocBFSRes =
//     std::pair<DepHalfMap<PotAddrDepBeg>, DepHalfMap<PotCtrlDepBeg>>;

// class BFSCtx {
// public:
//   BFSCtx(MachineBasicBlock *MBB) : MBB(MBB){};

//   ~BFSCtx() {
//     if (!CallPath->empty()) {
//       CallPath->pop_back();
//     }
//   }

//   /// Runs the BFS algorithm in the given context. This function is called at
//   /// the beginning of any function including those which are encountered
//   /// through interprocedural analysis.
//   void runBFS();

//   /// Update all PotAddrDepBegs in the current context after a BasicBlock has
//   /// been visited by the BFS. 'Updating' referes to moving the DepChains
//   along
//   /// to successors of the BB the BFS just visited.
//   ///
//   /// \param MBB the BB the BFS just visited.
//   /// \param SBB one of \p BB's successors
//   /// \param BEDsForBB the back edge destination map.
//   void progressAddrDepDCPaths(MachineBasicBlock *MBB, MachineBasicBlock *SBB,
//                               BBtoBBSetMap &BEDsForBB);

//   /// Tries to delete unused DepChains for all PotAddrDepBegs in
//   /// the current context.
//   ///
//   /// \param MBB the BB the BFS just visited.
//   /// \param BEDs the set of back edge destinations for \p MBB.
//   void deleteAddrDepDCsAt(MachineBasicBlock *MBB,
//                           std::unordered_set<MachineBasicBlock *> &BEDs);

//   /// Checks if a function call has arguments which are part of DepChains in
//   the
//   /// current context. This function is expected to be called at the
//   beginning
//   /// of an interprocedural analysis and might reset DepChains if they don't
//   run
//   /// through any of the call's arguments.
//   ///
//   /// \param CI the function call to be checked.
//   /// \param ADBs the current ADBs.
//   /// \param ADBsForCall the PotAddrDepBegs which will be
//   ///  carried over to the called function. This map is left untouched if
//   none
//   ///  of the call's arguments are part of a DepChain.
//   void handleDependentFunctionArgs(MachineInstr *CI, MachineBasicBlock *MBB);

//   void handleCallInst(const MachineInstr &);
//   void handleLoadStoreInst(const MachineInstr &);
//   void handleBranchInst(const MachineInstr &);
//   void handleReturnInstruction(const MachineInstr &);
//   void handleInstruction(const MachineInstr &);

// protected:
//   MachineBasicBlock *MBB;

//   // All potential address dependency beginnings (ADBs) which are being
//   tracked. DepHalfMap<PotAddrDepBeg> ADBs;

//   // All potential control dependency beginnings (CDBs) which are being
//   tracked. DepHalfMap<PotCtrlDepBeg> CDBs;

//   // Potential beginnings where the return value is part of the DepChain.
//   DepHalfMap<PotAddrDepBeg> ReturnedADBs;

//   // All PotCtrlDeps which begin in the current function and haven't been
//   // resloed when the function returns.
//   DepHalfMap<PotCtrlDepBeg> ReturnedCDBs;

//   // The path which the BFS took to reach BB.
//   std::shared_ptr<CallPathStack> CallPath;

//   /// Prepares a newly created BFSCtx for interprocedural analysis.
//   ///
//   /// \param BB the first BasicBlock in the called function.
//   /// \param CallI the call instruction whose called function begins with \p
//   BB. void prepareInterproc(MachineBasicBlock *MBB, MachineInstr *CallI);

//   /// Spawns an interprocedural BFS from the current context.
//   ///
//   /// \param FirstBB the first BasicBlock of the called function.
//   /// \param CallI the call instructions which calls the function beginning
//   with
//   /// \p FirstBB.
//   InterprocBFSRes runInterprocBFS(MachineBasicBlock *FirstMBB,
//                                   MachineInstr *CallI);

//   /// Helper function for handleDependentFunctionArgs(). Checks if all
//   arguments
//   /// of a function call are part of all of a given PotAddrDepBeg's DepChains
//   /// and adds all depenet arguments to a given set. This function is used
//   for
//   /// determining whether a PotAddrDepBeg can carry over as potential full
//   /// dependency beginning into the interprocedural analysis.
//   ///
//   /// \param ADB the PotAddrDepBeg in question.
//   /// \param CallI the call instruction whose arguments should be checked
//   ///  against \p ADB's dep chains.
//   /// \param DependentArgs the set which will contain all dependent function
//   ///  arguments on return.
//   ///
//   /// \returns true if all of \p CallI's arguments are part of all of \p
//   ADB's
//   ///  DepChains.
//   //  bool areAllFunctionArgsPartOfAllDepChains(
//   //      PotAddrDepBeg &ADB, MachineInstr *CallI,
//   //      std::unordered_set<Value *> &DependentArgs);

//   unsigned recLevel() { return CallPath->size(); }

//   constexpr unsigned recLimit() const;

//   /// Checks whether the BFS can visit a given BB and adds it to the BFSQueue
//   if
//   /// this is the case.
//   ///
//   /// \param SBB the successor the BFS wants to visit.
//   /// \param BFSInfo the BFS Info for the current function.
//   /// \param BEDs the set of back edge destinations for the current BB.
//   ///
//   /// \returns true if the BFS has seen all of \p SBB's predecessors.
//   bool bfsCanVisit(MachineBasicBlock *SBB,
//                    std::unordered_map<MachineBasicBlock *, BFSBBInfo>
//                    &BFSInfo, std::unordered_set<MachineBasicBlock *> &BEDs);

//   std::string getFullPath(MachineInstr *MI, bool viaFiles = false) {
//     return convertPathToString(viaFiles) + getInstLocationString(MI,
//     viaFiles);
//   }

//   std::string getFullPathViaFiles(MachineInstr *MI) {
//     return convertPathToString() + getInstLocationString(MI);
//   }

//   std::string convertPathToString(bool viaFiles = false) {
//     std::string PathStr{""};

//     for (auto &CallI : *CallPath)
//       PathStr += (getInstLocationString(CallI, viaFiles) + "  ");

//     return PathStr;
//   }

//   void parseDepHalfString(StringRef Annot,
//                           SmallVector<std::string, 5> &AnnotData);

//   void buildBackEdgeMap(BBtoBBSetMap *BEDsForBB, MachineFunction *F);

//   void buildBFSInfo(std::unordered_map<MachineBasicBlock *, BFSBBInfo>
//   *BFSInfo,
//                     BBtoBBSetMap *BEDsForBB, MachineFunction *F);

//   void removeBackEdgesFromSuccessors(
//       MachineBasicBlock *MBB, std::unordered_set<MachineBasicBlock *> *BEDs,
//       std::unordered_set<MachineBasicBlock *> *SuccessorsWOBackEdges) {
//     for (auto *SBB : MBB->successors()) {
//       if (BEDs->find(SBB) == BEDs->end()) {
//         SuccessorsWOBackEdges->insert(SBB);
//       }
//     }
//   }

//   std::string buildInlineString(MachineInstr *MI);
// };

// class VerCtx : public BFSCtx {
// public:
//   VerCtx(MachineBasicBlock *MBB,
//          std::shared_ptr<DepHalfMap<VerAddrDepBeg>> BrokenADBs,
//          std::shared_ptr<DepHalfMap<VerAddrDepEnd>> BrokenADEs,
//          std::shared_ptr<DepHalfMap<VerCtrlDepBeg>> BrokenCDBs,
//          std::shared_ptr<DepHalfMap<VerCtrlDepEnd>> BrokenCDEs,
//          std::shared_ptr<IDReMap> RemappedIDs,
//          std::shared_ptr<VerIDSet> VerifiedIDs)
//       : BFSCtx(MBB), BrokenADBs(BrokenADBs), BrokenADEs(BrokenADEs),
//         BrokenCDBs(BrokenCDBs), BrokenCDEs(BrokenCDEs),
//         RemappedIDs(RemappedIDs), VerifiedIDs(VerifiedIDs) {}

//   VerCtx(VerCtx &VC, MachineBasicBlock *MBB, MachineInstr *CallI) :
//   VerCtx(VC) {
//     prepareInterproc(MBB, CallI);
//     ReturnedADBs.clear();
//     ReturnedCDBs.clear();
//   }

//   void handleDepAnnotations(MachineInstr *MI, MDNode *MDAnnotation);

// private:
//   // Contains all unverified address dependency beginning annotations.
//   std::shared_ptr<DepHalfMap<VerAddrDepBeg>> BrokenADBs;
//   // Contains all unverified address dependency ending annotations.
//   std::shared_ptr<DepHalfMap<VerAddrDepEnd>> BrokenADEs;
//   // Contains all unverified control dependency beginning annotations.
//   std::shared_ptr<DepHalfMap<VerCtrlDepBeg>> BrokenCDBs;
//   // Contains all unverified control dependency ending annotations.
//   std::shared_ptr<DepHalfMap<VerCtrlDepEnd>> BrokenCDEs;

//   // All remapped IDs which were discovered from the current root function.
//   std::shared_ptr<IDReMap> RemappedIDs;

//   // Contains all IDs which have been verified in the current module.
//   std::shared_ptr<VerIDSet> VerifiedIDs;

//   bool handleAddrDepID(std::string const &ID, MachineInstr *MI,
//                        std::string &ParsedPathTo,
//                        std::string &ParsedPathToViaFiles, bool
//                        ParsedFullDep);

//   bool handleCtrlDepID(std::string const &ID, MachineInstr *MI,
//                        std::string &ParsedPathTo,
//                        std::string &ParsedPathToViaFiles);

//   void updateID(std::string &ID) {
//     if (RemappedIDs->find(ID) == RemappedIDs->end()) {
//       RemappedIDs->emplace(ID, std::unordered_set<std::string>{ID + "-#1"});
//       ID = ID + "-#1";
//     } else {
//       auto S = RemappedIDs->at(ID).size();
//       RemappedIDs->at(ID).insert(ID + "-#" + std::to_string(S + 1));
//       ID = ID + "-#" + std::to_string(S + 1);
//     }
//   }

//   void markIDAsVerified(std::string &ParsedID, bool ctrl = false) {
//     auto delID = [](auto &ID, auto &Bs, auto &Es, auto &RemappedIDs) {
//       Bs->erase(ID);
//       Es->erase(ID);

//       if (RemappedIDs->find(ID) != RemappedIDs->end())
//         for (auto const &ReID : RemappedIDs->at(ID)) {
//           Bs->erase(ReID);
//           Es->erase(ReID);
//         }
//     };

//     if (ctrl)
//       delID(ParsedID, BrokenCDBs, BrokenCDEs, RemappedIDs);
//     else
//       delID(ParsedID, BrokenADBs, BrokenADEs, RemappedIDs);

//     VerifiedIDs->insert(ParsedID);
//     RemappedIDs->erase(ParsedID);
//   }
// };

// // //<editor-fold desc="DepHalf">
// std::string DepHalf::getID() const {
//   if (isa<PotAddrDepBeg>(this)) {
//     return this->ID;
//   }
//   if (const auto *PCDB = dyn_cast<PotCtrlDepBeg>(this)) {
//     return this->ID + "\n/\\" + PCDB->getBranchID();
//   }
//   if (const auto *VDH = dyn_cast<VerDepHalf>(this))
//     return VDH->getParsedID();
//   llvm_unreachable("unhandled case in getID");
// }
// // //</editor-fold>

// // //<editor-fold desc="PotAddrDepBeg">
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
                                 InstIdentifier InstID) {
  if (!isAt(MBB)) {
    return;
  }

  DCM.at(MBB).first.insert(InstID);
}

void PotAddrDepBeg::addToDCUnion(llvm::MachineBasicBlock *MBB,
                                 InstIdentifier InstID) {
  if (!isAt(MBB)) {
    return;
  }

  DCM.at(MBB).second.insert(InstID);
}

bool PotAddrDepBeg::tryAddValueToDepChains(llvm::MachineInstr *MI,
                                           InstIdentifier InstCmp,
                                           InstIdentifier InstAdd) {
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
    // TODO: get actual operand that is being stored
    //    auto *PotRedefOp = MI->getOperand(1);
    //    if (DCInter.find(PotRedefOp) != DCInter.end())
    //      DCInter.erase(PotRedefOp);
  }

  // Add to DCUnion and account for redefinition
  if (DCUnion.find(InstCmp) != DCUnion.end()) {
    DCUnion.insert(InstAdd);
    Ret = true;
  } else if (MI->mayStore()) {
    // TODO: get actual operand that is being stored
    //    auto *PotRedefOp = I->getOperand(1);
    //    if (DCUnion.find(PotRedefOp) != DCUnion.end())
    //      DCUnion.erase(PotRedefOp);
  }

  return Ret;
}

bool PotAddrDepBeg::belongsToAllDepChains(llvm::MachineBasicBlock *MBB,
                                          InstIdentifier InstID) const {
  if (DCM.find(MBB) == DCM.end()) {
    return false;
  }
  auto &DCInter = DCM.at(MBB).first;

  return DCInter.find(InstID) != DCInter.end() && DCM.size() == 1;
}

bool PotAddrDepBeg::belongsToDepChain(llvm::MachineBasicBlock *MBB,
                                      InstIdentifier InstID) const {
  if (DCM.find(MBB) == DCM.end()) {
    return false;
  }

  auto &DCUnion = DCM.at(MBB).second;

  return DCUnion.find(InstID) != DCUnion.end();
}

bool PotAddrDepBeg::belongsToSomeNotAllDepChains(llvm::MachineBasicBlock *MBB,
                                                 InstIdentifier InstID) const {
  if (DCM.find(MBB) == DCM.end()) {
    return false;
  }

  return !belongsToAllDepChains(MBB, InstID) && belongsToDepChain(MBB, InstID);
}

bool PotAddrDepBeg::depChainsShareValue(
    std::list<std::pair<MachineBasicBlock *, DepChain *>> &DCs,
    InstIdentifier InstID) const {
  for (auto &DCP : DCs) {
    if (DCP.second->find(InstID) == DCP.second->end()) {
      return false;
    }
  }

  return true;
}
// // //</editor-fold>

// // //<editor-fold desc="PotCtrlDepBeg">
// bool PotCtrlDepBeg::progressCtrlPaths(
//     llvm::MachineBasicBlock *MBB,
//     std::unordered_set<MachineBasicBlock *> *SuccessorsWOBackEdges,
//     bool HasBackEdges) {
//   // Skip beginnigns that lie outside the current BB's function. Necessary
//   // for interprocedural analysis.
//   if (!canResolve())
//     return false;

//   // Account for the case where there are no paths at the current BB, but the
//   // beginning isn't new.
//   if (!recentlyDiscovered() && !isAt(MBB))
//     return false;

//   // If the paths are empty, this dependency begins in BB. Only add
//   // successors and continue. Otherwise, continue below.
//   if (!recentlyDiscovered()) {
//     // Erase paths which run through the current BB.
//     // Only erase such paths if the current BB doesn't have a back edge or
//     // contains a return. If it does, the path through the back edge /
//     // reuturning block doesn't get resolved. Don't erase, only add
//     successors.
//     //
//     // This check also accounts for 'dead ends', which never get resolved
//     // either.
//     auto TerminatorInst = MBB->getFirstInstrTerminator();
//     //    if (!isa<ReturnInst>(BB->getTerminator()) && !HasBackEdges)
//     if ((!TerminatorInst.isEnd() && !TerminatorInst->isReturn()) &&
//         !HasBackEdges)
//       CtrlPaths.erase({MBB});

//     // If a control dependency gets resolved, there must be a point where
//     there
//     // is only one path left here, which is at the BB resolving the ctrl dep.
//     if (CtrlPaths.size() == 1)
//       if (SuccessorsWOBackEdges->size() == 1)
//         if (*SuccessorsWOBackEdges->begin() == *CtrlPaths.begin())
//           return true;
//   }

//   // Add paths for successors. If a path already is at a successor, the two
//   // paths merge.
//   for (auto &s : *SuccessorsWOBackEdges)
//     CtrlPaths.insert(s);

//   // Account for the case where the condition has a backedge, e.g. in a
//   do-while
//   // loop.
//   if (HasBackEdges)
//     CtrlPaths.insert(MBB);

//   return false;
// }
// // //</editor-fold>

// void BFSCtx::runBFS() {
//   // Maps a BB to the set of its back edge destinations (BEDs).
//   BBtoBBSetMap BEDsForBB;

//   buildBackEdgeMap(&BEDsForBB, MBB->getParent());

//   std::unordered_map<MachineBasicBlock *, BFSBBInfo> BFSInfo;

//   buildBFSInfo(&BFSInfo, &BEDsForBB, MBB->getParent());

//   std::queue<MachineBasicBlock *> BFSQueue = {};

//   BFSQueue.push(MBB);

//   while (!BFSQueue.empty()) {
//     auto &BB = BFSQueue.front();

//     for (auto &MI : *MBB) {
//       MI.dump();
//       if (MI.isCall()) {
//         errs() << "call inst\n" << (int)MI.getOperand(0).getType() << "\n";

//         handleCallInst(MI);
//       }
//       if (MI.mayLoadOrStore()) {
//         errs() << "load/store inst\n";

//         handleLoadStoreInst(MI);
//       }
//       if (MI.isBranch()) {
//         errs() << "branch inst\n";

//         handleBranchInst(MI);
//       }
//       if (MI.isReturn()) {
//         errs() << "return inst\n";

//         handleReturnInstruction(MI);
//       }
//       handleInstruction(MI);
//       //
//       //  MDNode *MDN = MI.getPCSections();
//       //  if (!MDN)
//       //    continue;
//       //
//       //  MDN->dump();
//     }

//     std::unordered_set<MachineBasicBlock *> SuccessorsWOBackEdges{};

//     removeBackEdgesFromSuccessors(MBB, &BEDsForBB.at(MBB),
//                                   &SuccessorsWOBackEdges);

//     for (auto &SBB : SuccessorsWOBackEdges) {
//       if (bfsCanVisit(SBB, BFSInfo, BEDsForBB.at(SBB)))
//         BFSQueue.push(SBB);

//       progressAddrDepDCPaths(BB, SBB, BEDsForBB);
//     }

//     deleteAddrDepDCsAt(BB, BEDsForBB.at(BB));

//     BFSQueue.pop();
//   }
// }

// bool BFSCtx::bfsCanVisit(
//     MachineBasicBlock *SBB,
//     std::unordered_map<MachineBasicBlock *, BFSBBInfo> &BFSInfo,
//     std::unordered_set<MachineBasicBlock *> &BEDs) {
//   auto &NextMaxHits{BFSInfo.at(SBB).MaxHits};
//   auto &NextCurrentHits{BFSInfo.at(SBB).CurrentHits};

//   if (NextMaxHits == 0 || ++NextCurrentHits == NextMaxHits)
//     return true;

//   return false;
// }

// void BFSCtx::progressAddrDepDCPaths(MachineBasicBlock *MBB,
//                                     MachineBasicBlock *SBB,
//                                     BBtoBBSetMap &BEDsForBB) {
//   for (auto &ADBP : ADBs) {
//     ADBP.second.progressDCPaths(MBB, SBB, BEDsForBB);
//   }
// }

// void BFSCtx::deleteAddrDepDCsAt(MachineBasicBlock *MBB,
//                                 std::unordered_set<MachineBasicBlock *>
//                                 &BEDs) {
//   for (auto &ADBP : ADBs) {
//     ADBP.second.deleteDCsAt(MBB, BEDs);
//   }
// }

// void BFSCtx::handleDependentFunctionArgs(MachineInstr *CI,
//                                          MachineBasicBlock *MBB) {
//   // if (!CI->isCall()) {
//   //   errs() << "Called handleDependentFunctionArgs on non-call
//   instruction.";
//   //   CI->dump();
//   //   return;
//   // }

//   // DepChain DependentArgs;

//   // for (auto &ADBP : ADBs) {
//   //   auto &ADB = ADBP.second;

//   //   bool FDep = allFunctionArgsPartOfAllDepChains(ADB, CI, DependentArgs);

//   //   // Instead of deleting an ADB if it doesn't run into a function, we
//   keep
//   //   it
//   //   // with an empty DCM, thereby ensuring that no further items can be
//   added
//   //   to
//   //   // the DepChain until control flow returns to this function, but still
//   //   // allowing an ending to be mapped to it when verifying.
//   //   if (DependentArgs.empty())
//   //     ADB.clearDCMap();
//   //   else {
//   //     ADB.resetDCMTo(MBB, FDep, DependentArgs);
//   //     ADB.addStepToPathFrom(CI);
//   //   }

//   //   DependentArgs.clear();
//   // }
// }

// // void prepareInterproc(MachineBasicBlock *MBB, MachineInstr *CallI) {}

// InterprocBFSRes runInterprocBFS(MachineBasicBlock *FirstMBB,
//                                 MachineInstr *CallI) {}

// constexpr unsigned BFSCtx::recLimit() const { return 4; }

// void BFSCtx::handleCallInst(const MachineInstr &MI) {
//   auto *MF = MI.getParent()->getParent();
//   auto &FunctionOperand = MI.getOperand(0);
//   assert(FunctionOperand.isGlobal() && "Expected operand to be a global");

//   auto &MMI = MF->getMMI();
//   auto *CalledF = MF->getFunction().getParent()->getFunction(
//       FunctionOperand.getGlobal()->getName());
//   if (!CalledF) {
//     errs() << "Called function '" << FunctionOperand.getGlobal()->getName()
//            << "' not found, ignoring\n";
//     return;
//   }
//   CalledF->dump();

//   auto &CalledMF = MMI.getOrCreateMachineFunction(*CalledF);

//   if (CalledMF.empty() || CalledF->isVarArg()) {
//     return;
//   }

//   if (this->recLevel() > this->recLimit()) {
//     return;
//   }

//   // TODO: run inter proc bfs
// }

// void BFSCtx::handleLoadStoreInst(const MachineInstr &MI) {}

// void BFSCtx::handleBranchInst(const MachineInstr &MI) {}

// void BFSCtx::handleReturnInstruction(const MachineInstr &MI) {}

// void BFSCtx::handleInstruction(const MachineInstr &MI) {
//   // TODO: add to dep chain for each operand
//   // need to walk back to find which instruction
//   // for (auto &ADBP : ADBs) {
//   //   ADBP.second.tryAddV // walk back and find id for each used register
//   // }
// }

namespace {

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

class BFSCtx {
public:
  BFSCtx(MachineBasicBlock *MBB) : MBB(MBB), ADBs() {}

  void runBFS();

private:
  MachineBasicBlock *MBB;

  DepHalfMap<PotAddrDepBeg> ADBs;

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
};

void BFSCtx::runBFS() {
  BBtoBBSetMap BEDsForBB;

  buildBackEdgeMap(&BEDsForBB, MBB->getParent());

  std::unordered_map<MachineBasicBlock *, BFSBBInfo> BFSInfo;

  buildBFSInfo(&BFSInfo, &BEDsForBB, MBB->getParent());

  std::queue<MachineBasicBlock *> BFSQueue = {};

  BFSQueue.push(MBB);

  while (!BFSQueue.empty()) {
    auto &MBB = BFSQueue.front();

    // TODO: do something with the MBB
    errs() << "Visiting MBB " << MBB->getNumber() << "\n";

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
  CheckDepsPass() : MachineFunctionPass(ID) {}

  bool runOnMachineFunction(MachineFunction &MF) override;
};

char CheckDepsPass::ID = 0;

bool CheckDepsPass::runOnMachineFunction(MachineFunction &MF) {
  errs() << "Running dep checker on function " << MF.getName().str() << "\n";
  BFSCtx BFSCtx(&*MF.begin());
  BFSCtx.runBFS();

  return false;
}

} // namespace

FunctionPass *llvm::createCheckDepsPass() { return new CheckDepsPass(); }
