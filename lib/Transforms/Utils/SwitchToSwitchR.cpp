//===- SwitchToSwitchR.cpp - Replace 'switch' instruction with 'switchr' --===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// The SwitchToSwitchR transformation rewrites classic 'switch' instructions 
// with 'switchr' ones.
// Note, 'switchr' instruction introduced to add
// case ranges support. If 'switch' contains consecutive cases with the
// same successor, these cases will automatically converted into case-range
// in 'switchr'.
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "switchtoswitchr"

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/PassRegistry.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/ConstantRange.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
using namespace llvm;

STATISTIC(NumSwitchRInserted, "Number of 'switchr' was inserted.");

namespace {
  /// SwitchToSwitchR Pass - Replace all SwitchInst instructions with chained branch
  /// instructions.
  class SwitchToSwitchR : public FunctionPass {
  public:
    static char ID; // Pass identification, replacement for typeid
    SwitchToSwitchR() : FunctionPass(ID) {
      initializeSwitchToSwitchRPass(*PassRegistry::getPassRegistry());
    }

    virtual bool runOnFunction(Function &F);

  private:
    void processSwitchInst(SwitchInst *SI);
    void optimizeTerminator(Instruction* ToBeRemoved,
                            Value* Condition,
                            SwitchRInst::SuccessorsArrayRef Successors,
                            SwitchRInst::CasesArrayRef Cases);
  };
}

char SwitchToSwitchR::ID = 0;
INITIALIZE_PASS(SwitchToSwitchR, "switchtoswitchr",
                "Replaces classic 'switch' instructions with 'switchr' ones.",
                false, false)

// Publicly exposed interface to pass...
char &llvm::SwitchToSwitchRID = SwitchToSwitchR::ID;
// createSwitchToSwitchRPass - Interface to this file...
FunctionPass *llvm::createSwitchToSwitchRPass() {
  return new SwitchToSwitchR();
}

bool SwitchToSwitchR::runOnFunction(Function &F) {
  bool Changed = false;

  for (Function::iterator I = F.begin(), E = F.end(); I != E; ) {
    BasicBlock *Cur = I++; // Advance over block so we don't traverse new blocks

    if (SwitchInst *SI = dyn_cast<SwitchInst>(Cur->getTerminator())) {
      Changed = true;
      processSwitchInst(SI);
    }
  }

  return Changed;
}

struct SwitchRCaseCmp {
  bool operator()(const std::pair<ConstantRange, unsigned> &LHS,
                  const std::pair<ConstantRange, unsigned> &RHS) {
    if (LHS.first.getLower().ult(RHS.first.getLower()))
      return true;
    if (RHS.first.getLower().ult(LHS.first.getLower()))
      return false;
    return (LHS.first.getSetSize().ult(RHS.first.getSetSize()));
  }
};

// processSwitchInst - Replace the specified switch instruction with a sequence
// of chained if-then insts in a balanced binary search.
//
void SwitchToSwitchR::processSwitchInst(SwitchInst *SI) {
  BasicBlock *CurBlock = SI->getParent();
  Value *Val = SI->getCondition();  // The value we are switching on...
  BasicBlock* Default = SI->getDefaultDest();

  // If there is only the default destination,
  // don't bother with the code below.
  if (!SI->getNumCases()) {
    BranchInst::Create(Default, CurBlock);
    CurBlock->getInstList().erase(SI);
    return;
  }

  SmallVector<BasicBlock*, 32> Successors(SI->getNumSuccessors(), 0);
  SmallVector<std::pair<ConstantRange, unsigned>, 32 > Cases;

  for (unsigned i = 0, e = SI->getNumSuccessors(); i != e; ++i)
    Successors[i] = SI->getSuccessor(i);

  // Note: Internally we treat empty set as full set too.
  ConstantRange FullSet(Val->getType()->getScalarSizeInBits(), false);
  Cases.push_back(std::make_pair(FullSet, 0));

  for (SwitchInst::CaseIt
       i = SI->case_begin(), e = SI->case_end(); i != e; ++i) {
    const APInt &L = i.getCaseValue()->getValue();
    APInt U = L;

    // Do increment.
    if (U == APInt::getMaxValue(L.getBitWidth()))
      U = APInt::getMinValue(L.getBitWidth());
    else
      ++U;

    Cases.push_back(std::make_pair(ConstantRange(L, U), i.getSuccessorIndex()));
  }

  std::sort(Cases.begin(), Cases.end(), SwitchRCaseCmp());

  optimizeTerminator(SI, Val, Successors, Cases);
}

struct MergeInfo {
  MergeInfo() : Index((unsigned)(-1)), NumMergedIn((unsigned)(-1)) {}
  MergeInfo(unsigned I, unsigned NMergedIn)
  : Index(I), NumMergedIn(NMergedIn) {}
  unsigned Index;
  unsigned NumMergedIn; // How many duplicates were merged.
};

void SwitchToSwitchR::optimizeTerminator(
    Instruction* ToBeRemoved,
    Value* Condition,
    SwitchRInst::SuccessorsArrayRef Successors,
    SwitchRInst::CasesArrayRef Cases) {

  // Don't like to read ab-ra-ca-da-bra::iterator, we better do typedef.
  typedef DenseMap<BasicBlock*, MergeInfo> SuccessorsDenseMap;
  typedef SuccessorsDenseMap::iterator SuccessorsDenseMapIt;

  SuccessorsDenseMap SuccessorsMap;
  SmallVector<std::pair<ConstantRange, unsigned>, 32 > NewCases;

  // Analyze successors, calculate how many would be merged.
  for (unsigned i = 0, e = Successors.size(); i != e; ++i) {
    std::pair<SuccessorsDenseMapIt, bool> mapIt =
        SuccessorsMap.insert(std::make_pair(
            Successors[i], MergeInfo(SuccessorsMap.size(), 0)));
    if (!mapIt.second)
      ++mapIt.first->second.NumMergedIn;
  }

  // Create new cases array. Instead just re-index successors.
  for (unsigned i = 0, e = Cases.size(); i != e; ++i) {
    BasicBlock* Successor = Successors[Cases[i].second];
    unsigned NewSuccessorIndex = SuccessorsMap[Successor].Index;
    NewCases.push_back(std::make_pair(Cases[i].first, NewSuccessorIndex));
  }

  // Convert SuccessorsMap into new Successors array.
  SmallVector<BasicBlock*, 32> NewSuccessors(SuccessorsMap.size(), 0);
  for (SuccessorsDenseMapIt i = SuccessorsMap.begin(), e = SuccessorsMap.end();
       i != e; ++i)
    NewSuccessors[i->second.Index] = i->first;

  // Create new 'switchr' instruction.
  BasicBlock* CurBlock = ToBeRemoved->getParent();

  SwitchRInst::Create(Condition, NewSuccessors, NewCases, CurBlock);
  CurBlock->getInstList().erase(ToBeRemoved);

  ++NumSwitchRInserted;
}
