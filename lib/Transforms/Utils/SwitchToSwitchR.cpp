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

  SmallVector<std::pair<ConstantRange, BasicBlock*>, 32 > Cases;

  // Note: Internally we treat empty set as full set too.
  ConstantRange FullSet(Val->getType()->getScalarSizeInBits(), false);
  Cases.push_back(std::make_pair(FullSet, Default));

  for (SwitchInst::CaseIt
       i = SI->case_begin(), e = SI->case_end(); i != e; ++i) {
    const APInt &L = i.getCaseValue()->getValue();
    APInt U = L;

    // Do increment.
    if (U == APInt::getMaxValue(L.getBitWidth()))
      U = APInt::getMinValue(L.getBitWidth());
    else
      ++U;

    Cases.push_back(std::make_pair(ConstantRange(L, U), i.getCaseSuccessor()));
  }

  SwitchRInst::Create(Val, Cases, CurBlock, true /* Sort the cases */);
  CurBlock->getInstList().erase(SI);

  ++NumSwitchRInserted;
}
