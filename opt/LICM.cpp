//
//  LICM.cpp
//  uscc
//
//  Implements basic loop invariant code motion
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------
#include "Passes.h"
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wconversion"
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/ValueTracking.h>
#pragma clang diagnostic pop

using namespace llvm;

namespace uscc
{
namespace opt
{
    
bool LICM::isSafeToHoistInstr(llvm::Instruction* inst){
    return (mCurrLoop->hasLoopInvariantOperands(inst) &&
            isSafeToSpeculativelyExecute(inst) && (
            isa<BinaryOperator>(inst) || isa<CastInst>(inst) || isa<SelectInst>(inst) ||
            isa<GetElementPtrInst>(inst) || isa<CmpInst>(inst))
            );
}

void LICM::hoistInstr(llvm::Instruction* inst){
    auto preheaderBlock = mCurrLoop->getLoopPreheader();
    auto terminator = preheaderBlock->getTerminator();
    inst->moveBefore(terminator);
    mChanged = true;
}

void LICM::hoistPreOrder(llvm::DomTreeNode *node){
    auto block = node->getBlock();
    if (mLoopInfo->getLoopFor(block) == mCurrLoop){
        for (auto it = block->begin(); it != block->end(); ) {
            auto currInst = it;
            ++it;
            if (isSafeToHoistInstr(currInst)) {
                hoistInstr(currInst);
            }
        }
    }
    for (auto child : node->getChildren()){
        hoistPreOrder(child);
    }
}
    
bool LICM::runOnLoop(llvm::Loop *L, llvm::LPPassManager &LPM)
{
	mChanged = false;
	
	// PA5: Implement
    // Save the current loop
    mCurrLoop = L;
    // Grab the loop info
    mLoopInfo = &getAnalysis<LoopInfo>();
    // Grab the dominator tree
    mDomTree = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    
    auto node = mDomTree->getRootNode();
    hoistPreOrder(node);

	return mChanged;
}

void LICM::getAnalysisUsage(AnalysisUsage &Info) const
{
	// PA5: Implement
    // LICM does not modify the CFG
    Info.setPreservesCFG();
    // Execute after dead blocks have been removed
    Info.addRequired<DeadBlocks>();
    // Use the built-in Dominator tree and loop info passes
    Info.addRequired<DominatorTreeWrapperPass>();
    Info.addRequired<LoopInfo>();
}


	
} // opt
} // uscc

char uscc::opt::LICM::ID = 0;
