//
//  DeadBlocks.cpp
//  uscc
//
//  Implements Dead Block Removal optimization pass.
//  This removes blocks from the CFG which are unreachable.
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
#include <llvm/IR/CFG.h>
#include <llvm/ADT/DepthFirstIterator.h>
#pragma clang diagnostic pop
#include <set>

using namespace llvm;

namespace uscc
{
namespace opt
{
	
bool DeadBlocks::runOnFunction(Function& F)
{
	bool changed = false;
	
	// PA5: Implement
    std::set<BasicBlock*> visitedBlock;
    std::set<BasicBlock*> visitingBlock;
    visitedBlock.insert(F.begin());
    visitingBlock.insert(F.begin());
    while (!visitingBlock.empty()) {
        auto block = *(visitingBlock.begin());
        visitingBlock.erase(block);
        
        if (visitedBlock.find(block) == visitedBlock.end()) {
            visitedBlock.insert(block);
        }
        
        for (auto it = succ_begin(block); it != succ_end(block); ++it) {
            if (visitedBlock.find(block) == visitedBlock.end()) {
                visitingBlock.insert(block);
            }
        }
        for (auto it = succ_begin(block); it != succ_end(block); ++it) {
            if (visitedBlock.find(*it) == visitedBlock.end()
                && visitingBlock.find(*it) == visitingBlock.end()){
                visitingBlock.insert(*it);
            }
        }
        visitedBlock.insert(block);
        visitingBlock.erase(block);
    }
    
    std::set<BasicBlock*> unreachableSet;
    for (auto it = F.begin(); it != F.end(); ++it) {
        if (visitedBlock.find(it) == visitedBlock.end()) {
            unreachableSet.insert(it);
        }
    }
    
    for (auto block : unreachableSet){
        for (auto it = succ_begin(block); it != succ_end(block); ++it) {
            it->removePredecessor(block);
        }
        block->eraseFromParent();
    }

	
	return changed;
}
	
void DeadBlocks::getAnalysisUsage(AnalysisUsage& Info) const
{
	// PA5: Implement
    Info.addRequired<ConstantBranch>();
}

} // opt
} // uscc

char uscc::opt::DeadBlocks::ID = 0;
