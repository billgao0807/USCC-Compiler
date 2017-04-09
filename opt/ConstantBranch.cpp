//
//  ContantBranch.cpp
//  uscc
//
//  Implements Constant Branch Folding opt pass.
//  This converts conditional branches on constants to
//  unconditional branches.
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
#pragma clang diagnostic pop
#include <set>

using namespace llvm;

namespace uscc
{
namespace opt
{
	
bool ConstantBranch::runOnFunction(Function& F)
{
	bool changed = false;
	
    std::set<BranchInst*> removeSet;
    // PA5: Implement
    for (auto BB = F.getBasicBlockList().begin(); BB != F.getBasicBlockList().end(); ++BB){
        for (auto i = BB->begin(); i != BB->end(); ++i){
            if (isa<BranchInst>(*i)) {
                auto br = cast<BranchInst>(i);
                if (br->isConditional()){
                    if(isa<ConstantInt>(br->getCondition())){
                        removeSet.insert(br);
                    }
                }
            }
        }
    }
    
    for (auto br : removeSet){
        changed = true;
        auto cond = cast<ConstantInt>(br->getCondition());
        auto parent = br->getParent();
        if (cond->isOne()) {
            auto newInst = BranchInst::Create(br->getSuccessor(0));
            parent->getInstList().insert(br, newInst);
            br->getSuccessor(1)->removePredecessor(parent);
        }
        else {
            auto newInst = BranchInst::Create(br->getSuccessor(1));
            parent->getInstList().insert(br, newInst);
            br->getSuccessor(0)->removePredecessor(parent);
        }
        br->eraseFromParent();
    }
    
    return changed;
}

void ConstantBranch::getAnalysisUsage(AnalysisUsage& Info) const
{
	// PA5: Implement
    Info.addRequired<ConstantOps>();
}
	
} // opt
} // uscc

char uscc::opt::ConstantBranch::ID = 0;
