//
//  Passes.h
//  uscc
//
//  Declares the opt passes supported by USCC
//
//  At the moment, there are four passes:
//     * Constant op removal
//     * Constant branch folding
//     * Removal of dead blocks from CFG
//     * Loop Invariant Code Motion (LICM)
//
//  These passes will execute if uscc is ran with -O
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------
#pragma once
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wconversion"
#include <llvm/Pass.h>
#include <llvm/Analysis/LoopPass.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Dominators.h>
#pragma clang diagnostic pop

using llvm::FunctionPass;
using llvm::LoopPass;

namespace uscc
{

namespace opt
{

// Helper function for registering the opt passes
void registerOptPasses(llvm::legacy::PassManager& pm);

// Declares the Constant Propagation Pass
struct ConstantOps : public FunctionPass
{
	static char ID;
	ConstantOps() : FunctionPass(ID) {}
	
	virtual bool runOnFunction(llvm::Function& F) override;
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage& Info) const override;
};

// Declares the Constant Branch Folding Pass
struct ConstantBranch : public FunctionPass
{
	static char ID;
	ConstantBranch() : FunctionPass(ID) {}
	
	virtual bool runOnFunction(llvm::Function& F) override;
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage& Info) const override;
};

// Declares the Dead Block Removal Pass
struct DeadBlocks : public FunctionPass
{
	static char ID;
	DeadBlocks() : FunctionPass(ID) {}
	
	virtual bool runOnFunction(llvm::Function& F) override;
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage& Info) const override;
};
	
// Loop invariant code motion
struct LICM : public LoopPass
{
	static char ID;
	LICM() : LoopPass(ID) {}
	
	virtual bool runOnLoop(llvm::Loop* L, llvm::LPPassManager& LPM) override;
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage& Info) const override;

	// Data regarding the current loop
	llvm::Loop* mCurrLoop;

	// The dominator tree for this loop
	llvm::DominatorTree* mDomTree;

	// Loop information for this loop
	llvm::LoopInfo* mLoopInfo;

	// Denotes whether or not loop has been modified
	bool mChanged;
};
	
} // opt
} // uscc