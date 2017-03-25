//
//  SSABuilder.cpp
//  uscc
//
//  Implements SSABuilder class
//  
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#include "SSABuilder.h"
#include "../parse/Symbols.h"

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wconversion"
#include <llvm/IR/Value.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#pragma clang diagnostic pop

#include <list>

using namespace uscc::opt;
using namespace uscc::parse;
using namespace llvm;

// Called when a new function is started to clear out all the data
void SSABuilder::reset()
{
	// PA4: Implement
	for(auto pair: mVarDefs) {
		delete pair.second;
	}
	for(auto pair: mIncompletePhis) {
		delete pair.second;
	}
	mVarDefs.clear();
	mIncompletePhis.clear();
	mSealedBlocks.clear();
}

// For a specific variable in a specific basic block, write its value
void SSABuilder::writeVariable(Identifier* var, BasicBlock* block, Value* value)
{
	// PA4: Implement
	(*mVarDefs[block])[var] = value;
}

// Read the value assigned to the variable in the requested basic block
// Will recursively search predecessor blocks if it was not written in this block
Value* SSABuilder::readVariable(Identifier* var, BasicBlock* block)
{
	// PA4: Implement
	if (mVarDefs[block]->find(var) != mVarDefs[block]->end()) {
		return (*mVarDefs[block])[var];
	}
	return readVariableRecursive(var, block);
}

// This is called to add a new block to the maps
void SSABuilder::addBlock(BasicBlock* block, bool isSealed /* = false */)
{
	// PA4: Implement
	mVarDefs[block] = new SubMap;
	mIncompletePhis[block] = new SubPHI;
	if (isSealed) sealBlock(block);
}

// This is called when a block is "sealed" which means it will not have any
// further predecessors added. It will complete any PHI nodes (if necessary)
void SSABuilder::sealBlock(llvm::BasicBlock* block)
{
	// PA4: Implement
	for (auto var: *mIncompletePhis[block]) {
		addPhiOperands(var.first, var.second);
	}
	mSealedBlocks.insert(block);
	for (auto var : *mVarDefs[block]){
		if (isa<PHINode>(var.second))
			var.second = tryRemoveTrivialPhi(cast<PHINode>(var.second));
	}
}

// Recursively search predecessor blocks for a variable
Value* SSABuilder::readVariableRecursive(Identifier* var, BasicBlock* block)
{
	Value* retVal = nullptr;
	
	// PA4: Implement
	if (mSealedBlocks.find(block) == mSealedBlocks.end()) {
//		auto phi = PHINode::Create(var->llvmType(), 0, Twine("incmpphi"), block);
		auto phi = block->empty() ? PHINode::Create(var->llvmType(), 0, Twine("PhiNodeSeal"), block) : PHINode::Create(var->llvmType(), 0, Twine("PhiNodeSeal"), &block->front());
		(*mIncompletePhis[block])[var] = phi;
		retVal = phi;
	} else if (block->getSinglePredecessor() != nullptr) {
		retVal = readVariable(var, block->getSinglePredecessor());
	} else {
//		auto phi = PHINode::Create(var->llvmType(), 0, Twine("incmpphi"), block);
		auto phi = block->empty() ? PHINode::Create(var->llvmType(), 0, Twine("PhiNodeSeal"), block) : PHINode::Create(var->llvmType(), 0, Twine("PhiNodeSeal"), &block->front());
		writeVariable(var, block, phi);
		retVal = addPhiOperands(var, phi);
	}
	
	writeVariable(var, block, retVal);
	return retVal;
}

// Adds phi operands based on predecessors of the containing block
Value* SSABuilder::addPhiOperands(Identifier* var, PHINode* phi)
{
	// PA4: Implement
	for (auto it = pred_begin(phi->getParent()); it != pred_end(phi->getParent()); ++it){
		phi->addIncoming(readVariable(var, *it), *it);
	}
	
	return tryRemoveTrivialPhi(phi);
}

// Removes trivial phi nodes
Value* SSABuilder::tryRemoveTrivialPhi(llvm::PHINode* phi)
{
	Value* same = nullptr;
	
	// PA4: Implement
	for (int i = 0; i < phi->getNumOperands(); i++) {
		auto op = phi->getIncomingValue(i);
		if (op == same || op == phi) {
			continue;
		}
		if (same != nullptr) {
			return phi;
		}
		same = op;
	}
	if (same == nullptr) {
		same = UndefValue::get(phi->getType());
	}
	
	std::vector<Value*> users;
	
	for (auto it = phi->use_begin(); it != phi->use_end(); ++it) {
		if (*it != phi) users.push_back(*it);
	}
	phi->replaceAllUsesWith(same);
	if (!phi->getParent()) {
		return phi;
	}
	auto map = mVarDefs[phi->getParent()];
	for (auto it : *map){
		if (it.second == phi) {
			(*map)[it.first] = same;
		}
	}
	for (auto use : users){
		if (isa<PHINode>(use)) tryRemoveTrivialPhi(cast<PHINode>(use));
	}
	phi->eraseFromParent();
	
	return same;}
