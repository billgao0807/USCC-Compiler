//
//  ConstantOps.cpp
//  uscc
//
//  Implements constant propagation --
//  If a binary op or an icmp is operating on constants,
//  replace the instruction with the computed result
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

bool ConstantOps::runOnFunction(Function& F) {
	bool changed = false;
	
	// Make a set that contains the instructions we'll remove
	std::set<Instruction*> removeSet;
	
	// Loop through each block
	Function::iterator blockIter = F.begin();
	while (blockIter != F.end())
	{
		// Loop through instructions in block
		BasicBlock::iterator instrIter = blockIter->begin();
		while (instrIter != blockIter->end())
		{
			// Is this a binary op?
			if (BinaryOperator* binOp = dyn_cast<BinaryOperator>(instrIter))
			{
				// Make sure both are constant ints and 32-bit
				ConstantInt* lhs = dyn_cast<ConstantInt>(binOp->getOperand(0));
				ConstantInt* rhs = dyn_cast<ConstantInt>(binOp->getOperand(1));
				if (lhs != nullptr && rhs != nullptr &&
					lhs->getValue().isSignedIntN(32) && rhs->getValue().isSignedIntN(32))
				{
					// Now do the calculation
					APInt result = lhs->getValue();
					bool didCalc = true;
					switch (binOp->getOpcode())
					{
						case Instruction::Add:
							result += rhs->getValue();
							break;
						case Instruction::Sub:
							result -= rhs->getValue();
							break;
						case Instruction::Mul:
							result *= rhs->getValue();
							break;
						default:
							// For everything else, we didn't do a calculation
							didCalc = false;
							break;
					}
					
					// If we did a calculation, replace this instruction now
					if (didCalc)
					{
						removeSet.insert(instrIter);
						instrIter->replaceAllUsesWith(ConstantInt::get(instrIter->getContext(), result));
					}
				}
			}
			else if (ICmpInst* icmpOp = dyn_cast<ICmpInst>(instrIter))
			{
				// Is this one of our two desired predicates?
				CmpInst::Predicate pred = icmpOp->getPredicate();
				if (pred == CmpInst::ICMP_EQ || pred == CmpInst::ICMP_NE ||
					pred == CmpInst::ICMP_SGT || pred == CmpInst::ICMP_SLT)
				{
					// Make sure both are constant 32-bit ints
					ConstantInt* lhs = dyn_cast<ConstantInt>(icmpOp->getOperand(0));
					ConstantInt* rhs = dyn_cast<ConstantInt>(icmpOp->getOperand(1));
					if (lhs != nullptr && rhs != nullptr &&
						lhs->getBitWidth() == 32 && rhs->getBitWidth() == 32)
					{
						
						// Compute the instruction
						bool result = false;
						switch (pred)
						{
							case CmpInst::ICMP_EQ:
								result = (lhs->getValue() == rhs->getValue());
								break;
							case CmpInst::ICMP_NE:
								result = (lhs->getValue() != rhs->getValue());
								break;
							case CmpInst::ICMP_SGT:
								result = lhs->getValue().sgt(rhs->getValue());
								break;
							case CmpInst::ICMP_SLT:
								result = lhs->getValue().slt(rhs->getValue());
								break;
							default:
								// Note: This case can never be hit because of earlier condition
								break;
						}
						
						// Replace the instruction
						removeSet.insert(instrIter);
						if (result)
						{
							instrIter->replaceAllUsesWith(ConstantInt::getTrue(instrIter->getContext()));
						}
						else
						{
							instrIter->replaceAllUsesWith(ConstantInt::getFalse(instrIter->getContext()));
						}
					}
				}
			}
			
			++instrIter;
		}
		
		++blockIter;
	}
	
	// Now remove any instructions we flagged
	if (removeSet.size() > 0)
	{
		changed = true;
		for (std::set<Instruction*>::iterator i = removeSet.begin();
			 i != removeSet.end();
			 ++i)
		{
			(*i)->eraseFromParent();
		}
	}
	
	return changed;
}

void ConstantOps::getAnalysisUsage(AnalysisUsage& Info) const
{
	// This pass does not alter the CFG
	Info.setPreservesCFG();
}

} // opt
} // uscc

char uscc::opt::ConstantOps::ID = 0;
