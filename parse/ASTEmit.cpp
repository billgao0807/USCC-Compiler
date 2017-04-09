//
//  ASTNodes.cpp
//  uscc
//
//  Implements the emitIR function for every AST node.
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#include "ASTNodes.h"
#include "Emitter.h"

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
#include <llvm/IR/Intrinsics.h>
#pragma clang diagnostic pop

#include <vector>

using namespace uscc::parse;
using namespace llvm;

#define AST_EMIT(a) llvm::Value* a::emitIR(CodeContext& ctx) noexcept

// Program/Functions
AST_EMIT(ASTProgram)
{
	ctx.mModule = new Module("main", ctx.mGlobal);
	
	// Write the global string table
	ctx.mStrings.emitIR(ctx);
	
	// Emit declaration for stdlib "printf", if we need it
	if (ctx.mPrintfIdent != nullptr)
	{
		std::vector<llvm::Type*> printfArgs;
		printfArgs.push_back(llvm::Type::getInt8PtrTy(ctx.mGlobal));
		
		FunctionType* printfType = FunctionType::get(llvm::Type::getInt32Ty(ctx.mGlobal),
													 printfArgs, true);
		
		Function* func = Function::Create(printfType, GlobalValue::LinkageTypes::ExternalLinkage,
										  "printf", ctx.mModule);
		func->setCallingConv(CallingConv::C);
		
		// Map the printf ident to this function
		ctx.mPrintfIdent->setAddress(func);
	}
	
	// Emit code for all the functions
	for (auto f : mFuncs)
	{
		f->emitIR(ctx);
	}
	// A program actually doesn't have a value to return, since everything
	// is stored in Module
	return nullptr;
}

AST_EMIT(ASTFunction)
{
	FunctionType* funcType = nullptr;
	
	// First get the return type (there's only three choices)
	llvm::Type* retType = nullptr;
	if (mReturnType == Type::Int)
	{
		retType = llvm::Type::getInt32Ty(ctx.mGlobal);
	}
	else if (mReturnType == Type::Char)
	{
		retType = llvm::Type::getInt8Ty(ctx.mGlobal);
	}
	else
	{
		retType = llvm::Type::getVoidTy(ctx.mGlobal);
	}
	
	if (mArgs.size() == 0)
	{
		funcType = FunctionType::get(retType, false);
	}
	else
	{

		std::vector<llvm::Type*> args;
		for (auto arg : mArgs)
		{
			args.push_back(arg->getIdent().llvmType());
		}
		
		funcType = FunctionType::get(retType, args, false);
	}
	
	// Create the function, and make it the current one
	ctx.mFunc = Function::Create(funcType,
								 GlobalValue::LinkageTypes::ExternalLinkage,
								 mIdent.getName(), ctx.mModule);
	
	// Now that we have a new function, reset our SSA builder
	ctx.mSSA.reset();
	
	// Map the ident to this function
	mIdent.setAddress(ctx.mFunc);
	
	// Create the entry basic block
	ctx.mBlock = BasicBlock::Create(ctx.mGlobal, "entry", ctx.mFunc);
	// Add and seal this block
	ctx.mSSA.addBlock(ctx.mBlock, true);
	
	// If we have arguments, we need to set the name/value of them
	if (mArgs.size() > 0)
	{
		Function::arg_iterator iter = ctx.mFunc->arg_begin();
		Function::arg_iterator end = ctx.mFunc->arg_end();
		int i = 0;
		while (iter != end)
		{
			Identifier& argIdent = mArgs[i]->getIdent();
			iter->setName(argIdent.getName());
			
			// PA4: Remove the setAddress call
			// (Technically, iter actually has the value of the
			// arg, not its address...but we will use the address
			// member for this value)
//			argIdent.setAddress(iter);
			
			// PA4: Write to this identifier
			 argIdent.writeTo(ctx, iter);
			
			++i;
			++iter;
		}
	}
	
	ctx.mFunc->setCallingConv(CallingConv::C);
	
	// Add all the declarations for variables created in this function
	mScopeTable.emitIR(ctx);
	
	// Now emit the body
	mBody->emitIR(ctx);
	
	return ctx.mFunc;
}

AST_EMIT(ASTArgDecl)
{
	// This node actually doesn't have anything to emit
	return nullptr;
}

AST_EMIT(ASTArraySub)
{
	// Evaluate the sub expression to get the desired index
	Value* arrayIdx = mExpr->emitIR(ctx);
	
	// This address should already be saved
	Value* addr = mIdent.readFrom(ctx);
	
	// GEP from the array address
	IRBuilder<> build(ctx.mBlock);
	return build.CreateInBoundsGEP(addr, arrayIdx);
}

// Expressions

AST_EMIT(ASTBadExpr)
{
	// This node will never be emitted
	return nullptr;
}

AST_EMIT(ASTLogicalAnd)
{
	// This is extremely similar to logical or
	
	// Create the block for the RHS
	BasicBlock* rhsBlock = BasicBlock::Create(ctx.mGlobal, "and.rhs", ctx.mFunc);
	// Add the rhs block to SSA (not sealed)
	ctx.mSSA.addBlock(rhsBlock);
	
	// In both "true" and "false" condition, we'll jump to and.end
	// This is because we'll insert a phi node that assume false
	// if the and.end jump was from the lhs block
	BasicBlock* endBlock = BasicBlock::Create(ctx.mGlobal, "and.end", ctx.mFunc);
	// Also not sealed
	ctx.mSSA.addBlock(endBlock);
	
	// Now generate the LHS
	Value* lhsVal = mLHS->emitIR(ctx);
	
	BasicBlock* lhsBlock = ctx.mBlock;
	
	// Add the branch to the end of the LHS
	{
		IRBuilder<> build(ctx.mBlock);
		// We can assume it WILL be an i32 here
		// since it'd have been zero-extended otherwise
		lhsVal = build.CreateICmpNE(lhsVal, ctx.mZero, "tobool");
		build.CreateCondBr(lhsVal, rhsBlock, endBlock);
	}
	
	// rhsBlock should now be sealed
	ctx.mSSA.sealBlock(rhsBlock);
	
	// Code should now be generated in the RHS block
	ctx.mBlock = rhsBlock;
	Value* rhsVal = mRHS->emitIR(ctx);
	
	// This is the final RHS block (for the phi node)
	rhsBlock = ctx.mBlock;
	
	// Add the branch and the end of the RHS
	{
		IRBuilder<> build(ctx.mBlock);
		rhsVal = build.CreateICmpNE(rhsVal, ctx.mZero, "tobool");
		
		// We do an unconditional branch because the phi mode will handle
		// the correct value
		build.CreateBr(endBlock);
	}
	
	// endBlock should now be sealed
	ctx.mSSA.sealBlock(endBlock);
	
	ctx.mBlock = endBlock;
	
	IRBuilder<> build(ctx.mBlock);
	
	// Figure out the value to zext
	Value* zextVal = nullptr;
	
	// If rhs is not also false, we need to make a phi
	if (rhsVal != ConstantInt::getFalse(ctx.mGlobal))
	{
		PHINode* phi = build.CreatePHI(llvm::Type::getInt1Ty(ctx.mGlobal), 2);
		// If we came from the lhs, it had to be false
		phi->addIncoming(ConstantInt::getFalse(ctx.mGlobal), lhsBlock);
		phi->addIncoming(rhsVal, rhsBlock);
		zextVal = phi;
	}
	else
	{
		zextVal = ConstantInt::getFalse(ctx.mGlobal);
	}
	
	return build.CreateZExt(zextVal, llvm::Type::getInt32Ty(ctx.mGlobal));
}

AST_EMIT(ASTLogicalOr)
{
	// Create the block for the RHS
	BasicBlock* rhsBlock = BasicBlock::Create(ctx.mGlobal, "lor.rhs", ctx.mFunc);
	// Add the rhs block to SSA (not sealed)
	ctx.mSSA.addBlock(rhsBlock);

	// In both "true" and "false" condition, we'll jump to lor.end
	// This is because we'll insert a phi node that assume true
	// if the lor.end jump was from the lhs block
	BasicBlock* endBlock = BasicBlock::Create(ctx.mGlobal, "lor.end", ctx.mFunc);
	// Also not sealed
	ctx.mSSA.addBlock(endBlock);
	
	// Now generate the LHS
	Value* lhsVal = mLHS->emitIR(ctx);
	
	BasicBlock* lhsBlock = ctx.mBlock;
	
	// Add the branch to the end of the LHS
	{
		IRBuilder<> build(ctx.mBlock);
		// We can assume it WILL be an i32 here
		// since it'd have been zero-extended otherwise
		lhsVal = build.CreateICmpNE(lhsVal, ctx.mZero, "tobool");
		build.CreateCondBr(lhsVal, endBlock, rhsBlock);
	}
	
	// rhsBlock should now be sealed
	ctx.mSSA.sealBlock(rhsBlock);
	
	// Code should now be generated in the RHS block
	ctx.mBlock = rhsBlock;
	Value* rhsVal = mRHS->emitIR(ctx);
	
	// This is the final RHS block (for the phi node)
	rhsBlock = ctx.mBlock;
	
	// Add the branch and the end of the RHS
	{
		IRBuilder<> build(ctx.mBlock);
		rhsVal = build.CreateICmpNE(rhsVal, ctx.mZero, "tobool");
		
		// We do an unconditional branch because the phi mode will handle
		// the correct value
		build.CreateBr(endBlock);
	}
	
	// endBlock should now be sealed
	ctx.mSSA.sealBlock(endBlock);
	
	ctx.mBlock = endBlock;
	
	IRBuilder<> build(ctx.mBlock);
	
	// Figure out the value to zext
	Value* zextVal = nullptr;
	
	// If rhs is not also true, we need to make a phi
	if (rhsVal != ConstantInt::getTrue(ctx.mGlobal))
	{
		PHINode* phi = build.CreatePHI(llvm::Type::getInt1Ty(ctx.mGlobal), 2);
		// If we came from the lhs, it had to be false
		phi->addIncoming(ConstantInt::getTrue(ctx.mGlobal), lhsBlock);
		phi->addIncoming(rhsVal, rhsBlock);
		zextVal = phi;
	}
	else
	{
		zextVal = ConstantInt::getTrue(ctx.mGlobal);
	}
	
	return build.CreateZExt(zextVal, llvm::Type::getInt32Ty(ctx.mGlobal));
}

AST_EMIT(ASTBinaryCmpOp)
{
	Value* retVal = nullptr;
	
	// PA3: Implement
	IRBuilder<> build(ctx.mBlock);
	
	auto lhs = mLHS->emitIR(ctx);
	auto rhs = mRHS->emitIR(ctx);
	
	if(mOp == scan::Token::EqualTo) {
		retVal = build.CreateICmpEQ(lhs, rhs, "equal");
	} else if(mOp == scan::Token::NotEqual) {
		retVal = build.CreateICmpNE(lhs, rhs, "notEqual");
	} else if(mOp == scan::Token::GreaterThan) {
		retVal = build.CreateICmpSGT(lhs, rhs, "greaterThan");
	} else if(mOp == scan::Token::LessThan) {
		retVal = build.CreateICmpSLT(lhs, rhs, "lessThan");
	}
	
	retVal = build.CreateZExt(retVal, llvm::Type::getInt32Ty(ctx.mGlobal));
	
	return retVal;
}

AST_EMIT(ASTBinaryMathOp)
{
	Value* retVal = nullptr;
	
	// PA3: Implement
	IRBuilder<> build(ctx.mBlock);
	
	auto lhs = mLHS->emitIR(ctx);
	auto rhs = mRHS->emitIR(ctx);
	if(mOp == scan::Token::Plus) {
		retVal = build.CreateBinOp(Instruction::Add, lhs, rhs, "add");
	} else if(mOp == scan::Token::Minus) {
		retVal = build.CreateBinOp(Instruction::Sub, lhs, rhs, "sub");
	} else if(mOp == scan::Token::Mult) {
		retVal = build.CreateBinOp(Instruction::Mul, lhs, rhs, "mul");
	} else if(mOp == scan::Token::Div) {
		retVal = build.CreateBinOp(Instruction::SDiv, lhs, rhs, "sdiv");
	} else if(mOp == scan::Token::Mod) {
		retVal = build.CreateBinOp(Instruction::SRem, lhs, rhs, "add");
	}
	
	
	return retVal;
}

// Value -->
AST_EMIT(ASTNotExpr)
{
	Value* retVal = nullptr;
	
	// PA3: Implement
	IRBuilder<> build(ctx.mBlock);
	retVal = build.CreateICmpEQ(ctx.mZero, mExpr->emitIR(ctx), "add");
	retVal = build.CreateZExt(retVal, llvm::Type::getInt32Ty(ctx.mGlobal));
	
	return retVal;
}

// Factor -->
AST_EMIT(ASTConstantExpr)
{
	Value* retVal = nullptr;
	
	// PA3: Implement
	if (getType() == Type::Int) {
		retVal = ConstantInt::get(llvm::Type::getInt32Ty(ctx.mGlobal), getValue());
	} else if (getType() == Type::Char) {
		retVal = ConstantInt::get(llvm::Type::getInt8Ty(ctx.mGlobal), getValue());
	}
	
	return retVal;
}

AST_EMIT(ASTStringExpr)
{
	return mString->getValue();
}

AST_EMIT(ASTIdentExpr)
{
	return mIdent.readFrom(ctx);
}

AST_EMIT(ASTArrayExpr)
{
	// Generate the array subscript, which'll give us the address
	Value* addr = mArray->emitIR(ctx);

	IRBuilder<> build(ctx.mBlock);
	// Now load this value and return
	
	// NOTE: This still needs to be a load because arrays are in memory
	return build.CreateLoad(addr);
}

AST_EMIT(ASTFuncExpr)
{
	
	// At this point, we can assume the argument types match
	// Create the list of arguments
	std::vector<Value*> callList;
	for (auto arg : mArgs)
	{
		Value* argValue = arg->emitIR(ctx);
		// If this is an array or ptr, we need to change this to a getelemptr
		// (Provided it already isn't one)
		if (!isa<GetElementPtrInst>(argValue) &&
			argValue->getType()->isPointerTy())
		{
			if (argValue->getType()->getPointerElementType()->isArrayTy())
			{
				IRBuilder<> build(ctx.mBlock);
				std::vector<llvm::Value*> gepIdx;
				gepIdx.push_back(ctx.mZero);
				gepIdx.push_back(ctx.mZero);
				
				argValue = build.CreateInBoundsGEP(argValue, gepIdx);
			}
			else
			{
				IRBuilder<> build(ctx.mBlock);				
				// Need to return the address of the specific index in question
				// So need a GEP
				argValue = build.CreateInBoundsGEP(argValue, ctx.mZero);
			}
		}
			
		callList.push_back(argValue);
	}
	
	// Now call the function, and return it
	Value* retVal = nullptr;
	
	IRBuilder<> build(ctx.mBlock);
	if (mType != Type::Void)
	{
		retVal = build.CreateCall(mIdent.getAddress(), callList, "call");
	}
	else
	{
		retVal = build.CreateCall(mIdent.getAddress(), callList);
	}
	
	return retVal;
}

AST_EMIT(ASTIncExpr)
{
	Value* retVal = nullptr;
	
	// PA3: Implement
	auto val = mIdent.readFrom(ctx);
	auto one = ConstantInt::get(val->getType(), 1);
	IRBuilder<> build(ctx.mBlock);
	retVal = build.CreateBinOp(Instruction::Add, val, one, "add");
	mIdent.writeTo(ctx, retVal);
	return retVal;
}

AST_EMIT(ASTDecExpr)
{
	Value* retVal = nullptr;
	
	// PA3: Implement
	auto val = mIdent.readFrom(ctx);
	auto one = ConstantInt::get(val->getType(), 1);
	IRBuilder<> build(ctx.mBlock);
	retVal = build.CreateBinOp(Instruction::Sub, val, one, "sub");
	mIdent.writeTo(ctx, retVal);
	return retVal;
}

AST_EMIT(ASTAddrOfArray)
{
	return mArray->emitIR(ctx);
}

AST_EMIT(ASTToIntExpr)
{
	Value* exprVal = mExpr->emitIR(ctx);
	IRBuilder<> build(ctx.mBlock);
	return build.CreateSExt(exprVal, llvm::Type::getInt32Ty(ctx.mGlobal), "conv");
}

AST_EMIT(ASTToCharExpr)
{
	Value* exprVal = mExpr->emitIR(ctx);
	IRBuilder<> build(ctx.mBlock);
	return build.CreateTrunc(exprVal, llvm::Type::getInt8Ty(ctx.mGlobal), "conv");
}

// Declaration
AST_EMIT(ASTDecl)
{
	// If there's an expression, emit this also and store it in the ident
	if (mExpr)
	{
		Value* declExpr = mExpr->emitIR(ctx);
		
		IRBuilder<> build(ctx.mBlock);
		// If this is a string, we have to memcpy
		if (declExpr->getType()->isPointerTy())
		{
			// This address should already be saved
			Value* arrayLoc = mIdent.readFrom(ctx);
			
			// GEP the address of the src
			std::vector<llvm::Value*> gepIdx;
			gepIdx.push_back(ctx.mZero);
			gepIdx.push_back(ctx.mZero);
			
			Value*  src = build.CreateGEP(declExpr, gepIdx);
			
			// Memcpy into the array
			// memcpy(dest, src, size, align, volatile)
			build.CreateMemCpy(arrayLoc, src, mIdent.getArrayCount(), 1);
		}
		else
		{
			// Basic types can just be written
			mIdent.writeTo(ctx, declExpr);
		}
	}
	
	return nullptr;
}

// Statements
AST_EMIT(ASTCompoundStmt)
{
	// PA3: Implement
	for (auto del : mDecls ) {
		if (del) {
			del->emitIR(ctx);
		}
	}
	for (auto stm : mStmts ) {
		if (stm) {
			stm->emitIR(ctx);
		}
	}
	return nullptr;
}

AST_EMIT(ASTAssignStmt)
{
	// This is simpler than decl because we don't allow
	// assignments to happen later for full arrays
	
	// PA3: Implement
	if (mExpr) {
		auto val = mExpr->emitIR(ctx);
		mIdent.writeTo(ctx, val);
	}
	
	return nullptr;
}

AST_EMIT(ASTAssignArrayStmt)
{
	// Generate the expression
	Value* exprVal = mExpr->emitIR(ctx);
	
	// Generate the array subscript, which'll give us the address
	Value* addr = mArray->emitIR(ctx);

	IRBuilder<> build(ctx.mBlock);
	
	// NOTE: This is still a create store because arrays are always stack-allocated
	build.CreateStore(exprVal, addr);
	
	return nullptr;
}

AST_EMIT(ASTIfStmt)
{
	// PA3: Implement
	IRBuilder<> build(ctx.mGlobal);
	
	auto thenBlock = BasicBlock::Create(ctx.mGlobal, "if.then", ctx.mFunc);
	
	
	ctx.mSSA.addBlock(thenBlock);
	
	
	//Setup cond for branch
	auto cond = mExpr->emitIR(ctx);
	build.SetInsertPoint(ctx.mBlock);
	auto condResult = build.CreateICmpEQ(cond, ctx.mZero);
	//Two cases
	if (mElseStmt) {
		auto elseBlock = BasicBlock::Create(ctx.mGlobal, "if.else", ctx.mFunc);
		auto endBlock = BasicBlock::Create(ctx.mGlobal, "if.end", ctx.mFunc);
		ctx.mSSA.addBlock(elseBlock);
		
		build.CreateCondBr(condResult, elseBlock, thenBlock);
		
		//Else emit and branch
		ctx.mSSA.sealBlock(elseBlock);
		ctx.mBlock = elseBlock;
		mElseStmt->emitIR(ctx);
		build.SetInsertPoint(ctx.mBlock);
        ctx.mSSA.addBlock(endBlock);
		build.CreateBr(endBlock);
        
        //Then emit and branch
        ctx.mSSA.sealBlock(thenBlock);
        ctx.mBlock = thenBlock;
        mThenStmt->emitIR(ctx);
        build.SetInsertPoint(ctx.mBlock);
        build.CreateBr(endBlock);
        
        ctx.mSSA.sealBlock(endBlock);
        ctx.mBlock = endBlock;
	} else {
        auto endBlock = BasicBlock::Create(ctx.mGlobal, "if.end", ctx.mFunc);
        ctx.mSSA.addBlock(endBlock);
		build.CreateCondBr(condResult, endBlock, thenBlock);
        
        //Then emit and branch
        ctx.mSSA.sealBlock(thenBlock);
        ctx.mBlock = thenBlock;
        mThenStmt->emitIR(ctx);
        build.SetInsertPoint(ctx.mBlock);
        build.CreateBr(endBlock);
        
        ctx.mSSA.sealBlock(endBlock);
        ctx.mBlock = endBlock;
	}
	
	

	return nullptr;

}

AST_EMIT(ASTWhileStmt)
{
	// PA3: Implement
	IRBuilder<> build(ctx.mGlobal);

	auto condBlock = BasicBlock::Create(ctx.mGlobal, "while.cond", ctx.mFunc);
//	auto bodyBlock = BasicBlock::Create(ctx.mGlobal, "while.body", ctx.mFunc);
//	auto endBlock = BasicBlock::Create(ctx.mGlobal, "while.end", ctx.mFunc);

	ctx.mSSA.addBlock(condBlock);
	
	//Branch to cond
	build.SetInsertPoint(ctx.mBlock);
	build.CreateBr(condBlock);
	
	//Branch to body or end based on result
	ctx.mBlock = condBlock;
	auto cond = mExpr->emitIR(ctx);
	build.SetInsertPoint(ctx.mBlock);
	auto condResult = build.CreateICmpEQ(cond, ctx.mZero);
    
    auto bodyBlock = BasicBlock::Create(ctx.mGlobal, "while.body", ctx.mFunc);
	ctx.mSSA.addBlock(bodyBlock);
    auto endBlock = BasicBlock::Create(ctx.mGlobal, "while.end", ctx.mFunc);
	ctx.mSSA.addBlock(endBlock);
	build.CreateCondBr(condResult, endBlock, bodyBlock);
	
    ctx.mSSA.sealBlock(endBlock);
	//Branch from body to cond
	ctx.mBlock = bodyBlock;
	mLoopStmt->emitIR(ctx);
	build.SetInsertPoint(ctx.mBlock);
	build.CreateBr(condBlock);

	ctx.mSSA.sealBlock(condBlock);
    ctx.mSSA.sealBlock(bodyBlock);
	
	//Set mBlock to endBlock
	ctx.mBlock = endBlock;

	
	
	
	return nullptr;
}

AST_EMIT(ASTReturnStmt)
{
	// PA3: Implement
	IRBuilder<> build(ctx.mBlock);
	if (mExpr) {
		return build.CreateRet(mExpr->emitIR(ctx));
	}
	else {
		return build.CreateRetVoid();
	}
}

AST_EMIT(ASTExprStmt)
{
	// PA3: Implement
	// Just emit the expression, don't care about the value
	if (mExpr) mExpr->emitIR(ctx);
	return nullptr;
}

AST_EMIT(ASTNullStmt)
{
	// Doesn't do anything (hence empty)
	return nullptr;
}
