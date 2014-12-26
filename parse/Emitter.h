//
//  Emitter.h
//  uscc
//
//  Declares the helper classes related to LLVM IR
//  construction.
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
#include <llvm/IR/Value.h>
#pragma clang diagnostic pop

#include "Types.h"
#include "../opt/SSABuilder.h"

namespace uscc
{
namespace parse
{

class StringTable;
class Identifier;

struct CodeContext
{
	CodeContext(StringTable& strings);
	
	// Used for our SSA construction algorithm
	opt::SSABuilder mSSA;
	
	// Global context for LLVM
	llvm::LLVMContext& mGlobal;
	
	// Module for this program
	llvm::Module* mModule;
	
	// Current basic block
	llvm::BasicBlock* mBlock;
	
	// String table
	StringTable& mStrings;
	
	// This will be non-null if we need extern printf
	Identifier* mPrintfIdent;
	
	// Points to a constant value of zero
	llvm::Value* mZero;
	
	// stores the current function
	llvm::Function* mFunc;
};

class Parser;

class Emitter
{
public:
	Emitter(Parser& parser) noexcept;
	void optimize() noexcept;
	void print() noexcept;
	void writeBitcode(const char* fileName) noexcept;
	bool verify() noexcept;
	bool writeAsm(const char* fileName) noexcept;
private:
	CodeContext mContext;
};

} // uscc
} // parse
