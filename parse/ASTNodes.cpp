//
//  ASTNodes.cpp
//  uscc
//
//  Implements helper functions used by a handful of AST
//  nodes.
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#include "ASTNodes.h"

using namespace uscc::parse;
using std::shared_ptr;

void ASTProgram::addFunction(shared_ptr<ASTFunction> func) noexcept
{
	mFuncs.push_back(func);
}

// Add an argument to this function
void ASTFunction::addArg(shared_ptr<ASTArgDecl> arg) noexcept
{
	mArgs.push_back(arg);
}

// Returns true if the type passed in matches the argument
// declaration for that particular argument
bool ASTFunction::checkArgType(unsigned int argNum, Type type) const noexcept
{
	if (argNum > 0 && argNum <= mArgs.size())
	{
		return mArgs[argNum - 1]->getType() == type;
	}
	else
	{
		return false;
	}
}

Type ASTFunction::getArgType(unsigned int argNum) const noexcept
{
	if (argNum > 0 && argNum <= mArgs.size())
	{
		return mArgs[argNum - 1]->getType();
	}
	else
	{
		return Type::Void;
	}
}

// Set the compound statement body
void ASTFunction::setBody(shared_ptr<ASTCompoundStmt> body) noexcept
{
	mBody = body;
}
