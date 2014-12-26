//
//  ASTExpr.cpp
//  uscc
//
//  Implements code related to expression AST nodes.
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#include "ASTNodes.h"
#include "Symbols.h"
#include <sstream>

using namespace uscc::parse;

// Expression AST Nodes

// Finalize the op.
// Call this after both lhs/rhs are set, and
// it will evaluate the type of the expression.
// Returns false if this is an invalid operation.
bool ASTLogicalAnd::finalizeOp() noexcept
{
	// PA2: Implement
	
	return true;
}

bool ASTLogicalOr::finalizeOp() noexcept
{
	// PA2: Implement
	
	return true;
}

bool ASTBinaryCmpOp::finalizeOp() noexcept
{
	// PA2: Implement
	
	return true;
}

bool ASTBinaryMathOp::finalizeOp() noexcept
{
	// PA2: Implement
	
	return true;
}

ASTConstantExpr::ASTConstantExpr(const std::string& constStr)
{
	// ConstExpr is always evaluated as a 32-bit integer
	// it can later be converted to a char at assignment
	mType = Type::Int;
	
	// Is this a character in ''?
	if (constStr[0] == '\'')
	{
		if (constStr == "\'\\t\'")
		{
			mValue = '\t';
		}
		else if (constStr == "\'\\n\'")
		{
			mValue = '\n';
		}
		else
		{
			mValue = constStr[1];
		}
	}
	else
	{
		// NOTE: This WILL throw if the value is out of bounds
		std::istringstream ss(constStr);
		ss >> mValue;
		if (ss.fail())
		{
			throw std::invalid_argument(constStr);
		}
	}
}

ASTStringExpr::ASTStringExpr(const std::string& str, StringTable& tbl)
{
	// This function can only be called if this is a valid string
	std::string actStr = str.substr(1, str.length() - 2);
	mType = Type::CharArray;
	
	// Replace valid escape sequences
	size_t pos = actStr.find("\\n");
	while (pos != std::string::npos)
	{
		actStr.replace(pos, 2, "\n");
		pos = actStr.find("\\n");
	}
	
	pos = actStr.find("\\t");
	while (pos != std::string::npos)
	{
		actStr.replace(pos, 2, "\t");
		pos = actStr.find("\\t");
	}
	
	// Now grab this from the StringTable
	mString = tbl.getString(actStr);
}

void ASTFuncExpr::addArg(std::shared_ptr<ASTExpr> arg) noexcept
{
	mArgs.push_back(arg);
}
