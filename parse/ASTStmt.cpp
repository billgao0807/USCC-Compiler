//
//  ASTStmt.cpp
//  uscc
//
//  Implements functions related to statement AST nodes.
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

void ASTCompoundStmt::addDecl(shared_ptr<ASTDecl> decl) noexcept
{
	mDecls.push_back(decl);
}

void ASTCompoundStmt::addStmt(shared_ptr<ASTStmt> stmt) noexcept
{
	mStmts.push_back(stmt);
}

shared_ptr<ASTStmt> ASTCompoundStmt::getLastStmt() noexcept
{
	if (mStmts.size() > 0)
	{
		return mStmts.back();
	}
	else
	{
		return nullptr;
	}
}
