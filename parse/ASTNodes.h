//
//  ASTNodes.h
//  uscc
//
//  Declares all of the AST node classes that are used
//  by the parser.
//
//  Each AST node supports pretty-printing its node
//  contents as well as generating the LLVM IR.
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#pragma once

#include <ostream>
#include <string>
#include <memory>
#include <list>
#include <vector>

#include "Types.h"
#include "Symbols.h"
#include "../scan/Tokens.h"

// Macro so I don't have to copy/paste over and over
#define AST_DECL_PRINT_EMIT() \
virtual void printNode(std::ostream& output, int depth = 0) const noexcept override; \
virtual llvm::Value* emitIR(CodeContext& ctx) noexcept override;

namespace llvm
{
	class Value;
}

namespace uscc
{
namespace parse
{

class CodeContext;
	
class ASTNode
{
public:
	virtual void printNode(std::ostream& output, int depth = 0) const noexcept = 0;
	virtual llvm::Value* emitIR(CodeContext& ctx) noexcept = 0;
	virtual ~ASTNode() { }
protected:
	ASTNode() { }
	ASTNode(const ASTNode& copy) { }
	ASTNode& operator=(const ASTNode& rhs) { return *this; }
};

class ASTFunction;

class ASTProgram : public ASTNode
{
public:
	void addFunction(std::shared_ptr<ASTFunction> func) noexcept;
	AST_DECL_PRINT_EMIT();
private:
	std::list<std::shared_ptr<ASTFunction>> mFuncs;
};
	
// Function AST Nodes
class ASTCompoundStmt;
class ASTArgDecl;
class ASTExpr;

class ASTFunction : public ASTNode
{
public:
	ASTFunction(Identifier& ident, Type returnType, SymbolTable::ScopeTable& scopeTable) noexcept
	: mIdent(ident)
	, mReturnType(returnType)
	, mScopeTable(scopeTable)
	{ }
	
	// Add an argument to this function
	void addArg(std::shared_ptr<ASTArgDecl> arg) noexcept;
		
	// Set the compound statement body
	void setBody(std::shared_ptr<ASTCompoundStmt> body) noexcept;
	
	Type getReturnType() const noexcept
	{
		return mReturnType;
	}
	
	// Returns the number of arguments
	size_t getNumArgs() const noexcept
	{
		return mArgs.size();
	}
	
	// Returns true if the type passed in matches the argument
	// declaration for that particular argument
	bool checkArgType(unsigned int argNum, Type type) const noexcept;
	
	Type getArgType(unsigned int argNum) const noexcept;
	
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTCompoundStmt> mBody;
	std::vector<std::shared_ptr<ASTArgDecl>> mArgs;
	Identifier& mIdent;
	SymbolTable::ScopeTable& mScopeTable;
	Type mReturnType;
};

class ASTArgDecl : public ASTNode
{
public:
	ASTArgDecl(Identifier& ident) noexcept
	: mIdent(ident)
	{ }
	
	Type getType() const noexcept
	{
		return mIdent.getType();
	}
	
	Identifier& getIdent() noexcept
	{
		return mIdent;
	}
	
	AST_DECL_PRINT_EMIT();
private:
	Identifier& mIdent;
};

// Expression AST Nodes
class ASTExpr : public ASTNode
{
public:
	ASTExpr() noexcept
	: mType(Type::Void)
	{ }
	
	Type getType() const noexcept
	{
		return mType;
	}
protected:
	// All expressions have a type
	// (used for semantic evaluation)
	Type mType;
};

// Array subscript helper node
class ASTArraySub : public ASTNode
{
public:
	ASTArraySub(Identifier& ident, std::shared_ptr<ASTExpr> expr) noexcept
	: mIdent(ident)
	, mExpr(expr)
	{ }
	
	Type getType() const noexcept
	{
		return mIdent.getType();
	}
	
	AST_DECL_PRINT_EMIT();
private:
	Identifier& mIdent;
	std::shared_ptr<ASTExpr> mExpr;
};

// "Bad" expr is returned if a () subexpr fails, so at least
// further ops will recognize it as a potentially valid op
class ASTBadExpr : public ASTExpr
{
public:
	AST_DECL_PRINT_EMIT();
};

class ASTLogicalAnd : public ASTExpr
{
public:
	// We need to be able to manually set the lhs/rhs
	void setLHS(std::shared_ptr<ASTExpr> lhs) noexcept
	{
		mLHS = lhs;
	}
	void setRHS(std::shared_ptr<ASTExpr> rhs) noexcept
	{
		mRHS = rhs;
	}
	
	// Finalize the op.
	// Call this after both lhs/rhs are set, and
	// it will evaluate the type of the expression.
	// Returns false if this is an invalid operation.
	bool finalizeOp() noexcept;
	
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTExpr> mLHS;
	std::shared_ptr<ASTExpr> mRHS;
};

class ASTLogicalOr : public ASTExpr
{
public:
	// We need to be able to manually set the lhs/rhs
	void setLHS(std::shared_ptr<ASTExpr> lhs) noexcept
	{
		mLHS = lhs;
	}
	void setRHS(std::shared_ptr<ASTExpr> rhs) noexcept
	{
		mRHS = rhs;
	}
	
	// Finalize the op.
	// Call this after both lhs/rhs are set, and
	// it will evaluate the type of the expression.
	// Returns false if this is an invalid operation.
	bool finalizeOp() noexcept;
	
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTExpr> mLHS;
	std::shared_ptr<ASTExpr> mRHS;
};

class ASTBinaryCmpOp : public ASTExpr
{
public:
	ASTBinaryCmpOp(scan::Token::Tokens op) noexcept
	: mOp(op)
	{ }
	
	// We need to be able to manually set the lhs/rhs
	void setLHS(std::shared_ptr<ASTExpr> lhs) noexcept
	{
		mLHS = lhs;
	}
	void setRHS(std::shared_ptr<ASTExpr> rhs) noexcept
	{
		mRHS = rhs;
	}
	
	// Finalize the op.
	// Call this after both lhs/rhs are set, and
	// it will evaluate the type of the expression.
	// Returns false if this is an invalid operation.
	bool finalizeOp() noexcept;
	
	AST_DECL_PRINT_EMIT();
private:
	scan::Token::Tokens mOp;
	std::shared_ptr<ASTExpr> mLHS;
	std::shared_ptr<ASTExpr> mRHS;
};
	
class ASTBinaryMathOp : public ASTExpr
{
public:
	ASTBinaryMathOp(scan::Token::Tokens op) noexcept
	: mOp(op)
	{ }
	
	// We need to be able to manually set the lhs/rhs
	void setLHS(std::shared_ptr<ASTExpr> lhs) noexcept
	{
		mLHS = lhs;
	}
	void setRHS(std::shared_ptr<ASTExpr> rhs) noexcept
	{
		mRHS = rhs;
	}
	
	// Finalize the op.
	// Call this after both lhs/rhs are set, and
	// it will evaluate the type of the expression.
	// Returns false if this is an invalid operation.
	bool finalizeOp() noexcept;
	
	AST_DECL_PRINT_EMIT();
private:
	scan::Token::Tokens mOp;
	std::shared_ptr<ASTExpr> mLHS;
	std::shared_ptr<ASTExpr> mRHS;
};

// Value -->

// ! Factor
class ASTNotExpr : public ASTExpr
{
public:
	ASTNotExpr(std::shared_ptr<ASTExpr> expr) noexcept
	: mExpr(expr)
	{
		mType = mExpr->getType();
	}
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTExpr> mExpr;
};
	
// Factor -->

class ASTConstantExpr : public ASTExpr
{
public:
	ASTConstantExpr(const std::string& constStr);
	int getValue() const noexcept
	{
		return mValue;
	}
	
	void changeToInt() noexcept
	{
		mType = Type::Int;
	}
	
	void changeToChar() noexcept
	{
		mType = Type::Char;
	}
	
	AST_DECL_PRINT_EMIT();
private:
	int mValue;
};
	
class ASTStringExpr : public ASTExpr
{
public:
	ASTStringExpr(const std::string& str, StringTable& tbl);
	size_t getLength() const noexcept
	{
		return mString->getText().size();
	}
	
	AST_DECL_PRINT_EMIT();
private:
	ConstStr* mString;
};

class ASTIdentExpr : public ASTExpr
{
public:
	ASTIdentExpr(Identifier& ident) noexcept
	: mIdent(ident)
	{
		mType = mIdent.getType();
	}
	AST_DECL_PRINT_EMIT();
private:
	Identifier& mIdent;
};

// id [ Expr ]
class ASTArrayExpr : public ASTExpr
{
public:
	ASTArrayExpr(std::shared_ptr<ASTArraySub> array) noexcept
	: mArray(array)
	{
		if (mArray->getType() == Type::IntArray)
		{
			mType = Type::Int;
		}
		else
		{
			mType = Type::Char;
		}
	}
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTArraySub> mArray;
};

// id ( FuncCallArgs )
class ASTFuncExpr : public ASTExpr
{
public:
	ASTFuncExpr(Identifier& ident) noexcept
	: mIdent(ident)
	{
		if (mIdent.getFunction())
		{
			mType = mIdent.getFunction()->getReturnType();
		}
		else
		{
			mType = Type::Void;
		}
	}
	
	void addArg(std::shared_ptr<ASTExpr> arg) noexcept;
	size_t getNumArgs() const noexcept
	{
		return mArgs.size();
	}
	
	AST_DECL_PRINT_EMIT();
private:
	Identifier& mIdent;
	std::list<std::shared_ptr<ASTExpr>> mArgs;
};

// ++ id
class ASTIncExpr : public ASTExpr
{
public:
	ASTIncExpr(Identifier& ident) noexcept
	: mIdent(ident)
	{
		mType = mIdent.getType();
	}
	AST_DECL_PRINT_EMIT();
private:
	Identifier& mIdent;
};

// -- id
class ASTDecExpr : public ASTExpr
{
public:
	ASTDecExpr(Identifier& ident) noexcept
	: mIdent(ident)
	{
		mType = mIdent.getType();
	}
	AST_DECL_PRINT_EMIT();
private:
	Identifier& mIdent;
};

class ASTAddrOfArray : public ASTExpr
{
public:
	ASTAddrOfArray(std::shared_ptr<ASTArraySub> array) noexcept
	: mArray(array)
	{
		mType = mArray->getType();
	}
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTArraySub> mArray;
};

// Used for type conversion from char to int
class ASTToIntExpr : public ASTExpr
{
public:
	ASTToIntExpr(std::shared_ptr<ASTExpr> expr) noexcept
	: mExpr(expr)
	{
		mType = Type::Int;
	}
	
	std::shared_ptr<ASTExpr> getChild() noexcept
	{
		return mExpr;
	}
	
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTExpr> mExpr;
};

// Used for type conversion from int to char
class ASTToCharExpr : public ASTExpr
{
public:
	ASTToCharExpr(std::shared_ptr<ASTExpr> expr) noexcept
	: mExpr(expr)
	{
		mType = Type::Char;
	}
	
	std::shared_ptr<ASTExpr> getChild() noexcept
	{
		return mExpr;
	}
	
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTExpr> mExpr;
};

// Declaration Node
class ASTDecl : public ASTNode
{
public:
	ASTDecl(Identifier& ident, std::shared_ptr<ASTExpr> expr = nullptr) noexcept
	: mIdent(ident)
	, mExpr(expr)
	{ }
	AST_DECL_PRINT_EMIT();
private:
	Identifier& mIdent;
	std::shared_ptr<ASTExpr> mExpr;
};
	
// Statement AST Nodes
class ASTStmt : public ASTNode
{
	
};

class ASTCompoundStmt : public ASTStmt
{
public:
	AST_DECL_PRINT_EMIT();
	void addDecl(std::shared_ptr<ASTDecl> decl) noexcept;
	void addStmt(std::shared_ptr<ASTStmt> stmt) noexcept;
	std::shared_ptr<ASTStmt> getLastStmt() noexcept;
private:
	std::list<std::shared_ptr<ASTDecl>> mDecls;
	std::list<std::shared_ptr<ASTStmt>> mStmts;
};

class ASTAssignStmt : public ASTStmt
{
public:
	ASTAssignStmt(Identifier& ident, std::shared_ptr<ASTExpr> expr) noexcept
	: mIdent(ident)
	, mExpr(expr)
	{ }
	AST_DECL_PRINT_EMIT();
private:
	Identifier& mIdent;
	std::shared_ptr<ASTExpr> mExpr;
};
	
class ASTAssignArrayStmt : public ASTStmt
{
public:
	ASTAssignArrayStmt(std::shared_ptr<ASTArraySub> array,
					   std::shared_ptr<ASTExpr> expr) noexcept
	: mArray(array)
	, mExpr(expr)
	{ }
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTArraySub> mArray;
	std::shared_ptr<ASTExpr> mExpr;
};

class ASTIfStmt : public ASTStmt
{
public:
	ASTIfStmt(std::shared_ptr<ASTExpr> expr, std::shared_ptr<ASTStmt> thenStmt,
			  std::shared_ptr<ASTStmt> elseStmt = nullptr) noexcept
	: mExpr(expr)
	, mThenStmt(thenStmt)
	, mElseStmt(elseStmt)
	{ }
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTExpr> mExpr;
	std::shared_ptr<ASTStmt> mThenStmt;
	std::shared_ptr<ASTStmt> mElseStmt;
};

class ASTWhileStmt : public ASTStmt
{
public:
	ASTWhileStmt(std::shared_ptr<ASTExpr> expr, std::shared_ptr<ASTStmt> loopStmt) noexcept
	: mExpr(expr)
	, mLoopStmt(loopStmt)
	{ }
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTExpr> mExpr;
	std::shared_ptr<ASTStmt> mLoopStmt;
};
	
class ASTReturnStmt : public ASTStmt
{
public:
	ASTReturnStmt(std::shared_ptr<ASTExpr> expr) noexcept
	: mExpr(expr)
	{ }
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTExpr> mExpr;
};

class ASTExprStmt : public ASTStmt
{
public:
	ASTExprStmt(std::shared_ptr<ASTExpr> expr) noexcept
	: mExpr(expr)
	{ }
	AST_DECL_PRINT_EMIT();
private:
	std::shared_ptr<ASTExpr> mExpr;
};

class ASTNullStmt : public ASTStmt
{
	AST_DECL_PRINT_EMIT();
};


} // parse
} // uscc
