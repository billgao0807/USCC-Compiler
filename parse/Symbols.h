//
//  Symbols.h
//  uscc
//
//  Defines the symbol and string tables used for
//  semantic analysis.
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#pragma once
#include <string>
#include <memory>
#include <unordered_map>
#include <list>

#include "Types.h"

namespace llvm
{
	class Value;
	class Type;
}

namespace uscc
{
namespace parse
{

class ASTFunction;
struct CodeContext;

// An identifier is constructed per each entry in the symbol table
class Identifier
{
	friend class SymbolTable;
public:
	const std::string& getName() const noexcept
	{
		return mName;
	}
	void setType(Type type) noexcept
	{
		mType = type;
	}
	Type getType() const noexcept
	{
		return mType;
	}
	
	// Sets number of elements in an array
	// (used only for array types)
	void setArrayCount(size_t count) noexcept
	{
		mArrayCount = count;
	}
	size_t getArrayCount() const noexcept
	{
		return mArrayCount;
	}
	bool isArray() const noexcept
	{
		return (mType == Type::CharArray ||
				mType == Type::IntArray);
	}
	
	// For function identifiers
	bool isFunction() const noexcept
	{
		return mType == Type::Function;
	}
	
	std::shared_ptr<ASTFunction> getFunction() const noexcept
	{
		return mFunctionNode;
	}
	
	void setFunction(std::shared_ptr<ASTFunction> func) noexcept
	{
		mFunctionNode = func;
	}
	
	bool isDummy() const noexcept
	{
		return mName == "@@variable" || mName == "@@function";
	}
	
	llvm::Value* getAddress() noexcept
	{
		return mAddress;
	}
	
	void setAddress(llvm::Value* value) noexcept
	{
		mAddress = value;
	}
	
	llvm::Type* llvmType(bool treatArrayAsPtr = true) noexcept;
	
	llvm::Value* readFrom(CodeContext& ctx) noexcept;
	
	void writeTo(CodeContext& ctx, llvm::Value* value) noexcept;
	
private:
	// Private constructor so only the symbol table can create
	Identifier(const char* name)
	: mName(name)
	, mFunctionNode(nullptr)
	, mAddress(nullptr)
	, mType(Type::Void)
	, mArrayCount(-1)
	{ }
	
	std::string mName;
	std::shared_ptr<ASTFunction> mFunctionNode;
	llvm::Value* mAddress;
	Type mType;
	size_t mArrayCount;
};

// NOTE: I don't use shared_ptrs for the symbol table
// because the idea is the symbol table won't be deleted
// until program execution ends.
class SymbolTable
{
public:
	class ScopeTable;
	
	SymbolTable() noexcept;
	~SymbolTable() noexcept;
	
	// Returns true if this variable is already declared
	// in this scope (ignoring parent scopes).
	// Used to prevent redeclaration in the same scope,
	// which is disallowed.
	bool isDeclaredInScope(const char* name) const noexcept;
	
	// Creates the requested identifier, and returns a pointer
	// to it.
	// NOTE: If the identifier already exists, nothing will happen.
	// This means you should first check with isDeclaredInScope.
	Identifier* createIdentifier(const char* name);
	
	// Returns a pointer to the identifier, if it's found
	// Otherwise returns nullptr
	Identifier* getIdentifier(const char* name);
	
	// Enters a new scope, and returns a pointer to this scope table
	ScopeTable* enterScope();
	
	// Exits the current scope and moves the current scope back to
	// the previous scope table.
	void exitScope();

	// Prints the symbol table to the specified stream
	void print(std::ostream& output) const noexcept;

	// Symbol table for a specific scope
	class ScopeTable
	{
	public:
		ScopeTable(ScopeTable* parent) noexcept;
		~ScopeTable() noexcept;
		
		// Adds the requested identifier to the table
		void addIdentifier(Identifier* ident);
		
		// Searches this scope for an identifier with
		// the requested name. Returns nullptr if not found.
		Identifier* searchInScope(const char* name) noexcept;
		
		// Searches this scope first, and if not found searches
		// through parent scopes. Returns nullptr if not found.
		Identifier* search(const char* name) noexcept;
		
		// Emits declarations for ALL non-function symbols
		// in this scope. Used to front-load all stack-based variables
		// to the start of the function
		void emitIR(CodeContext& ctx);
		
		// Prints the scope table to the specified stream
		void print(std::ostream& output, int depth = 0) const noexcept;

		ScopeTable* getParent()
		{
			return mParent;
		}
	private:
		// Hash table contains all the identifiers in this scope
		std::unordered_map<std::string, Identifier*> mSymbols;
		
		// List of the child tables
		std::list<ScopeTable*> mChildren;
		
		// Points to parent ScopeTable
		ScopeTable* mParent;
	};
	
private:
	// Pointer to the current scope table
	ScopeTable* mCurrScope;
};
	
// Used to store/reference constant strings
class ConstStr
{
	friend class StringTable;
public:
	ConstStr(std::string& text)
	: mText(text)
	, mValue(nullptr)
	{
		
	}
	
	const std::string& getText() const noexcept
	{
		return mText;
	}
	
	llvm::Value* getValue() const noexcept
	{
		return mValue;
	}
private:
	std::string mText;
	llvm::Value* mValue;
};
	
class StringTable
{
public:
	StringTable() noexcept;
	~StringTable() noexcept;
	
	// Looks up the requested string in the string table
	// If it exists, returns the corresponding ConstStr
	// Otherwise, constructs a new ConstStr and returns that
	ConstStr* getString(std::string& val) noexcept;
	
	// Emit this table to the IR contstants
	void emitIR(CodeContext& ctx) noexcept;
private:
	std::unordered_map<std::string, ConstStr*> mStrings;
};

} // uscc
} // parse
