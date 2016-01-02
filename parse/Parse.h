//
//  Parse.h
//  uscc
//
//  This declares the parser class including all of the
//  mutually recursive parsing functions.
//
//  If the parse is successful, it will create an AST
//
//  These functions are implemented in three different
//  source files - Parse.cpp, ParseExpr.cpp, ParseStmt.cpp
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#pragma once

#include "../scan/Tokens.h"
#include <initializer_list>
#include <fstream>
#include <memory>
#include <list>
#include "ASTNodes.h"
#include "ParseExcept.h"
#include "Symbols.h"

class FlexLexer;

namespace uscc
{
namespace parse
{
	
class Identifier;

class Parser
{
	friend class Emitter;
public:
	// Constructor takes in a file name and performs the parse
	Parser(const char* fileName, std::ostream* errStream,
		   std::ostream* ASTStream, bool outputSymbols);
	
	// Destructor not virtual; I don't expect any inheritance
	~Parser();
	
	// Returns true if the parse was successful
	bool IsValid() const noexcept
	{
		return mErrors.size() == 0;
	}
	
	size_t GetNumErrors() const noexcept
	{
		return mErrors.size();
	}
	
protected:
	// Various helper functions
	
	// Returns the current token
	scan::Token::Tokens peekToken() const noexcept
	{
		return mCurrToken;
	}
	
	// Returns the string for the current token's text
	const char* getTokenTxt() const noexcept;
	
	// Consumes the current token, and moves to the next
	// token that's not a NewLine or Comment.
	//
	// Throws an exception if next token is Unknown,
	// if unknownIsExcept is true
	void consumeToken(bool unknownIsExcept = true);
	
	// Sees if the token matches the requested.
	// If it does, it'll consume the token and return true
	// otherwise it'll return false
	//
	// Throws an exception if next token is Unknown
	bool peekAndConsume(scan::Token::Tokens desired);
	
	// Returns true if the current token matches one of the tokens
	// in the list.
	bool peekIsOneOf(const std::initializer_list<scan::Token::Tokens>& list) noexcept;
	
	// Matches the current token against the requested token,
	// and consumes it.
	//
	// Throws an exception if there is a mismatch.
	//
	// NOTE: You should ONLY use this for terminals that are always a specific text.
	void matchToken(scan::Token::Tokens desired);
	
	// Matches the current token against the first element
	// in the initializer_list. Then consumes and verifies all
	// remaining requested elements.
	//
	// Throws an exception if there is a mismatch.
	// Since it throws an exception, it should only be used in instances where a
	// specific token order is the ONLY valid match.
	// It also throws an exception of the next token is Unknown
	//
	// NOTE: You should ONLY use this for terminals that are always a specific text.
	// Don't use it for identifier, constant, or string, because you'll have no way to
	// get the text.
	void matchTokenSeq(const std::initializer_list<scan::Token::Tokens>& list);
	
	// Consumes tokens until either a match or EOF is found
	void consumeUntil(scan::Token::Tokens desired) noexcept;
	
	// consumeUntil for a list of tokens
	void consumeUntil(const std::initializer_list<scan::Token::Tokens>& list) noexcept;
	
	// Helper functions to report syntax errors
	void reportError(const ParseExcept& except) noexcept;
	void reportError(const std::string& msg) noexcept;
	
	// Helper function to report a semantic error
	// (These only display if mCheckSemant == true)
	void reportSemantError(const std::string& msg, int colOverride = -1,
						   int lineOverride = -1) noexcept;
	
	// Struct used to store an error
	struct Error
	{
		Error(const std::string& msg, int lineNum, int colNum)
		: mMsg(msg)
		, mLineNum(lineNum)
		, mColNum(colNum)
		{ }
		
		std::string mMsg;
		int mLineNum;
		int mColNum;
	};
	
	// Write an error message to the error stream
	void displayErrorMsg(const std::string& line, std::shared_ptr<Error> error) noexcept;
	
	// Writes out all the error messages
	void displayErrors() noexcept;
	
	// Gets the variable, if it exists. Otherwise
	// reports a semant error and returns @@variable
	Identifier* getVariable(const char* name) noexcept;
	
	// Returns a char* that contains the type name
	const char* getTypeText(Type type) const noexcept;
	
	// Takes the expression, and if it's an char expression, converts it to an int type
	// expression.
	// Otherwise it doesn't do anything.
	std::shared_ptr<ASTExpr> charToInt(std::shared_ptr<ASTExpr> expr) noexcept;
	
	// Like the above, but in reverse
	std::shared_ptr<ASTExpr> intToChar(std::shared_ptr<ASTExpr> expr) noexcept;
	
protected:
	// These are all the mutually recursive parse functions
	
	// The entry point for the parser (in Parse.cpp)
	std::shared_ptr<ASTProgram> parseProgram();
	
	// Functions (in Parse.cpp)
	std::shared_ptr<ASTFunction> parseFunction();
	std::shared_ptr<ASTArgDecl> parseArgDecl();
	
	// Declaration (in ParseStmt.cpp)
	std::shared_ptr<ASTDecl> parseDecl();
	
	// Statements (in ParseStmt.cpp)
	std::shared_ptr<ASTStmt> parseStmt();
	// If the compound statement is a function body, then the symbol table scope
	// change will happen at a higher level, so it shouldn't happen in
	// parseCompoundStmt.
	std::shared_ptr<ASTCompoundStmt> parseCompoundStmt(bool isFuncBody = false);
	std::shared_ptr<ASTStmt> parseAssignStmt();
	std::shared_ptr<ASTIfStmt> parseIfStmt();
	std::shared_ptr<ASTWhileStmt> parseWhileStmt();
	std::shared_ptr<ASTReturnStmt> parseReturnStmt();
	std::shared_ptr<ASTExprStmt> parseExprStmt();
	std::shared_ptr<ASTNullStmt> parseNullStmt();
	
	// Expressions (in ParseExpr.cpp)
	std::shared_ptr<ASTExpr> parseExpr();
	std::shared_ptr<ASTLogicalOr> parseExprPrime(std::shared_ptr<ASTExpr> lhs);
	
	// AndTerm (in ParseExpr.cpp)
	std::shared_ptr<ASTExpr> parseAndTerm();
	std::shared_ptr<ASTLogicalAnd> parseAndTermPrime(std::shared_ptr<ASTExpr> lhs);
	
	// RelExpr (in ParseExpr.cpp)
	std::shared_ptr<ASTExpr> parseRelExpr();
	std::shared_ptr<ASTBinaryCmpOp> parseRelExprPrime(std::shared_ptr<ASTExpr> lhs);
	
	// NumExpr (in ParseExpr.cpp)
	std::shared_ptr<ASTExpr> parseNumExpr();
	std::shared_ptr<ASTBinaryMathOp> parseNumExprPrime(std::shared_ptr<ASTExpr> lhs);
	
	// Term (in ParseExpr.cpp)
	std::shared_ptr<ASTExpr> parseTerm();
	std::shared_ptr<ASTBinaryMathOp> parseTermPrime(std::shared_ptr<ASTExpr> lhs);
	
	// Value (in ParseExpr.cpp)
	std::shared_ptr<ASTExpr> parseValue();
	
	// Factor (in ParseExpr.cpp)
	std::shared_ptr<ASTExpr> parseFactor();
	std::shared_ptr<ASTExpr> parseParenFactor();
	std::shared_ptr<ASTConstantExpr> parseConstantFactor();
	std::shared_ptr<ASTStringExpr> parseStringFactor();
	// parseIdentFactor parses id, id [Expr], and id (FunCallArgs)
	std::shared_ptr<ASTExpr> parseIdentFactor();
	std::shared_ptr<ASTExpr> parseIncFactor();
	std::shared_ptr<ASTExpr> parseDecFactor();
	std::shared_ptr<ASTExpr> parseAddrOfArrayFactor();
	
private:
	// Disallow copy/assignment
	Parser(const Parser& copy) { }
	Parser& operator=(const Parser& rhs) { return *this; }
	
	// Pointer to the root of our AST root
	std::shared_ptr<ASTProgram> mRoot;
	
	// Used to resolve AsisgnStmt/Factor ambiguity
	Identifier* mUnusedIdent;
	std::shared_ptr<ASTArraySub> mUnusedArray;
	
	// Symbol table corresponding to the parsed file
	SymbolTable mSymbols;
	// String table for this file
	StringTable mStrings;
	
	// Flex wrapper class
	FlexLexer* mLexer;

	// Name of the file we're parsing
	const char* mFileName;
	// File stream that we use to process the file
	std::ifstream mFileStream;
	// Ostream exceptions should be output to
	std::ostream* mErrStream;
	// Ostream for AST output
	std::ostream* mASTStream;
	
	// Tracks the return type of the current function
	Type mCurrReturnType;
	
	// Current active token
	uscc::scan::Token::Tokens mCurrToken;
	
	// Keeps track of the line number in the file
	unsigned int mLineNumber;
	// Keeps track of the column number in the current line
	unsigned int mColNumber;
	
	// List used to store all of the errors
	std::list<std::shared_ptr<Error>> mErrors;
	
	// Track whether we need printf
	bool mNeedPrintf;
	
	// Do we want to check for semantic errors?
	bool mCheckSemant;

	// Do we want to output the symbol table?
	bool mOutputSymbols;
};

} // parse
} // uscc
