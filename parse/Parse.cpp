//
//  Parse.cpp
//  uscc
//
//  Implements all of the helper/diagnostic functions
//  in the Parser class, as well as some of the primary
//  recursive descent functions such as parseProgram
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#include "Parse.h"
#include <FlexLexer.h>
#include "Symbols.h"

// Used if you want to see each token
#define DEBUG_PRINT_TOKENS 0
#include <sstream>

#if DEBUG_PRINT_TOKENS
#include <iostream>
#endif

using namespace uscc::parse;
using namespace uscc::scan;
using std::shared_ptr;
using std::make_shared;

// Constructor takes in a file name and performs the parse
Parser::Parser(const char* fileName, std::ostream* errStream,
			   std::ostream* ASTStream, bool outputSymbols)
: mCurrToken(Token::Unknown)
, mFileName(fileName)
, mFileStream(fileName)
, mErrStream(errStream)
, mASTStream(ASTStream)
, mLineNumber(1)
, mColNumber(1)
, mUnusedIdent(nullptr)
, mNeedPrintf(false)
, mCheckSemant(false) // PA2: Change to true
, mOutputSymbols(outputSymbols)
{
	if (mFileStream.is_open())
	{
		mLexer = new yyFlexLexer(&mFileStream);
				
		try
		{
			// Get the first token
			consumeToken();

			// Now start the parse
			mRoot = parseProgram();
		}
		catch (ParseExcept& e)
		{
			reportError(e);
		}
	}
	else
	{
		throw FileNotFound();
	}
	
	if (!IsValid())
	{
		displayErrors();
	}
}

// Destructor not virtual; I don't expect any inheritance
Parser::~Parser()
{
	delete mLexer;
}

// Returns the string for the current token's text
const char* Parser::getTokenTxt() const noexcept
{
	const char* retVal = "";
	if (mCurrToken != Token::Unknown && mCurrToken != Token::EndOfFile)
	{
		retVal = mLexer->YYText();
	}
	
	return retVal;
}

// Consumes the current token, and moves to the next
// token that's not a NewLine or Comment.
//
// Throws an exception if next token is Unknown,
// if unknownIsExcept is true
void Parser::consumeToken(bool unknownIsExcept)
{
	// Add to the column number once we move past
	// this token.
	if (mCurrToken != Token::Unknown)
	{
		int len = Token::Lengths[mCurrToken];
		if (len != -1)
		{
			mColNumber += len;
		}
		else
		{
			mColNumber += mLexer->YYLeng();
		}
	}
	
	do
	{
		mCurrToken = static_cast<Token::Tokens>(mLexer->yylex());
#if DEBUG_PRINT_TOKENS
		if (mCurrToken == Token::Comment)
		{
			std::cout << Token::Names[mCurrToken] << ": " << mLexer->YYText();
		}
		else if (mCurrToken != Token::Newline && mCurrToken != Token::Space &&
				 mCurrToken != Token::Tab)
		{
			std::cout << Token::Names[mCurrToken] << ": " << mLexer->YYText() << "\n";
		}
#endif
		if (mCurrToken == Token::Newline || mCurrToken == Token::Comment)
		{
			mLineNumber++;
			mColNumber = 1;
		}
		else if (mCurrToken == Token::Space || mCurrToken == Token::Tab)
		{
			mColNumber++;
		}
		else if (mCurrToken == Token::Unknown)
		{
			// We don't want to always throw an exception, in case we are in
			// error recovery mode.
			if (unknownIsExcept)
			{
				throw UnknownToken(mLexer->YYText(), mColNumber);
			}
			else
			{
				std::string msg("Invalid symbol: ");
				msg += mLexer->YYText();
				reportError(msg);
				mColNumber++;
			}
		}
	}
	while(mCurrToken == Token::Newline || mCurrToken == Token::Comment ||
		  mCurrToken == Token::Space || mCurrToken == Token::Tab ||
		  mCurrToken == Token::Unknown);
}

// Sees if the token matches the requested.
// If it does, it'll consume the token and return true
// otherwise it'll return false
//
// Throws an exception if next token is Unknown
bool Parser::peekAndConsume(Token::Tokens desired)
{
	if (mCurrToken == desired)
	{
		consumeToken();
		return true;
	}
	
	return false;
}
	
// Returns true if the current token matches one of the tokens
// in the list.
bool Parser::peekIsOneOf(const std::initializer_list<Token::Tokens>& list) noexcept
{
	for (Token::Tokens t : list)
	{
		if (t == peekToken())
		{
			return true;
		}
	}
	return false;
}

// Matches the current token against the requested token,
// and consumes it.
//
// Throws an exception if there is a mismatch.
//
// NOTE: You should ONLY use this for terminals that are always a specific text.
void Parser::matchToken(Token::Tokens desired)
{
	if (!peekAndConsume(desired))
	{
		throw TokenMismatch(desired, mCurrToken, getTokenTxt());
	}
}

// Matches the current token against the first element
// in the initializer_list. Then consumes and checks all
// remaining requested elements.
//
// Throws an exception if there is a mismatch.
// Since it throws an exception, it should only be used in instances where a
// specific token order is the ONLY valid match.
//
// Also throws an exception if next token is Unknown
//
// NOTE: You should ONLY use this for terminals that are always a specific text.
// Don't use it for identifier, constant, or string, because you'll have no way to
// get the text.
void Parser::matchTokenSeq(const std::initializer_list<Token::Tokens>& list)
{
	for (Token::Tokens t : list)
	{
		if (!peekAndConsume(t))
		{
			throw TokenMismatch(t, mCurrToken, getTokenTxt());
		}
	}
}

// Consumes tokens until either a match or EOF is found
//
// Throws an exception if next token is Unknown
void Parser::consumeUntil(Token::Tokens desired) noexcept
{
	while (mCurrToken != desired && mCurrToken != Token::EndOfFile)
	{
		consumeToken(false);
	}
}

// consumeUntil for a list of tokens
//
// Throws an exception if next token is Unknown
void Parser::consumeUntil(const std::initializer_list<Token::Tokens>& list) noexcept
{
	if (mCurrToken == Token::EndOfFile)
	{
		return;
	}
	
	do
	{
		for (auto t : list)
		{
			if (mCurrToken == t)
			{
				return;
			}
		}
		
		consumeToken(false);
	}
	while (mCurrToken != Token::EndOfFile);
}
			
// Helper functions to report syntax errors
void Parser::reportError(const ParseExcept& except) noexcept
{
	std::stringstream errStrm;
	except.printException(errStrm);
	mErrors.push_back(std::make_shared<Error>(errStrm.str(), mLineNumber, mColNumber));
}
			
void Parser::reportError(const std::string& msg) noexcept
{
	mErrors.push_back(std::make_shared<Error>(msg, mLineNumber, mColNumber));
}
	
void Parser::reportSemantError(const std::string& msg, int colOverride, int lineOverride) noexcept
{
	if (mCheckSemant)
	{
		int col;
		if (colOverride == -1)
		{
			col = mColNumber;
		}
		else
		{
			col = colOverride;
		}
		
		int line;
		if (lineOverride == -1)
		{
			line = mLineNumber;
		}
		else
		{
			line = lineOverride;
		}
		
		mErrors.push_back(make_shared<Error>(msg, line, col));
	}
}

void Parser::displayErrorMsg(const std::string& line, std::shared_ptr<Error> error) noexcept
{
	(*mErrStream) << mFileName << ":" << error->mLineNum << ":" << error->mColNum;
	(*mErrStream) << ": error: ";
	(*mErrStream) << error->mMsg << std::endl;
	
	(*mErrStream) << line << std::endl;
	// Now add the caret
	for (int i = 0; i < error->mColNum - 1; i++)
	{
		if (line[i] == '\t')
		{
			(*mErrStream) << '\t';
		}
		else
		{
			(*mErrStream) << ' ';
		}
	}
	(*mErrStream) << '^' << std::endl;
}
	
void Parser::displayErrors() noexcept
{
	// Output errors
	// Move the filestream back to the start
	int lineNum = 0;
	std::string lineTxt;
	mFileStream.clear();
	mFileStream.seekg(0, std::ios::beg);
	for (auto i = mErrors.begin();
		 i != mErrors.end();
		 ++i)
	{
		while (lineNum < (*i)->mLineNum)
		{
			std::getline(mFileStream, lineTxt);
			lineNum++;
		}
		
		displayErrorMsg(lineTxt, *i);
	}
}

Identifier* Parser::getVariable(const char* name) noexcept
{
	// PA2: Implement properly
	
	Identifier* ident = mSymbols.createIdentifier(name);
	
	return ident;
}

const char* Parser::getTypeText(Type type) const noexcept
{
	switch (type)
	{
		case Type::Char:
			return "char";
		case Type::Int:
			return "int";
		case Type::Void:
			return "void";
		case Type::CharArray:
			return "char[]";
		case Type::IntArray:
			return "int[]";
		case Type::Function:
			return "function";
	}
}

// Takes the expression, and if it's a char expression, converts it to an int type
// expression.
// Otherwise it doesn't do anything.
std::shared_ptr<ASTExpr> Parser::charToInt(std::shared_ptr<ASTExpr> expr) noexcept
{
	std::shared_ptr<ASTExpr> retVal = expr;
	
	// PA2: Implement
	
	return retVal;
}

// Like the above, but in reverse
std::shared_ptr<ASTExpr> Parser::intToChar(std::shared_ptr<ASTExpr> expr) noexcept
{
	std::shared_ptr<ASTExpr> retVal = expr;
	
	// PA2: Implement
	
	return retVal;
}

// The entry point for the parser
shared_ptr<ASTProgram> Parser::parseProgram()
{
	// Create our base program node.
	shared_ptr<ASTProgram> retVal = make_shared<ASTProgram>();
	
	shared_ptr<ASTFunction> func = parseFunction();
	
	while (func)
	{
		retVal->addFunction(func);
		func = parseFunction();
	}
	
	if (peekToken() != Token::EndOfFile)
	{
		reportError("Expected end of file");
	}
	
	if (IsValid())
	{
		if (mASTStream)
		{
			retVal->printNode((*mASTStream));
			if (mOutputSymbols)
			{
				mSymbols.print((*mASTStream));
			}
		}
	}
	
	return retVal;
}
	
shared_ptr<ASTFunction> Parser::parseFunction()
{
	shared_ptr<ASTFunction> retVal;
	
	// Check for a return type
	if (peekIsOneOf({Token::Key_void, Token::Key_int, Token::Key_char}))
	{
		Type retType;
		
		switch(peekToken())
		{
			case Token::Key_char:
				retType = Type::Char;
				break;
			case Token::Key_int:
				retType = Type::Int;
				break;
			default:
			case Token::Key_void:
				retType = Type::Void;
				break;
		}
		
		mCurrReturnType = retType;
		
		consumeToken();
		
		// Add a useful message if they're trying to return
		// an array, which USC doesn't allow
		if (peekAndConsume(Token::LBracket))
		{
			reportSemantError("USC does not allow return of array types", mColNumber - 1);
			consumeUntil(Token::RBracket);
			if (peekToken() == Token::EndOfFile)
			{
				throw EOFExcept();
			}
			matchToken(Token::RBracket);
		}
		
		Identifier* ident = nullptr;
		if (peekToken() != Token::Identifier)
		{
			// If we don't have an identifier, then just make one with @@function
			// so the parse will continue
			std::string err = "Function name ";
			err += getTokenTxt();
			err += " is invalid";
			reportError(err);
			
			// Set this to a bogus debug symbol so the parse continues
			
			ident = mSymbols.getIdentifier("@@function");
			// skip until the open parenthesis
			consumeUntil(Token::LParen);
			if (peekToken() == Token::EndOfFile)
			{
				throw EOFExcept();
			}
		}
		else
		{
			// We're making a new function, see if it's valid to do so
			if (mSymbols.isDeclaredInScope(getTokenTxt()))
			{
				// Invalid redeclaration
				std::string err = "Invalid redeclaration of function '";
				err += getTokenTxt();
				err += '\'';
				reportSemantError(err);
				
				// Set the identifier to @@function
				ident = mSymbols.getIdentifier("@@function");
			}
			else
			{
				ident = mSymbols.createIdentifier(getTokenTxt());
				ident->setType(Type::Function);
				
				if (ident->getName() == "main" && retType != Type::Int)
				{
					reportSemantError("Function 'main' must return an int");
				}
			}
			
			consumeToken();
		}
		
		// Once we are here, it's time to enter the scope of the function,
		// since arguments count as the function's main body scope
		SymbolTable::ScopeTable* table = mSymbols.enterScope();
		
		retVal = make_shared<ASTFunction>(*ident, retType, *table);
		
		// If this isn't the dummy function, hook up the node
		if (!ident->isDummy())
		{
			ident->setFunction(retVal);
		}
		
		if (peekAndConsume(Token::LParen))
		{
			try
			{
				shared_ptr<ASTArgDecl> arg = parseArgDecl();
				while (arg)
				{
					retVal->addArg(arg);
					if (peekAndConsume(Token::Comma))
					{
						arg = parseArgDecl();
						if (!arg)
						{
							throw ParseExceptMsg("Additional function argument must follow a comma.");
						}
					}
					else
					{
						break;
					}
				}
			}
			catch (ParseExcept& e)
			{
				reportError(e);
				consumeUntil(Token::RParen);
				if (peekToken() == Token::EndOfFile)
				{
					throw EOFExcept();
				}
			}
			
			matchToken(Token::RParen);
			if (ident->getName() == "main" && retVal->getNumArgs() != 0)
			{
				reportSemantError("Function 'main' cannot take any arguments");
			}
		}
		else
		{
			std::string err = "Missing argument declaration for function ";
			err += ident->getName();
			reportError(err);
			// skip until the compound stmt
			consumeUntil(Token::LBrace);
			if (peekToken() == Token::EndOfFile)
			{
				throw EOFExcept();
			}
		}
		
		// Grab the compound statement for this function
		shared_ptr<ASTCompoundStmt> funcCompoundStmt;
		try
		{
			funcCompoundStmt = parseCompoundStmt(true);
		}
		catch (ParseExcept& e)
		{
			// Something really bad happened here
			reportError(e);
			// Skip all the tokens until the } brace
			consumeUntil(Token::RBrace);
			if (peekToken() == Token::EndOfFile)
			{
				throw EOFExcept();
			}
			consumeToken();
		}
		
		// Exit the scope, before we potentially throw out of this function
		// for a non-EOF message.
		mSymbols.exitScope();
		
		if (!funcCompoundStmt)
		{
			throw ParseExceptMsg("Function implementation missing");
		}
		
		// Add the compound statement to this function
		retVal->setBody(funcCompoundStmt);
	}
	
	return retVal;
}
	
shared_ptr<ASTArgDecl> Parser::parseArgDecl()
{
	shared_ptr<ASTArgDecl> retVal;
	
	if (peekIsOneOf({Token::Key_int, Token::Key_char}))
	{
		Type varType = Type::Void;
		switch (peekToken())
		{
			case Token::Key_int:
				varType = Type::Int;
				break;
			case Token::Key_char:
				varType = Type::Char;
				break;
			default:
				// Shouldn't get here
				varType = Type::Void;
				break;
		}
		
		consumeToken();
		
		if (peekToken() != Token::Identifier)
		{
			throw ParseExceptMsg("Unnamed function parameters are not allowed");
		}
		
		// For now, set it to the default "error" until we see if this is a new
		// identifier
		Identifier* ident = mSymbols.getIdentifier("@@variable");
		if (mSymbols.isDeclaredInScope(getTokenTxt()))
		{
			std::string errMsg("Invalid redeclaration of argument '");
			errMsg += getTokenTxt();
			errMsg += '\'';
			// Leave at @@variable
		}
		else
		{
			ident = mSymbols.createIdentifier(getTokenTxt());
		}
		
		consumeToken();
		
		// Is this an array type?
		if (peekAndConsume(Token::LBracket))
		{
			matchToken(Token::RBracket);
			if (varType == Type::Int)
			{
				varType = Type::IntArray;
			}
			else if (varType == Type::Char)
			{
				varType = Type::CharArray;
			}
		}
		ident->setType(varType);
		
		retVal = make_shared<ASTArgDecl>(*ident);
	}
	
	return retVal;
}
