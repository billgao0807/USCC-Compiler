//
//  ParseExcept.h
//  uscc
//
//  Defines exceptions that can be thrown during the parse.
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#pragma once

#include <exception>
#include <ostream>
#include "../scan/Tokens.h"

namespace uscc
{
namespace parse
{

class ParseExcept : public virtual std::exception
{
public:
	virtual const char* what() const noexcept override
	{
		return "Exception while parsing";
	}
	
	virtual void printException(std::ostream& output) const noexcept;
};
	
class ParseExceptMsg : public virtual ParseExcept
{
public:
	ParseExceptMsg(const char* msg)
	: mMsg(msg)
	{ }
	
	virtual const char* what() const noexcept override
	{
		return "Exception while parsing w/ message";
	}
	
	virtual void printException(std::ostream& output) const noexcept override;
	
private:
	const char* mMsg;
};

class FileNotFound : public virtual ParseExcept
{
public:
	virtual const char* what() const noexcept override
	{
		return "File not found\n";
	}
};
	
class EOFExcept : public virtual ParseExcept
{
public:
	virtual const char* what() const noexcept override
	{
		return "Unexpected end of file";
	}
};

class UnknownToken : public virtual ParseExcept
{
public:
	UnknownToken(const char* tokStr, unsigned int& colNum)
	: mToken(tokStr)
	, mColNum(colNum)
	{ }
	
	virtual ~UnknownToken() override
	{
		mColNum++;
	}
	
	virtual const char* what() const noexcept override
	{
		return "Unknown token";
	}
	
	virtual void printException(std::ostream& output) const noexcept override;
private:
	const char* mToken;
	unsigned int& mColNum;
};
	
class TokenMismatch : public virtual ParseExcept
{
public:
	TokenMismatch(scan::Token::Tokens expected, scan::Token::Tokens actual,
				  const char* tokStr)
	: mExpectedTok(expected)
	, mActualTok(actual)
	, mTokenStr(tokStr)
	{ }
	
	virtual const char* what() const noexcept override
	{
		return "Token mismatch detected";
	}
	
	virtual void printException(std::ostream& output) const noexcept override;
	
private:
	scan::Token::Tokens mExpectedTok;
	scan::Token::Tokens mActualTok;
	const char* mTokenStr;
};
	
class OperandMissing : public virtual ParseExcept
{
public:
	OperandMissing(scan::Token::Tokens op)
	: mOp(op)
	{ }
	
	virtual const char* what() const noexcept override
	{
		return "Missing binary operand";
	}
	
	virtual void printException(std::ostream& output) const noexcept override;
private:
	scan::Token::Tokens mOp;
};
	
} // parse
} // uscc
