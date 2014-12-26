//
//  ParseExcept.cpp
//  uscc
//
//  Implements exceptions that are thrown during parse
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#include "ParseExcept.h"

using namespace uscc::parse;
using namespace uscc::scan;

void ParseExcept::printException(std::ostream& output) const noexcept
{
	output << what();
}

void ParseExceptMsg::printException(std::ostream& output) const noexcept
{
	output << mMsg;
}

void UnknownToken::printException(std::ostream& output) const noexcept
{
	output << "Invalid symbol: " << mToken;
}
	
void TokenMismatch::printException(std::ostream& output) const noexcept
{
	output << "Expected: " << Token::Values[mExpectedTok];
	output << " but saw: ";
	if (mActualTok != Token::Constant && mActualTok != Token::String &&
		mActualTok != Token::Identifier)
	{
		output << Token::Values[mActualTok];
	}
	else
	{
		output << mTokenStr;
	}
}
	
void OperandMissing::printException(std::ostream& output) const noexcept
{
	output << "Binary operation " << Token::Values[mOp];
	output << " requires two operands.";
}
