//
//  Tokens.h
//  uscc
//
//  Defines the token enum used by the scanner.
//  This file is generated via X Macros, and has a container
//  "Token" struct
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#pragma once

namespace uscc
{
namespace scan
{
struct Token
{

	// Would prefer to use an enum class instead of the Token
	// namespace, but the flex class would freak out.
	enum Tokens
	{
		#define TOKEN(a,b,c) a,
		#include "Tokens.def"
		#undef TOKEN
	};

	static const char** Names;

	static const char** Values;
	
	static const int* Lengths;
};
} // scan
} // uscc
