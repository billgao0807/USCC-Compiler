//
//  Types.h
//  uscc
//
//  Defines Types, for supporting semantic analysis
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
namespace parse
{

enum class Type
{
	Void = 0,
	Int,
	Char,
	IntArray,
	CharArray,
	Function
};

} // parse
} // uscc
