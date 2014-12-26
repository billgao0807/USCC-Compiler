//
//  Tokens.cpp
//  uscc
//
//  Uses X Macros to generate global data used mostly for
//  diagnostic messages.
//
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#include "Tokens.h"

using namespace uscc::scan;

namespace
{
    
static const char* Names_data[] =
{
    #define TOKEN(a,b,c) #a,
    #include "Tokens.def"
    #undef TOKEN
};
    
static const char* Values_data[] =
{
    #define TOKEN(a,b,c) b,
    #include "Tokens.def"
    #undef TOKEN
};
	
static const int Lengths_data[] =
{
#define TOKEN(a,b,c) c,
#include "Tokens.def"
#undef TOKEN
};
    
} // anonymous

const char** Token::Names = Names_data;
const char** Token::Values = Values_data;
const int* Token::Lengths = Lengths_data;
