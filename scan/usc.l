%option noyywrap
%option nounistd

%{
#include "Tokens.h"
using namespace uscc::scan;
%}

%%

%{
    /* Keywords */
%}

"char"                  { return Token::Key_char; }
"else"                  { return Token::Key_else; }
"if"                    { return Token::Key_if; }
"int"                   { return Token::Key_int; }
"return"                { return Token::Key_return; }
"void"                  { return Token::Key_void; }
"while"                 { return Token::Key_while; }

%{
    /* Expression Operators */
%}
"="						{ return Token::Assign; }
"+"						{ return Token::Plus; }
"-"						{ return Token::Minus; }
"*"						{ return Token::Mult; }
"/"						{ return Token::Div; }
"%"                     { return Token::Mod; }
"++"                    { return Token::Inc; }
"--"                    { return Token::Dec; }
"["                     { return Token::LBracket; }
"]"                     { return Token::RBracket; }
"=="                    { return Token::EqualTo; }
"!="                    { return Token::NotEqual; }
"||"					{ return Token::Or; }
"&&"					{ return Token::And; }
"!"						{ return Token::Not; }
"<"                     { return Token::LessThan; }
">"                     { return Token::GreaterThan; }
"("						{ return Token::LParen; }
")"						{ return Token::RParen; }
"&"						{ return Token::Addr; }

%{
    /* Other */
%}
";"                     { return Token::SemiColon; }
"{"                     { return Token::LBrace; }
"}"                     { return Token::RBrace; }
","                     { return Token::Comma; }

%{
    /* Values */
%}

"\'"("\\t"|"\\n"|.)"\'" { return Token::Constant; }
"-"?(0|([1-9][0-9]*))   { return Token::Constant; }
\"([^\\\"]|\\n|\\t)*\"  { return Token::String; }

%{
    /* Identifier */
%}

[a-zA-Z_][a-zA-Z0-9_]*  { return Token::Identifier; }

%{
    /* White space/comments */
%}

" "						{ return Token::Space; }
"\t"					{ return Token::Tab; }

("\n"|"\r\n")           { return Token::Newline; }
"//".*(\n|"\r\n")       { return Token::Comment; }

%{
    /* Unknown token */
%}

.						{ return Token::Unknown; }

%%
