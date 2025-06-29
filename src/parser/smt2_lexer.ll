/* Definitions Section */

%{
#include "smt2_lexer.h"

/* using "token" to make the returns for the tokens shorter to type */
using Token = yaga::parser::Token;

/* define yyterminate as this instead of NULL */
#define yyterminate() return( Token::EOF_TOK )

%}



%option noyywrap
%option nounput
%option c++
%option yyclass="yaga::parser::smt2_lexer"

NEW_LINE        [\n]+
WHITESPACE      [ \t\r\f]+
STRING_LITERAL  \"(\"\"|[^"])*\"
NAT_NUM         [0-9]+
DECIMAL         [0-9]+\.[0-9]+
BINARY_NUM      #b[01]+
HEX_NUM         #x[0-9a-fA-F]+
SIMPLE_SYMBOL   [a-zA-Z~!@\$%\^&\*+=<>\.\?/_-][a-zA-Z0-9~!@\$%\^&\*+=<>\.\?/_-]*
QUOTED_SYMBOL   \|[^\|\\]*\|

%%

    /* Rules Section */
%{
using namespace yaga::parser;
%}


"assert"            return Token::ASSERT_TOK;
"as"                return Token::AS_TOK;
"!"                 return Token::ATTRIBUTE_TOK;
"check-sat"         return Token::CHECK_SAT_TOK;
"declare-const"     return Token::DECLARE_CONST_TOK;
"declare-fun"       return Token::DECLARE_FUN_TOK;
"declare-sort"      return Token::DECLARE_SORT_TOK;
"define-const"      return Token::DEFINE_CONST_TOK;
"define-fun"        return Token::DEFINE_FUN_TOK;
"define-sort"       return Token::DEFINE_SORT_TOK;
"echo"              return Token::ECHO_TOK;
"exit"              return Token::EXIT_TOK;
"get-assertions"    return Token::GET_ASSERTIONS_TOK;
"get-assignment"    return Token::GET_ASSIGNMENT_TOK;
"get-info"          return Token::GET_INFO_TOK;
"get-interpolant"   return Token::GET_INTERPOLANT_TOK;
"get-model"         return Token::GET_MODEL_TOK;
"get-option"        return Token::GET_OPTION_TOK;
"get-unsat-core"    return Token::GET_UNSAT_CORE_TOK;
"get-value"         return Token::GET_VALUE_TOK;
"_"                 return Token::INDEX_TOK;
"let"               return Token::LET_TOK;
"("                 return Token::LPAREN_TOK;
"match"             return Token::MATCH_TOK;
"par"               return Token::PAR_TOK;
"pop"               return Token::POP_TOK;
"push"              return Token::PUSH_TOK;
"reset"             return Token::RESET_TOK;
")"                 return Token::RPAREN_TOK;
"set-info"          return Token::SET_INFO_TOK;
"set-logic"         return Token::SET_LOGIC_TOK;
"set-option"        return Token::SET_OPTION_TOK;

{WHITESPACE}        /* skip whitespaces */
{NEW_LINE}          /* skip newlines */
\;.*                /* skip comment until newline */
{STRING_LITERAL}    return Token::STRING_LITERAL;
{NAT_NUM}           return Token::INTEGER_LITERAL;
{DECIMAL}           return Token::DECIMAL_LITERAL;
{HEX_NUM}           return Token::HEX_LITERAL;
{BINARY_NUM}        return Token::BINARY_LITERAL;
\:{SIMPLE_SYMBOL}   return Token::KEYWORD;
{QUOTED_SYMBOL}     return Token::QUOTED_SYMBOL;
{SIMPLE_SYMBOL}     return Token::SYMBOL;


. parseError("Error finding token"); break;

%%

/* User Code Section */