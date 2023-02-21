#ifndef PERUN_FLEX_LEXER_H
#define PERUN_FLEX_LEXER_H

// https://stackoverflow.com/a/40665154/4917890
#if !defined(yyFlexLexerOnce)
#include <FlexLexer.h>
#endif

#include "smt2_tokens.h"

#include <string_view>

namespace perun::parser {

class Flex_lexer : public yyFlexLexer {

protected:
    virtual Token lex_scan() = 0;

public:
    void unexpected_token_error(Token token);

    void parseError(std::string_view msg);

    bool eatTokenChoice(Token t, Token f);

    Token next_token();

    char const* token_string();

};

} // namespace perun::parser

#endif // PERUN_FLEX_LEXER_H
