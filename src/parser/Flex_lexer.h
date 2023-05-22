#ifndef YAGA_FLEX_LEXER_H
#define YAGA_FLEX_LEXER_H

// https://stackoverflow.com/a/40665154/4917890
#if !defined(yyFlexLexerOnce)
#include <FlexLexer.h>
#endif

#include "smt2_tokens.h"

#include <string_view>

namespace yaga::parser {

class Flex_lexer : public yyFlexLexer {

protected:
    virtual Token lex_scan() = 0;

public:
    void unexpected_token_error(Token token);

    void parseError(std::string_view msg);

    /**
     * Consumes the next token; errors if it is not the token t
     * @param t the expected token
     */
    void eat_token(Token t);

    /**
     * Consumes the next token; returns true if it was token t, false if it was token f; error otherwise
     * @param t first possible token
     * @param f second possible token
     * @return true if the consumed token was t, false if it was f
     */
    bool eat_token_choice(Token t, Token f);

    /**
     * Consumes and returns the next token
     * @return the next token
     */
    Token next_token();

    /**
     * Gets the string representation of the last consumed token
     */
    char const* token_string();

};

} // namespace yaga::parser

#endif // YAGA_FLEX_LEXER_H
