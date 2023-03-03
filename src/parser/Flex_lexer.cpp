#include "Flex_lexer.h"

namespace perun::parser {

void Flex_lexer::parseError(std::string_view msg) { throw std::logic_error(std::string(msg)); }

bool Flex_lexer::eatTokenChoice(Token t, Token f)
{
    Token tt = next_token();
    if (tt == t)
    {
        return true;
    }
    else if (tt != f)
    {
        unexpected_token_error(tt);
    }
    return false;
}

void Flex_lexer::eat_token(Token t)
{
    Token tt = next_token();
    if (t != tt) {
        unexpected_token_error(tt);
    }
}

Token Flex_lexer::next_token()
{
    return lex_scan();
}

char const* Flex_lexer::token_string()
{
    return YYText();
}


void Flex_lexer::unexpected_token_error(Token)
{
    throw std::logic_error("Unexpected token encountered");
}

} // namespace perun::parser