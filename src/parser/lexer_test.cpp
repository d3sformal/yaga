#include "smt2_lexer.h"

using namespace yaga;

int main()
{
    parser::smt2_lexer lexer;
    parser::Token token;
    do
    {
        token = lexer.lex_scan();
        std::cout << static_cast<std::underlying_type<parser::Token>::type>(token) << std::endl;
    } while (token != yaga::parser::Token::EOF_TOK);

    return 0;
}

