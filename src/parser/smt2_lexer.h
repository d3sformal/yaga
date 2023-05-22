#ifndef YAGA_SMT2_LEXER_H
#define YAGA_SMT2_LEXER_H

#include "Flex_lexer.h"

/* Use custom lex method */
#undef YY_DECL
#define YY_DECL yaga::parser::Token yaga::parser::smt2_lexer::lex_scan()

namespace yaga::parser {

class smt2_lexer : public Flex_lexer {
public:
    Token lex_scan() override;
};

} // namespace yaga::parser

#endif // YAGA_SMT2_LEXER_H
