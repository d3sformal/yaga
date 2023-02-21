#ifndef PERUN_SMT2_LEXER_H
#define PERUN_SMT2_LEXER_H

#include "Flex_lexer.h"

/* Use custom lex method */
#undef YY_DECL
#define YY_DECL perun::parser::Token perun::parser::smt2_lexer::lex_scan()

namespace perun::parser {

class smt2_lexer : public Flex_lexer {
public:
    Token lex_scan() override;
};

} // namespace perun::parser

#endif // PERUN_SMT2_LEXER_H
