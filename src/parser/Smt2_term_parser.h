#ifndef PERUN_SMT2_TERM_PARSER_H
#define PERUN_SMT2_TERM_PARSER_H

#include "smt2_lexer.h"

#include <vector>

#include "Term_types.h"

namespace perun::parser
{

using term_t = terms::term_t;

struct OpInfo
{
    std::string name;
};

class Smt2_term_parser {
    smt2_lexer & lexer;

    std::string token_to_symbol(Token token);

    term_t make_term(OpInfo const&, std::vector<term_t> const&);

    term_t get_term_for_name(std::string const&);

public:
    explicit Smt2_term_parser(smt2_lexer & lexer): lexer(lexer) {}

    term_t parse_term();
};

} // namespace perun::parser
#endif // PERUN_SMT2_TERM_PARSER_H
