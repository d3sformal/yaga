#ifndef PERUN_SMT2_TERM_PARSER_H
#define PERUN_SMT2_TERM_PARSER_H

#include <vector>

#include "Parser_context.h"
#include "smt2_lexer.h"
#include "Term_types.h"

namespace perun::parser
{

using term_t = terms::term_t;
using type_t = terms::type_t;

struct OpInfo
{
    std::string name;
};

class Smt2_term_parser {
    smt2_lexer & lexer;
    Parser_context & parser_context;

    std::string token_to_symbol(Token token);

    term_t make_term(OpInfo const&, std::vector<term_t>&&);

    term_t get_term_for_symbol(std::string const&);

public:
    explicit Smt2_term_parser(smt2_lexer & lexer, Parser_context & ctx)
        : lexer(lexer), parser_context(ctx) {}

    term_t parse_term();

    std::string parse_symbol();

    type_t parse_sort();

    std::string parse_keyword();
    std::string parse_sexpr();
};

} // namespace perun::parser
#endif // PERUN_SMT2_TERM_PARSER_H
