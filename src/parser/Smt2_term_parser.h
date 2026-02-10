#ifndef YAGA_SMT2_TERM_PARSER_H
#define YAGA_SMT2_TERM_PARSER_H

#include <vector>

#include "Parser_context.h"
#include "smt2_lexer.h"
#include "Term_types.h"

namespace yaga::parser
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

    /**
     * Parses SMT-LIB2 term attributes from an annotated term expression.
     *
     * This method handles attribute parsing within a (! <term> <attribute>*) expression.
     * Currently supports the `:named` attribute which assigns a name to the term.
     *
     * @param term Reference to the term being annotated. May be modified based on
     *             the parsed attributes (e.g., by setting a name via `:named`).
     *
     * @throws Unexpected token error if an unsupported attribute or malformed
     *         syntax is encountered.
     */
    void parse_attributes(term_t& term);

    /**
     * Parses a group of symbols, either as a single symbol or a parenthesized list.
     *
     * This method handles two syntactic forms:
     * - A single symbol: `foo` or `|quoted symbol|`
     * - A parenthesized list: `(foo bar baz)` or `(|a| |b|)`
     *
     * @param can_be_empty If true, allows the group to be empty (represented by
     *                     encountering a closing parenthesis immediately). If false,
     *                     an empty group will trigger an unexpected token error.
     *
     * @return An unordered set containing all parsed symbol names.
     *
     * @throws Unexpected token error if the syntax is invalid or if an empty group
     *         is encountered when can_be_empty is false.
     */
    std::unordered_set<std::string> parse_symbol_group(bool can_be_empty = false);
public:
    explicit Smt2_term_parser(smt2_lexer & lexer, Parser_context & ctx)
        : lexer(lexer), parser_context(ctx) {}

    term_t parse_term();

    std::string parse_symbol();

    type_t parse_sort();

    std::vector<type_t> parse_sort_list();

    std::string parse_keyword();
    std::string parse_sexpr();

    std::vector<Sorted_var> parse_sorted_var_list();

    /**
     * Parses two interpolation groups for Craig interpolation queries.
     *
     * Interpolation groups define the partition of formulas into two sets (A and B)
     * for computing an interpolant. Each group can be specified as either a single
     * symbol or a parenthesized list of symbols.
     *
     * @return A pair of unordered sets where:
     *         - first: the set of symbol names in the first interpolation group (A)
     *         - second: the set of symbol names in the second interpolation group (B),
     *                   which may be empty if not specified
     *
     * @throws Unexpected token error if the syntax is malformed.
     */
    std::pair<std::unordered_set<std::string>, std::unordered_set<std::string>> parse_interpolation_groups();
};

} // namespace yaga::parser
#endif // YAGA_SMT2_TERM_PARSER_H
