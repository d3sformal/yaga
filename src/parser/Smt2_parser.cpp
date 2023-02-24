#include "Smt2_parser.h"

#include <stdexcept>
#include <fstream>
#include <vector>

#include "Smt2_term_parser.h"
#include "Term_types.h"
#include "Term_manager.h"
#include "smt2_lexer.h"

namespace perun::parser {

#define UNIMPLEMENTED throw std::logic_error("Not implemented yet!")

using term_t = terms::term_t;

class Smt2_command_context {
    std::istream& input;
    smt2_lexer lexer;

    Smt2_term_parser term_parser;
    Parser_context parser_context;
    std::vector<term_t> assertions;

    bool parse_command();

    void parse_error(std::string const& msg);

    void print_answer(Solver_answer answer);

public:
    Smt2_command_context(std::istream& input, terms::Term_manager& term_manager)
        : input(input), term_parser(lexer, parser_context), parser_context(term_manager)
    {}
    void execute();
};

void Smt2_command_context::execute()
{
    lexer.yyrestart(input);
    while(parse_command()) { /* empty */ }
}

bool Smt2_command_context::parse_command()
{
    if (lexer.eatTokenChoice(Token::EOF_TOK, Token::LPAREN_TOK))
    {
        // EOF
        return false;
    }

    Token tok = lexer.next_token();
    switch (tok)
    {
    // (assert <term>)
    case Token::ASSERT_TOK:
    {
        term_t term = term_parser.parse_term();
        assertions.push_back(term);
    }
    break;


    // (check-sat)
    case Token::CHECK_SAT_TOK:
    {
        auto res = parser_context.check_sat();
        print_answer(res);
    }
    break;

    // (declare-fun <symbol> (<sort>∗) <sort>)
    // (declare-const <symbol> <sort>)
    case Token::DECLARE_CONST_TOK:
    case Token::DECLARE_FUN_TOK:
    {
        std::string name = term_parser.parse_symbol();
        std::vector<terms::type_t> sorts;
        if (tok == Token::DECLARE_FUN_TOK)
        {
            // FIXME: Support function symbol
            // HACK: For now only empty sort list
            lexer.eat_token(Token::LPAREN_TOK);
            lexer.eat_token(Token::RPAREN_TOK);
        }
        terms::type_t t = term_parser.parse_sort();
        parser_context.mk_constant(t, name);
    }
    break;

    // (declare-sort <symbol> <numeral>)
    case Token::DECLARE_SORT_TOK:
    {
        UNIMPLEMENTED;
    }
    break;

    // (define-const <symbol> <sort> <term>)
    case Token::DEFINE_CONST_TOK:
    {
        UNIMPLEMENTED;
    }
    break;
    // (define-fun <symbol> (<sorted_var>*) <sort> <term>)
    case Token::DEFINE_FUN_TOK:
    {
        UNIMPLEMENTED;
    }
    break;
    // (define-sort <symbol> (<symbol>*) <sort>)
    case Token::DEFINE_SORT_TOK:
    {
        UNIMPLEMENTED;
    }
    break;
    // (echo <string>)
    case Token::ECHO_TOK:
    {
        UNIMPLEMENTED;
    }
    break;
    // (exit)
    case Token::EXIT_TOK:
    {
        return false;
    }
    break;

    // (get-assertions)
    case Token::GET_ASSERTIONS_TOK:
    {
        UNIMPLEMENTED;
    }
    break;
    // (get-assignment)
    case Token::GET_ASSIGNMENT_TOK:
    {
        UNIMPLEMENTED;
    }
    break;

    // (get-info <keyword>)
    case Token::GET_INFO_TOK:
    {
        UNIMPLEMENTED;
    }
    break;

    // (get-model)
    case Token::GET_MODEL_TOK:
    {
        UNIMPLEMENTED;
    }
    break;
    // (get-option <keyword>)
    case Token::GET_OPTION_TOK:
    {
        UNIMPLEMENTED;
    }
    break;

    // (get-unsat-core)
    case Token::GET_UNSAT_CORE_TOK:
    {
        UNIMPLEMENTED;
    }
    break;
    // (get-value (<term>*))
    case Token::GET_VALUE_TOK:
    {
        UNIMPLEMENTED;
    }
    break;

    // (pop <numeral>?)
    case Token::POP_TOK:
    {
        UNIMPLEMENTED;
    }
    break;
    // (push <numeral>?)
    case Token::PUSH_TOK:
    {
        UNIMPLEMENTED;
    }
    break;
    // (reset)
    case Token::RESET_TOK:
    {
        UNIMPLEMENTED;
    }
    break;
    // (set-info <attribute>)
    case Token::SET_INFO_TOK:
    {
        UNIMPLEMENTED;
    }
    break;
    // (set-logic <symbol>)
    case Token::SET_LOGIC_TOK:
    {
        std::string name = term_parser.parse_symbol();
        if (name != "QF_LRA")
        {
            std::cerr << "Unsupported logic " << name << std::endl;
            return false;
        }
    }
    break;
    // (set-option <option>)
    case Token::SET_OPTION_TOK:
    {
        UNIMPLEMENTED;
    }
    break;

    case Token::EOF_TOK:
        parse_error("Expected SMT-LIBv2 command");
        break;
    default:
        lexer.unexpected_token_error(tok);
        break;
    }
    lexer.eat_token(Token::RPAREN_TOK);
    return true;
}
void Smt2_command_context::parse_error(std::string const& msg)
{
    UNIMPLEMENTED;
}
void Smt2_command_context::print_answer(Solver_answer answer)
{
    UNIMPLEMENTED;
}

void Smt2_parser::parse_file(std::string const& file_name)
{
    std::ifstream file_stream;
    file_stream.exceptions(std::ifstream::failbit | std::ifstream::badbit);
    file_stream.open(file_name);

    terms::Term_manager tm;
    Smt2_command_context ctx(file_stream, tm);
    ctx.execute();
}

} // namespace perun::parser