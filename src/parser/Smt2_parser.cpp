#include "Smt2_parser.h"

#include <stdexcept>
#include <fstream>
#include <vector>

#include "Smt2_term_parser.h"
#include "Term_manager.h"
#include "Term_types.h"
#include "smt2_lexer.h"
#include "Solver_wrapper.h"

namespace yaga::parser {

#define UNIMPLEMENTED throw std::logic_error("Not implemented yet!")

using term_t = terms::term_t;

/** Print value of named terms.
 */
class Print_model final : public Default_model_visitor {
    terms::Term_manager& term_manager;
    // output stream where the model will be printed
    std::ostream& output;

    void print_variable(Variable_type var) {
        if (std::holds_alternative<bool>(var))
            output << (std::get<bool>(var) ? "true" : "false");
        else if (std::holds_alternative<Rational>(var))
            output << std::get<Rational>(var);
    }

    void print_type(type_t type) {
        switch (type) {
        default:
        case terms::types::bool_type:
            output << "Bool";
            break;
        case terms::types::real_type:
            output << "Real";
            break;
        }
    }

public:
    virtual ~Print_model() = default;

    Print_model(terms::Term_manager& manager, std::ostream& output) 
        : term_manager(manager), output(output) {}

    /** Print an error message to the output stream
     * 
     * @param msg error message
     */
    void error(std::string_view msg) { output << "(error \"" << msg << "\")\n"; }

    /** Print beginning of a list of results.
     */
    void begin_list() { output << "("; }

    /** Print end of a list of results.
     */
    void end_list() { output << ")\n"; }

    /** Print value of a variable in the SMT-LIB format:
     * 
     * (define-fun <var-name> () <sort> <var-value>)
     * 
     * @param term term which represents a rational variable
     * @param value value of @p term
     */
    void visit(term_t term, Variable_type const& value) override
    {
        if (auto name = term_manager.get_term_name(term))
        {
            output << "(define-fun " << *name << " () ";
            print_type(value.index());
            output << " ";
            print_variable(value);
            output << ")\n";
        }
    }

    /** Print value of a function in the SMT-LIB format:
     *
     * (define-fun <fun-name> (<sorted-var>*) <sort> <fun-value>)
     *
     * @param term term which represents a function symbol
     * @param values function values of @p term
     */
    void visit_fnc(terms::term_t term, std::map<std::vector<Variable_type>, Variable_type> const& values) override
    {
        if (auto name = term_manager.get_term_name(term))
        {
            output << "(define-fun " << *name << " (";

            std::vector<std::string> arg_names;
            auto arg_vector = values.begin()->first;
            for (size_t i = 0; i < arg_vector.size(); ++i)
            {
                std::string arg_name = "x" + std::to_string(i);
                arg_names.push_back(arg_name);
                output << (i > 0 ? " (" : "(") << arg_name << " "
                       << (std::holds_alternative<bool>(arg_vector[i]) ? "Bool" : "Real") << ")";
            }

            output << ") ";

            auto it = values.begin();
            auto else_value = it->second;
            it++;

            print_type(else_value.index());

            output << "\n";

            int parentheses = (int)values.size();
            for (; it != values.end(); it++)
            {
                output << "  (ite";

                if (arg_names.size() > 1)
                    output << " (and";

                auto arg_values = it->first;
                for (size_t j = 0; j < arg_values.size(); ++j)
                {
                    output << " (= " << arg_names[j] + " ";
                    print_variable(arg_values[j]);
                    output << ")";
                }

                if (arg_names.size() > 1)
                    output << ")";

                output << " ";
                print_variable(it->second);
                output << "\n";
            }

            output << "       ";
            print_variable(else_value);
            output << " ";
            for (; parentheses > 0; parentheses--)
            {
                output << ")";
            }
            output << "\n";
        }
    }
};

class Smt2_command_context {
    std::istream& input;
    std::ostream& output;
    smt2_lexer lexer;

    Smt2_term_parser term_parser;
    Parser_context parser_context;
    terms::Term_manager& term_manager;
    std::vector<term_t> assertions;
    std::optional<Solver_answer> last_answer;

    bool parse_command();

    void parse_error(std::string const& msg);

    void print_answer(Solver_answer answer);

public:
    Smt2_command_context(std::istream& input, std::ostream& output, terms::Term_manager& term_manager, Options const& opts)
        : input(input), output(output), term_parser(lexer, parser_context), parser_context(term_manager, opts), term_manager(term_manager)
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
    if (lexer.eat_token_choice(Token::EOF_TOK, Token::LPAREN_TOK))
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
        last_answer = parser_context.check_sat(assertions);
        print_answer(*last_answer);
    }
    break;

    // (declare-const <symbol> <sort>)
    case Token::DECLARE_CONST_TOK:
    {
        std::string name = term_parser.parse_symbol();
        terms::type_t t = term_parser.parse_sort();
        parser_context.declare_uninterpreted_constant(t, name);
    }
    break;

    // (declare-fun <symbol> (<sort>∗) <sort>)
    case Token::DECLARE_FUN_TOK:
    {
        std::string name = term_parser.parse_symbol();
        std::vector<terms::type_t> sorts;

        lexer.eat_token(Token::LPAREN_TOK);
        sorts = term_parser.parse_sort_list();

        terms::type_t ret_type = term_parser.parse_sort();
        parser_context.declare_uninterpreted_function(ret_type, std::move(sorts), name);
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
        auto name = term_parser.parse_symbol();
        auto sorted_vars = term_parser.parse_sorted_var_list();
        auto return_sort = term_parser.parse_sort();
        parser_context.push_binding_scope();
        auto bound_vars = parser_context.bind_vars(sorted_vars);
        term_t function_body = term_parser.parse_term();
        parser_context.pop_binding_scope();
        parser_context.store_defined_fun(name, function_body, std::move(bound_vars), return_sort);
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
        Print_model printer(term_manager, output);
        if (!last_answer)
        {
            printer.error("use (check-sat) before (get-model)");
        }
        else if (last_answer != Solver_answer::SAT)
        {
            printer.error("(get-model) is only available if (check-sat) returns sat");
        }
        else // last_answer == SAT
        {
            printer.begin_list();
            parser_context.model(printer);
            printer.end_list();
        }
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
        std::string keyword = term_parser.parse_keyword();
        std::string value = term_parser.parse_sexpr();
        // TODO: Do something with the values
        (void)keyword;
        (void)value;
        break;
    }
    // (set-logic <symbol>)
    case Token::SET_LOGIC_TOK:
    {
        std::string name = term_parser.parse_symbol();
        if (name != "QF_LRA")
        {
            std::cerr << "Unsupported logic " << name << std::endl;
            return false;
        }
        break;
    }
    // (set-option <option>)
    case Token::SET_OPTION_TOK:
    {
        std::string keyword = term_parser.parse_keyword();
        std::string value = term_parser.parse_sexpr();
        // TODO: Do something with the values
        (void)keyword;
        (void)value;
        break;
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
void Smt2_command_context::parse_error(std::string const&)
{
    UNIMPLEMENTED;
}
void Smt2_command_context::print_answer(Solver_answer answer)
{
    switch (answer)
    {
    case Solver_answer::SAT:
        output << "sat" << std::endl;
        break;
    case Solver_answer::UNSAT:
        output << "unsat" << std::endl;
        break;
    case Solver_answer::UNKNOWN:
        output << "unknown" << std::endl;
        break;
    case Solver_answer::ERROR:
        output << "error" << std::endl;
        break;
    }

}

void Smt2_parser::parse_file(std::string const& file_name)
{
    std::ifstream file_stream;
    file_stream.exceptions(std::ifstream::failbit | std::ifstream::badbit);
    file_stream.open(file_name);

    parse(file_stream, std::cout);
}

void Smt2_parser::parse(std::istream& input, std::ostream& output)
{
    terms::Term_manager tm;
    Smt2_command_context ctx(input, output, tm, options);
    ctx.execute();
}

} // namespace yaga::parser