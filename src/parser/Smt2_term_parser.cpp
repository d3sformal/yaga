#include "Smt2_term_parser.h"

#include <cassert>
#include <optional>
#include <tuple>
#include <vector>

namespace perun::parser
{

#define UNIMPLEMENTED throw std::logic_error("Not implemented yet!")


enum class ParseCtx
{
    /**
     * NEXT_ARG: in context (<op> <term>* <term>
     * `op` specifies the operator we parsed.
     * `args` contain the accumulated list of arguments.
     */
    NEXT_ARG,

    /**
     * Let bindings
     *
     * LET_NEXT_BIND: in context (let (<binding>* (<symbol> <term>
     * `op` contains:
     * - d_name: the name of last bound variable.
     *
     * LET_BODY: in context (let (<binding>*) <term>
     */
    LET_NEXT_BIND,
    LET_BODY,

    /**
     * Term annotations
     *
     * TERM_ANNOTATE_BODY: in context (! <term>
     *
     * TERM_ANNOTATE_NEXT_ATTR: in context (! <term> <attr>* <keyword> <term_spec>
     * where notice that <term_spec> may be a term or a list of terms.
     * `op` contains:
     * - d_expr: the body of the term annotation.
     * - d_kind: the kind to apply to the current <term_spec> (if any).
     * `args` contain the accumulated patterns or quantifier attributes.
     */
    TERM_ANNOTATE_BODY,
    TERM_ANNOTATE_NEXT_ATTR
};

term_t Smt2_term_parser::parse_term() {
    using arg_list_t = std::vector<term_t>;
    std::vector<std::tuple<ParseCtx, OpInfo, arg_list_t>> ctx_stack;
    std::vector<std::vector<std::pair<std::string, term_t>>> letBinders;
    bool needs_context_update = false;
    std::optional<term_t> ret{};
    do {
        Token token = lexer.next_token();
        switch (token) {
        case Token::LPAREN_TOK: {
            token = lexer.next_token();
            switch (token)
            {
            case Token::AS_TOK:
            case Token::INDEX_TOK:
                UNIMPLEMENTED;
            case Token::LPAREN_TOK:
            {
                token = lexer.next_token();
                switch (token)
                {
                case Token::AS_TOK:
                case Token::INDEX_TOK:
                    UNIMPLEMENTED;
                default:
                    lexer.unexpected_token_error(token);
                    break;
                }
            }
            break;
            case Token::LET_TOK:
            {
                ctx_stack.push_back({ParseCtx::LET_NEXT_BIND, OpInfo{}, {}});
                needs_context_update = true;
                letBinders.emplace_back();
            }
            break;
            case Token::MATCH_TOK:
            case Token::ATTRIBUTE_TOK:
                UNIMPLEMENTED;
            case Token::SYMBOL:
            case Token::QUOTED_SYMBOL:
            {
                OpInfo op_info;
                op_info.name = token_to_symbol(token);
                ctx_stack.push_back({ParseCtx::NEXT_ARG, op_info, {}});
            }
            break;
            default:
                lexer.unexpected_token_error(token);
                break;
            }
        }
        break;
        case Token::RPAREN_TOK:
        {
            if (ctx_stack.empty())
            {
                lexer.unexpected_token_error(token);
            }
            // should only be here if we are expecting arguments
            assert(get<ParseCtx>(ctx_stack.back()) == ParseCtx::NEXT_ARG);
            // Construct the application term specified by ctx_stack.back()
            auto& op = get<OpInfo>(ctx_stack.back());
            ret = make_term(op, std::move(get<arg_list_t>(ctx_stack.back())));
            ctx_stack.pop_back();
        }
        break;
        case Token::SYMBOL:
        case Token::QUOTED_SYMBOL:
        {
            std::string name = token_to_symbol(token);
            ret = get_term_for_symbol(name);
        }
        break;
        case Token::INTEGER_LITERAL:
        {
            auto numeral_string = lexer.token_string();
            ret = parser_context.mk_numeral(numeral_string);
        }
        break;
        case Token::DECIMAL_LITERAL:
        {
            UNIMPLEMENTED;
        }
        break;
        case Token::HEX_LITERAL:
        {
            UNIMPLEMENTED;
        }
        break;
        case Token::BINARY_LITERAL:
        {
            UNIMPLEMENTED;
        }
        break;
        case Token::STRING_LITERAL:
        {
            UNIMPLEMENTED;
        }
        break;
        default:
            lexer.unexpected_token_error(token);
            break;
        }

        while (!ctx_stack.empty() && (ret.has_value() || needs_context_update))
        {
            needs_context_update = false;
            auto ctx = get<ParseCtx>(ctx_stack.back());
            switch (ctx)
            {
            case ParseCtx::NEXT_ARG: {
                // we are parsing the argument list, store the current term and continue
                assert(ret.has_value());
                get<arg_list_t>(ctx_stack.back()).push_back(ret.value());
                ret.reset();
            }
            break;
            case ParseCtx::LET_NEXT_BIND: {
                // if we parsed a term, process it as a binding
                if (ret.has_value())
                {
                    assert(!letBinders.empty());
                    auto& let_binder = letBinders.back();
                    // add binding from the symbol to ret
                    let_binder.emplace_back(get<OpInfo>(ctx_stack.back()).name, ret.value());
                    ret.reset();
                    // close the current binding
                    lexer.eat_token(Token::RPAREN_TOK);
                }
                else
                {
                    // eat the opening left parenthesis of the binding list
                    lexer.eat_token(Token::LPAREN_TOK);
                }
                // see if there is another binding
                if (lexer.eatTokenChoice(Token::LPAREN_TOK, Token::RPAREN_TOK))
                {
                    // (, another binding: setup parsing the next term
                    // get the symbol and store in the ParseOp
                    get<OpInfo>(ctx_stack.back()).name = parse_symbol();
                }
                else
                {
                    // ), we are now looking for the body of the let
                    get<ParseCtx>(ctx_stack.back()) = ParseCtx::LET_BODY;
                    parser_context.add_let_bindings(std::move(letBinders.back()));
                    letBinders.pop_back();
                }
            }
            break;
            case ParseCtx::LET_BODY: {
                // the let body is the returned term
                lexer.eat_token(Token::RPAREN_TOK);
                ctx_stack.pop_back();
                parser_context.pop_let_bindings();
            }
            break;
            default:
                UNIMPLEMENTED;
            }
        }
    } while (!ctx_stack.empty());
    assert(ret.has_value());
    return ret.value();
}

std::string Smt2_term_parser::token_to_symbol(Token token)
{
    switch (token)
    {
    case Token::SYMBOL:
        return lexer.token_string();
    case Token::QUOTED_SYMBOL:
    {
        std::string symbol = lexer.token_string();
        assert(symbol[0] == '|' && symbol.back() == '|');
        // strip off the quotes
        symbol = symbol.erase(0, 1);
        symbol = symbol.erase(symbol.size() - 1, 1);
        return symbol;
    }
    default:
        lexer.unexpected_token_error(token);
        break;
    }
    throw std::logic_error("UNREACHABLE!");
}

std::string Smt2_term_parser::parse_symbol()
{
    Token tok = lexer.next_token();
    std::string id = token_to_symbol(tok);
    return id;
}

term_t Smt2_term_parser::make_term(OpInfo const& op_info, std::vector<term_t>&& args)
{
    return parser_context.resolve_term(op_info.name, std::move(args));
}

term_t Smt2_term_parser::get_term_for_symbol(std::string const& symbol)
{
    return parser_context.get_term_for_symbol(symbol);
}
type_t Smt2_term_parser::parse_sort()
{
    Token tok = lexer.next_token();
    if (tok != Token::SYMBOL) {
        lexer.unexpected_token_error(tok);
    }
    auto sort_name = token_to_symbol(tok);
    return parser_context.get_type_for_symbol(sort_name);
}

} // namespace perun::parser
