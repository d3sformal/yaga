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
    std::vector<std::tuple<ParseCtx, OpInfo, std::vector<term_t>>> ctx_stack;
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
            ret = make_term(op, get<2>(ctx_stack.back()));
            ctx_stack.pop_back();
        }
        break;
        case Token::SYMBOL:
        case Token::QUOTED_SYMBOL:
        {
            std::string name = token_to_symbol(token);
            ret = get_term_for_name(name);
        }
        break;
        case Token::INTEGER_LITERAL:
        {
            UNIMPLEMENTED;
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

        while (!ctx_stack.empty() && (ret.has_value() || needs_context_update)) {
            needs_context_update = false;
            UNIMPLEMENTED;
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

term_t Smt2_term_parser::make_term(OpInfo const& op_info, std::vector<term_t> const& args)
{
    UNIMPLEMENTED;
}

term_t Smt2_term_parser::get_term_for_name(std::string const&)
{
    UNIMPLEMENTED;
}
type_t Smt2_term_parser::parse_sort()
{
    UNIMPLEMENTED;
}

} // namespace perun::parser
