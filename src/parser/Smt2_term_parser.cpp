#include "Smt2_term_parser.h"

#include <cassert>
#include <optional>
#include <tuple>
#include <vector>

namespace yaga::parser
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
            case Token::ATTRIBUTE_TOK:
            {
                // we are inside (!...) expression
                term_t base_term = parse_term();
                parse_attributes(base_term);
                ret = base_term;
                break;
            }
            case Token::MATCH_TOK:
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
            auto decimal_string = lexer.token_string();
            ret = parser_context.mk_decimal(decimal_string);
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
                if (lexer.eat_token_choice(Token::LPAREN_TOK, Token::RPAREN_TOK))
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

std::vector<type_t> Smt2_term_parser::parse_sort_list()
{
    auto result = std::vector<type_t>();
    Token tok = lexer.next_token();
    while (tok != Token::RPAREN_TOK) {
        if (tok != Token::SYMBOL) {
            lexer.unexpected_token_error(tok);
        }
        auto sort_name = token_to_symbol(tok);
        type_t sort = parser_context.get_type_for_symbol(sort_name);
        result.push_back(sort);

        tok = lexer.next_token();
    }
    return result;
}

std::string Smt2_term_parser::parse_keyword()
{
    lexer.eat_token(Token::KEYWORD);
    std::string value = lexer.token_string();
    assert(!value.empty() && value[0] == ':');
    return value.erase(0,1);
}

std::string Smt2_term_parser::parse_sexpr()
{
    // TODO: Check the token?
    Token tok = lexer.next_token();
    (void)tok;
    return lexer.token_string();
}

std::vector<Sorted_var> Smt2_term_parser::parse_sorted_var_list()
{
    std::vector<Sorted_var> vars;
    lexer.eat_token(Token::LPAREN_TOK);
    // while the next token is LPAREN, exit if RPAREN
    while (lexer.eat_token_choice(Token::LPAREN_TOK, Token::RPAREN_TOK))
    {
        auto name = parse_symbol();
        auto type = parse_sort();
        vars.push_back({name, type});
        lexer.eat_token(Token::RPAREN_TOK);
    }
    return vars;
}

void Smt2_term_parser::parse_attributes(term_t& term) {
    while (true) {
        Token attr_tok = lexer.next_token();
        if (attr_tok == Token::RPAREN_TOK) {
            break;  // end of attribute list
        }

        if (attr_tok != Token::KEYWORD) {
            lexer.unexpected_token_error(attr_tok);
        }

        std::string attr_name = lexer.token_string();
        assert(!attr_name.empty() && attr_name[0] == ':');
        attr_name.erase(0, 1);

        if (attr_name ==  "named") {
            Token name_tok = lexer.next_token();
            if (name_tok != Token::SYMBOL && name_tok != Token::QUOTED_SYMBOL) {
                lexer.unexpected_token_error(name_tok);
            }
            std::string name = token_to_symbol(name_tok);
            parser_context.set_term_name(term, name);
        }
        else {
            lexer.unexpected_token_error(attr_tok);
        }
    }
}

std::pair<std::unordered_set<std::string>, std::unordered_set<std::string>> Smt2_term_parser::parse_interpolation_groups(){
    // Parse first group
    std::unordered_set<std::string> group1 = parse_symbol_group();
    std::unordered_set<std::string> group2 = parse_symbol_group(true);;

    if ( !group2.empty() && lexer.next_token() != Token::RPAREN_TOK) {
        lexer.unexpected_token_error(lexer.get_last_token());
    }

    return {group1, group2};
}

std::unordered_set<std::string> Smt2_term_parser::parse_symbol_group(bool can_be_empty) {
    std::unordered_set<std::string> result;
    Token tok = lexer.next_token();

    if (tok == Token::LPAREN_TOK) {
        // Parse a list of symbols/quoted symbols
        Token next = lexer.next_token();
        while (next != Token::RPAREN_TOK) {
            if (next != Token::SYMBOL && next != Token::QUOTED_SYMBOL) {
                lexer.unexpected_token_error(next);
            }
            result.insert(token_to_symbol(next));
            next = lexer.next_token();
        }
    } else if (tok == Token::SYMBOL || tok == Token::QUOTED_SYMBOL) {
        result.insert(token_to_symbol(tok));
    } else if (can_be_empty && tok == Token::RPAREN_TOK) {
        return result;
    } else {
        lexer.unexpected_token_error(tok);
    }
    return result;
}

} // namespace yaga::parser
