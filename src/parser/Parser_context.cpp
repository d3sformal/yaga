#include "Parser_context.h"

#include "Solver_wrapper.h"
#include "Term_manager.h"
#include "Terms.h"

#define UNIMPLEMENTED throw std::logic_error("Not implemented yet!")

namespace perun::parser {

void Parser_context::add_let_bindings(let_bindings_t&& bindings)
{
    let_records.push_frame();
    for (auto&& [name, term] : bindings)
    {
        let_records.add_binding(name, term);
    }
}

void Parser_context::pop_let_bindings() { let_records.pop_frame(); }

term_t Parser_context::get_term_for_symbol(std::string const& symbol)
{
    auto maybe_term = let_records.get(symbol);
    if (maybe_term.has_value())
    {
        return maybe_term.value();
    }
    term_t t = term_manager.get_term_by_name(symbol);
    assert(t != terms::null_term);
    return t;
}

type_t Parser_context::get_type_for_symbol(std::string const& symbol)
{
    if (symbol == "Bool") {
        return terms::types::bool_type;
    }
    if (symbol == "Real") {
        return terms::types::real_type;
    }
    throw std::logic_error("Requested unknown type");
}

Solver_answer Parser_context::check_sat(std::vector<term_t> const& assertions)
{
    return Solver_wrapper(term_manager).check(assertions);
}

term_t Parser_context::declare_uninterpreted_constant(terms::type_t sort, std::string const& name)
{
    term_t term = term_manager.mk_uninterpreted_constant(sort);
    term_manager.set_term_name(term, name);
    return term;
}

term_t Parser_context::mk_numeral(std::string const& numeric_string)
{
    return term_manager.mk_arithmetic_constant(numeric_string);
}

term_t Parser_context::resolve_term(std::string const& name, std::vector<term_t>&& args)
{
    if (name == ">=")
    {
        return mk_geq(std::move(args));
    }
    else if (name == "<=")
    {
        return mk_leq(std::move(args));
    }
    else if (name == "<")
    {
        return mk_lt(std::move(args));
    }
    else if (name == ">")
    {
        return mk_gt(std::move(args));
    }
    else if (name == "=")
    {
        return mk_eq(std::move(args));
    }
    else if (name == "or")
    {
        return mk_or(std::move(args));
    }
    else if (name == "and")
    {
        return mk_and(std::move(args));
    }
    else if (name == "not")
    {
        assert(args.size() == 1);
        return terms::opposite_term(args[0]);
    }
    else if (name == "-")
    {
        if (args.size() == 1)
        {
            return mk_unary_minus(args[0]);
        }
        else
        {
            assert(args.size() == 2);
            return mk_binary_minus(args[0], args[1]);
        }
    }
    else if (name == "+")
    {
        return term_manager.mk_arithmetic_plus(args);
    }
    else if (name == "*")
    {
        return mk_times(args);
    }
    else if (name == "/")
    {
        assert(args.size() == 2);
        return mk_binary_divides(args[0], args[1]);
    }
    else if (name == "ite")
    {
        return mk_ite(args);
    }
    UNIMPLEMENTED;
}

term_t Parser_context::mk_leq(std::vector<term_t>&& args)
{
    if (args.size() == 2)
    {
        return mk_binary_leq(args[0], args[1]);
    }
    UNIMPLEMENTED;
}

term_t Parser_context::mk_geq(std::vector<term_t>&& args)
{
    if (args.size() == 2)
    {
        return mk_binary_geq(args[0], args[1]);
    }
    UNIMPLEMENTED;
}

term_t Parser_context::mk_lt(std::vector<term_t>&& args)
{
    return terms::opposite_term(mk_geq(std::move(args)));
}

term_t Parser_context::mk_gt(std::vector<term_t>&& args)
{
    return terms::opposite_term(mk_leq(std::move(args)));
}

term_t Parser_context::mk_eq(std::vector<term_t>&& args)
{
    if (args.size() == 2)
    {
        return mk_binary_eq(args[0], args[1]);
    }
    UNIMPLEMENTED;
}

term_t Parser_context::mk_binary_eq(term_t t1, term_t t2)
{
    type_t type = term_manager.get_term_type(t1);
    if (type != term_manager.get_term_type(t2)) {
        throw std::logic_error("Types do not match");
    }

    if (type == terms::types::real_type) {
        return term_manager.mk_arithmetic_eq(t1, t2);
    }
    if (type == terms::types::bool_type)
    {
        return term_manager.mk_iff(t1, t2);
    }
    UNIMPLEMENTED;
}

term_t Parser_context::mk_binary_geq(term_t t1, term_t t2)
{
    return term_manager.mk_arithmetic_geq(t1, t2);
}

term_t Parser_context::mk_binary_leq(term_t t1, term_t t2)
{
    return term_manager.mk_arithmetic_leq(t1, t2);
}

term_t Parser_context::mk_or(std::vector<term_t>&& args)
{
    return term_manager.mk_or(args);
}

term_t Parser_context::mk_and(std::vector<term_t>&& args)
{
    return term_manager.mk_and(args);
}

term_t Parser_context::mk_unary_minus(term_t t)
{
    return term_manager.mk_unary_minus(t);
}

term_t Parser_context::mk_binary_minus(term_t t1, term_t t2)
{
    return term_manager.mk_arithmetic_minus(t1, t2);
}

term_t Parser_context::mk_times(std::span<term_t> args)
{
    return term_manager.mk_arithmetic_times(args);
}

term_t Parser_context::mk_binary_divides(term_t t1, term_t t2)
{
    return term_manager.mk_divides(t1, t2);
}

term_t Parser_context::mk_ite(std::span<term_t> args)
{
    assert(args.size() == 3);
    return term_manager.mk_ite(args[0], args[1], args[2]);
}

} // namespace perun::parser