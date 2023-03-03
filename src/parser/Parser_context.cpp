#include "Parser_context.h"

#include "Term_manager.h"

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

term_t Parser_context::resolve_term(std::string const& name, std::vector<term_t> const& args)
{
    UNIMPLEMENTED;
}

term_t Parser_context::get_term_for_symbol(std::string const& symbol)
{
    auto maybe_term = let_records.get(symbol);
    if (maybe_term.has_value())
    {
        return maybe_term.value();
    }
    UNIMPLEMENTED;
}

type_t Parser_context::get_type_for_symbol(std::string const& symbol)
{
    // TODO: Implement type table
    UNIMPLEMENTED;
}

Solver_answer Parser_context::check_sat()
{
    UNIMPLEMENTED;
}

term_t Parser_context::declare_uninterpreted_constant(terms::type_t sort, std::string const& name)
{
    term_manager.mk_uninterpreted_constant(sort);
    UNIMPLEMENTED;
}

} // namespace perun::parser