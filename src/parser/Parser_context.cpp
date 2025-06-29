#include "Parser_context.h"

#include "Solver_wrapper.h"
#include "Term_manager.h"
#include "Terms.h"
#include "Term_rewriter.h"

#define UNIMPLEMENTED throw std::logic_error("Not implemented yet!")

namespace yaga::parser {

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
    if (symbol == "true")
    {
        return terms::true_term;
    }
    if (symbol == "false")
    {
        return terms::false_term;
    }
    auto maybe_term = let_records.get(symbol);
    if (maybe_term.has_value())
    {
        return maybe_term.value();
    }
    if (defined_functions.has(symbol))
    {
        auto defined = defined_functions.get(symbol);
        assert(defined.signature.args.empty());
        return defined.body;
    }
    auto t = term_manager.get_term_by_name(symbol);
    assert(t.has_value());
    return t.value();
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
    return solver.check(assertions);
}

void Parser_context::set_logic(Initializer const& init) {
    solver.set_logic(init);
}

bool Parser_context::has_uf() {
    return solver.has_uf();
}

void Parser_context::model(Default_model_visitor& visitor)
{
    solver.model(visitor);
}

term_t Parser_context::declare_uninterpreted_constant(terms::type_t sort, std::string const& name)
{
    term_t term = term_manager.mk_uninterpreted_constant(sort);
    term_manager.set_term_name(term, name);
    return term;
}

void Parser_context::declare_uninterpreted_function(terms::type_t ret_type, std::vector<terms::type_t> && arg_sorts, std::string const& name)
{
    term_t fnc_term = term_manager.mk_uninterpreted_constant(ret_type);
    term_manager.set_term_name(fnc_term, name);

    declared_functions.insert(name, Function_declaration(name, std::move(arg_sorts), ret_type));
}

term_t Parser_context::mk_numeral(std::string const& numeric_string)
{
    return term_manager.mk_integer_constant(numeric_string);
}

term_t Parser_context::mk_decimal(std::string const& decimal_string)
{
    return term_manager.mk_rational_constant(decimal_string);
}

term_t Parser_context::resolve_term(std::string const& name, std::vector<term_t>&& args)
{
    if (defined_functions.has(name))
    {
        return resolve_defined_function(name, args);
    } else if (declared_functions.has(name))
    {
        auto declared_function = declared_functions.get(name);
        auto expected_count = declared_function.arg_types.size();
        assert(expected_count == args.size()); (void) expected_count;

        for (size_t i = 0; i < args.size(); ++i)
        {
            type_t expected_type = declared_function.arg_types[i];
            assert(expected_type == term_manager.get_type(args[i])); (void) expected_type;
        }

        return term_manager.mk_app(name, declared_function.return_type, args);
    }
    return term_manager.mk_term(name, args, true);
}

std::vector<term_t> Parser_context::bind_vars(std::span<Sorted_var> sorted_vars)
{
    std::vector<term_t> ret;
    ret.reserve(sorted_vars.size());
    for (auto && sorter_var : sorted_vars)
    {
        term_t var = term_manager.mk_uninterpreted_constant(sorter_var.type);
        let_records.add_binding(sorter_var.var_name, var);
        ret.push_back(var);
    }
    return ret;
}
void Parser_context::store_defined_fun(std::string const& name, term_t definition,
                                       std::vector<term_t> && formal_args, type_t return_sort)
{
    defined_functions.insert(name, Function_template(name, std::move(formal_args), return_sort, definition));
}

void Parser_context::push_binding_scope()
{
    let_records.push_frame();
}

void Parser_context::pop_binding_scope()
{
    let_records.pop_frame();
}

term_t resolve(Function_template const& function_template, std::span<term_t> args, terms::Term_manager& term_manager);

term_t Parser_context::resolve_defined_function(std::string const& name, std::span<term_t> args)
{
    auto const& function_template = defined_functions.get(name);
    return resolve(function_template, args, term_manager);
}

term_t resolve(Function_template const& function_template, std::span<term_t> args, terms::Term_manager& term_manager)
{
    using subst_map_t = std::unordered_map<term_t, term_t>;
    auto size = function_template.signature.args.size();
    assert(size == args.size());
    subst_map_t subst_map;
    for (std::size_t i = 0u; i != size; ++i)
    {
        subst_map.insert({function_template.signature.args[i], args[i]});
    }
    return terms::simultaneous_variable_substitution(term_manager, subst_map, function_template.body);
}

Solver_answer Parser_context::get_interpolant(const std::vector<term_t>& group1, std::vector<term_t> const& group2, std::vector<term_t> const& assertions){
    //TODO
    throw std::logic_error("Not implemented yet!");
}


} // namespace yaga::parser