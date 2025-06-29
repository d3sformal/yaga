#ifndef YAGA_PARSER_CONTEXT_H
#define YAGA_PARSER_CONTEXT_H

#include <cassert>
#include <optional>
#include <span>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "Options.h"
#include "Solver_answer.h"
#include "Solver_wrapper.h"

namespace yaga::terms {
class Term_manager;
}

namespace yaga::parser {

using term_t = terms::term_t;
using type_t = terms::type_t;
using let_bindings_t = std::vector<std::pair<std::string, term_t>>;

struct Sorted_var
{
    std::string var_name;
    type_t type;
};

class Let_binder {
    term_t current_value;
    std::vector<term_t> shadowed_values;
public:
    Let_binder(term_t t) : current_value(t) {}
    Let_binder(Let_binder const&) = delete;
    Let_binder& operator=(Let_binder const&) = delete;
    Let_binder(Let_binder&&) = default;
    Let_binder& operator=(Let_binder&&) = default;
    term_t get_value() const { return current_value; }
    bool has_shadow_value() const { return !shadowed_values.empty(); }
    void restore_shadowed_value() { current_value = shadowed_values.back(); shadowed_values.pop_back(); }
    void add_value(term_t val) {
        shadowed_values.push_back(current_value);
        current_value = val;
    }
};

class Let_records {
    std::unordered_map<std::string, Let_binder> let_binders;
    std::vector<std::string> known_binders;
    std::vector<std::size_t> frame_limits;

    bool has(std::string const & name) const { return let_binders.find(name) != let_binders.end(); }
public:
    std::optional<term_t> get(std::string const& let_symbol) const {
        auto it = let_binders.find(let_symbol);
        if (it != let_binders.end()) {
            return it->second.get_value();
        }
        return {};
    }
    void push_frame() { frame_limits.push_back(known_binders.size()); }

    void pop_frame()
    {
        auto limit = frame_limits.back();
        frame_limits.pop_back();
        while (known_binders.size() > limit) {
            std::string binder = std::move(known_binders.back());
            known_binders.pop_back();
            assert(this->has(binder));
            auto& values = let_binders.at(binder);
            if (values.has_shadow_value()) {
                values.restore_shadowed_value();
            } else {
                let_binders.erase(binder);
            }
        }
    }

    void add_binding(std::string const& name, term_t term) {
        if (not this->has(name)) {
            let_binders.insert({name, Let_binder(term)});
        } else {
            let_binders.at(name).add_value(term);
        }
        known_binders.push_back(name);
    }
};

struct Function_signature {
    std::string name;
    std::vector<term_t> args;
    type_t return_type;
};

struct Function_template {
    Function_signature signature;
    term_t body;

    Function_template(std::string name, std::vector<term_t> args, type_t ret_type, term_t body)
    : signature{std::move(name), std::move(args), ret_type}, body(body) {}
};

struct Function_declaration {
    std::string name;
    std::vector<type_t> arg_types;
    type_t return_type;

    Function_declaration(std::string name, std::vector<type_t> arg_types, type_t ret_type)
    : name(std::move(name)), arg_types(std::move(arg_types)), return_type(ret_type) {}
};

class Defined_functions {
    std::unordered_map<std::string, Function_template> defined_functions;

public:
    bool has(std::string const & name) const
    {
        return defined_functions.find(name) != defined_functions.end();
    }

    void insert(std::string const & name, Function_template && templ)
    {
        assert(not has(name));
        defined_functions.insert({name, std::move(templ)});
    }

    Function_template const& get(std::string const& name) const
    {
        return defined_functions.at(name);
    }
};

class Declared_functions {
    std::unordered_map<std::string, Function_declaration> declared_functions;

public:
    bool has(std::string const & name) const
    {
        return declared_functions.find(name) != declared_functions.end();
    }

    void insert(std::string const & name, Function_declaration && decl)
    {
        assert(not has(name));
        declared_functions.insert({name, std::move(decl)});
    }

    Function_declaration const& get(std::string const& name) const
    {
        return declared_functions.at(name);
    }
};

class Parser_context {
public:
    Parser_context(terms::Term_manager& term_manager, Options const& options) 
        : term_manager(term_manager), solver(term_manager, options) {}

    void add_let_bindings(let_bindings_t&& bindings);

    void pop_let_bindings();

    term_t resolve_term(std::string const& name, std::vector<term_t>&& args);

    term_t get_term_for_symbol(std::string const& symbol);

    type_t get_type_for_symbol(std::string const& symbol);

    void set_term_name(term_t t, std::string const& name) {
        term_manager.set_term_name(t, name);
    }

    Solver_answer check_sat(std::vector<term_t> const& assertions);

    void set_logic(Initializer const& init);

    bool has_uf();

    void model(Default_model_visitor& visitor);

    term_t declare_uninterpreted_constant(terms::type_t sort, std::string const& name);
    void declare_uninterpreted_function(terms::type_t ret_type, std::vector<terms::type_t> && arg_sorts, std::string const& name);

    term_t mk_numeral(std::string const& numeric_string);
    term_t mk_decimal(std::string const& decimal_string);

    /*
     * Bindings
     */
    void push_binding_scope();
    void pop_binding_scope();

    std::vector<term_t> bind_vars(std::span<Sorted_var> sorted_vars);

    void store_defined_fun(std::string const& name, term_t definition, std::vector<term_t> && formal_args, type_t ret_sort);

    Solver_answer get_interpolant(std::vector<term_t> const& group1, std::vector<term_t> const& group2, const std::vector<term_t>& assertions);

private:
    Let_records let_records;

    Defined_functions defined_functions;
    Declared_functions declared_functions;

    terms::Term_manager& term_manager;

    Solver_wrapper solver;

    term_t resolve_defined_function(std::string const& name, std::span<term_t> args);
};

}

#endif // YAGA_PARSER_CONTEXT_H
