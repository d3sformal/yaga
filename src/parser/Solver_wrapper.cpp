#include "Solver_wrapper.h"

#include "Solver.h"
#include "Theory_combination.h"
#include "Bool_theory.h"
#include "Linear_arithmetic.h"
#include "Generalized_vsids.h"
#include "Term_visitor.h"

namespace perun::parser
{

using term_t = terms::term_t;

class Collect_vars_config : public terms::Default_visitor_config
{
    terms::Term_table const& term_table;
public:
    std::unordered_map<terms::type_t, std::vector<term_t>> vars;

    explicit Collect_vars_config(terms::Term_table const& term_table) : term_table(term_table) {}

    void visit(term_t t) override
    {
        if (term_table.get_kind(t) == terms::Kind::UNINTERPRETED_TERM)
        {
            terms::type_t type = term_table.get_type(t);
            vars[type].push_back(t);
        }
    }
};

namespace{
struct Linear_polynomial {
    std::vector<int> vars;
    std::vector<Rational> coef;
    Rational constant;

    void negate();
};
}

class Internalizer_config : public terms::Default_visitor_config
{
    terms::Term_table const& term_table;
    Linear_arithmetic& plugin;
    Trail& trail;
    Database& database;
    std::unordered_map<term_t, int> internal_rational_vars;

    // HACK: We need to store literals
    // x >= 0 (positive in term representation) is internalized as ~(x < 0), which is negative
    std::unordered_map<term_t, Literal> internal_bool_vars; // Only positive terms should be added to this map!

    Linear_polynomial internalize_poly(term_t t);
    int internal_rational_var(term_t t) const
    {
        assert(internal_rational_vars.find(t) != internal_rational_vars.end());
        return internal_rational_vars.at(t);
    }

    inline Variable new_bool_var()
    {
        auto num_bool = static_cast<int>(trail.model<bool>(Variable::boolean).num_vars());

        trail.resize(Variable::boolean, num_bool + 1);
        plugin.on_variable_resize(Variable::boolean, num_bool + 1);
        return Variable{num_bool, Variable::boolean};
    }

public:
    Internalizer_config(
        terms::Term_table const& term_table,
        Linear_arithmetic& la_plugin,
        Trail& trail,
        Database& database,
        std::unordered_map<term_t, int> internal_rational_vars,
        std::unordered_map<term_t, int> const& internal_bool_vars
        )
        : term_table(term_table), plugin(la_plugin), trail(trail), database(database),
          internal_rational_vars(std::move(internal_rational_vars))
    {
        for (auto&& [var, index] : internal_bool_vars)
        {
            this->internal_bool_vars.insert({var, Literal(index)});
        }
    }

    void visit(term_t) override;

    std::optional<Literal> get_literal_for(term_t t) const;
};

Solver_answer Solver_wrapper::check(std::vector<term_t> const& assertions)
{
    Solver solver;
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();

    solver.set_restart_policy<Glucose_restart>();
    solver.set_variable_order<Generalized_vsids>(lra);

    auto const& term_table = term_manager.get_term_table();
    Collect_vars_config config(term_table);
    terms::Visitor<Collect_vars_config> visitor(term_table, config);

    visitor.visit(assertions);
    auto get_var_count = [&](terms::type_t type) {
        auto it = config.vars.find(type);
        return it == config.vars.end() ? 0 : it->second.size();
    };
    auto bool_vars_count = get_var_count(terms::types::bool_type);
    auto real_vars_count = get_var_count(terms::types::real_type);

    solver.trail().set_model<bool>(Variable::boolean, bool_vars_count);
    solver.trail().set_model<Rational>(Variable::rational, real_vars_count);

    // Cnfize and assert clauses to the solver
    auto vars_map = [&config](terms::type_t type){
       auto it = config.vars.find(type);
       std::unordered_map<term_t, int> map;
       if (it != config.vars.end())
       {
           auto const& vars = it->second;
           for (std::size_t i = 0u; i < vars.size(); ++i)
           {
               auto [_, inserted] = map.insert({vars[i], i});
               assert(inserted); (void)inserted;
           }
       }
       return map;
    };
    Internalizer_config internalizer_config(term_table, lra, solver.trail(), solver.db(), vars_map(terms::types::real_type), vars_map(terms::types::bool_type));
    terms::Visitor<Internalizer_config> internalizer(term_table, internalizer_config);
    internalizer.visit(assertions);

    // add top level assertions to the solver
    for (term_t assertion : assertions)
    {
        auto possibly_literal = internalizer_config.get_literal_for(terms::positive_term(assertion));
        assert(possibly_literal.has_value());
        Literal literal = possibly_literal.value();
        if (terms::polarity_of(assertion))
        {
            literal = literal.negate();
        }
        solver.db().assert_clause(literal);
    }

    auto res = solver.check();
    if (res == Solver::Result::sat)
    {
        return Solver_answer::SAT;
    }
    else if (res == Solver::Result::unsat)
    {
        return Solver_answer::UNSAT;
    }
    assert(false);
    return Solver_answer::UNKNOWN;
}

Linear_polynomial Internalizer_config::internalize_poly(term_t t)
{
    auto kind = term_table.get_kind(t);
    if (kind == terms::Kind::ARITH_CONSTANT)
    {
        return {{},{},term_table.arithmetic_constant_value(t)};
    }
    if (kind == terms::Kind::UNINTERPRETED_TERM)
    {
        return {{internal_rational_var(t)}, {1}, 0};
    }
    if (kind == terms::Kind::ARITH_PRODUCT)
    {
        return {{internal_rational_var(term_table.var_of_product(t))},{term_table.coeff_of_product(t)}, 0};
    }
    assert(kind == terms::Kind::ARITH_POLY);
    if (kind == terms::Kind::ARITH_POLY)
    {
        auto args = term_table.get_args(t);
        Linear_polynomial poly;
        poly.vars.reserve(args.size());
        poly.coef.reserve(args.size());
        for (term_t arg : args)
        {
            auto arg_kind = term_table.get_kind(arg);
            if (arg_kind == terms::Kind::ARITH_CONSTANT)
            {
                poly.constant = term_table.arithmetic_constant_value(arg);
            }
            else if (arg_kind == terms::Kind::UNINTERPRETED_TERM)
            {
                poly.vars.push_back(internal_rational_var(arg));
                poly.coef.emplace_back(1);
            }
            else
            {
                assert(arg_kind == terms::Kind::ARITH_PRODUCT);
                poly.vars.push_back(internal_rational_var(term_table.var_of_product(arg)));
                poly.coef.push_back(term_table.coeff_of_product(arg));
            }
        }
        return poly;
    }
    throw std::logic_error("UNREACHABLE!");
}

void Linear_polynomial::negate()
{
    for (auto& c : coef)
    {
        c = -c;
    }
    constant = -constant;
}

void Internalizer_config::visit(term_t t)
{
    auto kind = term_table.get_kind(t);
    switch (kind) {
    case terms::Kind::ARITH_GE_ATOM: {
        auto poly_term = term_table.get_args(t)[0];
        auto internal_poly = internalize_poly(poly_term);
        bool negated = terms::polarity_of(t);
        if (!negated) // We need to change "p >= 0" to "-p <= 0"
        {
            internal_poly.negate();
        }
        auto constraint =
            negated ? plugin.constraint(trail, internal_poly.vars, internal_poly.coef,
                                        Order_predicate::Type::lt, -internal_poly.constant)
                    : plugin.constraint(trail, internal_poly.vars, internal_poly.coef,
                                        Order_predicate::Type::leq, -internal_poly.constant);
        Literal lit = negated ? constraint.lit().negate() : constraint.lit();
        term_t positive_term = terms::positive_term(t);
        assert(internal_bool_vars.find(positive_term) == internal_bool_vars.end());
        internal_bool_vars.insert({positive_term, lit});
        return;
    }
    case terms::Kind::ARITH_EQ_ATOM: {
        auto poly_term = term_table.get_args(t)[0];
        auto internal_poly = internalize_poly(poly_term);
        auto constraint = plugin.constraint(trail, internal_poly.vars, internal_poly.coef, Order_predicate::Type::eq, -internal_poly.constant);
        Literal lit = constraint.lit();
        assert(!lit.is_negation());
        term_t positive_term = terms::positive_term(t);
        assert(internal_bool_vars.find(positive_term) == internal_bool_vars.end());
        internal_bool_vars.insert({positive_term, lit});
        return;
    }
    case terms::Kind::UNINTERPRETED_TERM:
        if (term_table.get_type(t) == terms::types::bool_type)
        {
            assert(internal_bool_vars.find(t) != internal_bool_vars.end());
        }
        else if (term_table.get_type(t) == terms::types::real_type)
        {
            assert(internal_rational_vars.find(t) != internal_rational_vars.end());
        }
        return;
    case terms::Kind::OR_TERM:
    {
        bool is_negated = terms::polarity_of(t);
        auto args = term_table.get_args(t);
        assert(args.size() >= 2);
        term_t positive_term = terms::positive_term(t);
        assert(internal_bool_vars.find(positive_term) == internal_bool_vars.end());
        Variable var = new_bool_var();
        Literal lit = Literal(var.ord());
        internal_bool_vars.insert({positive_term, lit});
        std::vector<Literal> arg_literals;
        for (term_t arg : args)
        {
            term_t pos_arg = terms::positive_term(arg);
            assert(internal_bool_vars.find(pos_arg) != internal_bool_vars.end());
            auto arg_lit = internal_bool_vars.at(pos_arg);
            if (terms::polarity_of(arg))
            {
                arg_lit.negate();
            }
            arg_literals.push_back(arg_lit);
        }
        if (is_negated)
        {
            lit = lit.negate();
            std::ranges::for_each(arg_literals, [](Literal& lit) { lit = lit.negate(); });
        }
        // binary clauses
        for (auto arg_lit : arg_literals)
        {
            database.assert_clause(lit, arg_lit.negate());
        }
        // big clause
        arg_literals.push_back(lit.negate());
        database.assert_clause(std::move(arg_literals));
        return;
    }
    default:
        throw std::logic_error("Unhandled internalize case!");
    }
}

std::optional<Literal> Internalizer_config::get_literal_for(term_t t) const
{
    auto it = internal_bool_vars.find(t);
    return it == internal_bool_vars.end() ? std::optional<Literal>{} : it->second;
}

}