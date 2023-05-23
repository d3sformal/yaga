#include "Solver_wrapper.h"

namespace yaga::parser
{

using term_t = terms::term_t;

namespace {
struct Linear_polynomial {
    std::vector<int> vars;
    std::vector<Rational> coef;
    Rational constant = 0;

    void negate();

    void subtract_var(Variable v);
};
}

class Internalizer_config : public terms::Default_visitor_config
{
    terms::Term_manager const& term_manager;
    Yaga& solver;
    std::unordered_map<terms::term_t, int> internal_rational_vars;

    // HACK: We need to store literals
    // x >= 0 (positive in term representation) is internalized as ~(x < 0), which is negative
    std::unordered_map<terms::term_t, Literal> internal_bool_vars; // Only positive terms should be added to this map!

    Linear_polynomial internalize_poly(terms::term_t t);
    inline int internal_rational_var(terms::term_t t) const
    {
        assert(internal_rational_vars.find(t) != internal_rational_vars.end());
        return internal_rational_vars.at(t);
    }

    inline Variable new_bool_var()
    {
        return solver.make(Variable::boolean);
    }

    inline Variable new_real_var()
    {
        return solver.make(Variable::rational);
    }

public:
    Internalizer_config(
        terms::Term_manager const& term_manager,
        Yaga& solver
        )
        : term_manager(term_manager), solver(solver)
    { }

    void visit(terms::term_t) override;

    std::optional<Literal> get_literal_for(terms::term_t t) const;

    /** Get a range of boolean variables (pairs of `term_t` and `Literal`)
     * 
     * @return range of internalized boolean variables
     */
    inline std::ranges::view auto bool_vars() const 
    { 
        return std::ranges::views::all(internal_bool_vars); 
    }

    /** Get a range of rational variables (pairs of `term_t` and variable ordinal integer)
     * 
     * @return range of internalized rational variables
     */
    inline std::ranges::view auto rational_vars() const 
    { 
        return std::ranges::views::all(internal_rational_vars); 
    }
};

Solver_wrapper::Solver_wrapper(terms::Term_manager& term_manager)
    : term_manager(term_manager), solver(logic::qf_lra) {}

Solver_answer Solver_wrapper::check(std::vector<term_t> const& assertions)
{
    if (std::ranges::any_of(assertions, [](term_t t) { return t == terms::false_term; }))
    {
        return Solver_answer::UNSAT;
    }

    // Cnfize and assert clauses to the solver
    solver.init(logic::qf_lra);
    Internalizer_config internalizer_config{term_manager, solver};
    terms::Visitor<Internalizer_config> internalizer(term_manager, internalizer_config);
    internalizer.visit(assertions);

    // add top level assertions to the solver
    for (term_t assertion : assertions)
    {
        if (assertion == terms::true_term) { continue; }
        auto possibly_literal = internalizer_config.get_literal_for(term_manager.positive_term(assertion));
        assert(possibly_literal.has_value());
        Literal literal = possibly_literal.value();
        if (term_manager.is_negated(assertion))
        {
            literal.negate();
        }
        solver.assert_clause(literal);
    }

    // remember term-variable mapping
    variables.clear();
    for (auto& [term, lit] : internalizer_config.bool_vars())
    {
        if (term_manager.get_kind(term) == terms::Kind::UNINTERPRETED_TERM)
        {
            variables.insert({term, lit.var()});
        }
    }
    for (auto& [term, var_ord] : internalizer_config.rational_vars())
    {
        if (term_manager.get_kind(term) == terms::Kind::UNINTERPRETED_TERM)
        {
            variables.insert({term, Variable{var_ord, Variable::rational}});
        }
    }

    auto res = solver.solver().check();
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

void Solver_wrapper::model(Default_model_visitor& visitor)
{
    auto& bool_model = solver.solver().trail().model<bool>(Variable::boolean);
    auto& lra_model = solver.solver().trail().model<Rational>(Variable::rational);
    for (auto& [term, var] : variables)
    {
        if (var.type() == Variable::boolean)
        {
            if (bool_model.is_defined(var.ord()))
            {
                visitor.visit(term, bool_model.value(var.ord()));
            }
        }
        else if (var.type() == Variable::rational)
        {
            if (lra_model.is_defined(var.ord()))
            {
                visitor.visit(term, lra_model.value(var.ord()));
            }
        }
    }
}

Linear_polynomial Internalizer_config::internalize_poly(term_t t)
{
    auto kind = term_manager.get_kind(t);
    if (kind == terms::Kind::ARITH_CONSTANT)
    {
        return {{},{},term_manager.arithmetic_constant_value(t)};
    }
    if (kind == terms::Kind::UNINTERPRETED_TERM || kind == terms::Kind::ITE_TERM)
    {
        return {{internal_rational_var(t)}, {1}, 0};
    }
    if (kind == terms::Kind::ARITH_PRODUCT)
    {
        return {{internal_rational_var(term_manager.var_of_product(t))},{term_manager.coeff_of_product(t)}, 0};
    }
    assert(kind == terms::Kind::ARITH_POLY);
    if (kind == terms::Kind::ARITH_POLY)
    {
        auto args = term_manager.get_args(t);
        Linear_polynomial poly;
        poly.vars.reserve(args.size());
        poly.coef.reserve(args.size());
        assert(poly.constant == 0);
        for (term_t arg : args)
        {
            auto arg_kind = term_manager.get_kind(arg);
            if (arg_kind == terms::Kind::ARITH_CONSTANT)
            {
                poly.constant = term_manager.arithmetic_constant_value(arg);
            }
            else if (arg_kind == terms::Kind::UNINTERPRETED_TERM or arg_kind == terms::Kind::ITE_TERM)
            {
                poly.vars.push_back(internal_rational_var(arg));
                poly.coef.emplace_back(1);
            }
            else
            {
                assert(arg_kind == terms::Kind::ARITH_PRODUCT);
                poly.vars.push_back(internal_rational_var(term_manager.var_of_product(arg)));
                poly.coef.push_back(term_manager.coeff_of_product(arg));
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

void Linear_polynomial::subtract_var(Variable v)
{
    assert(std::ranges::find(vars, v.ord()) == vars.end());
    this->vars.push_back(v.ord());
    this->coef.emplace_back(-1);
}

void Internalizer_config::visit(term_t t)
{
    auto kind = term_manager.get_kind(t);
    switch (kind) {
    case terms::Kind::ARITH_GE_ATOM: {
        auto poly_term = term_manager.get_args(t)[0];
        assert(poly_term != terms::zero_term);
        auto internal_poly = internalize_poly(poly_term);
        bool negated = term_manager.is_negated(t);
        if (!negated) // We need to change "p >= 0" to "-p <= 0"
        {
            internal_poly.negate();
        }
        auto constraint_literal =
            negated ? solver.linear_constraint(internal_poly.vars, internal_poly.coef,
                                        Order_predicate::Type::lt, -internal_poly.constant)
                    : solver.linear_constraint(internal_poly.vars, internal_poly.coef,
                                        Order_predicate::Type::leq, -internal_poly.constant);
        Literal lit = negated ? ~constraint_literal : constraint_literal;
        term_t positive_term = term_manager.positive_term(t);
        assert(internal_bool_vars.find(positive_term) == internal_bool_vars.end());
        internal_bool_vars.insert({positive_term, lit});
        return;
    }
    case terms::Kind::ARITH_EQ_ATOM: {
        auto poly_term = term_manager.get_args(t)[0];
        auto internal_poly = internalize_poly(poly_term);
        Literal lit = solver.linear_constraint(internal_poly.vars, internal_poly.coef, Order_predicate::Type::eq, -internal_poly.constant);
        assert(!lit.is_negation());
        term_t positive_term = term_manager.positive_term(t);
        assert(internal_bool_vars.find(positive_term) == internal_bool_vars.end());
        internal_bool_vars.insert({positive_term, lit});
        return;
    }
    case terms::Kind::ARITH_BINEQ_ATOM: {
        auto args = term_manager.get_args(t);
        term_t lhs = args[0];
        term_t rhs = args[1];
        assert(term_manager.is_uninterpreted_constant(lhs) or term_manager.is_ite(lhs));
        assert(term_manager.is_uninterpreted_constant(rhs) || term_manager.is_ite(rhs) || term_manager.is_arithmetic_constant(rhs));
        auto poly = [&]() -> Linear_polynomial {
            if (term_manager.is_arithmetic_constant(rhs))
            {
                return {{internal_rational_var(lhs)}, {1}, -term_manager.arithmetic_constant_value(rhs)};
            }
            else
            {
                return {{internal_rational_var(lhs), internal_rational_var(rhs)}, {1, -1}, 0};
            }
        }();
        Literal lit = solver.linear_constraint(poly.vars, poly.coef, Order_predicate::Type::eq, -poly.constant);
        assert(!lit.is_negation());
        term_t positive_term = term_manager.positive_term(t);
        assert(internal_bool_vars.find(positive_term) == internal_bool_vars.end());
        internal_bool_vars.insert({positive_term, lit});
        return;
    }
    case terms::Kind::UNINTERPRETED_TERM:
        if (term_manager.get_type(t) == terms::types::bool_type)
        {
            Variable bool_var = solver.make(Variable::boolean);
            t = term_manager.positive_term(t);
            auto [_, inserted] = internal_bool_vars.insert({t, Literal(bool_var.ord())});
            assert(inserted); (void)(inserted);
        }
        else if (term_manager.get_type(t) == terms::types::real_type)
        {
            Variable rational_var = solver.make(Variable::rational);
            auto [_, inserted] = internal_rational_vars.insert({t, rational_var.ord()});
            assert(inserted); (void)(inserted);
        }
        return;
    case terms::Kind::OR_TERM:
    {
        auto args = term_manager.get_args(t);
        assert(args.size() >= 2);
        term_t positive_term = term_manager.positive_term(t);
        assert(internal_bool_vars.find(positive_term) == internal_bool_vars.end());
        Variable var = new_bool_var();
        Literal lit = Literal(var.ord());
        internal_bool_vars.insert({positive_term, lit});
        std::vector<Literal> arg_literals;
        arg_literals.reserve(args.size());
        for (term_t arg : args)
        {
            term_t pos_arg = term_manager.positive_term(arg);
            assert(internal_bool_vars.find(pos_arg) != internal_bool_vars.end());
            auto arg_lit = internal_bool_vars.at(pos_arg);
            if (term_manager.is_negated(arg))
            {
                arg_lit.negate();
            }
            arg_literals.push_back(arg_lit);
        }
        // binary clauses
        for (auto arg_lit : arg_literals)
        {
            solver.assert_clause(lit, ~arg_lit);
        }
        // big clause
        arg_literals.push_back(~lit);
        solver.assert_clause(std::move(arg_literals));
        return;
    }
    case terms::Kind::ITE_TERM:
    {
        // Extend if we decide to enable boolean ITEs as well
        assert(term_manager.get_type(t) == terms::types::real_type);
        if (term_manager.get_type(t) == terms::types::real_type)
        {
            auto args = term_manager.get_args(t);
            term_t cond_term = args[0];
            term_t true_branch = args[1];
            term_t false_branch = args[2];
            auto var = new_real_var();
            assert(internal_rational_vars.find(t) == internal_rational_vars.end());
            internal_rational_vars.insert({t, var.ord()});
            auto true_poly = internalize_poly(true_branch);
            auto false_poly = internalize_poly(false_branch);
            // Let v = ite(c, t, f). Then we assert that c => (t = v) and ~c => (f = v)
            true_poly.subtract_var(var);
            false_poly.subtract_var(var);
            // TODO: Must the variables be sorted?
            auto true_constraint = solver.linear_constraint(true_poly.vars, true_poly.coef, Order_predicate::Type::eq, -true_poly.constant);;
            auto false_constraint = solver.linear_constraint(false_poly.vars, false_poly.coef, Order_predicate::Type::eq, -false_poly.constant);
            assert(!term_manager.is_negated(cond_term)); // MB: ITE are normalized to have positive condition
            assert(internal_bool_vars.find(cond_term) != internal_bool_vars.end());
            Literal l = internal_bool_vars.at(cond_term);
            solver.assert_clause(l, false_constraint);
            solver.assert_clause(~l, true_constraint);
        }
        return;
    }

    case terms::Kind::CONSTANT_TERM:
    {
        if (t != terms::true_term)
        {
            throw std::logic_error("Unhandled internalize case!");
        }
        return;
    }

    case terms::Kind::ARITH_CONSTANT:
    case terms::Kind::ARITH_PRODUCT:
    case terms::Kind::ARITH_POLY:
        return;
    default:
        throw std::logic_error("Unhandled internalize case!");
    }
}

std::optional<Literal> Internalizer_config::get_literal_for(term_t t) const
{
    auto it = internal_bool_vars.find(t);
    return it == internal_bool_vars.end() ? std::optional<Literal>{} : it->second;
}

} // namespace yaga::parser