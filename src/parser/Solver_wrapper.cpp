#include "Solver_wrapper.h"
#include "utils/Utils.h"
#include <variant>

namespace yaga::parser
{

using term_t = terms::term_t;

Solver_wrapper::Solver_wrapper(terms::Term_manager& term_manager, Options const& opts)
    : term_manager(term_manager), options(opts),
      internalizer_config(term_manager, solver), internalizer(term_manager, internalizer_config),
      solver(term_manager, internalizer_config.rational_vars(), internalizer_config.bool_vars()) {}

void Solver_wrapper::set_logic(Initializer const& init) {
    solver.set_logic(init, options);
}

bool Solver_wrapper::has_uf() {
    return solver.has_uf();
}

Solver_answer Solver_wrapper::check(std::vector<term_t> const& assertions)
{
    /*printf("\n --- ASSERTIONS: --- \n");
    for (size_t i = 0; i < assertions.size(); ++i)
    {
        utils::Utils::print_term(assertions[i], term_manager);
    }*/

    if (std::ranges::any_of(assertions, [](term_t t) { return t == terms::false_term; }))
    {
        return Solver_answer::UNSAT;
    }

    // Cnfize and assert clauses to the solver
    solver.init();

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

    //std::cout << "\n\n --- Variables: --- \n";

    for (auto& [term, lit] : internalizer_config.bool_vars())
    {
        if (term_manager.get_kind(term) == terms::Kind::UNINTERPRETED_TERM || term_manager.get_kind(term) == terms::Kind::APP_TERM)
        {
            variables.insert({term, lit.var()});
        }

        //std::cout << "Var #" << lit.var().ord() << ": (boolean) ";
        //utils::Utils::print_term(term, term_manager);
    }
    for (auto& [term, var_ord] : internalizer_config.rational_vars())
    {
        if (term_manager.get_kind(term) == terms::Kind::UNINTERPRETED_TERM || term_manager.get_kind(term) == terms::Kind::APP_TERM)
        {
            variables.insert({term, Variable{var_ord, Variable::rational}});
        }

        //std::cout << "Var #" << var_ord << ": (rational) ";
        //utils::Utils::print_term(term, term_manager);
    }

    auto res = solver.solver().check();

    if (options.print_stats)
    {
        std::cout << "Conflicts = " << solver.solver().num_conflicts() << "\n";
        std::cout << "Conflict clauses = " << solver.solver().num_conflict_clauses() << "\n";
        std::cout << "Learned clauses = " << solver.solver().num_learned_clauses() << "\n";
        std::cout << "Decisions = " << solver.solver().num_decisions() << "\n";
        std::cout << "Restarts = " << solver.solver().num_restarts() << "\n";
    }

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
        if (term_manager.get_kind(term) != terms::Kind::UNINTERPRETED_TERM)
            continue;

        if (var.type() == Variable::boolean && bool_model.is_defined(var.ord()))
        {
            visitor.visit(term, static_cast<bool>(bool_model.value(var.ord())));
        }
        else if (var.type() == Variable::rational && lra_model.is_defined(var.ord()))
        {
            visitor.visit(term, lra_model.value(var.ord()));
        }
    }

    auto fnc_model = solver.get_function_model();
    if (!fnc_model.has_value())
        return;

    for (auto const& fnc : fnc_model.value()) {
        auto fnc_term = fnc.first;
        auto fnc_values = fnc.second;
        visitor.visit_fnc(fnc_term, fnc_values);
    }
}

utils::Linear_polynomial Internalizer_config::internalize_poly(term_t t)
{
    auto kind = term_manager.get_kind(t);
    if (kind == terms::Kind::ARITH_CONSTANT)
    {
        return {{},{},term_manager.arithmetic_constant_value(t)};
    }
    if (kind == terms::Kind::UNINTERPRETED_TERM || kind == terms::Kind::ITE_TERM || kind == terms::Kind::APP_TERM)
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
        utils::Linear_polynomial poly;
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
            else if (arg_kind == terms::Kind::UNINTERPRETED_TERM or arg_kind == terms::Kind::ITE_TERM or arg_kind == terms::Kind::APP_TERM)
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
        assert(term_manager.is_uninterpreted(lhs) || term_manager.is_ite(lhs));
        assert(term_manager.is_uninterpreted(rhs) || term_manager.is_ite(rhs) || term_manager.is_arithmetic_constant(rhs));
        auto poly = [&]() -> utils::Linear_polynomial {
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
    case terms::Kind::APP_TERM: {
        terms::type_t term_type = term_manager.get_type(t);
        Variable::Type var_type;
        switch (term_type) {
        case terms::types::real_type:
            var_type = Variable::rational;
            break;
        case terms::types::bool_type:
            var_type = Variable::boolean;
            break;
        }

        Variable var = solver.make_function_application(var_type, t);

        switch (term_type) {
        case terms::types::real_type:
            insert_var(internal_rational_vars, t, var.ord());
            break;
        case terms::types::bool_type:
            insert_var(internal_bool_vars, t, Literal(var.ord()));
            break;
        }

        return;
    }
    case terms::Kind::UNINTERPRETED_TERM:
        if (term_manager.get_type(t) == terms::types::bool_type)
        {
            Variable bool_var = solver.make(Variable::boolean);
            t = term_manager.positive_term(t);
            insert_var(internal_bool_vars, t, Literal(bool_var.ord()));
        }
        else if (term_manager.get_type(t) == terms::types::real_type)
        {
            Variable rational_var = solver.make(Variable::rational);
            insert_var(internal_rational_vars, t, rational_var.ord());
        }
        return;
    case terms::Kind::OR_TERM:
    {
        auto args = term_manager.get_args(t);
        assert(args.size() >= 2);
        assert(std::all_of(args.begin(), args.end(), [&](term_t t){return term_manager.get_type(t) == terms::types::bool_type;}));
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