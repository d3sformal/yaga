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

    // TODO: Cnfize and assert clauses to the solver

    // auto res = solver.check();

    return Solver_answer::UNKNOWN;
}

}