#include "Solver_wrapper.h"

#include "Solver.h"
#include "Theory_combination.h"
#include "Bool_theory.h"
#include "Linear_arithmetic.h"

#include "Generalized_vsids.h"

namespace perun::parser
{

using term_t = terms::term_t;

Solver_answer Solver_wrapper::check(std::vector<term_t> const& assertions)
{
    Solver solver;
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();

    solver.set_restart_policy<Glucose_restart>();
    solver.set_variable_order<Generalized_vsids>(lra);

    // TODO: Collect number of variables

    // TODO: Cnfize and assert clauses to the solver

    // auto res = solver.check();

    return Solver_answer::UNKNOWN;
}

}