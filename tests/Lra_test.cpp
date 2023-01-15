#include <catch2/catch_test_macros.hpp>

#include "test.h"
#include "Solver.h"
#include "Bool_theory.h"
#include "Linear_arithmetic.h"
#include "Theory_combination.h"
#include "Restart.h"
#include "First_unassigned.h"

TEST_CASE("Check a satisfiable formula in LRA", "[lra][sat][integration]")
{
    using namespace perun;
    using namespace perun::test;

    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Linear_arithmetic::Value_type>(Variable::rational, 2);
    solver.set_restart_policy<No_restart>();
    solver.set_variable_order<First_unassigned>();
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();
    lra.on_variable_resize(Variable::rational, 2); // TODO: user should not be required to call this
    auto linear = factory(lra, solver.trail());
    auto [x, y] = real_vars<2>();

    solver.db().assert_clause(clause(linear(x + 2 * y <= 8)));
    solver.db().assert_clause(clause(linear(2 * x + y >= 2)));
    // x is negative and y is positive or vice versa
    solver.db().assert_clause(clause(linear(x >= 0), linear(y >= 0)));
    solver.db().assert_clause(clause(linear(x < 0), linear(y < 0)));

    auto result = solver.check();
    auto models = lra.relevant_models(solver.trail());
    REQUIRE(result == Solver::Result::sat);

    auto x_val = models.owned().value(x.ord());
    auto y_val = models.owned().value(y.ord());
    REQUIRE(models.owned().is_defined(x.ord()));
    REQUIRE(models.owned().is_defined(y.ord()));
    REQUIRE(x_val + 2 * y_val <= 8);
    REQUIRE(2 * x_val + y_val >= 2);
    REQUIRE((x_val >= 0 || y_val >= 0));
    REQUIRE((x_val < 0 || y_val < 0));
}

TEST_CASE("Check an unsatisfiable formula in LRA", "[lra][usnat][integration]")
{
    using namespace perun;
    using namespace perun::test;

    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Linear_arithmetic::Value_type>(Variable::rational, 2);
    solver.set_restart_policy<No_restart>();
    solver.set_variable_order<First_unassigned>();
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();
    lra.on_variable_resize(Variable::rational, 2); 
    auto linear = factory(lra, solver.trail());
    auto [x, y] = real_vars<2>();

    solver.db().assert_clause(clause(linear(x + y < 1)));
    solver.db().assert_clause(clause(linear(x - y > 0)));
    solver.db().assert_clause(clause(-linear(x >= 0), linear(y > 1.0 / 2)));
    solver.db().assert_clause(clause(-linear(x < 0), linear(y > 1)));

    auto result = solver.check();
    REQUIRE(result == Solver::Result::unsat);
}