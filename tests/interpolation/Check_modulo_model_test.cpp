#include <catch2/catch_test_macros.hpp>
#include <fstream>

#include "test.h"
#include "Solver.h"
#include "Bool_theory.h"
#include "Linear_arithmetic.h"
#include "Theory_combination.h"
#include "Restart.h"
#include "First_unassigned.h"
#include "Smtlib_parser.h"
#include "Rational.h"

using namespace yaga;
using namespace yaga::test;
using namespace yaga::literals;

TEST_CASE("Check a formula with an input model", "[integration][lra][sat]")
{
    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Rational>(Variable::rational, 2);
    solver.set_restart_policy<No_restart>();
    solver.set_variable_order<First_unassigned>();
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();
    auto linear = factory(lra, solver.trail());
    auto [x, y] = real_vars<2>();

    solver.db().assert_clause(clause(linear(x >= 0)));
    solver.db().assert_clause(clause(linear(x + 1 == y)));

    TrailModelsSnapshot modelsSnapshot(solver.trail());
    modelsSnapshot.model<Rational>(Variable::rational)->set_value(x.ord(), 1);

    auto result = solver.check(modelsSnapshot);
    REQUIRE(result == Solver::Result::sat);

    auto models = lra.relevant_models(solver.trail());
    auto x_val = models.owned().value(x.ord());
    auto y_val = models.owned().value(y.ord());
    REQUIRE(models.owned().is_defined(x.ord()));
    REQUIRE(models.owned().is_defined(y.ord()));
    REQUIRE(x_val == 1);
    REQUIRE(x_val + 1 == y_val);

    REQUIRE(solver.get_model_interpolant().size() == 0);
}

TEST_CASE("Check a formula with an input model that cannot be extended to full model", "[integration][lra][unsat]")
{
    // sat formula
    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Rational>(Variable::rational, 2);
    solver.set_restart_policy<No_restart>();
    solver.set_variable_order<First_unassigned>();
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();
    auto linear = factory(lra, solver.trail());
    auto [x, y] = real_vars<2>();

    solver.db().assert_clause(clause(linear(x >= 0)));
    solver.db().assert_clause(clause(linear(x + 1 == y)));

    TrailModelsSnapshot modelsSnapshot(solver.trail());
    modelsSnapshot.model<Rational>(Variable::rational)->set_value(y.ord(), -2);

    auto result = solver.check(modelsSnapshot);
    REQUIRE(result == Solver::Result::unsat);

    std::vector<Clause> expected = {{linear(y >= 1).lit()}};
    REQUIRE(solver.get_model_interpolant() == expected);
}

TEST_CASE("Check a propositional formula with an input model that can be extended to full model", "[integration][bool_theory][sat]")
{
    // sat formula
    Solver solver;
    solver.set_theory<Bool_theory>();
    solver.set_variable_order<Evsids>();
    solver.set_restart_policy<No_restart>();
    solver.trail().set_model<bool>(Variable::boolean, 3);
    auto a = bool_var(0);
    auto b = bool_var(1);
    auto c = bool_var(2);

    solver.db().assert_clause(lit(a.ord()), lit(b.ord()));
    solver.db().assert_clause(~lit(a.ord()), lit(c.ord()));
    solver.db().assert_clause(~lit(b.ord()), ~lit(c.ord()));

    TrailModelsSnapshot modelsSnapshot(solver.trail());
    modelsSnapshot.model<bool>(Variable::boolean)->set_value(a.ord(), true);

    auto result = solver.check(modelsSnapshot);
    REQUIRE(result == Solver::Result::sat);

    auto model = solver.trail().model<bool>(Variable::boolean);
    REQUIRE(model->is_defined(a.ord()));
    REQUIRE(model->value(a.ord()) == true);
    REQUIRE(model->is_defined(b.ord()));
    REQUIRE(model->value(b.ord()) == false);
    REQUIRE(model->is_defined(c.ord()));
    REQUIRE(model->value(c.ord()) == true);

    REQUIRE(solver.get_model_interpolant().size() == 0);
}

TEST_CASE("Check a formula with an input model that causes a conflict in decide method in Boolean theory plugin", "[integration][lra][unsat]")
{
    // sat formula
    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 1);
    solver.trail().set_model<Rational>(Variable::rational, 1);
    solver.set_restart_policy<No_restart>();
    solver.set_variable_order<First_unassigned>();
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();
    auto linear = factory(lra, solver.trail());
    auto [x] = real_vars<1>();
    auto a = bool_var(0);

    solver.db().assert_clause(lit(a.ord()));
    solver.db().assert_clause(~lit(a.ord()), linear(x == 0).lit());

    TrailModelsSnapshot modelsSnapshot(solver.trail());
    modelsSnapshot.model<Rational>(Variable::rational)->set_value(x.ord(), 1);

    auto result = solver.check(modelsSnapshot);
    REQUIRE(result == Solver::Result::unsat);

    std::vector<Clause> expected = {{linear(x == 0).lit()}};
    REQUIRE(solver.get_model_interpolant() == expected);
}

TEST_CASE("Check a formula with an input model that causes a conflict in decide method in LRA plugin", "[integration][lra][unsat]")
{
    // sat formula
    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 1);
    solver.trail().set_model<Rational>(Variable::rational, 1);
    solver.set_restart_policy<No_restart>();
    solver.set_variable_order<First_unassigned>();
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();
    auto linear = factory(lra, solver.trail());
    auto [x] = real_vars<1>();
    auto a = bool_var(0);

    solver.db().assert_clause(lit(a.ord()));
    solver.db().assert_clause(~lit(a.ord()), linear(x == 0).lit());

    TrailModelsSnapshot modelsSnapshot(solver.trail());
    modelsSnapshot.model<bool>(Variable::boolean)->set_value(a.ord(), false);

    auto result = solver.check(modelsSnapshot);
    REQUIRE(result == Solver::Result::unsat);

    std::vector<Clause> expected = {{lit(a.ord())}};
    REQUIRE(solver.get_model_interpolant() == expected);
}
