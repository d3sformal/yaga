#include <catch2/catch_test_macros.hpp>

#include <fstream>

#include "test.h"
#include "Solver.h"
#include "Bool_theory.h"
#include "Combined_order.h"
#include "Generalized_vsids.h"
#include "Linear_arithmetic.h"
#include "Theory_combination.h"
#include "Restart.h"
#include "First_unassigned.h"
#include "Smtlib_parser.h"

TEST_CASE("Check a satisfiable formula in LRA", "[lra][sat][integration]")
{
    using namespace perun;
    using namespace perun::test;

    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Linear_arithmetic::Rational>(Variable::rational, 2);
    solver.set_restart_policy<No_restart>();
    solver.set_variable_order<First_unassigned>();
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();
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

TEST_CASE("Solve system of equations in LRA", "[lra][sat][integration]")
{
    using namespace perun;
    using namespace perun::test;

    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Linear_arithmetic::Rational>(Variable::rational, 3);
    solver.set_restart_policy<No_restart>();
    solver.set_variable_order<First_unassigned>();
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();
    auto linear = factory(lra, solver.trail());
    auto [x, y, z] = real_vars<3>();

    solver.db().assert_clause(clause(linear(x + y + z == 8)));
    solver.db().assert_clause(clause(linear(2 * x - y - 4 * z == 4)));
    solver.db().assert_clause(clause(linear(x - y - 2 * z == 2)));

    auto result = solver.check();
    auto models = lra.relevant_models(solver.trail());
    REQUIRE(result == Solver::Result::sat);

    auto x_val = models.owned().value(x.ord());
    auto y_val = models.owned().value(y.ord());
    auto z_val = models.owned().value(z.ord());
    REQUIRE(x_val + y_val + z_val == 8);
    REQUIRE(2 * x_val - y_val - 4 * z_val == 4);
    REQUIRE(x_val - y_val - 2 * z_val == 2);
}

TEST_CASE("Solve system with a mix of equations and inequalities in LRA", "[lra][sat][integration]")
{
    using namespace perun;
    using namespace perun::test;

    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Linear_arithmetic::Rational>(Variable::rational, 3);
    solver.set_restart_policy<No_restart>();
    solver.set_variable_order<First_unassigned>();
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();
    auto linear = factory(lra, solver.trail());
    auto [x, y, z] = real_vars<3>();

    solver.db().assert_clause(clause(linear(x + y + z == 8)));
    solver.db().assert_clause(clause(linear(x + y > 0)));
    solver.db().assert_clause(clause(linear(y + z != 0)));
    solver.db().assert_clause(clause(linear(x > 0)));
    solver.db().assert_clause(clause(linear(y < 0)));

    auto result = solver.check();
    auto models = lra.relevant_models(solver.trail());
    REQUIRE(result == Solver::Result::sat);

    auto x_val = models.owned().value(x.ord());
    auto y_val = models.owned().value(y.ord());
    auto z_val = models.owned().value(z.ord());
    REQUIRE(x_val + y_val + z_val == 8);
    REQUIRE(x_val + y_val > 0);
    REQUIRE(y_val + z_val != 0);
    REQUIRE(x_val > 0);
    REQUIRE(y_val < 0);
}

TEST_CASE("Check an unsatisfiable formula in LRA", "[lra][unsat][integration]")
{
    using namespace perun;
    using namespace perun::test;
    using namespace perun::literals;

    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Linear_arithmetic::Rational>(Variable::rational, 2);
    solver.set_restart_policy<No_restart>();
    solver.set_variable_order<First_unassigned>();
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();
    auto linear = factory(lra, solver.trail());
    auto [x, y] = real_vars<2>();

    solver.db().assert_clause(clause(linear(x + y < 1)));
    solver.db().assert_clause(clause(linear(x - y > 0)));
    solver.db().assert_clause(clause(~linear(x >= 0), linear(y > 1_r / 2)));
    solver.db().assert_clause(clause(~linear(x < 0), linear(y > 1)));

    auto result = solver.check();
    REQUIRE(result == Solver::Result::unsat);
}

TEST_CASE("Check a satisfiable LRA formula parsed from SMTLIB", "[lra][unsat][integration]")
{
    using namespace perun;
    using namespace perun::test;
    using namespace perun::literals;

    // modified version of the benchmark:
    // https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LRA/-/blob/master/meti-tarski/CMOS/CMOS-opamp-chunk-0016.smt2
    std::stringstream input;
    input << "(declare-fun skoX () Real)\n";
    input << "(declare-fun skoY () Real)\n";
    input << "(declare-fun pi () Real)\n";
    input << "(assert (and (> pi (/ 15707963 5000000)) (and (not (<= (/ 31415927 10000000) pi)) (and (<= skoY (* pi (/ 1 3))) (and (<= (* pi (/ 1 4)) skoY) (and (<= skoX 120) (<= 100 skoX)))))))\n";

    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Linear_arithmetic::Rational>(Variable::rational, 0);
    solver.set_restart_policy<No_restart>();
    solver.set_variable_order<First_unassigned>();
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();

    Smtlib_parser<Direct_interpreter> parser{lra, solver.db(), solver.trail()};
    parser.parse(input);

    auto result = solver.check();

    auto& real_model = solver.trail().model<Fraction<int>>(Variable::rational);
    auto sko_x = real_model.value(parser.listener().var("skoX").ord());
    auto sko_y = real_model.value(parser.listener().var("skoY").ord());
    auto pi = real_model.value(parser.listener().var("pi").ord());

    REQUIRE(result == Solver::Result::sat);
    REQUIRE(pi < 31415927_r / 10000000);
    REQUIRE(pi > 15707963_r / 5000000);
    REQUIRE(sko_y <= pi / 3);
    REQUIRE(pi / 4 <= sko_y);
    REQUIRE(sko_x <= 120);
    REQUIRE(100 <= sko_x);
}

TEST_CASE("Check an unsatisfiable LRA formula parsed from SMTLIB", "[lra][unsat][integration]")
{
    using namespace perun;
    using namespace perun::test;

    // https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LRA/-/blob/master/meti-tarski/CMOS/CMOS-opamp-chunk-0024.smt2
    std::stringstream input;
    input << "(declare-fun skoX () Real)\n";
    input << "(declare-fun skoY () Real)\n";
    input << "(declare-fun pi () Real)\n";
    input << "(assert (and (= skoX 0) (and (not (<= pi (/ 15707963 5000000))) (and (not (<= (/ 31415927 10000000) pi)) (and (<= skoY (* pi (/ 1 3))) (and (<= (* pi (/ 1 4)) skoY) (and (<= skoX 120) (<= 100 skoX))))))))\n";

    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Linear_arithmetic::Rational>(Variable::rational, 0);
    solver.set_restart_policy<No_restart>();
    solver.set_variable_order<First_unassigned>();
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();

    Smtlib_parser<Direct_interpreter> parser{lra, solver.db(), solver.trail()};
    parser.parse(input);

    auto result = solver.check();
    REQUIRE(result == Solver::Result::unsat);
}