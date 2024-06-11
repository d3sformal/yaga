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
#include "Rational.h"
#include "Yaga.h"

using namespace yaga;
using namespace yaga::test;
using namespace yaga::literals;

TEST_CASE("Check a satisfiable formula in LRA", "[lra][sat][integration]")
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
    REQUIRE(x_val + 2_r * y_val <= 8);
    REQUIRE(2_r * x_val + y_val >= 2);
    REQUIRE((x_val >= 0 || y_val >= 0));
    REQUIRE((x_val < 0 || y_val < 0));
}

TEST_CASE("Solve system of equations in LRA", "[lra][sat][integration]")
{

    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Rational>(Variable::rational, 3);
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
    REQUIRE(2_r * x_val - y_val - 4_r * z_val == 4);
    REQUIRE(x_val - y_val - 2_r * z_val == 2);
}
TEST_CASE("Solve system with a mix of equations and inequalities in LRA", "[lra][sat][integration]")
{
    Solver solver;
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Rational>(Variable::rational, 3);
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

    solver.db().assert_clause(clause(linear(x + y < 1)));
    solver.db().assert_clause(clause(linear(x - y > 0)));
    solver.db().assert_clause(clause(~linear(x >= 0), linear(y > 1_r / 2)));
    solver.db().assert_clause(clause(~linear(x < 0), linear(y > 1)));

    auto result = solver.check();
    REQUIRE(result == Solver::Result::unsat);
}

TEST_CASE("Check a satisfiable LRA formula parsed from SMTLIB", "[lra][unsat][integration]")
{
    // modified version of the benchmark:
    // https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LRA/-/blob/master/meti-tarski/CMOS/CMOS-opamp-chunk-0016.smt2
    std::stringstream input;
    input << "(declare-fun skoX () Real)\n";
    input << "(declare-fun skoY () Real)\n";
    input << "(declare-fun pi () Real)\n";
    input << "(assert (and (> pi (/ 15707963 5000000)) (and (not (<= (/ 31415927 10000000) pi)) (and (<= skoY (* pi (/ 1 3))) (and (<= (* pi (/ 1 4)) skoY) (and (<= skoX 120) (<= 100 skoX)))))))\n";

    Options opts;
    Yaga smt{terms::Term_manager()};
    smt.set_logic(logic::qf_lra, opts);
    Smtlib_parser<Direct_interpreter> parser{smt};
    parser.parse(input);

    auto result = smt.solver().check();

    auto& real_model = smt.solver().trail().model<Rational>(Variable::rational);
    auto sko_x = real_model.value(parser.listener().var("skoX").ord());
    auto sko_y = real_model.value(parser.listener().var("skoY").ord());
    auto pi = real_model.value(parser.listener().var("pi").ord());

    REQUIRE(result == Solver::Result::sat);
    REQUIRE(pi < 31415927_r / 10000000);
    REQUIRE(pi > 15707963_r / 5000000);
    REQUIRE(sko_y <= pi / 3);
    REQUIRE(pi / 4 <= sko_y);
    REQUIRE(sko_x <= 120);
    REQUIRE(100_r <= sko_x);
}

TEST_CASE("Check an unsatisfiable LRA formula parsed from SMTLIB", "[lra][unsat][integration]")
{
    // https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LRA/-/blob/master/meti-tarski/CMOS/CMOS-opamp-chunk-0024.smt2
    std::stringstream input;
    input << "(declare-fun skoX () Real)\n";
    input << "(declare-fun skoY () Real)\n";
    input << "(declare-fun pi () Real)\n";
    input << "(assert (and (= skoX 0) (and (not (<= pi (/ 15707963 5000000))) (and (not (<= (/ 31415927 10000000) pi)) (and (<= skoY (* pi (/ 1 3))) (and (<= (* pi (/ 1 4)) skoY) (and (<= skoX 120) (<= 100 skoX))))))))\n";

    Options opts;
    Yaga smt{terms::Term_manager()};
    smt.set_logic(logic::qf_uflra, opts);
    Smtlib_parser<Direct_interpreter> parser{smt};
    parser.parse(input);

    auto result = smt.solver().check();
    REQUIRE(result == Solver::Result::unsat);
}

TEST_CASE("Formula which forces the solver to generate duplicate constraints and clauses", "[lra][sat][integration]")
{
    Yaga_test test;
    test.input() << "(declare-fun x () Real)\n";
    test.input() << "(declare-fun y () Real)\n";
    test.input() << "(declare-fun z () Real)\n";
    test.input() << "(declare-fun b () Bool)\n";
    test.input() << "(assert (or (not b) (< (+ x y) 0)))\n";
    test.input() << "(assert (or (not b) (> x 0)))\n";
    test.input() << "(assert (or (not b) (< (+ z y) 0)))\n";
    test.input() << "(assert (or (not b) (> z 0)))\n";
    // make sure that y is decided first and then b
    test.input() << "(assert (< y 1000))\n";
    test.input() << "(assert (< y 1001))\n";
    test.input() << "(assert (< y 1002))\n";
    test.input() << "(assert (< y 1003))\n";
    test.input() << "(assert (< y 1004))\n";
    test.run();

    REQUIRE(test.answer() == Solver_answer::SAT);
    if (*test.boolean("b"))
    {
        REQUIRE(*test.real("x") + *test.real("y") < 0);
        REQUIRE(*test.real("x") > 0);
        REQUIRE(*test.real("z") + *test.real("y") < 0);
        REQUIRE(*test.real("z") > 0);
    }
}