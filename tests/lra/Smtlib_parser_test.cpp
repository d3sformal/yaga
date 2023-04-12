#include <catch2/catch_test_macros.hpp>

#include <iostream>
#include <sstream>

#include "test.h"
#include "Smtlib_parser.h"
#include "Perun.h"

TEST_CASE("Parse boolean functions", "[test_parser]")
{
    using namespace perun;
    using namespace perun::test;

    Perun smt{logic::qf_lra};
    Smtlib_parser<Direct_interpreter> parser{smt};

    std::stringstream input;
    input << "(declare-fun b1 () Bool)\n";
    input << "(declare-fun b2 () Bool)\n";
    input << "(declare-fun b3 () Bool)\n";
    input << "(declare-fun b4 () Bool)\n";

    SECTION("non-negated binary and")
    {
        input << "(assert (and b1 b2))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 5);
        REQUIRE(smt.solver().db().asserted().size() == 3);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(4), lit(0)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(~lit(4), lit(1)));
        REQUIRE(smt.solver().db().asserted()[2] == clause(lit(4)));
    }

    SECTION("non-negated n-ary and")
    {
        input << "(assert (and b1 b2 b3 b4))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 5);
        REQUIRE(smt.solver().db().asserted().size() == 5);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(4), lit(0)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(~lit(4), lit(1)));
        REQUIRE(smt.solver().db().asserted()[2] == clause(~lit(4), lit(2)));
        REQUIRE(smt.solver().db().asserted()[3] == clause(~lit(4), lit(3)));
        REQUIRE(smt.solver().db().asserted()[4] == clause(lit(4)));
    }

    SECTION("non-negated and with a TRUE constant")
    {
        input << "(assert (and b1 true b3 b4))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 5);
        REQUIRE(smt.solver().db().asserted().size() == 4);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(4), lit(0)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(~lit(4), lit(2)));
        REQUIRE(smt.solver().db().asserted()[2] == clause(~lit(4), lit(3)));
        REQUIRE(smt.solver().db().asserted()[3] == clause(lit(4)));
    }

    SECTION("negated and")
    {
        input << "(assert (not (and b1 b2)))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 5);
        REQUIRE(smt.solver().db().asserted().size() == 2);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(4), ~lit(0), ~lit(1)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(lit(4)));
    }

    SECTION("non-negated binary or")
    {
        input << "(assert (or b1 b2))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 5);
        REQUIRE(smt.solver().db().asserted().size() == 2);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(4), lit(0), lit(1)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(lit(4)));
    }

    SECTION("non-negated n-ary or")
    {
        input << "(assert (or b1 b2 b3 b4))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 5);
        REQUIRE(smt.solver().db().asserted().size() == 2);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(4), lit(0), lit(1), lit(2), lit(3)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(lit(4)));
    }

    SECTION("non-negated or with a FALSE constant")
    {
        input << "(assert (or b1 false b3 b4))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 5);
        REQUIRE(smt.solver().db().asserted().size() == 2);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(4), lit(0), lit(2), lit(3)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(lit(4)));
    }

    SECTION("negated or")
    {
        input << "(assert (not (or b1 b2)))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 5);
        REQUIRE(smt.solver().db().asserted().size() == 3);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(4), ~lit(0)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(~lit(4), ~lit(1)));
        REQUIRE(smt.solver().db().asserted()[2] == clause(lit(4)));
    }

    SECTION("constant and/or")
    {
        input << "(assert (or (and (or b1 true) false) b1 b2))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 5);
        REQUIRE(smt.solver().db().asserted().size() == 2);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(4), lit(0), lit(1)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(lit(4)));
    }
}

TEST_CASE("Parse boolean equality", "[test_parser]")
{
    using namespace perun;
    using namespace perun::test;

    Perun smt{logic::qf_lra};
    Smtlib_parser<Direct_interpreter> parser{smt};

    std::stringstream input;
    input << "(declare-fun b1 () Bool)\n";
    input << "(declare-fun b2 () Bool)\n";
    input << "(declare-fun b3 () Bool)\n";
    input << "(declare-fun b4 () Bool)\n";

    SECTION("non-negated =")
    {
        input << "(assert (= b1 b2))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 5);
        REQUIRE(smt.solver().db().asserted().size() == 3);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(4), ~lit(0), lit(1)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(~lit(4), lit(0), ~lit(1)));
        REQUIRE(smt.solver().db().asserted()[2] == clause(lit(4)));
    }

    SECTION("negated =")
    {
        input << "(assert (not (= b1 b2)))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 5);
        REQUIRE(smt.solver().db().asserted().size() == 3);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(4), lit(0), lit(1)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(~lit(4), ~lit(0), ~lit(1)));
        REQUIRE(smt.solver().db().asserted()[2] == clause(lit(4)));
    }

    SECTION("non-negated with TRUE on the right-hand-side")
    {
        input << "(assert (= b1 true))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(lit(0)));
    }

    SECTION("non-negated with TRUE on the left-hand-side")
    {
        input << "(assert (= true b1))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(lit(0)));
    }

    SECTION("non-negated with FALSE on the right-hand-side")
    {
        input << "(assert (= b1 false))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(0)));
    }

    SECTION("non-negated with FALSE on the left-hand-side")
    {
        input << "(assert (= false b1))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(0)));
    }

    SECTION("negated with TRUE on the right-hand-side")
    {
        input << "(assert (not (= b1 true)))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(0)));
    }

    SECTION("negated with FALSE on the right-hand-side")
    {
        input << "(assert (not (= b1 false)))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(lit(0)));
    }
}

TEST_CASE("Parse linear polynomial", "[test_parser]")
{
    using namespace perun;
    using namespace perun::test;

    Perun smt{logic::qf_lra};
    Smtlib_parser<Direct_interpreter> parser{smt};

    auto linear = factory(smt);
    auto [x, y, z, w] = real_vars<4>();

    std::stringstream input;
    input << "(declare-fun x () Real)\n";
    input << "(declare-fun y () Real)\n";
    input << "(declare-fun z () Real)\n";
    input << "(declare-fun w () Real)\n";

    SECTION("distribute * over +")
    {
        input << "(assert (< (* (+ (* x 3) (* 4 y)) 2) z))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 1);
        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(linear(6 * x + 8 * y - z < 0)));
    }

    SECTION("<=")
    {
        input << "(assert (<= x y))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 1);
        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(linear(x <= y)));
    }

    SECTION(">")
    {
        input << "(assert (> x y))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 1);
        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(linear(x > y)));
    }

    SECTION(">=")
    {
        input << "(assert (>= x y))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 1);
        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(linear(x >= y)));
    }

    SECTION("=")
    {
        input << "(assert (= x y))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 1);
        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(linear(x - y == 0)));
    }

    SECTION("not <")
    {
        input << "(assert (not (< x y)))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 1);
        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(linear(x >= y)));
    }

    SECTION("not <=")
    {
        input << "(assert (not (<= x y)))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 1);
        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(linear(x > y)));
    }

    SECTION("not >")
    {
        input << "(assert (not (> x y)))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 1);
        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(linear(x <= y)));
    }

    SECTION("not >=")
    {
        input << "(assert (not (>= x y)))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 1);
        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(linear(x < y)));
    }

    SECTION("not =")
    {
        input << "(assert (not (= x y)))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<bool>(Variable::boolean).num_vars() == 1);
        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(linear(x - y != 0)));
    }
}

TEST_CASE("Parse if-then-else with real output", "[test_parser]")
{
    using namespace perun;
    using namespace perun::test;

    Perun smt{logic::qf_lra};
    Smtlib_parser<Direct_interpreter> parser{smt};

    auto linear = factory(smt);
    auto [x, y, z, w, new_var] = real_vars<5>();

    std::stringstream input;
    input << "(declare-fun x () Real)\n";
    input << "(declare-fun y () Real)\n";
    input << "(declare-fun z () Real)\n";
    input << "(declare-fun w () Real)\n";

    SECTION("with LRA constraint as condition")
    {
        input << "(assert (= (ite (< x y) z w) 0))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 5);
        REQUIRE(smt.solver().db().asserted().size() == 3);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~linear(x < y), linear(new_var - z == 0)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(linear(x < y), linear(new_var - w == 0)));
        REQUIRE(smt.solver().db().asserted()[2] == clause(linear(new_var == 0)));
    }

    SECTION("with FALSE condition")
    {
        input << "(assert (< (ite (= 20 40) x y) 0))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(linear(y < 0)));
    }

    SECTION("with TRUE condition")
    {
        input << "(assert (< (ite (= 40 40) x y) 0))";
        parser.parse(input);

        REQUIRE(smt.solver().trail().model<Rational>(Variable::rational).num_vars() == 4);
        REQUIRE(smt.solver().db().asserted().size() == 1);
        REQUIRE(smt.solver().db().asserted()[0] == clause(linear(x < 0)));
    }
}

TEST_CASE("parse if-then-else with a boolean output", "[test_parser]")
{
    using namespace perun;
    using namespace perun::test;

    Perun smt{logic::qf_lra};
    Smtlib_parser<Direct_interpreter> parser{smt};

    auto linear = factory(smt);
    auto [x, y, z] = real_vars<3>();

    std::stringstream input;
    input << "(declare-fun b1 () Bool)\n";
    input << "(declare-fun b2 () Bool)\n";
    input << "(declare-fun b3 () Bool)\n";
    input << "(declare-fun b4 () Bool)\n";
    input << "(declare-fun x () Real)\n";
    input << "(declare-fun y () Real)\n";
    input << "(declare-fun z () Real)\n";

    SECTION("basic condition")
    {
        input << "(assert (ite b1 b2 b3))";
        parser.parse(input);

        REQUIRE(smt.solver().db().asserted().size() == 3);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(4), ~lit(0), lit(1)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(~lit(4), lit(0), lit(2)));
        REQUIRE(smt.solver().db().asserted()[2] == clause(lit(4)));
    }

    SECTION("with linear constraints")
    {
        input << "(assert (ite (< x 0) (= y 0) (= z 0)))";
        parser.parse(input);

        REQUIRE(smt.solver().db().asserted().size() == 3);
        REQUIRE(smt.solver().db().asserted()[0] == clause(~lit(7), ~linear(x < 0), linear(y == 0)));
        REQUIRE(smt.solver().db().asserted()[1] == clause(~lit(7), linear(x < 0), linear(z == 0)));
        REQUIRE(smt.solver().db().asserted()[2] == clause(lit(7)));
    }
}