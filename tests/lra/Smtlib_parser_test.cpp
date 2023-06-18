#include <catch2/catch_test_macros.hpp>

#include <iostream>
#include <sstream>
#include <string>
#include <regex>
#include <optional>

#include "test.h"
#include "Terms.h"
#include "Solver_answer.h"
#include "Smtlib_parser.h"
#include "Smt2_parser.h"
#include "Yaga.h"

TEST_CASE("Parse boolean functions", "[test_parser]")
{
    using namespace yaga;
    using namespace yaga::parser;
    using namespace yaga::terms;
    using namespace yaga::test;

    Yaga_test test;
    test.input() << "(declare-fun b1 () Bool)\n";
    test.input() << "(declare-fun b2 () Bool)\n";
    test.input() << "(declare-fun b3 () Bool)\n";
    test.input() << "(declare-fun b4 () Bool)\n";

    SECTION("non-negated binary and")
    {
        test.input() << "(assert (and b1 b2))\n";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1") == true);
        REQUIRE(test.boolean("b2") == true);
    }

    SECTION("non-negated n-ary and")
    {
        test.input() << "(assert (and b1 b2 b3 b4))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1") == true);
        REQUIRE(test.boolean("b2") == true);
        REQUIRE(test.boolean("b3") == true);
        REQUIRE(test.boolean("b4") == true);
    }

    SECTION("non-negated and with a TRUE constant")
    {
        test.input() << "(assert (and b1 true b3 b4))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
    }

    SECTION("negated and")
    {
        test.input() << "(assert (not (and b1 b2)))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1").has_value());
        REQUIRE(test.boolean("b2").has_value());
        REQUIRE(!(*test.boolean("b1") && *test.boolean("b2")));
    }

    SECTION("non-negated binary or")
    {
        test.input() << "(assert (or b1 b2))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1").has_value());
        REQUIRE(test.boolean("b2").has_value());
        REQUIRE((*test.boolean("b1") || *test.boolean("b2")));
    }

    SECTION("non-negated n-ary or")
    {
        test.input() << "(assert (or b1 b2 b3 b4))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1").has_value());
        REQUIRE(test.boolean("b2").has_value());
        REQUIRE(test.boolean("b3").has_value());
        REQUIRE(test.boolean("b4").has_value());
        REQUIRE((*test.boolean("b1") || *test.boolean("b2") || *test.boolean("b3") || *test.boolean("b4")));
    }

    SECTION("non-negated or with a FALSE constant")
    {
        test.input() << "(assert (or b1 false b3 b4))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1").has_value());
        REQUIRE(test.boolean("b3").has_value());
        REQUIRE(test.boolean("b4").has_value());
        REQUIRE((*test.boolean("b1") || *test.boolean("b3") || *test.boolean("b4")));
    }

    SECTION("negated or")
    {
        test.input() << "(assert (not (or b1 b2)))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1") == false);
        REQUIRE(test.boolean("b2") == false);
    }

    SECTION("constant and/or")
    {
        test.input() << "(assert (or (and (or b1 true) false) b1 b2))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1").has_value());
        REQUIRE(test.boolean("b2").has_value());
        REQUIRE((*test.boolean("b1") || *test.boolean("b2")));
    }
}

TEST_CASE("Parse boolean equality", "[test_parser]")
{
    using namespace yaga;
    using namespace yaga::parser;
    using namespace yaga::terms;
    using namespace yaga::test;

    Yaga_test test;
    test.input() << "(declare-fun b1 () Bool)\n";
    test.input() << "(declare-fun b2 () Bool)\n";
    test.input() << "(declare-fun b3 () Bool)\n";
    test.input() << "(declare-fun b4 () Bool)\n";

    SECTION("non-negated =")
    {
        test.input() << "(assert (= b1 b2))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1").has_value());
        REQUIRE(test.boolean("b2").has_value());
        REQUIRE(test.boolean("b1") == test.boolean("b2"));
    }

    SECTION("negated =")
    {
        test.input() << "(assert (not (= b1 b2)))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1").has_value());
        REQUIRE(test.boolean("b2").has_value());
        REQUIRE(test.boolean("b1") != test.boolean("b2"));
    }

    SECTION("non-negated with TRUE on the right-hand-side")
    {
        test.input() << "(assert (= b1 true))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1") == true);
    }

    SECTION("non-negated with TRUE on the left-hand-side")
    {
        test.input() << "(assert (= true b1))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1") == true);
    }

    SECTION("non-negated with FALSE on the right-hand-side")
    {
        test.input() << "(assert (= b1 false))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1") == false);
    }

    SECTION("non-negated with FALSE on the left-hand-side")
    {
        test.input() << "(assert (= false b1))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1") == false);
    }

    SECTION("negated with TRUE on the right-hand-side")
    {
        test.input() << "(assert (not (= b1 true)))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1") == false);
    }

    SECTION("negated with FALSE on the right-hand-side")
    {
        test.input() << "(assert (not (= b1 false)))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.boolean("b1") == true);
    }
}

TEST_CASE("Parse linear polynomial", "[test_parser]")
{
    using namespace yaga;
    using namespace yaga::test;

    Yaga_test test;
    test.input() << "(declare-fun x () Real)\n";
    test.input() << "(declare-fun y () Real)\n";
    test.input() << "(declare-fun z () Real)\n";
    test.input() << "(declare-fun w () Real)\n";

    SECTION("distribute * over +")
    {
        test.input() << "(assert (< (* (+ (* x 3) (* 4 y)) 2) z))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("x").has_value());
        REQUIRE(test.real("y").has_value());
        REQUIRE(test.real("z").has_value());
        REQUIRE(*test.real("x") * 6 + *test.real("y") * 8 - *test.real("z") < Rational{0});
    }

    SECTION("<=")
    {
        test.input() << "(assert (<= x y))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("x").has_value());
        REQUIRE(test.real("y").has_value());
        REQUIRE(*test.real("x") <= *test.real("y"));
    }

    SECTION(">")
    {
        test.input() << "(assert (> x y))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("x").has_value());
        REQUIRE(test.real("y").has_value());
        REQUIRE(*test.real("x") > *test.real("y"));
    }

    SECTION(">=")
    {
        test.input() << "(assert (>= x y))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("x").has_value());
        REQUIRE(test.real("y").has_value());
        REQUIRE(*test.real("x") >= *test.real("y"));
    }

    SECTION("=")
    {
        test.input() << "(assert (= x y))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("x").has_value());
        REQUIRE(test.real("y").has_value());
        REQUIRE(*test.real("x") == *test.real("y"));
    }

    SECTION("not <")
    {
        test.input() << "(assert (not (< x y)))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("x").has_value());
        REQUIRE(test.real("y").has_value());
        REQUIRE(*test.real("x") >= *test.real("y"));
    }

    SECTION("not <=")
    {
        test.input() << "(assert (not (<= x y)))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("x").has_value());
        REQUIRE(test.real("y").has_value());
        REQUIRE(*test.real("x") > *test.real("y"));
    }

    SECTION("not >")
    {
        test.input() << "(assert (not (> x y)))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("x").has_value());
        REQUIRE(test.real("y").has_value());
        REQUIRE(*test.real("x") <= *test.real("y"));
    }

    SECTION("not >=")
    {
        test.input() << "(assert (not (>= x y)))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("x").has_value());
        REQUIRE(test.real("y").has_value());
        REQUIRE(*test.real("x") < *test.real("y"));
    }

    SECTION("not =")
    {
        test.input() << "(assert (not (= x y)))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("x").has_value());
        REQUIRE(test.real("y").has_value());
        REQUIRE(*test.real("x") != *test.real("y"));
    }
}

TEST_CASE("Parse if-then-else with real output", "[test_parser]")
{
    using namespace yaga;
    using namespace yaga::test;

    Yaga_test test;
    test.input() << "(declare-fun x () Real)\n";
    test.input() << "(declare-fun y () Real)\n";
    test.input() << "(declare-fun z () Real)\n";
    test.input() << "(declare-fun w () Real)\n";

    SECTION("with LRA constraint as condition")
    {
        test.input() << "(assert (= (ite (< x y) z w) 0))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("x").has_value());
        REQUIRE(test.real("y").has_value());
        REQUIRE(test.real("z").has_value());
        REQUIRE(test.real("w").has_value());

        if (*test.real("x") < *test.real("y"))
        {
            REQUIRE(test.real("z") == Rational{0});
        }
        else
        {
            REQUIRE(test.real("w") == Rational{0});
        }
    }

    SECTION("with FALSE condition")
    {
        test.input() << "(assert (< (ite (= 20 40) x y) 0))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("y").has_value());
        REQUIRE(*test.real("y") < Rational{0});
    }

    SECTION("with TRUE condition")
    {
        test.input() << "(assert (< (ite (= 40 40) x y) 0))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::SAT);
        REQUIRE(test.real("x").has_value());
        REQUIRE(*test.real("x") < Rational{0});
    }
}