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

TEST_CASE("Parse real terms with :named attributes", "[test_parser][interpolation_token]")
{
    using namespace yaga;
    using namespace yaga::test;
    using namespace yaga::parser;

    Yaga_test test;
    test.input() << "(set-logic QF_LRA)";
    test.input() << "(declare-fun x () Real)";
    test.input() << "(declare-fun y () Real)";

    SECTION("with :named attributes")
    {
        test.input() << "(assert (! (and (>= x 0) (= (+ x 1) y)) :named A))";
        test.input() << "(assert (! (< y 0) :named B))";
        test.run_check();

        REQUIRE(test.answer() == Solver_answer::UNSAT);
    }
}

TEST_CASE("Interpolation token parsing", "[test_parser][interpolation_token]")
{
    using namespace yaga;
    using namespace yaga::test;
    using namespace yaga::parser;

    Yaga_test test;
    test.input() << "(set-logic QF_LRA)";
    test.input() << "(declare-fun x () Real)";
    test.input() << "(declare-fun y () Real)";
    test.input() << "(declare-fun z () Real)";
    test.input() << "(assert (! (> x 0) :named A))";
    test.input() << "(assert (! (= x 0) :named B))";
    test.input() << "(assert (! (< y 0) :named C))";
    test.input() << "(assert (! (> y x) :named D))";

    SECTION("test interpolation groups parsing")
    {
        test.input() << "(check-sat)";
        test.input() << "(get-interpolant A B)";
        test.run();

        REQUIRE(test.answer() == Solver_answer::UNSAT);
    }

    SECTION("test interpolation groups parsing with parenthesis")
    {
        test.input() << "(check-sat)";
        test.input() << "(get-interpolant (A) (B))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::UNSAT);
    }

    SECTION("test interpolation groups with more names")
    {
        test.input() << "(check-sat)";
        test.input() << "(get-interpolant (A C) D)";
        test.run();

        REQUIRE(test.answer() == Solver_answer::UNSAT);
    }

    SECTION("test interpolation complement group")
    {
        test.input() << "(check-sat)";
        test.input() << "(get-interpolant (A C))";
        test.run();

        REQUIRE(test.answer() == Solver_answer::UNSAT);
    }
}

TEST_CASE("Interpolation parser error handling", "[test_parser][interpolation_token][error]")
{
    using namespace yaga;
    using namespace yaga::test;
    using namespace yaga::parser;

    Yaga_test test;
    test.input() << "(set-logic QF_LRA)";
    test.input() << "(declare-fun x () Real)";
    test.input() << "(declare-fun y () Real)";
    test.input() << "(assert (! (>= x 0) :named A))";
    test.input() << "(assert (! (= (+ x 1) y) :named B))";

    SECTION("test interpolation with SAT result - error")
    {
        test.input() << "(check-sat)";
        test.input() << "(get-interpolant (A) (B))";  // Should be SAT, no interpolant exists

        REQUIRE_THROWS_AS(test.run(), std::runtime_error);
    }

    test.input() << "(assert (! (< y 0) :named C))";

    SECTION("test non-disjoint interpolation groups error - B appears in both  groups")
    {
        test.input() << "(check-sat)";
        test.input() << "(get-interpolant (A B) (B C))";
        
        REQUIRE_THROWS_AS(test.run(), std::runtime_error);
    }

    SECTION("test empty interpolation groups error - first group is empty")
    {
        test.input() << "(check-sat)";
        test.input() << "(get-interpolant () (A))";
        
        REQUIRE_THROWS_AS(test.run(), std::runtime_error);
    }

    SECTION("test both empty interpolation groups error")
    {
        test.input() << "(check-sat)";
        test.input() << "(get-interpolant () ())";
        
        REQUIRE_THROWS_AS(test.run(), std::runtime_error);
    }

    SECTION("test interpolation with non-existent named assertions error")
    {
        test.input() << "(check-sat)";
        test.input() << "(get-interpolant (A) (NonExistent))";
        
        REQUIRE_THROWS_AS(test.run(), std::runtime_error);
    }
}

