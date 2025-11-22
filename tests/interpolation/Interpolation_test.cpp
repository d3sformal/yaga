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

TEST_CASE("Simple interpolation test", "[test_parser]")
{
    using namespace yaga;
    using namespace yaga::test;
    using namespace yaga::parser;

    Yaga_test test;
    test.input() << "(set-logic QF_LRA)";
    test.input() << "(declare-fun x () Real)";
    test.input() << "(declare-fun y () Real)";

    SECTION("simple interpolant")
    {
        test.input() << "(assert (! (= x 0) :named A))";
        test.input() << "(assert (! (= x 1) :named B))";
        test.input() << "(check-sat)";
        test.input() << "(get-interpolant A B)";
        test.run(false, true);

        REQUIRE(test.answer() == Solver_answer::UNSAT);

        std::string actual_interpolant = Yaga_test::normalize_sexpr(test.interpolant());
        std::string expected_interpolant = Yaga_test::normalize_sexpr("(= x 0)");

        REQUIRE(actual_interpolant == expected_interpolant);
    }

    SECTION("simple interpolant with complement group")
    {
        test.input() << "(assert (! (> x y) :named A))";
        test.input() << "(assert (> y 2))";
        test.input() << "(assert (< x 1))";
        test.input() << "(check-sat)";
        test.input() << "(get-interpolant A)";
        test.run(false, true);
    
        REQUIRE(test.answer() == Solver_answer::UNSAT);

        std::string actual_interpolant = Yaga_test::normalize_sexpr(test.interpolant());
        std::string expected_interpolant = Yaga_test::normalize_sexpr("(not (>= (+ (* (- 1) x) y) 0))"); // (x > y)
        REQUIRE(actual_interpolant == expected_interpolant);
    }

    SECTION("interpolant with complement group")
    {
        test.input() << "(assert (! (>= x 5) :named A))";
        test.input() << "(assert (< x 3))";
        test.input() << "(check-sat)";
        test.input() << "(get-interpolant (A))";
        test.run(false, true);
        
        REQUIRE(test.answer() == Solver_answer::UNSAT);
        std::cout << "After unsat" << std::endl;
        std::string actual_interpolant = Yaga_test::normalize_sexpr(test.interpolant());
        std::string expected_interpolant = Yaga_test::normalize_sexpr("(not (>= x 5))");
        REQUIRE(actual_interpolant == expected_interpolant);
    }
}

TEST_CASE("Interpolation result verification", "[interpolation]")
{
    using namespace yaga;
    using namespace yaga::test;
    using namespace yaga::parser;
    
    Yaga_test test;
    test.input() << "(set-logic QF_LRA)";
    test.input() << "(declare-fun x () Real)";
    test.input() << "(declare-fun y () Real)";

    SECTION("simple interpolant with multiple groups")
    {
        test.input() << "(assert (! (>= x 0) :named A))";
        test.input() << "(assert (! (= (+ x 1) y) :named B))";
        test.input() << "(assert (! (< y 0) :named C))";
        test.input() << "(get-interpolant (A B) (C))";
        
        test.run(false, true);
        
        REQUIRE(test.answer() == Solver_answer::UNSAT);
        
        std::string actual_interpolant = Yaga_test::normalize_sexpr(test.interpolant());
        std::string expected_interpolant = Yaga_test::normalize_sexpr("(>= y 0)");
        REQUIRE(actual_interpolant == expected_interpolant);
    }
}

TEST_CASE("Interpolation with complicated inputs", "[interpolation]")
{
    using namespace yaga;
    using namespace yaga::test;
    using namespace yaga::parser;

    Yaga_test test;
    test.input() << "(set-logic QF_LRA)";
    test.input() << "(declare-fun x () Real)";
    test.input() << "(declare-fun y () Real)";
    test.input() << "(declare-fun z () Real)";

    test.input() << "(declare-fun w () Real)";
    test.input() << "(declare-fun a () Real)";
    test.input() << "(assert (!  (and (= x 0) (= y 1) (= z 2)) :named B))";
    test.input() << "(assert (!  (and (or (not (= x 0)) (< z 0) (< (+ z w) 2)) (or (not (= y 1)) (> (+ w a) 0) (> w 0)) (or (< a 0) (< (+ x y z) 0))) :named A))";
    
    SECTION("multiple groups")
    {
        test.input() << "(get-interpolant A B)";
        test.run(false, true);

        REQUIRE(test.answer() == Solver_answer::UNSAT);

        std::string actual_interpolant = Yaga_test::normalize_sexpr(test.interpolant());
        std::string expected_interpolant = Yaga_test::normalize_sexpr("(or (not (= x 0)) (not (= y 1)) (not (>= z 0)) (not (>= (+ x y z) 0)) (not (>= (+ (- 2) z) 0)))");
        REQUIRE(actual_interpolant == expected_interpolant);

    }
}

TEST_CASE("Interpolation triggering conflict inside decide method", "[interpolation]"){
    using namespace yaga;
    using namespace yaga::test;
    using namespace yaga::parser;
    
    Yaga_test test;
    test.input() << "(set-logic QF_LRA)";
    test.input() << "(declare-fun x () Real)";
    test.input() << "(declare-fun y () Real)";
    test.input() << "(declare-fun z () Real)";
    test.input() << "(declare-fun a () Bool)";

    SECTION("Variation 1"){

        test.input() << "(assert (! (and (> x z) (> z 1)) :named A))";
        test.input() << "(assert (! (= 0 x) :named B))";
        test.input() << "(get-interpolant A B)";
        test.run(false, true);
        REQUIRE(test.answer() == Solver_answer::UNSAT);

        std::string actual_interpolant = Yaga_test::normalize_sexpr(test.interpolant());
        std::string expected_interpolant = Yaga_test::normalize_sexpr("(not (>= (+ 1 (* (- 1) x)) 0))");
        REQUIRE(actual_interpolant == expected_interpolant);
    }

    SECTION("Variation 2"){

        test.input() << "(assert (! (and (not a) (or a (= x 0))) :named A))";
        test.input() << "(assert (! (= 1 x) :named B))";
        test.input() << "(get-interpolant A B)";
        test.run(false, true);
        REQUIRE(test.answer() == Solver_answer::UNSAT);

        std::string actual_interpolant = Yaga_test::normalize_sexpr(test.interpolant());
        std::string expected_interpolant = Yaga_test::normalize_sexpr("(= x 0)");
        REQUIRE(actual_interpolant == expected_interpolant);
    }

    SECTION("Variation 3"){

        test.input() << "(assert (! (and (> x y) (a) (or (not a) (> y 0)) ) :named A))";
        test.input() << "(assert (! (and (a) (= 0 x)) :named B))";
        test.input() << "(get-interpolant A B)";
        test.run(false, true);
        REQUIRE(test.answer() == Solver_answer::UNSAT);

        std::string actual_interpolant = Yaga_test::normalize_sexpr(test.interpolant());
        std::string expected_interpolant = Yaga_test::normalize_sexpr("(not (>= (* (- 1) x) 0))"); //(x > 0)
        REQUIRE(actual_interpolant == expected_interpolant);
    }
}