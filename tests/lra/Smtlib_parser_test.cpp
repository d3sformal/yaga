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

class Parser_test {
private:
    std::stringstream input_stream;
    std::stringstream output_stream;
    yaga::Solver_answer last_answer;
    std::unordered_map<std::string, bool> bool_model;
    std::unordered_map<std::string, yaga::Rational> lra_model;
    yaga::parser::Smt2_parser parser;

    /** Read parser answer from the output
     */
    inline void read_answer()
    {
        std::string line;
        std::getline(output(), line);
        if (line == "sat")
        {
            last_answer = yaga::Solver_answer::SAT;
        }
        else if (line == "unsat")
        {
            last_answer = yaga::Solver_answer::UNSAT;
        }
        else if (line == "error")
        {
            last_answer = yaga::Solver_answer::ERROR;
        }
        else 
        {
            last_answer = yaga::Solver_answer::UNKNOWN;
        }
    }

    /** Parse an integer from an input stream as rational
     * 
     * @param input input stream with an integer
     * @return parsed integer as a rational number
     */
    inline yaga::Rational parse_integer(std::istream& input)
    {
        yaga::Rational ret{0};
        while (!input.fail() && !input.eof())
        {
            auto c = input.get();
            if (std::isdigit(c))
            {
                ret = ret * 10 + (c - '0');
            }
            else
            {
                break;
            }
        }
        return ret;
    }

    /** Skip whitespace characters in @p input
     * 
     * @param input input character stream
     */
    inline void skip_space(std::istream& input)
    {
        while (!input.fail() && !input.eof() && std::isspace(input.peek()))
        {
            input.get();
        }
    }

    /** Skip @p cp from @p input
     * 
     * @param input input stream
     * @param cp code point to skip
     */
    inline void skip(std::istream& input, int cp)
    {
        skip_space(input);
        if (input.peek() == cp)
        {
            input.get();
        }
    }

    /** Parse `<natural>` or `(- <natural>)`
     * 
     * @param input input character stream
     * @return parsed integer
     */
    inline yaga::Rational parse_num(std::istream& input)
    {
        yaga::Rational ret{0};
        skip_space(input);
        if (input.peek() == '(')
        {
            skip(input, '(');
            skip_space(input);
            skip(input, '-');
            skip_space(input);
            ret = parse_integer(input);
            ret.negate();
            skip(input, ')');
        }
        else
        {
            ret = parse_integer(input);
        }
        return ret;
    }

    /** Parse a rational value expression:
     * - `<natural>`
     * - `(- <natural>)`
     * - `(/ <natural> <natural>)`
     * - `(/ (- <natural>) <natural>)`
     * 
     * @param input input character stream
     * @return rational value parsed from @p input
     */
    inline yaga::Rational parse_rational(std::istream& input)
    {
        yaga::Rational ret{0};

        skip_space(input);
        if (input.peek() == '(')
        {
            skip(input, '(');
            skip_space(input);

            if (input.peek() == '-')
            {
                skip(input, '-');
                skip_space(input);
                ret = parse_integer(input);
                ret.negate();
            }
            else if (input.peek() == '/')
            {
                skip(input, '/');
                auto num = parse_num(input);

                skip_space(input);
                auto denom = parse_integer(input);
                ret = num / denom;
            }
            else
            {
                throw std::logic_error{"Invalid rational expression."};
            }

            skip_space(input);
            skip(input, ')');
        }
        else
        {
            ret = parse_integer(input);
        }
        return ret;
    }

    /** Read values of variables.
     */
    inline void read_model()
    {
        bool_model.clear();
        lra_model.clear();
        std::regex define{"\\(define-fun ([A-Za-z0-9]+) \\(\\) ([A-Za-z0-9]+) (.+)\\)"};

        // skip (
        char begin;
        output() >> begin;
        for (;;)
        {
            std::string line;
            std::getline(output(), line);

            std::smatch match;
            if (std::regex_match(line, match, define))
            {
                auto name = match[1];
                auto type = match[2];
                std::stringstream value{match[3]};
                if (type == "Bool")
                {
                    bool_model.insert({name, value.str() == "true"});
                }
                else if (type == "Real")
                {
                    lra_model.insert({name, parse_rational(value)});
                }
            }
            else
            {
                break;
            }
        }
    }
public:
    /** Stream with SMT-LIB input
     * 
     * @return reference to the input stream
     */
    inline std::stringstream& input() { return input_stream; }

    /** Stream with parser output
     * 
     * @return stream with output 
     */
    inline std::stringstream& output() { return output_stream; }

    /** Get solver answer of the last `run()` call.
     * 
     * @return answer of the last check.
     */
    inline yaga::Solver_answer answer() const { return last_answer; }

    /** Run the parser with `input()`.
     */
    inline void run()
    {
        input() << "(check-sat)\n(get-model)\n";
        parser.parse(input(), output());
        output().seekg(0, std::ios::beg);
        read_answer();
        read_model();
    }

    /** Get value of a boolean variable
     * 
     * @param name name of a boolean variable
     * @return value of the variable @p name
     */
    inline std::optional<bool> boolean(std::string const& name) const
    {
        auto it = bool_model.find(name);
        return it != bool_model.end() ? std::optional{it->second} : std::nullopt;
    }

    /** Get value of a rational variable
     * 
     * @param name name of a rational variable
     * @return value of the variable @p name
     */
    inline std::optional<yaga::Rational> real(std::string const& name) const
    {
        auto it = lra_model.find(name);
        return it != lra_model.end() ? std::optional{it->second} : std::nullopt;
    }
};

TEST_CASE("Parse boolean functions", "[test_parser]")
{
    using namespace yaga;
    using namespace yaga::parser;
    using namespace yaga::terms;
    using namespace yaga::test;

    Parser_test test;
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
        REQUIRE((*test.boolean("b1") || *test.boolean("b2")));
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

    Parser_test test;
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

    Parser_test test;
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

    Parser_test test;
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