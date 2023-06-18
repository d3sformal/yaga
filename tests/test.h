#ifndef YAGA_TEST_H
#define YAGA_TEST_H

#include <algorithm>
#include <cassert>
#include <tuple>
#include <ranges>
#include <regex>
#include <string>
#include <sstream>
#include <unordered_map>
#include <vector>

#include "test_expr.h"
#include "Literal.h"
#include "Clause.h"
#include "Linear_constraints.h"
#include "Rational.h"
#include "Solver_answer.h"
#include "Smt2_parser.h"

namespace yaga::test {

inline yaga::Literal lit(int ord)
{
    return yaga::Literal{ord};
}

template<typename... Args>
inline Clause clause(Args&&... args)
{
    return Clause{std::forward<Args>(args)...};
}

inline yaga::Variable bool_var(int ord)
{
    return yaga::Variable{ord, yaga::Variable::boolean};
}

inline yaga::Variable real_var(int ord)
{
    return yaga::Variable{ord, yaga::Variable::rational};
}

// create a tuple of real variables
template<std::size_t... vars>
inline auto real_vars(std::integer_sequence<std::size_t, vars...>)
{
    return std::tuple{Variable{vars, Variable::rational}...};
}

// create a tuple of real variables
template<int count>
inline auto real_vars()
{
    return real_vars(std::make_index_sequence<count>());
}

// create clause from a list of linear constraints
template<typename Value, typename... Tail>
inline Clause clause(Linear_constraint<Value> cons, Linear_constraint<Tail>... tail)
{
    return clause(cons.lit(), tail.lit()...);
}

/** Parse formula in LRA and run the solver.
 */
class Yaga_test {
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

}

#endif // YAGA_TEST_H