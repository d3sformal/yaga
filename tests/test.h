#ifndef YAGA_TEST_H
#define YAGA_TEST_H

#include <algorithm>
#include <cassert>
#include <map>
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
    using function_map_t = std::map<std::vector<terms::var_value_t>, terms::var_value_t>;
    using type_map_t = std::unordered_map<std::string, terms::type_t>;
    std::stringstream input_stream;
    std::stringstream output_stream;
    yaga::Solver_answer last_answer;
    std::unordered_map<std::string, bool> bool_model;
    std::unordered_map<std::string, yaga::Rational> lra_model;
    std::unordered_map<std::string, function_map_t> fnc_model;
    std::map<std::string, type_map_t> fnc_params;
    std::unordered_map<std::string, terms::var_value_t> fnc_trailing_values;
    type_map_t fnc_ret_types;
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

    inline terms::var_value_t parse_value(terms::type_t type, std::istringstream& input)
    {
        if (type == terms::types::bool_type) {
            return input.str() == "true";
        } else if (type == terms::types::real_type) {
            return parse_rational(input);
        } else {
            throw std::logic_error("Parsing values of this type is not supported");
        }
    }

    inline terms::type_t parse_type(std::string const& str)
    {
        if (str == "Bool") {
            return terms::types::bool_type;
        } else if (str == "Real") {
            return terms::types::real_type;
        } else {
            return terms::types::null_type;
        }
    }

    inline void insert_param_types(std::string const& fnc, std::string const& params)
    {
        type_map_t& params_map = fnc_params[fnc];

        std::size_t idx = params.find('(');
        while (idx != std::string::npos) {
            std::size_t param_end = params.find(')', idx+1);
            std::size_t space = params.find(' ', idx+1);

            std::string p_name = params.substr(idx+1, space - idx - 1);
            std::string p_type = params.substr(space+1, param_end - space - 1);
            terms::type_t type = parse_type(p_type);
            params_map[p_name] = type;

            idx = params.find('(', idx+1);
        }
    }

    inline terms::var_value_t parse_fnc_parameter(std::string const& fnc, std::string const& inp)
    {
        std::size_t idx1 = inp.find(' ');
        std::size_t idx2 = inp.find(' ', idx1 + 1);
        std::string par_name = inp.substr(idx1 + 1, idx2 - idx1 - 1);
        std::string par_val_str = inp.substr(idx2 + 1, inp.size() - idx2 - 1);
        std::istringstream par_val_stream(par_val_str);
        terms::type_t par_type = fnc_params[fnc][par_name];
        return parse_value(par_type, par_val_stream);
    }

    inline std::vector<terms::var_value_t> parse_fnc_parameters(std::string const& fnc, std::string const& inp)
    {
        std::vector<terms::var_value_t> result;
        if (inp.starts_with("and")) {
            std::size_t idx = inp.find('=');
            while (idx != inp.size() + 2) {
                std::size_t next_idx = inp.find('=', idx + 1);
                if (next_idx == std::string::npos)
                    next_idx = inp.size() + 2;

                result.push_back(parse_fnc_parameter(fnc, inp.substr(idx, next_idx - idx - 3)));

                idx = next_idx;
            }

        } else if (inp.starts_with("=")) {
            result.push_back(parse_fnc_parameter(fnc, inp));
        } else {
            throw std::logic_error("Unsupported ite function paramater format");
        }

        return result;
    }

    /** Read values of variables.
     */
    inline void read_model()
    {
        bool_model.clear();
        lra_model.clear();
        fnc_model.clear();
        fnc_params.clear();
        std::regex define{"\\(define-fun ([A-Za-z0-9]+) \\(\\) ([A-Za-z0-9]+) (.+)\\)"};
        std::regex define_fnc{"\\(define-fun ([A-Za-z0-9]+) \\(((?:\\([A-Za-z0-9 ]+\\)| )+)\\) ([A-Za-z0-9]+)"};
        std::regex ite{" *\\(ite \\(([=\\/\\(\\) A-Za-z0-9\\-]+)\\) ([0-9A-Za-z\\(\\) \\-\\/]+)"};
        std::regex trailing_value{" *([A-Za-z0-9\\(\\)\\/ \\-]+) \\)+"};

        // skip (
        char begin;
        output() >> begin;

        std::string fnc_name;
        for (;;)
        {
            std::string line;
            std::getline(output(), line);

            std::smatch match;

            if (! fnc_name.empty())
            {
                // the following lines form a function definition - an ite expression or a single trailing value

                if (std::regex_match(line, match, ite))
                {
                    auto params = match[1];
                    std::vector<terms::var_value_t> param_vals = parse_fnc_parameters(fnc_name, params);

                    auto ret_type = fnc_ret_types[fnc_name];
                    std::istringstream ret_value_string{match[2]};
                    auto ret_value = parse_value(ret_type, ret_value_string);

                    fnc_model[fnc_name][param_vals] = ret_value;
                }
                else if (std::regex_match(line, match, trailing_value))
                {
                    auto type = fnc_ret_types[fnc_name];
                    std::istringstream value_string{match[1]};
                    auto value = parse_value(type, value_string);
                    fnc_trailing_values[fnc_name] = value;

                    fnc_name.clear();
                }
                else
                {
                    throw std::logic_error("Unsupported function model format");
                }
            }
            else
            {
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
                else if (std::regex_match(line, match, define_fnc))
                {
                    auto name = match[1];
                    auto params = match[2];
                    auto ret_type = match[3];

                    fnc_name = name;
                    insert_param_types(fnc_name, params);
                    fnc_ret_types[fnc_name] = parse_type(ret_type);
                }
                else
                {
                    break;
                }
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

    inline std::optional<terms::var_value_t> fnc_value(std::string const& name, std::vector<terms::var_value_t> const& args) const
    {
        auto it_f = fnc_model.find(name);
        if (it_f == fnc_model.end())
            return std::nullopt;

        function_map_t const& fn_map = it_f->second;
        auto it = fn_map.find(args);
        return it != fn_map.end() ? std::optional{it->second} : std::nullopt;
    }
};

}

#endif // YAGA_TEST_H