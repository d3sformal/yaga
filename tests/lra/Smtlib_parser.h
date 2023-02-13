#ifndef PERUN_TEST_SMTLIB_PARSER_H
#define PERUN_TEST_SMTLIB_PARSER_H

#include <array>
#include <iostream>
#include <string>
#include <sstream>
#include <istream>
#include <vector>
#include <memory>
#include <concepts>
#include <map>

#include "test_expr.h"
#include "Fraction.h"
#include "Linear_arithmetic.h"
#include "Linear_constraint.h"
#include "Literal.h"
#include "Clause.h"
#include "Database.h"

namespace perun::test {

// directly translate smtlib expressions to linear constraints and clauses
class Direct_interpreter {
public:
    using Polynomial_type = Linear_polynomial<Fraction<int>>;
    using Value_type = Fraction<int>;

    inline explicit Direct_interpreter(Linear_arithmetic& lra, Database& db, Trail& trail) 
        : lra(&lra), db(&db), trail(&trail) {}

    // declare a new variable
    inline void declare(std::string const& id, std::string const& type) 
    {
        Variable var;
        if (type == "Real")
        {
            var = new_real_var();
        }
        else
        {
            var = new_bool_var();
        }
        auto [_, is_inserted] = vars.insert({id, var});
        if (!is_inserted)
        {
            std::cerr << "Redefinition of variable '" << id << "'\n";
        }
    }

    // parse a constant
    inline void constant(Value_type val) 
    {
        push(Polynomial_type{
            .vars = std::vector<int>{},
            .coef = std::vector<Value_type>{},
            .constant = val
        });
    }

    // parse a variable identifier
    inline void identifier(std::string const& id)
    {
        if (id == "true")
        {
            push(true_lit);
            return;
        }
        else if (id == "false")
        {
            push(true_lit.negate());
            return;
        }

        auto var_it = vars.find(id);
        if (var_it == vars.end())
        {
            std::cerr << "Unkown variable '" << id << "'\n";
        }
        else if (var_it->second.type() == Variable::rational)
        {
            push(Polynomial_type{
                .vars = std::vector{var_it->second.ord()},
                .coef = std::vector<Value_type>{1},
                .constant = 0
           });
        }
        else if (var_it->second.type() == Variable::boolean)
        {
            Literal lit{var_it->second.ord()};
            if (negate)
            {
                lit = lit.negate();
            }
            push(lit);
        }
    }

    // start parsing (assert ...)
    inline void enter_assert() {}

    // end parsing (assert ...)
    inline void exit_assert() 
    {
        // variable which defines the expression has to be true
        auto lit = pop_lit();
        if (lit == true_lit)
        {
            return;
        }
        assert(lit != true_lit.negate());
        assert_clause(Clause{lit});
    }

    // start parsing a function in SMTLIB assert
    inline void enter_fun(std::string const& name) 
    {
        if (name == "not")
        {
            negate = !negate;
        }
    }

    // end parsing a function in SMTLIB assert
    inline void exit_fun(std::string const& name, int num_args) 
    {
        if (name == "not")
        {
            negate = !negate;
        }
        else if (name == "ite")
        {
            ite();
        }
        else if (name == "-" && num_args == 1)
        {
            unary_minus();
        }
        else if (name == "+" || name == "-" || name == "*" || name == "/")
        {
            arithmetic(name);
        }
        else if (name == "<" || name == "<=" || name == "=" || name == ">" || name == ">=")
        {
            if (last_type == Variable::boolean)
            {
                assert(name == "=");
                bool_equality();
            }
            else
            {
                order_pred(name);
            }
        }
        else if (name == "and" || name == "or")
        {
            boolean(name, num_args);
        }
        else if (name == "=>")
        {
            boolean("or", /*num_args=*/2);
        }
        else
        {
            assert(false && "unkown function");
        }
    }

    // start parsing argument of a function in an asserted expression
    inline void enter_arg(std::string const& fun_name, int index)
    {
        if (fun_name == "=>" && index == 0)
        {
            negate = !negate;
        }
    }

    // finish parsing argument of a function in an asserted expression
    inline void exit_arg(std::string const& fun_name, int index)
    {
        if (fun_name == "=>" && index == 0)
        {
            negate = !negate;
        }
    }

    // get variable object from user-defined variable name
    inline Variable var(std::string const& name) const
    {
        auto it = vars.find(name);
        assert(it != vars.end());
        return it->second;
    }

    inline Literal true_constant() const { return true_lit; }

private:
    // stack with literals
    std::vector<Literal> lits;
    // stack with linear polynomials
    std::vector<Polynomial_type> poly;
    // type of the last argument pushed to the stack
    Variable::Type last_type = Variable::rational;
    // should current literal be negated
    bool negate = false;
    // map user-defined variable name -> variable
    std::unordered_map<std::string, Variable> vars;
    Linear_arithmetic* lra;
    Database* db;
    Trail* trail;
    // placeholder for a literal which represents a constant TRUE
    inline static Literal true_lit{std::numeric_limits<int>::max() - 1};

    // check whether `lit` represents a boolean constant (TRUE or FALSE)
    inline bool is_constant(Literal lit) const { return lit.var() == true_lit.var(); }

    // encode a boolean function (and/or)
    inline void boolean(std::string const& name, int num_args)
    {
        bool is_or = (name == "or" && !negate) || (name == "and" && negate);

        std::vector<Literal> args;
        std::optional<Literal> value;
        for (int i = 0; i < num_args; ++i)
        {
            auto arg = pop_lit();
            auto it = std::find(args.begin(), args.end(), arg);

            if (!is_constant(arg) && it == args.end())
            {
                args.push_back(arg);
            }
            else if (arg == true_lit && is_or)
            {
                value = true_lit;
            }
            else if (arg == true_lit.negate() && !is_or)
            {
                value = true_lit.negate();
            }
        }

        if (value) // constant
        {
            push(value.value());
        }
        else
        {
            auto new_var = new_bool_var();
            Literal new_lit{new_var.ord()};
            push(new_lit);

            assert(std::find_if(args.begin(), args.end(), [&](auto lit) {
                return is_constant(lit);
            }) == args.end());

            if (is_or)
            {
                Clause res{new_lit.negate()};
                res.insert(res.end(), args.rbegin(), args.rend());
                assert_clause(std::move(res));
            }
            else // and 
            {
                for (auto arg : args | std::views::reverse)
                {
                    assert_clause(Clause{new_lit.negate(), arg});
                }
            }
        }
    }

    // encode = if both arguments are boolean functions
    inline void bool_equality()
    {
        auto rhs = pop_lit();
        auto lhs = pop_lit();
        if (is_constant(lhs))
        {
            std::swap(lhs, rhs);
        }

        if (rhs == true_lit)
        {
            push(lhs);
        }
        else if (rhs == true_lit.negate())
        {
            push(lhs.negate());
        }
        else if (!negate)
        {
            assert(!is_constant(lhs));
            assert(!is_constant(rhs));
            Literal new_lit{new_bool_var().ord()};
            assert_clause(Clause{new_lit.negate(), lhs.negate(), rhs});
            assert_clause(Clause{new_lit.negate(), lhs, rhs.negate()});
            push(new_lit);
        }
        else // negate
        {
            assert(!is_constant(lhs));
            assert(!is_constant(rhs));
            Literal new_lit{new_bool_var().ord()};
            assert_clause(Clause{new_lit.negate(), lhs.negate(), rhs.negate()});
            assert_clause(Clause{new_lit.negate(), lhs, rhs});
            push(new_lit);
        }
    }

    // encode order predicate <, <=, >, >= or equality =
    inline void order_pred(std::string const& name)
    {
        assert(last_type == Variable::rational);
        auto rhs = pop_poly();
        auto lhs = pop_poly();
        auto norm_poly = lhs - rhs;

        bool is_empty = true;
        for (auto coef : norm_poly.coef)
        {
            if (coef != 0)
            {
                is_empty = false;
                break;
            }
        }

        if (is_empty)
        {
            Literal lit;
            if ((name == "<" && norm_poly.constant < 0) || (name == "<=" && norm_poly.constant <= 0) || 
                (name == "=" && norm_poly.constant != 0) || (name == ">" && norm_poly.constant > 0) ||
                (name == ">=" && norm_poly.constant >= 0))
            {
                lit = true_lit.negate();
            }
            else
            {
                lit = true_lit;
            }
            push(negate ? lit.negate() : lit);
            return;
        }

        Linear_constraint<Fraction<int>> cons;
        if (name == "<")
        {
            cons = lra->constraint(*trail, norm_poly.vars, norm_poly.coef, Order_predicate::lt, -norm_poly.constant);
        }
        else if (name == "<=")
        {
            cons = lra->constraint(*trail, norm_poly.vars, norm_poly.coef, Order_predicate::leq, -norm_poly.constant);
        }
        else if (name == "=")
        {
            cons = lra->constraint(*trail, norm_poly.vars, norm_poly.coef, Order_predicate::eq, -norm_poly.constant);
        }
        else if (name == ">")
        {
            norm_poly = rhs - lhs;
            cons = lra->constraint(*trail, norm_poly.vars, norm_poly.coef, Order_predicate::lt, -norm_poly.constant);
        }
        else // if (name == ">=")
        {
            assert(name == ">=");
            norm_poly = rhs - lhs;
            cons = lra->constraint(*trail, norm_poly.vars, norm_poly.coef, Order_predicate::leq, -norm_poly.constant);
        }

        if (negate)
        {
            cons = cons.negate();
        }
        push(cons.lit());
    }

    // translate unary -
    inline void unary_minus()
    {
        auto val = pop_poly();
        for (auto& c : val.coef)
        {
            c = -c;
        }
        val.constant = -val.constant;
        push(val);
    }

    // encode an arithmetic operation +, -, *, /
    inline void arithmetic(std::string const& name)
    {
        auto rhs = pop_poly();
        auto lhs = pop_poly();

        Polynomial_type res;
        if (name == "+")
        {
            res = lhs + rhs;
        }
        else if (name == "-")
        {
            res = lhs - rhs;
        }
        else // if (name == "*" || name == "/")
        {
            res = lhs;
            auto mult = rhs.constant;
            if (!rhs.vars.empty())
            {
                assert(lhs.vars.empty());
                res = rhs;
                mult = lhs.constant;
            }
            
            if (name == "/")
            {
                mult = mult.inv();
            }
            res.constant *= mult;
            for (auto& coef : res.coef)
            {
                coef *= mult;
            }
        }
        push(res);
    }

    // encode if-then-else (one boolean function on the stack and two polynomials)
    inline void ite()
    {
        auto if_false = pop_poly();
        auto if_true = pop_poly();

        auto cond_lit = pop_lit();
        if (cond_lit == true_lit)
        {
            push(if_true);
        }
        else if (cond_lit == true_lit.negate())
        {
            push(if_false);
        }
        else // !is_constant(cond_lit)
        {
            push(perun::test::poly(new_real_var()));
            auto true_poly = poly.back() - if_true;
            auto false_poly = poly.back() - if_false;
            auto true_res = lra->constraint(*trail, true_poly.vars, true_poly.coef, Order_predicate::eq, -true_poly.constant);
            auto false_res = lra->constraint(*trail, false_poly.vars, false_poly.coef, Order_predicate::eq, -false_poly.constant);

            assert_clause(Clause{cond_lit.negate(), true_res.lit()});
            assert_clause(Clause{cond_lit, false_res.lit()});
        }
    }

    inline Literal pop_lit()
    {
        assert(!lits.empty());
        auto lit = lits.back();
        lits.pop_back();
        return lit;
    }

    inline Polynomial_type pop_poly()
    {
        assert(!poly.empty());
        auto val = std::move(poly.back());
        poly.pop_back();
        return val;
    }

    inline void push(Literal lit)
    {
        last_type = Variable::boolean;
        lits.push_back(lit);
    }

    inline void push(Polynomial_type const& value)
    {
        last_type = Variable::rational;
        poly.push_back(value);
    }

    inline Variable new_bool_var()
    {
        auto num_bool = static_cast<int>(trail->model<bool>(Variable::boolean).num_vars());

        trail->resize(Variable::boolean, num_bool + 1);
        lra->on_variable_resize(Variable::boolean, num_bool + 1);
        return Variable{num_bool, Variable::boolean};
    }

    inline Variable new_real_var()
    {
        auto num_real = static_cast<int>(trail->model<Fraction<int>>(Variable::rational).num_vars());
        trail->resize(Variable::rational, num_real + 1);
        lra->on_variable_resize(Variable::rational, num_real + 1);
        return Variable{num_real, Variable::rational};
    }

    inline void assert_clause(Clause const& clause)
    {
        assert(std::find_if(clause.begin(), clause.end(), [&](auto lit) {
            return is_constant(lit);
        }) == clause.end());
        db->assert_clause(clause);
    }
};

template<class Listener>
class Smtlib_parser {
public:
    template<typename... Args>
    inline explicit Smtlib_parser(Args&&... args) : list(Listener{std::forward<Args>(args)...}) {}

    void parse(std::istream& in)
    {
        while (parse_fun(in))
        {
        }
    }

    bool parse_fun(std::istream& in)
    {
        skip_space(in);
        if (in.fail() || in.eof())
        {
            return false;
        }
        eat(in, '(');
        auto id = read_id(in);
        if (id == "declare-fun")
        {
            parse_declare(in);
        }
        else if (id == "assert")
        {
            parse_assert(in);
        }
        else // unkown function -> skip
        {
            std::cerr << "Unkown function: '" << id << "'\n";
            for (; !in.fail() && !in.eof() && in.peek() != ')'; in.get())
            {
            }
        }
        eat(in, ')');

        return true;
    }

    void parse_declare(std::istream& in)
    {
        auto id = read_id(in);
        eat(in, '(');
        eat(in, ')');
        auto type = read_id(in);

        listener().declare(id, type);
    }

    void parse_assert(std::istream& in)
    {
        listener().enter_assert();
        parse_term(in);
        listener().exit_assert();
    }

    void parse_term(std::istream& in)
    {
        skip_space(in);
        if (std::isdigit(in.peek()))
        {
            auto value = read_constant(in);
            listener().constant(value);
        }
        else if (is_id(in.peek()))
        {
            auto id = read_id(in);
            auto def_it = defs.find(id);
            if (def_it != defs.end()) // definition
            {
                std::stringstream stream{def_it->second};
                parse_term(stream);
            }
            else // variable
            {
                listener().identifier(id);
            }
        }
        else
        {
            eat(in, '(');
            auto id = read_id(in);
            if (id == "let")
            {
                eat(in, '(');
                for (;;)
                {
                    skip_space(in);
                    if (in.eof() || in.fail() || in.peek() == ')')
                    {
                        break;
                    }

                    eat(in, '(');
                    auto name = read_id(in);
                    auto str = read_closed_subexpr(in);
                    defs[name] = str;
                    eat(in, ')');
                }
                eat(in, ')');
                parse_term(in);
            }
            else
            {
                listener().enter_fun(id);
                int num_args = 0;
                for (;;)
                {
                    skip_space(in);
                    if (in.peek() == ')')
                    {
                        break;
                    }
                    listener().enter_arg(id, num_args);
                    parse_term(in);
                    listener().exit_arg(id, num_args);
                    ++num_args;
                }
                listener().exit_fun(id, num_args);
            }
            eat(in, ')');
        }
    }

    std::string read_closed_subexpr(std::istream& in)
    {
        skip_space(in);
        std::stringstream buffer;
        int num_open = 1;
        while (!in.fail() && !in.eof() && num_open > 0)
        {
            if (in.peek() == '(')
            {
                ++num_open;
            }
            else if (in.peek() == ')')
            {
                --num_open;
                if (num_open <= 0)
                {
                    break;
                }
            }
            buffer << (char)in.get();
        }
        return buffer.str();
    }

    void eat(std::istream& in, char c)
    {
        skip_space(in);
        if (in.peek() == c)
        {
            in.get();
        }
        else 
        {
            std::cerr << "Expected '" << (char)c << "', got '" << (char)in.peek() << "'\n";
        }
    }

    Fraction<int> read_constant(std::istream& in)
    {
        skip_space(in);

        int num = 0;
        int denom = 1;

        while (std::isdigit(in.peek()))
        {
            num = num * 10 + (in.get() - '0');
        }

        if (in.peek() == '.')
        {
            in.get();
            while (std::isdigit(in.peek()))
            {
                num = num * 10 + (in.get() - '0');
                denom *= 10;
            }
        }
        return {num, denom};
    }

    std::string read_id(std::istream& in)
    {
        skip_space(in);

        std::stringstream stream;
        while (!in.fail() && is_id(in.peek()))
        {
            stream << (char)in.get();
        }
        return stream.str();
    }

    bool is_id(int c)
    {
        for (auto other_c : std::array{'~', '!', '@', '$', '%', '^', '&', '*', '_', '-', '+', '=', '<', '>', '.', '?', '/'})
        {
            if (c == other_c)
            {
                return true;
            }
        }
        return std::isalnum(c);
    }

    void skip_space(std::istream& in)
    {
        while (!in.fail() && std::isspace(in.peek()))
        {
            in.get();
        }
    }

    Listener& listener() { return list; }

private:
    Listener list;
    // map definition name to definition
    std::unordered_map<std::string, std::string> defs;
};

}

#endif // PERUN_TEST_SMTLIB_PARSER_H