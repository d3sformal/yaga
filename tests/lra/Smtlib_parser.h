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
        db->assert_clause(Clause{lit});
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
            order_pred(name);
        }
        else if (name == "and" || name == "or")
        {
            boolean(name, num_args);
        }
    }

    // get variable object from user-defined variable name
    inline Variable var(std::string const& name) const
    {
        auto it = vars.find(name);
        assert(it != vars.end());
        return it->second;
    }

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

    // encode a boolean function (and/or)
    inline void boolean(std::string const& name, int num_args)
    {
        for (; num_args > 1; --num_args)
        {
            auto rhs = pop_lit();
            auto lhs = pop_lit();

            if (lhs == rhs)
            {
                push(lhs);
            }
            else
            {
                push(Literal{new_bool_var().ord()});

                if ((name == "or" && !negate) || (name == "and" && negate))
                {
                    encode_or(lhs, rhs, lits.back());
                }
                else 
                {
                    encode_and(lhs, rhs, lits.back());
                }
            }
        }
    }

    // encode order predicate <, <=, >, >= or equality =
    inline void order_pred(std::string const& name)
    {
        if (last_type == Variable::boolean)
        {
            assert(name == "=");
            auto rhs = pop_lit();
            auto lhs = pop_lit();
            Literal new_lit{new_bool_var().ord()};

            db->assert_clause(new_lit.negate(), lhs.negate(), rhs);
            db->assert_clause(new_lit.negate(), lhs, rhs.negate());
            push(new_lit);
            return;
        }

        auto rhs = pop_poly();
        auto lhs = pop_poly();
        auto norm_poly = lhs - rhs;

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
        auto new_var = new_real_var();
        auto if_false = pop_poly();
        auto if_true = pop_poly();

        push(perun::test::poly(new_var));
        auto true_poly = poly.back() - if_true;
        auto false_poly = poly.back() - if_false;
        auto true_res = lra->constraint(*trail, true_poly.vars, true_poly.coef, Order_predicate::eq, -true_poly.constant);
        auto false_res = lra->constraint(*trail, false_poly.vars, false_poly.coef, Order_predicate::eq, -false_poly.constant);

        auto cond_lit = pop_lit();
        db->assert_clause(Clause{cond_lit.negate(), true_res.lit()});
        db->assert_clause(Clause{cond_lit, false_res.lit()});
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

    inline void encode_and(Literal a, Literal b, Literal new_lit)
    {
        db->assert_clause(Clause{new_lit.negate(), a});
        db->assert_clause(Clause{new_lit.negate(), b});
    }

    inline void encode_or(Literal a, Literal b, Literal new_lit)
    {
        db->assert_clause(Clause{new_lit.negate(), a, b});
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
                    parse_term(in);
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