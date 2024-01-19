#include "Term_manager.h"

#include <algorithm>
#include <numeric>

#include "Arithmetic_polynomial.h"
#include "Terms.h"

#define UNIMPLEMENTED throw std::logic_error("Not implemented yet!")

namespace yaga::terms {

Term_manager::Term_manager()
{
    term_table = std::make_unique<Term_table>();
}

Term_manager::~Term_manager() = default;

void Term_manager::set_term_name(term_t t, std::string const& name)
{
    term_table->set_term_name(t, name);
}

std::optional<std::string_view> Term_manager::get_term_name(term_t t) const
{
    return term_table->get_term_name(t);
}

std::optional<term_t> Term_manager::get_term_by_name(std::string const& name)
{
    return term_table->get_term_by_name(name);
}

type_t Term_manager::get_type(term_t term) const
{
    return term_table->get_type(term);
}

std::span<const term_t> Term_manager::get_args(term_t term) const
{
    return term_table->get_args(term);
}

Kind Term_manager::get_kind(term_t term) const
{
    return term_table->get_kind(term);
}

int32_t Term_manager::index_of(term_t term) const
{
    return terms::index_of(term);
}

term_t Term_manager::positive_term(term_t term) const
{
    return terms::positive_term(term);
}

bool Term_manager::is_negated(term_t term) const
{
    return terms::is_negated(term);
}

Rational const& Term_manager::arithmetic_constant_value(term_t term) const
{
    return term_table->arithmetic_constant_value(term);
}

bool Term_manager::is_arithmetic_constant(term_t term) const
{
    return term_table->is_arithmetic_constant(term);
}

bool Term_manager::is_uninterpreted_constant(term_t term) const
{
    return term_table->is_uninterpreted_constant(term);
}

bool Term_manager::is_arithmetic_product(term_t term) const
{
    return term_table->is_arithmetic_product(term);
}

bool Term_manager::is_arithmetic_polynomial(term_t term) const
{
    return term_table->is_arithmetic_polynomial(term);
}

bool Term_manager::is_ite(term_t term) const
{
    return term_table->is_ite(term);
}

term_t Term_manager::var_of_product(term_t arithmetic_product) const
{
    return term_table->var_of_product(arithmetic_product);
}

Rational const& Term_manager::coeff_of_product(term_t arithmetic_product) const
{
    return term_table->coeff_of_product(arithmetic_product);
}

term_t Term_manager::mk_uninterpreted_constant(type_t type)
{
    return term_table->new_uninterpreted_constant(type);
}

// TODO: Maybe this should be in the rewriter?
term_t Term_manager::mk_term(Kind kind, std::span<term_t> args)
{
    switch (kind)
    {
    case Kind::ARITH_GE_ATOM:
        assert(args.size() == 1);
        return mk_arithmetic_geq(args[0], zero_term);
    case Kind::ARITH_EQ_ATOM:
        assert(args.size() == 1);
        return mk_arithmetic_eq(args[0], zero_term);
    case Kind::ARITH_BINEQ_ATOM:
        assert(args.size() == 2);
        return mk_arithmetic_eq(args[0], args[1]);
    case Kind::EQ_TERM:
        assert(args.size() == 2);
        return mk_binary_eq(args[0], args[1]);
    case Kind::OR_TERM:
        return mk_or(args);
    case Kind::ARITH_PRODUCT:
        return mk_arithmetic_times(args);
    case Kind::ARITH_POLY:
        return mk_arithmetic_plus(args);
    case Kind::ITE_TERM:
        assert(args.size() == 3);
        return mk_ite(args[0], args[1], args[2]);

    case Kind::UNINTERPRETED_TERM:
    case Kind::ARITH_CONSTANT:
        assert(false);
        throw std::logic_error("Unexpected situation");
    default:
        throw std::logic_error("Case not covered!");
    }
}

term_t Term_manager::mk_term(std::string const& op, std::span<term_t> args)
{
    if (op == ">=")
    {
        assert(args.size() == 2);
        return mk_arithmetic_geq(args[0], args[1]);
    }
    else if (op == "<=")
    {
        assert(args.size() == 2);
        return mk_arithmetic_leq(args[0], args[1]);
    }
    else if (op == "<")
    {
        assert(args.size() == 2);
        return mk_arithmetic_lt(args[0], args[1]);
    }
    else if (op == ">")
    {
        assert(args.size() == 2);
        return mk_arithmetic_gt(args[0], args[1]);
    }
    else if (op == "=")
    {
        return mk_eq(args);
    }
    else if (op == "or")
    {
        return mk_or(args);
    }
    else if (op == "and")
    {
        return mk_and(args);
    }
    else if (op == "=>")
    {
        assert(args.size() == 2);
        return mk_implies(args[0], args[1]);
    }
    else if (op == "not")
    {
        assert(args.size() == 1);
        return terms::opposite_term(args[0]);
    }
    else if (op == "-")
    {
        if (args.size() == 1)
        {
            return mk_unary_minus(args[0]);
        }
        else
        {
            assert(args.size() == 2);
            return mk_arithmetic_minus(args[0], args[1]);
        }
    }
    else if (op == "+")
    {
        return mk_arithmetic_plus(args);
    }
    else if (op == "*")
    {
        return mk_arithmetic_times(args);
    }
    else if (op == "/")
    {
        assert(args.size() == 2);
        return mk_divides(args[0], args[1]);
    }
    else if (op == "ite")
    {
        assert(args.size() == 3);
        return mk_ite(args[0], args[1], args[2]);
    }
    else if (op == "xor")
    {
        assert(args.size() == 2);
        return mk_xor(args[0], args[1]);
    }
    UNIMPLEMENTED;
}

term_t Term_manager::mk_app(std::string const& name, type_t ret_type, std::span<term_t> args)
{
    auto fnc_symbol = get_term_by_name(name);
    assert(fnc_symbol.has_value());

    std::vector<term_t> args_with_symbol = std::vector<term_t>();
    args_with_symbol.push_back(fnc_symbol.value());

    for (auto arg : args)
    {
        args_with_symbol.push_back(arg);
    }

    return term_table->app_term(ret_type, args_with_symbol);
}

term_t Term_manager::mk_eq(std::span<term_t> args)
{
    if (args.size() == 2)
    {
        return mk_binary_eq(args[0], args[1]);
    }
    UNIMPLEMENTED;
}

term_t Term_manager::mk_binary_eq(term_t t1, term_t t2)
{
    type_t type = get_type(t1);
    if (type != get_type(t2)) {
        throw std::logic_error("Types do not match");
    }

    if (type == terms::types::real_type) {
        return mk_arithmetic_eq(t1, t2);
    }
    if (type == terms::types::bool_type)
    {
        return mk_iff(t1, t2);
    }
    UNIMPLEMENTED;
}

term_t Term_manager::mk_or(std::span<term_t> args)
{
    if (args.empty()) { return false_term; }

    // Sort arguments to easily detect true/false terms, duplicates, and opposite pairs
    std::ranges::sort(args);
    term_t first = args[0];
    if (first == true_term) { return true_term; }
    uint32_t simplified_args_count = (first == false_term ? 0 : 1);
    term_t previous = first;
    for (std::size_t i = 1; i < args.size(); ++i) {
        term_t current = args[i];
        if (previous != current) { // otherwise just skip
            if (current == opposite_term(previous)) { return true_term; }
            assert(current != true_term and current != false_term);
            previous = current;
            args[simplified_args_count] = current;
            ++simplified_args_count;
        }
    }
    if (simplified_args_count <= 1) { return previous; } // Either false term or the unique non-false term
    return term_table->or_term(args.first(simplified_args_count));
}

term_t Term_manager::mk_and(std::span<term_t> args)
{
    for (term_t & arg : args)
    {
        arg = opposite_term(arg);
    }
    return opposite_term(mk_or(args));
}

term_t Term_manager::mk_binary_or(term_t x, term_t y)
{
    if (x == y) { return x; }
    if (x == true_term) { return x; }
    if (y == true_term) { return y; }
    if (x == false_term) { return y; }
    if (y == false_term) { return x; }
    if (opposite_term(x) == y) { return true_term; }

    std::array<term_t, 2> args {x, y};
    if (y < x) { std::swap(args[0], args[1]); }
    return term_table->or_term(args);
}

term_t Term_manager::mk_binary_and(term_t x, term_t y)
{
    return opposite_term(mk_binary_or(opposite_term(x), opposite_term(y)));
}

term_t Term_manager::mk_implies(term_t x, term_t y) {
    return mk_binary_or(opposite_term(x), y);
}

term_t Term_manager::mk_iff(term_t t1, term_t t2)
{
    // TODO: handle better?
    return mk_binary_and(mk_implies(t1, t2), mk_implies(t2, t1));
}

term_t Term_manager::mk_xor(term_t t1, term_t t2)
{
    // TODO: handle better?
    return mk_binary_and(mk_binary_or(t1, t2), opposite_term(mk_binary_and(t1, t2)));
}


term_t Term_manager::mk_integer_constant(std::string const& str)
{
    Rational rat(str.c_str());
    assert(rat.isInteger());
    return term_table->arithmetic_constant(rat);
}

term_t Term_manager::mk_rational_constant(std::string const& str)
{
    // TODO: This should be revisited and checked if it can be improved
    auto separator_position = str.find('.');
    if (separator_position == std::string::npos)
    {
        return mk_integer_constant(str);
    }
    auto integral_part = str.substr(0, separator_position);
    auto integral_value = Rational(integral_part.c_str()); // TODO: Make Rational accept string_view
    std::string fractional_part = str.substr(separator_position + 1);
    auto precision = Rational(1);
    for (auto i = 0u; i < fractional_part.size(); ++i)
    {
        precision *= 10;
    }

    auto fractional_value = Rational(fractional_part.c_str());
    auto gcd_value = gcd(precision, fractional_value);
    auto num = fractional_value / gcd_value;
    auto den = precision / gcd_value;
    num = integral_value * den + num;
    return term_table->arithmetic_constant(num / den);
}

bool Term_manager::is_var_like(term_t t) const
{
    auto kind = get_kind(t);
    assert(kind != Kind::ITE_TERM or get_type(t) == types::real_type);
    return kind == Kind::UNINTERPRETED_TERM or kind == Kind::ITE_TERM;
}

term_t Term_manager::mk_arithmetic_eq(term_t t1, term_t t2)
{
    if (t1 == t2)
    {
        return true_term;
    }
    auto p = term_to_poly(t1);
    auto other = term_to_poly(t2);
    p.merge(other, -1);
    assert(p.size() != 0);
    if (p.size() <= 2)
    {
        if (p.size() == 1)
        {
            auto const& mono = *p.begin();
            if (mono.var == term_t::Undef)
            {
                // t1 - t2 is a non-zero constant
                assert(mono.coeff != 0);
                return false_term;
            }
            else
            {
                // t1 - t2 is c*x for some constant c and variable x
                return term_table->arithmetic_eq_zero(mono.var);
            }
            assert(false);
        }
        assert(p.size() == 2);
        auto it = p.begin();
        auto const& mono1 = *it;
        auto const& mono2 = *(++it);
        // p is c1*x1 + c2*x2
        // Simplify (p = 0) to (x2 = -c1/c2) if x1 is UNDEF
        if (mono1.var == term_t::Undef)
        {
            assert(mono1.coeff != 0 and mono2.coeff != 0);
            term_t coeff = term_table->arithmetic_constant(-mono1.coeff / mono2.coeff);
            return direct_arithmetic_binary_equality(mono2.var, coeff);
        }
        // NOTE that x2 can never be UNDEF, because UNDEF (constant monomial) is always the first one
        assert(mono2.var != term_t::Undef);
        // Simplify (p = 0) to (x1 = x2) if c1 + c2 = 0
        if (mono1.coeff + mono2.coeff == 0)
        {
            return direct_arithmetic_binary_equality(mono1.var, mono2.var);
        }
    }
    // TODO: Normalize the polynomial!
    term_t t = poly_to_term(p);
    return term_table->arithmetic_eq_zero(t);
}

term_t Term_manager::direct_arithmetic_binary_equality(term_t t1, term_t t2)
{
    assert(t1 != t2);
    assert(is_var_like(t1) or is_var_like(t2));
    if (not is_var_like(t1) or (is_var_like(t2) and t2 < t1))
    {
        std::swap(t1, t2);
    }
    return term_table->arithmetic_binary_eq(t1, t2);
}

term_t Term_manager::mk_arithmetic_leq(term_t t1, term_t t2)
{
    return mk_arithmetic_geq(t2, t1);
}

term_t Term_manager::mk_arithmetic_lt(term_t t1, term_t t2)
{
    return opposite_term(mk_arithmetic_geq(t1, t2));
}

term_t Term_manager::mk_arithmetic_gt(term_t t1, term_t t2)
{
    return mk_arithmetic_lt(t2, t1);
}

term_t Term_manager::mk_arithmetic_geq(term_t t1, term_t t2)
{
    // Transform to a form (t >= 0)
    term_t diff = mk_arithmetic_minus(t1, t2);
    if (term_table->is_arithmetic_constant(diff))
    {
        return term_table->arithmetic_constant_value(diff) >= 0 ? true_term : false_term;
    }
    return term_table->arithmetic_geq_zero(diff);
}

/*
 * Returns normalized term equal to "t1 - t2"
 */
term_t Term_manager::mk_arithmetic_minus(term_t t1, term_t t2)
{
    poly_t p1 = term_to_poly(t1);
    poly_t p2 = term_to_poly(t2);
    Rational neg_one = -1;
    p1.merge(p2, neg_one);
    return poly_to_term(p1);
}

term_t Term_manager::mk_unary_minus(term_t t)
{
    poly_t p = term_to_poly(t);
    p.negate();
    return poly_to_term(p);
}

poly_t Term_manager::term_to_poly(term_t term)
{
    poly_t poly;
    if (term_table->is_arithmetic_constant(term))
    {
        if (term != zero_term)
        {
            poly.add_term(term_t::Undef, term_table->arithmetic_constant_value(term));
        }
        return poly;
    }
    if (term_table->is_uninterpreted_constant(term) || term_table->is_ite(term) || term_table->is_app(term))
    {
        poly.add_term(term, Rational(1));
        return poly;
    }
    if (term_table->is_arithmetic_product(term))
    {
        poly.add_term(term_table->var_of_product(term), term_table->coeff_of_product(term));
        return poly;
    }
    if (term_table->is_arithmetic_polynomial(term))
    {
        auto const& children = term_table->monomials_of(term);
        for (term_t child : children)
        {
            poly.merge(term_to_poly(child), Rational(1));
        }
        return poly;
    }
    assert(false);
    throw std::logic_error("UNREACHABLE");
}

term_t Term_manager::poly_to_term(poly_t const& poly)
{
    auto n = poly.size();
    if (n == 0) { return zero_term; }

    auto monomial_to_term = [&](auto const& mono) {
        assert(!is_zero(mono.coeff));
        if (mono.var == term_t::Undef)
        {
            return term_table->arithmetic_constant(mono.coeff);
        }
        if (mono.coeff == Rational(1))
        {
            return mono.var;
        }
        return term_table->arithmetic_product(mono.coeff, mono.var);
    };

    if (n == 1)
    {
        auto const& mono = *poly.begin();
        return monomial_to_term(mono);
    }

    std::vector<term_t> mono_terms;
    mono_terms.reserve(n);
    for (auto const& mono : poly)
    {
        mono_terms.push_back(monomial_to_term(mono));
    }
    return term_table->arithmetic_polynomial(mono_terms);
}

term_t Term_manager::mk_arithmetic_plus(std::span<term_t> args)
{
    // TODO: Can we do something more efficient?
    poly_t res;
    for (term_t arg : args) {
        res.merge(term_to_poly(arg), 1);
    }
    return poly_to_term(res);
}

term_t Term_manager::mk_arithmetic_times(std::span<term_t> args)
{
    if (args.empty())
    {
        return term_table->arithmetic_constant(1);
    }
    if (args.size() == 1)
    {
        return args[0];
    }
    assert(args.size() == 2);
    auto pit = std::partition(args.begin(), args.end(),[this](term_t arg) { return this->term_table->is_arithmetic_constant(arg); });
    // constants are from begin to it, non-constants are from pit (included) until end
    assert(args.end() - pit <= 1);

    // fold all constants into a single value
    Rational val = 1;
    for (auto it = args.begin(); it != pit; ++it) {
        assert(term_table->is_arithmetic_constant(*it));
        val *= term_table->arithmetic_constant_value(*it);
    }
    if (val == 0)
    {
        return zero_term;
    }
    if (pit == args.end()) // just a constant value
    {
        return term_table->arithmetic_constant(val);
    }
    if (val == 1) // 1 * x -> x
    {
        return *pit;
    }
    // General term c * p
    term_t poly_term = *pit;
    switch(get_kind(poly_term))
    {
    case Kind::UNINTERPRETED_TERM:
    case Kind::ITE_TERM:
        assert(get_type(poly_term) == types::real_type);
        return term_table->arithmetic_product(val, *pit);
    case Kind::ARITH_PRODUCT: {
        term_t var = term_table->var_of_product(poly_term);
        auto const& coeff = term_table->coeff_of_product(poly_term);
        return term_table->arithmetic_product(coeff * val, var);
    }
    case Kind::ARITH_POLY:
    {
        auto poly = term_to_poly(poly_term);
        poly.multiply_by(val);
        return poly_to_term(poly);
    }
    default:
        assert(false);
        throw std::logic_error("UNREACHABLE");
    }

}

term_t Term_manager::mk_divides(term_t t1, term_t t2)
{
    assert(term_table->is_arithmetic_constant(t2));
    Rational const& value = term_table->arithmetic_constant_value(t2);
    if (term_table->is_arithmetic_constant(t1))
    {
        return term_table->arithmetic_constant(term_table->arithmetic_constant_value(t1) / value);
    }
    auto mult = value.inv();
    std::array<term_t,2> args {t1, term_table->arithmetic_constant(mult)};
    return mk_arithmetic_times(args);
}

term_t Term_manager::mk_ite(term_t i, term_t t, term_t e)
{
    assert(get_type(i) == types::bool_type);
    type_t type1 = get_type(t);
    if (get_type(e) != type1)
    {
        throw std::invalid_argument("Types in ITE do not match!");
    }
    if (type1 == types::bool_type)
    {
        return mk_bool_ite(i, t, e);
    }
    else if (type1 == types::real_type)
    {
        return mk_arithmetic_ite(i, t, e);
    }
    throw std::logic_error("UNREACHABLE!");
}

/*
 * Simplifications:
 *  ite c t t        --> t
 *  ite true t e     --> t
 *  ite false t e    --> e
 *
 *  ite c t (not t)  --> (c == t)
 *
 *  ite c c e        --> c or e
 *  ite c t c        --> c and t
 *  ite c (not c) e  --> (not c) and e
 *  ite c t (not c)  --> (not c) or t
 *
 *  ite c true e     --> c or e
 *  ite c false e    --> (not c) and e
 *  ite c t false    --> c and t
 *  ite c t true     --> (not c) or t
 *
 * Otherwise:
 *  ite (not c) t e  --> ite c e t
 */
term_t Term_manager::mk_bool_ite(term_t c, term_t t, term_t e)
{
    if (t == e) return t;
    if (c == true_term) return t;
    if (c == false_term) return e;

    if (t == opposite_term(e)) return mk_iff(c, t);

    if (c == t) return mk_binary_or(t, e);
    if (c == e) return mk_binary_and(e, t);
    if (c == opposite_term(t)) return mk_binary_and(t, e);
    if (c == opposite_term(e)) return mk_binary_or(e, t);

    if (t == true_term) return mk_binary_or(c, e);
    if (t == false_term) return mk_binary_and(opposite_term(c), e);
    if (e == false_term) return mk_binary_and(c, t);
    if (e == true_term) return mk_binary_or(opposite_term(c), t);

    if (is_negated(c))
    {
        c = opposite_term(c);
        std::swap(t,e);
    }
    // TODO: Implement handling in term_table
    return mk_binary_and(mk_implies(c, t), mk_implies(opposite_term(c), e));
    //return term_table->ite_term(c,t,e);
}

term_t Term_manager::mk_arithmetic_ite(term_t c, term_t t, term_t e)
{
    if (c == true_term) return t;
    if (c == false_term) return e;
    if (t == e) return t;

    if (is_negated(c))
    {
        c = opposite_term(c);
        std::swap(t, e);
    }

    return term_table->arithmetic_ite(c, t, e);
}

} // namespace yaga::terms
