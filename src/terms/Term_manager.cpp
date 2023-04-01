#include "Term_manager.h"

#include <algorithm>

#include "Arithmetic_polynomial.h"
#include "Terms.h"

namespace perun::terms {

Term_manager::Term_manager()
{
    term_table = std::make_unique<Term_table>();
}

Term_manager::~Term_manager() = default;

void Term_manager::set_term_name(term_t t, std::string const& name)
{
    term_table->set_term_name(t, name);
}

term_t Term_manager::get_term_by_name(std::string const& name)
{
    return term_table->get_term_by_name(name);
}

type_t Term_manager::get_term_type(term_t term)
{
    return term_table->get_type(term);
}

term_t Term_manager::mk_uninterpreted_constant(type_t type)
{
    return term_table->new_uninterpreted_constant(type);
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

term_t Term_manager::mk_integer_constant(std::string const& str)
{
    // TODO: This is very prototypish
    auto num = std::stoi(str);
    Rational rat(num);
    return term_table->arithmetic_constant(rat);
}

term_t Term_manager::mk_real_constant(std::string const& str)
{
    // TODO: Implement properly
    auto separator_position = str.find('.');
    if (separator_position == std::string::npos)
    {
        return mk_integer_constant(str);
    }
    auto integral_part = std::stoi(str.substr(0, separator_position));
    std::string fractional_str = str.substr(separator_position + 1);
    if (fractional_str.size() > 9) { throw std::logic_error("Unsupported yet!"); }
    auto precision = 1;
    for (auto i = 0u; i < fractional_str.size(); ++i)
    {
        precision *= 10;
    }

    auto fractional_part = std::stoi(fractional_str);
    auto gcd = std::gcd(precision, fractional_part);
    auto num = fractional_part / gcd;
    auto den = precision / gcd;
    num = integral_part * den + num;
    Rational rat(num, den);
    return term_table->arithmetic_constant(rat);
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
        // NOTE that x2 can never be UNDEF, because UNDEF (constant monomial) is always the first one
        // Simplify (p = 0) to (x1 = x2) if c1 + c2 = 0
        if (mono1.var == term_t::Undef)
        {
            term_t coeff = term_table->arithmetic_constant(-mono1.coeff / mono2.coeff);
            return direct_arithemetic_binary_equality(mono2.var, coeff);
        }
        assert(mono2.var != term_t::Undef);
        if (mono1.coeff + mono2.coeff == 0)
        {
            return direct_arithemetic_binary_equality(mono1.var, mono2.var);
        }
    }
    // TODO: Normalize the polynomial!
    term_t t = poly_to_term(p);
    return term_table->arithmetic_eq_zero(t);
}

term_t Term_manager::direct_arithemetic_binary_equality(term_t t1, term_t t2)
{
    assert(t1 != t2);
    if (t2 < t1)
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
    if (term_table->is_uninterpreted_constant(term) || term_table->is_ite(term))
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
    // constants are from begin to it, non-constants are from it (included) until end
    auto nonconstants_count = args.end() - pit;
    assert(nonconstants_count <= 1);
    // fold all constants into a single value
    Rational val = 1;
    for (auto it = args.begin(); it != pit; ++it) {
        assert(term_table->is_arithmetic_constant(*it));
        val *= term_table->arithmetic_constant_value(*it);
    }
    if (pit == args.end())
    {
        return term_table->arithmetic_constant(val);
    }
    else
    {
        return term_table->arithmetic_product(val, *pit);
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
    assert(get_term_type(i) == types::bool_type);
    type_t type1 = get_term_type(t);
    if (get_term_type(e) != type1)
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

    if (polarity_of(c))
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

    if (polarity_of(c))
    {
        c = opposite_term(c);
        std::swap(t, e);
    }

    return term_table->arithmetic_ite(c, t, e);
}

} // namespace perun::terms
