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
    throw std::logic_error("UNIMPLEMENTED!");
}

term_t Term_manager::mk_arithmetic_constant(std::string const& str)
{
    // TODO: This is very prototypish
    auto num = std::stoi(str);
    Rational rat(num);
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
            return term_table->arithmetic_binary_eq(mono2.var, coeff);
        }
        assert(mono2.var != term_t::Undef);
        if (mono1.coeff + mono2.coeff == 0)
        {
            return term_table->arithmetic_binary_eq(mono1.var, mono2.var);
        }
    }
    // TODO: Normalize the polynomial!
    term_t t = poly_to_term(p);
    return term_table->arithmetic_eq_zero(t);
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
    if (term_table->is_uninterpreted_constant(term))
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

} // namespace perun::terms
