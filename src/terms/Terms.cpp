#include "Terms.h"

#include <cassert>

namespace perun {
namespace terms {

namespace { // Hash functions. TODO: Improve
uint64_t hash_composite_term(Kind kind, std::span<term_t> args) {
    std::hash<int32_t> hasher;
    uint64_t result = hasher(static_cast<std::underlying_type<Kind>::type>(kind));
    for (term_t arg : args) {
        result = result * 31 + hasher(arg);
    }
    return result;
}

uint64_t hash_integer_term(Kind kind, type_t tau, int32_t index) {
    std::hash<int32_t> hasher;
    uint64_t result = hasher(static_cast<std::underlying_type<Kind>::type>(kind));
    result = result * 31 + hasher(tau);
    result = result * 31 + hasher(index);
    return result;
}

uint64_t hash_rational(Rational const& value) {
    std::hash<int32_t> hasher;
    uint64_t result = hasher(value.numerator());
    result = result * 31 + hasher(value.denominator());
    return result;
}
}

Term_table::Term_table()
{
    add_primitive_terms();
}

composite_term_descriptor_t::composite_term_descriptor_t(std::span<term_t> args)
    : m_args(args.begin(), args.begin())
{
}

std::unique_ptr<composite_term_descriptor_t>
composite_term_descriptor_t::make(std::span<term_t> args)
{
    return std::unique_ptr<composite_term_descriptor_t>(new composite_term_descriptor_t(args));
}

std::unique_ptr<rational_term_descriptor_t>
rational_term_descriptor_t::make(Rational const& val)
{
    return std::unique_ptr<rational_term_descriptor_t>(new rational_term_descriptor_t(val));
}

std::unique_ptr<constant_term_descriptor_t>
constant_term_descriptor_t::make(int32_t index)
{
    return std::unique_ptr<constant_term_descriptor_t>(new constant_term_descriptor_t(index));
}




Kind Term_table::get_kind(term_t t) { return inner_table[t].kind; }

type_t Term_table::get_type(term_t t) { return inner_table[t].type; }

term_descriptor_t const& Term_table::get_descriptor(term_t t) { return *inner_table[t].descriptor; }

term_t Term_table::construct_composite(Kind kind, type_t type, std::span<type_t> args)
{
    auto term = composite_term_descriptor_t::make(args);
    auto index = static_cast<int32_t>(inner_table.size()); // TODO: Check Max term count
    this->inner_table.push_back(Term{kind, type, std::move(term)});
    return positive_term(index);
}

term_t Term_table::construct_rational(Kind kind, type_t type, Rational const& value)
{
    auto term = rational_term_descriptor_t::make(value);
    auto index = static_cast<int32_t>(inner_table.size()); // TODO: Check Max term count
    this->inner_table.push_back(Term{kind, type, std::move(term)});
    return positive_term(index);
}

term_t Term_table::construct_constant(Kind kind, type_t type, int32_t index)
{
    auto term = constant_term_descriptor_t::make(index);
    auto term_index = static_cast<int32_t>(inner_table.size()); // TODO: Check Max term count
    this->inner_table.push_back(Term{kind, type, std::move(term)});
    return positive_term(term_index);
}

void Term_table::add_primitive_terms()
{
    assert(inner_table.empty());
    inner_table.push_back(Term{Kind::RESERVED_TERM, types::null_type, nullptr});

    term_t allocated_true_term = constant_term(types::bool_type, 0);
    assert(allocated_true_term == true_term);

    term_t allocated_zero = arithmetic_constant(Rational(0));
    assert(allocated_zero == zero_term);
}

term_t Term_table::constant_term(type_t tau, int32_t index)
{
    Constant_term_proxy proxy{Kind::CONSTANT_TERM, tau, hash_integer_term(Kind::CONSTANT_TERM, tau, index), *this, index};
    return known_terms.get_constant_term(proxy);
}

term_t Term_table::arithmetic_constant(Rational const& value)
{
    Rational_proxy proxy{hash_rational(value), *this, value};
    return known_terms.get_rational_term(proxy);
}

term_t Term_table::or_term(std::span<term_t> args)
{
    Composite_term_proxy proxy{Kind::OR_TERM, types::bool_type, hash_composite_term(Kind::OR_TERM, args), *this, args};
    return known_terms.get_composite_term(proxy);
}
term_t Term_table::uninterpreted_constant(type_t tau)
{
        throw std::logic_error("UNIMPLEMETED!");
}

} // namespace terms
} // namespace perun