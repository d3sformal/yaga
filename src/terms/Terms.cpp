#include "Terms.h"

#include <cassert>

namespace perun {
namespace terms {

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



} // namespace terms
} // namespace perun