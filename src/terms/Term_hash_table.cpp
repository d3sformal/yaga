#include "Term_hash_table.h"

#include <cassert>

#include "Terms.h"

namespace perun::terms {

term_t Term_hash_table::get_composite_term(Composite_term_proxy const& proxy)
{
    auto it = terms.find(proxy);
    if (it != terms.end())
    {
        return it->term;
    }
    term_t new_term = proxy.term_table.construct_composite(proxy.kind, proxy.type, proxy.args);
    auto [tit, inserted] = terms.insert({proxy.hash, new_term});
    assert(inserted);
    return it->term;
}

term_t Term_hash_table::get_rational_term(Rational_term_proxy const& proxy)
{
    auto it = terms.find(proxy);
    if (it != terms.end())
    {
        return it->term;
    }
    term_t new_term = proxy.term_table.construct_rational(proxy.kind, proxy.type, proxy.value);
    auto [tit, inserted] = terms.insert({proxy.hash, new_term});
    assert(inserted);
    return it->term;
}

bool Term_hash_table::KeyEqual::operator()(Composite_term_proxy const& proxy,
                                           Term_hash_table::Entry const& entry) const
{
    assert(proxy.hash == entry.hash);
    auto& term_table = proxy.term_table;
    if (term_table.get_kind(entry.term) != proxy.kind)
    {
        return false;
    }
    if (term_table.get_type(entry.term) != proxy.type)
    {
        return false;
    }
    auto const& other_descriptor = term_table.get_descriptor(entry.term);
    auto const& other_composite_descriptor =
        static_cast<composite_term_descriptor_t const&>(other_descriptor);
    if (other_composite_descriptor.size() != proxy.args.size())
    {
        return false;
    }
    return std::ranges::equal(other_composite_descriptor.args(), proxy.args);
}

bool Term_hash_table::KeyEqual::operator()(Rational_term_proxy const& proxy,
                                           Term_hash_table::Entry const& entry) const
{
    assert(proxy.hash == entry.hash);
    auto& term_table = proxy.term_table;
    if (term_table.get_kind(entry.term) != proxy.kind)
    {
        return false;
    }
    if (term_table.get_type(entry.term) != proxy.type)
    {
        return false;
    }
    auto const& other_descriptor = term_table.get_descriptor(entry.term);
    auto const& other_composite_descriptor =
        static_cast<rational_term_descriptor_t const&>(other_descriptor);
    return other_composite_descriptor.value() == proxy.value;
}

bool Term_hash_table::KeyEqual::operator()(Term_hash_table::Entry const& first,
                                           Term_hash_table::Entry const& second) const
{
    return first.hash == second.hash && first.term == second.term;
}

} // namespace perun::terms