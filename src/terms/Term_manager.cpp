#include "Term_manager.h"

#include <algorithm>

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
    throw std::logic_error("UNIMPLEMENTED!");
}

} // namespace perun::terms
