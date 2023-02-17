#ifndef PERUN_TERM_MANAGER_H
#define PERUN_TERM_MANAGER_H

#include <memory>
#include <span>

#include "Term_types.h"

namespace perun::terms {

class Term_table;

class Term_manager {
    std::unique_ptr<Term_table> term_table;

public:
    Term_manager();
    ~Term_manager();
    // Creates uninterpreted constants of type `type` (these are the free variables of formulae)
    term_t mk_uninterpreted_constant(type_t type);

    // Boolean terms
    term_t mk_or(std::span<term_t> args);
    term_t mk_and(std::span<term_t> args);


    term_t mk_binary_or(term_t x, term_t y);
    term_t mk_binary_and(term_t x, term_t y);
    term_t mk_implies(term_t x, term_t y);

};
} // namespace perun::terms

#endif // PERUN_TERM_MANAGER_H
