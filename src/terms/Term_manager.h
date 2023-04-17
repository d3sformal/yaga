#ifndef PERUN_TERM_MANAGER_H
#define PERUN_TERM_MANAGER_H

#include <memory>
#include <span>

#include "Arithmetic_polynomial.h"
#include "Term_types.h"

namespace perun::terms {

using poly_t = Polynomial<term_t>;

class Term_table;

class Term_manager {
    std::unique_ptr<Term_table> term_table;

public:
    Term_manager();
    ~Term_manager();

    // Generic method that delegates the work to specific methods for each operation
    term_t mk_term(std::string const& op, std::span<term_t> args);
    term_t mk_term(Kind kind, std::span<term_t> args);
    term_t mk_eq(std::span<term_t> args);
    term_t mk_binary_eq(term_t t1, term_t t2);

    // Creates uninterpreted constants of type `type` (these are the free variables of formulae)
    term_t mk_uninterpreted_constant(type_t type);

    // Boolean terms
    term_t mk_or(std::span<term_t> args);
    term_t mk_and(std::span<term_t> args);

    term_t mk_binary_or(term_t x, term_t y);
    term_t mk_binary_and(term_t x, term_t y);
    term_t mk_implies(term_t x, term_t y);
    term_t mk_iff(term_t t1, term_t t2);


    // Arithmetic terms
    term_t mk_integer_constant(std::string const& str);
    term_t mk_real_constant(std::string const& str);

    term_t mk_arithmetic_eq(term_t t1, term_t t2);

    term_t mk_arithmetic_geq(term_t t1, term_t t2);

    term_t mk_arithmetic_leq(term_t t1, term_t t2);

    term_t mk_arithmetic_gt(term_t t1, term_t t2);

    term_t mk_arithmetic_lt(term_t t1, term_t t2);

    term_t mk_arithmetic_minus(term_t t1, term_t t2);

    term_t mk_unary_minus(term_t t);

    term_t mk_arithmetic_plus(std::span<term_t> args);

    term_t mk_arithmetic_times(std::span<term_t> args);

    term_t mk_divides(term_t t1, term_t t2);

    term_t mk_ite(term_t i, term_t t, term_t e);

    // names
    void set_term_name(term_t t, std::string const& name);
    term_t get_term_by_name(std::string const& name);

    // term queries
    [[nodiscard]] type_t get_type(term_t term) const;

    [[nodiscard]] std::span<const term_t> get_args(term_t term) const;

    [[nodiscard]] Kind get_kind(term_t term) const;

    [[nodiscard]] Term_table const& get_term_table() const { return *term_table; }

private:
    term_t poly_to_term(poly_t const& poly);
    poly_t term_to_poly(term_t term);

    term_t mk_bool_ite(term_t i, term_t t, term_t e);
    term_t mk_arithmetic_ite(term_t i, term_t t, term_t e);

    term_t direct_arithmetic_binary_equality(term_t t1, term_t t2);

    // Helper method for polynomials, determines if a term can be treated as a variable
    // This includes variables (KIND::UNINTERPRETED_TERM) and ITEs
    bool is_var_like(term_t t) const;

};
} // namespace perun::terms

#endif // PERUN_TERM_MANAGER_H
