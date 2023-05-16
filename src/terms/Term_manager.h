#ifndef PERUN_TERM_MANAGER_H
#define PERUN_TERM_MANAGER_H

#include <memory>
#include <optional>
#include <span>

#include "Arithmetic_polynomial.h"
#include "Term_types.h"

namespace perun::terms {

using poly_t = Polynomial<term_t>;

class Term_table;

/**
 * Class for creating and querying terms. This is an outward facing class which wraps the internal
 * Term table. It performs some normalization to avoid having multiple representation of semantically
 * equivalent terms.
 */
class Term_manager {
    std::unique_ptr<Term_table> term_table;

public:
    Term_manager();
    ~Term_manager();

    /*
     * Generic method that delegates the work to specific methods for each operation
     */

    /**
     * Gets the term using the name of the operation and a list of argument terms
     * @param op name of the operation (function symbol)
     * @param args argument list
     * @return handle to the corresponding composite term
     */
    term_t mk_term(std::string const& op, std::span<term_t> args);

    /**
     * Gets the term of the specified kind with the given list of argument terms
     * @param kind the kind of the term
     * @param args the argument list
     * @return handle to the corresponding composite term
     */
    term_t mk_term(Kind kind, std::span<term_t> args);

    /**
     * Gets the equality term for the list of arguments.
     * At the moment only binary equality is supported.
     * @param args terms that are to be equal
     * @return the equality term
     */
    term_t mk_eq(std::span<term_t> args);

    /**
     * Gets the equality of the two terms.
     * The equality may be normalized. This means that it not necessarily true that LHS is t1
     * and RHS is t2.
     *
     * @param t1 first term
     * @param t2 second term
     * @return the equality term that is equivalent to "t1 = t2"
     */
    term_t mk_binary_eq(term_t t1, term_t t2);

    // Creates uninterpreted constants of type `type` (these are the free variables of formulae)

    /**
     * Creates a fresh uninterpreted constant of the given type
     *
     * @param type type of the constant
     * @return term representation of the constant
     */
    term_t mk_uninterpreted_constant(type_t type);

    /*
     * Boolean terms
     */

    term_t mk_or(std::span<term_t> args);
    term_t mk_and(std::span<term_t> args);

    term_t mk_binary_or(term_t x, term_t y);
    term_t mk_binary_and(term_t x, term_t y);
    term_t mk_implies(term_t x, term_t y);
    term_t mk_iff(term_t t1, term_t t2);
    term_t mk_xor(term_t t1, term_t t2);


    /*
     * Arithmetic terms
     */

    term_t mk_integer_constant(std::string const& str);

    term_t mk_rational_constant(std::string const& str);

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

    /*
     * term names
     */
    void set_term_name(term_t t, std::string const& name);
    std::optional<term_t> get_term_by_name(std::string const& name);

    /*
     * term queries
     */

    [[nodiscard]] type_t get_type(term_t term) const;

    [[nodiscard]] std::span<const term_t> get_args(term_t term) const;

    [[nodiscard]] Kind get_kind(term_t term) const;

    [[nodiscard]] int32_t index_of(term_t term) const;

    [[nodiscard]] term_t positive_term(term_t) const;

    [[nodiscard]] bool is_negated(term_t) const;

    [[nodiscard]] Rational const& arithmetic_constant_value(term_t) const;

    [[nodiscard]] bool is_arithmetic_constant(term_t t) const;

    [[nodiscard]] bool is_uninterpreted_constant(term_t) const;

    [[nodiscard]] bool is_arithmetic_product(term_t) const;

    [[nodiscard]] bool is_arithmetic_polynomial(term_t) const;

    [[nodiscard]] bool is_ite(term_t) const;

    [[nodiscard]] term_t var_of_product(term_t arithmetic_product) const;

    [[nodiscard]] Rational const& coeff_of_product(term_t arithmetic_product) const;

private:
    term_t poly_to_term(poly_t const& poly);
    poly_t term_to_poly(term_t term);

    term_t mk_bool_ite(term_t i, term_t t, term_t e);
    term_t mk_arithmetic_ite(term_t i, term_t t, term_t e);

    term_t direct_arithmetic_binary_equality(term_t t1, term_t t2);

    // Helper method for polynomials, determines if a term can be treated as a variable
    // This includes variables (KIND::UNINTERPRETED_TERM) and ITEs
    [[nodiscard]] bool is_var_like(term_t t) const;

};
} // namespace perun::terms

#endif // PERUN_TERM_MANAGER_H
