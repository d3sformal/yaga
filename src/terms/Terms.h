#ifndef PERUN_TERMS_H
#define PERUN_TERMS_H

#include <memory>
#include <optional>
#include <span>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "Rational.h"
#include "Term_hash_table.h"
#include "Term_types.h"

namespace perun::terms {

/**
 * Term descriptor contains additional information for different kinds of terms.
 *
 * Each kind uses a specialized subclass of this base class.
 */
struct term_descriptor_t
{
    virtual ~term_descriptor_t() = default;
};

/**
 * A term descriptor for any composite term, i.e., a term with an operator and arguments.
 * It stores the arguments of the composite term.
 *
 */
class composite_term_descriptor_t : public term_descriptor_t {
    std::vector<term_t> m_args;

    explicit composite_term_descriptor_t(std::span<term_t> args);

public:
    [[nodiscard]] std::size_t size() const noexcept { return m_args.size(); }
    [[nodiscard]] std::span<term_t const> args() const noexcept { return m_args; }

    static std::unique_ptr<composite_term_descriptor_t> make(std::span<term_t> args);
};

/**
 * A descriptor for terms representing rational numbers.
 * It stores the rational value of the corresponding term.
 */
class rational_term_descriptor_t : public term_descriptor_t {
    Rational m_value;

    explicit rational_term_descriptor_t(Rational const& val) : m_value(val) {}

public:
    static std::unique_ptr<rational_term_descriptor_t> make(Rational const& val);

    [[nodiscard]] Rational const& value() const { return m_value; }
};

/**
 * A descriptor for terms representing constant of a finite type.
 */
class constant_term_descriptor_t : public term_descriptor_t {
    int32_t m_index;

    explicit constant_term_descriptor_t(int32_t index) : m_index(index) {}

public:
    static std::unique_ptr<constant_term_descriptor_t> make(int32_t index);

    [[nodiscard]] int32_t index() const { return m_index; }
};


/*
 * Helper methods for simple queries on term handles
 */

/**
 * @param t term
 * @return index of the underlying term in the term table (same for the positive and negative terms)
 */
inline constexpr int32_t index_of(term_t t) { return t.x >> 1; }

/**
 * @param t term
 * @return Whether this handle represents negated term
 */
inline constexpr uint32_t is_negated(term_t t) { return ((uint32_t)t.x) & 1; }

/**
 * @param t term
 * @return Term handle representing the negation of the term
 */
inline constexpr term_t opposite_term(term_t t) { return term_t{t.x ^ 1}; }

/**
 * @param i index in the term table
 * @return Positive version of the term with index i
 */
inline constexpr term_t positive_term(int32_t i) { return term_t{i << 1}; }

/**
 * @param t term
 * @return Positive version of the term
 */
inline constexpr term_t positive_term(term_t t) { return positive_term(index_of(t)); }

/**
 * @param i index in the term table
 * @return Negative version of the term with index i
 */
inline constexpr term_t negative_term(int32_t i) { return term_t{(i << 1) | 1}; }

/**
 * @param t term
 * @return Negative version of the term
 */
inline constexpr term_t negative_term(term_t t) { return negative_term(index_of(t)); }

/**
 * Term table is the main internal data structure for creating, storing and querying terms.
 *
 * Terms are internally stored in a table (vector). To avoid duplication, hash consing is used.
 * Term_table cooperates with Term_hash_table on creating new terms; the process goes through
 * the hash table to check if the term we want to create already exists.
 * If it does, the existing terms is returned instead of creating new one.
 */
class Term_table {
    /**
     * Internal representation of terms.
     *
     * It stores the kind of the term, its type and additional information in the term descriptor.
     */
    struct Term {
        Kind kind;
        type_t type;
        std::unique_ptr<term_descriptor_t> descriptor;
    };

    using inner_table_t = std::vector<Term>;
    using symbol_table_t = std::unordered_map<std::string, term_t>;
    using name_table_t = std::unordered_map<term_t, std::string>;

    // The actual storage of terms
    inner_table_t inner_table;

    // Hash table to implement hash consing
    Term_hash_table known_terms;

    // Maps names to terms
    symbol_table_t symbol_table;

    // Maps terms to their canonical names
    name_table_t name_table;

    // Necessary initialization
    void add_primitive_terms();

    // Actual construction of terms. These methods always create new terms!
    friend class Term_hash_table;
    term_t construct_composite(Kind kind, type_t type, std::span<term_t> args);
    term_t construct_rational(Kind kind, type_t type, Rational const & value);
    term_t construct_constant(Kind kind, type_t type, int32_t index);
    term_t construct_uninterpreted_constant(type_t type);
public:
    Term_table();

    /**
     * Associate a term with the given name
     */
    void set_term_name(term_t, std::string const&);

    /**
     * Retrieves the term associated to the @p name
     *
     * @return Term associated with the name, or nothing if no term is associated with the name
     */
    std::optional<term_t> get_term_by_name(std::string const& name) const;

    /**
     *
     * @return Kind of the given term
     */
    Kind get_kind(term_t) const;

    /**
     *
     * @return Type of the given term
     */
    type_t get_type(term_t) const;

    /**
     *
     * @return The term descriptor of the given term
     */
    term_descriptor_t const& get_descriptor(term_t) const;


    /**
     * Retrieves the arguments (children) of the given term
     * @return the arguments of the given term
     */
    std::span<const term_t> get_args(term_t) const;

    /**
     * @param args Arguments of the disjunction
     * @return Term handle to the disjunction of the given terms
     */
    term_t or_term(std::span<term_t> args);

    /**
     * @param tau type of the constant, must be a finite type
     * @param index index of the constant in its type
     * @return Constant of the given type and index
     */
    term_t constant_term(type_t tau, int32_t index);

    /*
     *
     */

    /**
     * Creates new uninterpreted constant of the given type ("free variables" in formulae)
     * @param tau
     * @return new uninterpreted constant of the given type
     */
    term_t new_uninterpreted_constant(type_t tau);

    /**
     * Returns a term representing the given rational value
     * @param value the value of the term
     * @return Term representing the given rational value
     */
    term_t arithmetic_constant(Rational const & value);

    /**
     * Returns a product term (monomial) of the given variable term and its rational coefficient
     *
     * @param coeff the coefficient of the variable
     * @param var the variable term
     * @return product term
     */
    term_t arithmetic_product(Rational const& coeff, term_t var);

    /**
     * Returns a polynomial term (sum of monomials)
     * @param monomials monomials of the polynomial
     * @return the polynomial term
     */
    term_t arithmetic_polynomial(std::span<term_t> monomials);

    /*
     *
     */

    /**
     * Returns atom "t >= 0" for an arithmetic term t
     * @param t arithmetic term (left-hand side of the inequality)
     * @return the corresponding inequality term
     */
    term_t arithmetic_geq_zero(term_t t);

    /*
     * Atom (t = 0) for an arithmetic term t
     */

    /**
     * Returns atom "t = 0" for an arithmetic term t
     * @param t arithmetic term (left-hand side of the equality)
     * @return the corresponding equality term
     */
    term_t arithmetic_eq_zero(term_t t);

    /*
     * Atom (t1 = t2) for arithmetic terms t1, t2
     */

    /**
     * Returns an equality between two arithmetic terms.
     *
     * Used to to represent simple equalities when variable is equal to constant or another variable.
     * "x = c" is better representation, e.g., for substitutions, instead of "x - c = 0".
     *
     * @param t1 LHS of the equality
     * @param t2 RHS of the equality
     * @return the equality "t1 = t2"
     */
    term_t arithmetic_binary_eq(term_t t1, term_t t2);

    /**
     * Returns an if-the-else (ITE) term
     *
     * @param c the condition of the ITE
     * @param t the then term of the ITE
     * @param e the else term of the ITE
     * @return ITE(c,t,e)
     */
    term_t arithmetic_ite(term_t c, term_t t, term_t e);

    /*
     * Queries on terms
     */

    bool is_arithmetic_constant(term_t t) const;

    bool is_uninterpreted_constant(term_t) const;

    bool is_arithmetic_product(term_t) const;

    bool is_arithmetic_polynomial(term_t) const;

    bool is_ite(term_t) const;

    Rational const& arithmetic_constant_value(term_t) const;

    /**
     * Returns the variable "x" from a product term "c * x"
     *
     * @param arithmetic_product product term
     * @return variable of the arithmetic product term
     */
    term_t var_of_product(term_t arithmetic_product) const;

    /**
     * Returns the coefficient "c" from a product term "c * x"
     * The coefficient is returned as the rational number, not the corresponding term
     *
     * @param arithmetic_product product term
     * @return coefficient of the arithmetic product term
     */
    Rational const& coeff_of_product(term_t arithmetic_product) const;


    /**
     * Returns the list of monomial terms of the polynomial term
     *
     * @param arithmetic_polynomial polynomial term
     * @return The list of monomials of the polynomial
     */
    std::span<const term_t> monomials_of(term_t arithmetic_polynomial) const;

};

} // namespace perun::terms
#endif // PERUN_TERMS_H
