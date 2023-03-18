#ifndef PERUN_TERMS_H
#define PERUN_TERMS_H

#include <memory>
#include <span>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "Rational.h"
#include "Term_hash_table.h"
#include "Term_types.h"

namespace perun::terms {


struct term_descriptor_t
{
    virtual ~term_descriptor_t() = default;
};

class composite_term_descriptor_t : public term_descriptor_t {
    std::vector<term_t> m_args;

    explicit composite_term_descriptor_t(std::span<term_t> args);

public:
    [[nodiscard]] std::size_t size() const noexcept { return m_args.size(); }
    [[nodiscard]] std::span<term_t const> args() const noexcept { return m_args; }

    static std::unique_ptr<composite_term_descriptor_t> make(std::span<term_t> args);
};

class rational_term_descriptor_t : public term_descriptor_t {
    Rational m_value;

    explicit rational_term_descriptor_t(Rational const& val) : m_value(val) {}

public:
    static std::unique_ptr<rational_term_descriptor_t> make(Rational const& val);

    [[nodiscard]] Rational const& value() const { return m_value; }
};

class constant_term_descriptor_t : public term_descriptor_t {
    int32_t m_index;

    explicit constant_term_descriptor_t(int32_t index) : m_index(index) {}

public:
    static std::unique_ptr<constant_term_descriptor_t> make(int32_t index);

    [[nodiscard]] int32_t index() const { return m_index; }
};


/*
 * Extract term and polarity bit
 */
inline constexpr int32_t index_of(term_t t) { return t.x >> 1; }

inline constexpr uint32_t polarity_of(term_t t) { return ((uint32_t)t.x) & 1; }

inline constexpr term_t opposite_term(term_t t) { return term_t{t.x ^ 1}; }

inline constexpr term_t positive_term(int32_t i) { return term_t{i << 1}; }
inline constexpr term_t negative_term(int32_t i) { return term_t{(i << 1) | 1}; }


class Term_table {
    struct Term {
        Kind kind;
        type_t type;
        std::unique_ptr<term_descriptor_t> descriptor;
    };

    using inner_table_t = std::vector<Term>;
    using symbol_table_t = std::unordered_map<std::string, term_t>; // Maps name to term
    using name_table_t = std::unordered_map<term_t, std::string>; // Maps term to a canonical name

    inner_table_t inner_table;

    Term_hash_table known_terms;

    symbol_table_t symbol_table;
    name_table_t name_table;

    // Necessary initialization
    void add_primitive_terms();

public:
    Term_table();

    void set_term_name(term_t, std::string const&);
    term_t get_term_by_name(std::string const&) const;

    Kind get_kind(term_t) const;
    type_t get_type(term_t) const;
    term_descriptor_t const& get_descriptor(term_t) const;

    term_t construct_composite(Kind kind, type_t type, std::span<term_t> args);
    term_t construct_rational(Kind kind, type_t type, Rational const & value);
    term_t construct_constant(Kind kind, type_t type, int32_t index);
    term_t construct_uninterpreted_constant(type_t type);


    std::span<const term_t> get_args(term_t) const;

    term_t or_term(std::span<term_t> args);

    /*
     * Constant of the given type and index (type must be scalar or uninterpreted)
     */
    term_t constant_term(type_t tau, int32_t index);

    /*
     * Uninterpreted constant of the given type ("free variables" in formulae)
     */
    term_t new_uninterpreted_constant(type_t tau);

    term_t arithmetic_constant(Rational const & value);

    term_t arithmetic_product(Rational const& coeff, term_t var);

    term_t arithmetic_polynomial(std::span<term_t> monomials);

    /*
     * Atom (t >= 0) for an arithmetic term t
     */
    term_t arithmetic_geq_zero(term_t t);

    /*
     * Atom (t = 0) for an arithmetic term t
     */
    term_t arithmetic_eq_zero(term_t t);

    /*
     * Atom (t1 = t2) for arithmetic terms t1, t2
     */
    term_t arithmetic_binary_eq(term_t t1, term_t t2);

    /*
     * Queries on terms
     */

    bool is_arithmetic_constant(term_t t) const;

    bool is_uninterpreted_constant(term_t) const;

    bool is_arithmetic_product(term_t) const;

    bool is_arithmetic_polynomial(term_t) const;

    Rational const& arithmetic_constant_value(term_t) const;

    term_t var_of_product(term_t) const;

    Rational const& coeff_of_product(term_t) const;

    std::span<const term_t> monomials_of(term_t) const;

};

} // namespace perun::terms
#endif // PERUN_TERMS_H
