#ifndef PERUN_TERMS_H
#define PERUN_TERMS_H

#include <memory>
#include <span>
#include <unordered_set>
#include <vector>

#include "Rational.h"
#include "Term_hash_table.h"
#include "Term_types.h"

namespace perun::terms {


class term_descriptor_t {};

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
inline constexpr int32_t index_of(term_t t) { return t >> 1; }

inline constexpr uint32_t polarity_of(term_t t) { return ((uint32_t)t) & 1; }

inline constexpr term_t opposite_term(term_t t) { return t ^ 1; }

inline constexpr term_t true_term = 2;
inline constexpr term_t false_term = 3;
inline constexpr term_t zero_term = 4;

inline constexpr term_t positive_term(int32_t i) { return (i << 1); }
inline constexpr term_t negative_term(int32_t i) { return (i << 1) | 1; }


class Term_table {
    struct Term {
        Kind kind;
        type_t type;
        std::unique_ptr<term_descriptor_t> descriptor;
    };

    using inner_table_t = std::vector<Term>;

    inner_table_t inner_table;

    Term_hash_table known_terms;

    // Necessary initialization
    void add_primitive_terms();

public:
    Term_table();

    Kind get_kind(term_t);
    type_t get_type(term_t);
    term_descriptor_t const& get_descriptor(term_t);

    term_t construct_composite(Kind kind, type_t type, std::span<type_t> args);
    term_t construct_rational(Kind kind, type_t type, Rational const & value);
    term_t construct_constant(Kind kind, type_t type, int32_t index);
    term_t construct_uninterpreted_constant(type_t type);


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
};

} // namespace perun::terms
#endif // PERUN_TERMS_H
