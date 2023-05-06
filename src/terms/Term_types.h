#ifndef PERUN_TERM_TYPES_H
#define PERUN_TERM_TYPES_H

#include <cstdint>
#include <functional>

namespace perun::terms {

/**
 * A type representing terms which serves as a lightweight handle.
 * To get information about the underlying term, the corresponding term table must be queried
 * using this handle.
 *
 * The handle is represented with a 32-bit integer.
 * As an optimization, the least significant bit defines the polarity of the term.
 * Only boolean terms could possibly have thi bit set to 1 (which represents the negation of the
 * underlying term). The advantage is that negative terms do not have to stored explicitly
 * in the term table.
 *
 */
struct term_t {
    int32_t x;
    static const term_t Undef;

    friend auto operator<=>(term_t, term_t) = default;
};

using type_t = int32_t;

namespace types {
// Predefined types
static constexpr type_t null_type = -1;
static constexpr type_t bool_type = 0;
static constexpr type_t real_type = 1;
}

// Useful term constants
inline constexpr term_t null_term { -1 };
inline constexpr term_t true_term { 2 };
inline constexpr term_t false_term { 3 };
inline constexpr term_t zero_term { 4 };

inline constexpr term_t term_t::Undef = null_term;


/**
 * An enumeration of different kinds of terms
 */
enum class Kind {
    /*
     * Special marks
     */
    UNUSED_TERM,   // deleted term
    RESERVED_TERM, // mark for term indices that can't be used

    /*
     * Constants
     */
    CONSTANT_TERM,  // constant of uninterpreted/scalar/boolean types
    ARITH_CONSTANT, // rational constant

    /*
     * Non-constant, atomic terms
     */
    UNINTERPRETED_TERM, // (i.e., global variables, can't be bound).

    /*
     * Composites
     */
    ITE_TERM,      // if-then-else
    APP_TERM,      // application of an uninterpreted function
    EQ_TERM,       // equality
    DISTINCT_TERM, // distinct t_1 ... t_n
    OR_TERM,       // n-ary OR
    XOR_TERM,      // n-ary XOR

    ARITH_EQ_ATOM, // atom t == 0
    ARITH_GE_ATOM, // atom t >= 0
    ARITH_BINEQ_ATOM,   // equality: (t1 == t2)  (between two arithmetic terms, LHS is always a variable!)

    // Polynomials
    ARITH_PRODUCT, // arithmetic product, only linear for now
    ARITH_POLY, // polynomial with rational coefficients (more than one (product) monomial)

};

}

namespace std {
template <> struct hash<perun::terms::term_t>
{
    size_t operator()(perun::terms::term_t t) const
    {
        return std::hash<int32_t>()(t.x);
    }
};
}

#endif // PERUN_TERM_TYPES_H
