#ifndef PERUN_LITERAL_H_
#define PERUN_LITERAL_H_

#include <cmath>
#include <ostream>
#include <functional>

#include "Variable.h"

namespace perun {

struct Literal_hash;

/** Boolean variable or its negation.
 */
class Literal {
public:
    friend class Literal_hash;

    // default-constructible
    inline Literal() {}

    // copyable
    inline Literal(const Literal&) = default;
    inline Literal& operator=(const Literal&) = default;

    // comparison
    inline bool operator==(const Literal& other) const { return var_ == other.var_; }
    inline bool operator!=(const Literal& other) const { return !operator==(other); }

    /** Construct a literal from boolean variable ordinal number
     * 
     * @param var_ord 0-based ordinal number of a boolean variable
     */
    inline explicit Literal(int var_ord) : var_(var_ord + 1) {} // + 1 so that we can represent 0 and its negation

    /** Get negation of this literal
     * 
     * @return new literal which represents negation of this literal
     */
    inline Literal negate() const 
    {
        Literal r;
        r.var_ = -var_;
        return r;
    }

    // get representation of the boolean variable used in this literal
    inline Variable var() const { return {std::abs(var_) - 1, Variable::boolean}; }

    // check if variable `var()` is negated in this literal
    inline bool is_negation() const { return var_ < 0; }
private:
    // `variable ordinal + 1`, negative value indicates negative literal
    int var_;
};

inline std::ostream& operator<<(std::ostream& out, Literal lit)
{
    if (lit.is_negation())
    {
        out << "not(";
    }
    out << lit.var();
    if (lit.is_negation())
    {
        out << ")";
    }
    return out;
}

class Literal_hash {
public:
    // compute hash of a literal
    inline std::size_t operator()(Literal l) const { return hash_(l.var_); }
private:
    std::hash<int> hash_;
};

}

#endif // PERUN_LITERAL_H_