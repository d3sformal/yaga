#ifndef YAGA_VARIABLE_H
#define YAGA_VARIABLE_H

#include <ostream>

namespace yaga {

class Variable {
public:
    enum Type {
        boolean = 0,
        rational = 1,
    };

    // default constructible
    inline Variable() {}

    /** Create a new variable representation
     *
     * @param ord 0-based ordinal number of this variable
     * @param type type of this variable
     */
    inline Variable(int ord, Type type) : number(ord), var_type(type) {}

    /** Check whether this variable is equal to @p other
     * 
     * @param other other variable
     * @return true if this variable is equal to @p other
     */
    inline bool operator==(Variable const& other) const
    {
        return var_type == other.var_type && number == other.number;
    }

    /** Check whether this variable is equal to @p other
     * 
     * @param other other variable
     * @return true if this variable is not equal to @p other
     */
    inline bool operator!=(Variable const& other) const { return !operator==(other); }

    /** Three-way comparison of two variables
     * 
     * @param other other variable
     * @return value < 0 if this variable is less than @p other
     * @return value > 0 if this variable is greater than @p other
     * @return value == 0 if this variable is equal to @p other
     */
    inline int operator<=>(Variable const& other) const
    {
        if (type() < other.type())
        {
            return -1;
        }
        else if (type() > other.type())
        {
            return 1;
        }
        else // type() == other.type()
        {
            return ord() - other.ord();
        }
    }

    // get 0-based ordinal number of this variable
    inline int ord() const { return number; }
    // get type of this variable
    inline Type type() const { return var_type; }

private:
    // 0-based ordinal number of this variable
    int number;
    // type of this variable
    Type var_type;
};

struct Variable_hash {
    /** Compute hash of @p var
     *
     * @param var
     * @return hash of @p var
     */
    inline std::size_t operator()(Variable var) const
    {
        auto var_ord = static_cast<std::int64_t>(var.ord());
        auto type = static_cast<std::int64_t>(var.type());
        return std::hash<std::int64_t>{}((type << 32) | var_ord);
    }
};

inline std::ostream& operator<<(std::ostream& out, Variable var)
{
    if (var.type() == Variable::boolean)
    {
        out << "boolean(";
    }
    else if (var.type() == Variable::rational)
    {
        out << "rational(";
    }
    else
    {
        out << "type=" << var.type() << "(";
    }
    out << var.ord() << ")";
    return out;
}

} // namespace yaga

#endif // YAGA_VARIABLE_H