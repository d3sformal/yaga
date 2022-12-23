#ifndef PERUN_VARIABLE_H
#define PERUN_VARIABLE_H

#include <ostream>

namespace perun {

class Variable {
public:
    enum Type {
        boolean = 0,
    };

    // default constructible
    inline Variable() {}

    /** Create a new variable representation
     *
     * @param ord 0-based ordinal number of this variable
     * @param type type of this variable
     */
    inline Variable(int ord, Type type) : number(ord), var_type(type) {}

    // comparable
    inline bool operator==(Variable const& other) const
    {
        return var_type == other.var_type && number == other.number;
    }
    inline bool operator!=(Variable const& other) const { return !operator==(other); }

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

inline std::ostream& operator<<(std::ostream& out, Variable var)
{
    if (var.type() == Variable::boolean)
    {
        out << "boolean(";
    }
    else
    {
        out << "type=" << var.type() << "(";
    }
    out << var.ord() << ")";
    return out;
}

} // namespace perun

#endif // PERUN_VARIABLE_H