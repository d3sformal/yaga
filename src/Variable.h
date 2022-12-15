#ifndef PERUN_VARIABLE_H_
#define PERUN_VARIABLE_H_

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
    inline Variable(int ord, Type type) : ord_(ord), type_(type) {}

    // comparable
    inline bool operator==(const Variable& other) const { return type_ == other.type_ && ord_ == other.ord_; }
    inline bool operator!=(const Variable& other) const { return !operator==(other); }

    // get 0-based ordinal number of this variable
    inline int ord() const { return ord_; }
    // get type of this variable
    inline Type type() const { return type_; }
private:
    // 0-based ordinal number of this variable
    int ord_;
    // type of this variable
    Type type_;
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

}

#endif // PERUN_VARIABLE_H_