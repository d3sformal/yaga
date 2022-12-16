#ifndef PERUN_LITERAL_MAP_H_
#define PERUN_LITERAL_MAP_H_

#include <vector>

#include "Literal.h"

namespace perun {

template<typename T>
class Literal_map
{
public:
    using Reference = typename std::vector<T>::reference;
    using Const_reference = typename std::vector<T>::const_reference;

    inline Literal_map() {}

    inline Literal_map(std::size_t size) : values_(size) {}
    inline Literal_map(std::size_t size, T value) : values_(size, value) {}

    // non-copyable
    inline Literal_map(const Literal_map&) = delete;
    inline Literal_map& operator=(const Literal_map&) = delete;

    // movable
    inline Literal_map(Literal_map&&) = default;
    inline Literal_map& operator=(Literal_map&&) = default;

    // access values in the map
    inline Reference operator[](Literal lit) { return values_[index(lit)]; }
    inline Const_reference operator[](Literal lit) const { return values_[index(lit)]; }

    // range of values in the map
    inline auto begin() { return values_.begin(); }
    inline auto begin() const { return values_.begin(); }
    inline auto end() { return values_.end(); }
    inline auto end() const { return values_.end(); }

    // change the number of variables
    inline void resize(int num_vars) { values_.resize(num_vars * 2); }
private:
    std::vector<T> values_;

    // Map a literal to index for `values_`
    inline int index(Literal lit) const 
    { 
        return lit.var().ord() * 2 + static_cast<int>(lit.is_negation()); 
    }
};

}

#endif // PERUN_LITERAL_MAP_H_