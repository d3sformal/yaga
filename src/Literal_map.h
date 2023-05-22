#ifndef YAGA_LITERAL_MAP_H_
#define YAGA_LITERAL_MAP_H_

#include <vector>

#include "Literal.h"

namespace yaga {

/** Dense map from literals to values of type T
 *
 * @tparam T value type
 */
template <typename T> class Literal_map {
public:
    using Reference = typename std::vector<T>::reference;
    using Const_reference = typename std::vector<T>::const_reference;

    /** Create an empty map
     */
    inline Literal_map() {}

    /** Create a map with @p num_vars boolean variables
     *
     * @param num_vars number of boolean variables
     */
    inline explicit Literal_map(std::size_t num_vars) : values(num_vars * 2) {}

    /** Create a map with @p num_vars boolean variables where each literal is
     * mapped to @p value
     *
     * @param num_vars number of boolean variables
     * @param value value that will be copied to all literals
     */
    inline Literal_map(std::size_t num_vars, T value) : values(num_vars * 2, value) {}

    // non-copyable
    inline Literal_map(Literal_map const&) = delete;
    inline Literal_map& operator=(Literal_map const&) = delete;

    // movable
    inline Literal_map(Literal_map&&) = default;
    inline Literal_map& operator=(Literal_map&&) = default;

    /** Get value of @p lit
     *
     * @param lit literal
     * @return reference to a value mapped to @p lit
     */
    inline Reference operator[](Literal lit) { return values[index(lit)]; }

    /** Get value of @p lit
     *
     * @param lit literal
     * @return reference to a value mapped to @p lit
     */
    inline Const_reference operator[](Literal lit) const { return values[index(lit)]; }

    /** Map all literals to a copy of @p value
     *
     * @param value value copied to all literals
     */
    inline void assign(T value) { values.assign(values.size(), value); }

    /** Begin iterator of the range of values in this map in an unspecified
     * order.
     *
     * @return begin iterator of values in this map
     */
    inline auto begin() { return values.begin(); }

    /** Begin iterator of the range of values in this map in an unspecified
     * order.
     *
     * @return begin iterator of values in this map
     */
    inline auto begin() const { return values.begin(); }

    /** End iterator of the range of values in this map in an unspecified order.
     *
     * @return end iterator of values in this map
     */
    inline auto end() { return values.end(); }

    /** End iterator of the range of values in this map in an unspecified order.
     *
     * @return end iterator of values in this map
     */
    inline auto end() const { return values.end(); }

    /** Change the number of boolean variables
     *
     * @param num_vars new number of boolean variables
     */
    inline void resize(std::size_t num_vars) { values.resize(num_vars * 2); }

    /** Get number of boolean variables
     *
     * @return number of boolean variables
     */
    inline int num_vars() const { return values.size() / 2; }

private:
    std::vector<T> values;

    // Map a literal to index for `values`
    inline int index(Literal lit) const
    {
        return lit.var().ord() * 2 + static_cast<int>(lit.is_negation());
    }
};

} // namespace yaga

#endif // YAGA_LITERAL_MAP_H_