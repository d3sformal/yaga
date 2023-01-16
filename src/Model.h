#ifndef PERUN_MODEL_H
#define PERUN_MODEL_H

#include <optional>
#include <vector>

#include "Clause.h"
#include "Literal.h"

namespace perun {

class Model_base {
public:
    virtual ~Model_base() = default;

    /** Check whether a variable is defined.
     *
     * @param ord ordinal number of a variable
     * @return true iff variable @p ord is defined in this model
     */
    inline bool is_defined(int ord) const { return defined[ord]; }

    /** Make a variable undefined in this model.
     *
     * This method does not reset value of the variable.
     *
     * @param ord ordinal number of a variable
     */
    inline void clear(int ord) { defined[ord] = false; }

    /** Make all variables undefined in this model.
     *
     * This method does not reset value of any variable.
     */
    inline void clear() { defined.assign(defined.size(), false); }

    /** Get timestamp of a variable -- logical time when @p ord was assigned its most recent value
     * 
     * @param ord ordinal number of a variable
     * @return current timestamp of the value of variable @p ord
     */
    inline int timestamp(int ord) const { return ts[ord]; }

    /** Get number of variables in this model
     *
     * @return number of variables
     */
    inline std::size_t num_vars() const { return defined.size(); }

    /** Change number of variables
     *
     * @param num_vars new number of variables
     */
    virtual void resize(int num_vars) = 0;

protected:
    // bitset which represents subset of defined variables
    std::vector<bool> defined;
    // map variable ordinal -> timestamp
    std::vector<int> ts;
    // current timestamp of values in this model
    int global_ts = 0;
};

/** Partial model.
 *
 * Map from variable ordinal to its value and subset of defined variables.
 *
 * @tparam T type of variables stored in the model
 */
template <typename T> class Model final : public Model_base {
public:
    using Value_type = T;
    using Reference = typename std::vector<Value_type>::reference;
    using Const_reference = typename std::vector<Value_type>::const_reference;

    virtual ~Model() = default;

    /** Change number of variables
     *
     * @param num_vars new number of variables
     */
    void resize(int num_vars) override
    {
        values.resize(num_vars, Value_type{});
        defined.resize(num_vars, false);
        ts.resize(num_vars, -1);
    }

    /** Get value of a variable regardless if `is_defined()` is true.
     *
     * @param ord ordinal number of a variable
     * @return value of the variable in this model
     */
    inline Const_reference value(int ord) const { return values[ord]; }

    /** Set a new value for a variable and make it defined.
     *
     * @param ord ordinal number of a variable
     * @param val new value of variable @p ord
     */
    inline void set_value(int ord, Value_type val)
    {
        values[ord] = val;
        defined[ord] = true;
        ts[ord] = global_ts++;
    }

private:
    // map variable ordinal -> value
    std::vector<Value_type> values;
};

/** Evaluate @p lit in @p model
 *
 * @param model partial model
 * @param lit checked literal
 * @return true if @p lit is true in @p model
 * @return false if @p lit is false in @p model
 * @return none if @p lit is undefined in @p model
 */
inline std::optional<bool> eval(Model<bool> const& model, Literal lit)
{
    return model.is_defined(lit.var().ord()) ? model.value(lit.var().ord()) == !lit.is_negation()
                                             : std::optional<bool>{};
}

/** Evaluate @p clause in @p model
 *
 * @param model partial model
 * @param clause checked clause
 * @return true if there is at least one true literal in @p clause
 * @return false if all literals in @p clause are false
 * @return none otherwise
 */
inline std::optional<bool> eval(Model<bool> const& model, Clause const& clause)
{
    int num_assigned = 0;
    for (auto lit : clause)
    {
        auto val = eval(model, lit);
        if (val == true)
        {
            return true;
        }

        if (val.has_value())
        {
            ++num_assigned;
        }
    }
    return num_assigned >= static_cast<int>(clause.size()) ? false : std::optional<bool>{};
}

} // namespace perun

#endif // PERUN_MODEL_H