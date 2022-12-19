#ifndef PERUN_MODEL_H_
#define PERUN_MODEL_H_

#include <vector>
#include <optional>

#include "Literal.h"
#include "Clause.h"

namespace perun {

class Model_base {
public:
    virtual ~Model_base() = default;

    // check if a variable is defined
    inline bool is_defined(int ord) const { return defined_[ord]; }
    // make a variable undefined in this model
    inline void clear(int ord) { defined_[ord] = false; }
    // make all variables undefined in this model
    inline void clear() { defined_.assign(defined_.size(), false); }
    // get number of variables in this model
    inline std::size_t num_vars() const { return defined_.size(); }

    /** Change number of variables 
     * 
     * @param num_vars new number of variables 
     */
    virtual void resize(int num_vars) = 0;
protected:
    // bitset which represents subset of defined variables
    std::vector<bool> defined_;
};

/** Partial model.
 * 
 * Map from variable ordinal to its value and subset of defined variables.
 * 
 * @tparam T type of variables stored in the model
 */
template<typename T>
class Model final : public Model_base {
public:
    using Value_type = T;
    using Reference = typename std::vector<Value_type>::reference;
    using Const_reference = typename std::vector<Value_type>::const_reference;

    virtual ~Model() = default;

    void resize(int num_vars) override
    {
        values_.resize(num_vars, Value_type{});
        defined_.resize(num_vars, false);
    }

    // get value regardless if `is_defined()`
    inline Const_reference value(int ord) const { return values_[ord]; }

    // set a new value for a variable and make it defined
    inline void set_value(int ord, Value_type val) 
    { 
        values_[ord] = val; 
        defined_[ord] = true;
    }

private:
    // map variable ordinal -> value
    std::vector<Value_type> values_;
};

/** Evaluate @p lit in @p model
 * 
 * @param model partial model
 * @param lit checked literal
 * @return true if @p lit is true in @p model 
 * @return false if @p lit is false in @p model
 * @return none if @p lit is undefined in @p model
 */
inline std::optional<bool> eval(const Model<bool>& model, Literal lit)
{
    return model.is_defined(lit.var().ord()) ? 
                model.value(lit.var().ord()) == !lit.is_negation() : 
                std::optional<bool>{};
}

/** Evaluate @p clause in @p model
 * 
 * @param model partial model
 * @param clause checked clause
 * @return true if there is at least one true literal in @p clause 
 * @return false if all literals in @p clause are false
 * @return none otherwise 
 */
inline std::optional<bool> eval(const Model<bool>& model, const Clause& clause)
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

}

#endif // PERUN_MODEL_H_