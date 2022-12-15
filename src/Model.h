#ifndef PERUN_MODEL_H_
#define PERUN_MODEL_H_

#include <vector>

namespace perun {

class Model_base {
public:
    virtual ~Model_base() = default;

    // check if a variable is defined
    inline bool is_defined(int ord) const { return 0 <= ord && ord < static_cast<int>(defined_.size()) && defined_[ord]; }
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
 * Basically a map from variable ordinal to its value and subset of defined variables.
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

    // get value regardless if `is_defined()`
    inline void set_value(int ord, Value_type val) 
    { 
        values_[ord] = val; 
        defined_[ord] = true;
    }

private:
    // map variable ordinal -> value
    std::vector<Value_type> values_;
};

}

#endif // PERUN_MODEL_H_