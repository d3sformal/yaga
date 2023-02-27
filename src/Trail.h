#ifndef PERUN_TRAIL_H_
#define PERUN_TRAIL_H_

#include <cassert>
#include <memory>
#include <optional>
#include <tuple>
#include <vector>

#include "Clause.h"
#include "Literal.h"
#include "Model.h"
#include "Variable.h"

namespace perun {

class Trail {
public:
    struct Assignment {
        // assigned variable
        Variable var;
        // reason clause for the assignment or nullptr if this is a
        // decision/semantic propagation
        Clause* reason;

        // convert to pair so we can tie the properties
        inline operator std::pair<Variable, Clause*>() const { return {var, reason}; }
    };

    inline Trail() : assigned_stack(1) {}

    // get current decision level
    inline int decision_level() const { return static_cast<int>(assigned_stack.size()) - 1; }

    /** Get decision level of a variable
     *
     * @param var queried variable
     * @return level at which @p var was decided/propagated or non if @p var
     * does not have a value in this trail
     */
    inline std::optional<int> decision_level(Variable var) const
    {
        return var_level[var.type()][var.ord()] < 0 ? std::optional<int>{}
                                                    : var_level[var.type()][var.ord()];
    }

    /** Get reason why @p var was propagated
     *
     * @param var queried variable
     * @return reason clause which lead to propagation of @p var or nullptr if
     * there is no such clause in this trail
     */
    inline Clause const* reason(Variable var) const { return var_reason[var.type()][var.ord()]; }

    /** Get a list of variables together with reason clause assigned at decision
     * level @p level
     *
     * @param level decision level
     * @return list of variables assigned at decision level @p level
     */
    inline auto const& assigned(int level) const { return assigned_stack[level]; }

    /** Create a new model for variables of type @p type in this trail
     *
     * @tparam T value type of variables of type @p type
     * @param type type of variables
     * @param num_vars number of variables of the type @p type
     * @return reference to the model in this trail
     */
    template <typename T> inline Model<T>& set_model(Variable::Type type, int num_vars)
    {
        if (type >= var_models.size())
        {
            var_models.resize(static_cast<int>(type) + 1);
        }

        // create and add model for variables of this type
        auto model = std::make_unique<Model<T>>();
        auto ptr = model.get();
        var_models[type] = std::move(model);

        // set number of variables of this type
        resize(type, num_vars);
        return *ptr;
    }

    /** Get partial model for variable @p type
     *
     * @tparam T type of values in the model
     * @param type type of variables
     * @return partial model for @p type managed by this trail
     */
    template <typename T> inline Model<T>& model(Variable::Type type)
    {
        return dynamic_cast<Model<T>&>(*var_models[type]);
    }

    template <typename T> inline Model<T> const& model(Variable::Type type) const
    {
        return dynamic_cast<Model<T>&>(*var_models[type]);
    }

    // get model for each type in this trail
    inline auto models() const
    {
        int type = 0;
        std::vector<std::pair<Variable::Type, Model_base const*>> models;
        for (auto const& model : var_models)
        {
            if (model != nullptr)
            {
                models.emplace_back(std::pair{static_cast<Variable::Type>(type), model.get()});
            }
            ++type;
        }
        return models;
    }

    /** Change the number of variables of type @p type
     *
     * @param type type of variables
     * @param num_vars new number of variables of type @p type
     */
    inline void resize(Variable::Type type, int num_vars)
    {
        assert(type < var_models.size());

        var_models[type]->resize(num_vars);
        int num_types = std::max<int>(static_cast<int>(var_reason.size()), type + 1);
        var_reason.resize(num_types, std::vector<Clause const*>(num_vars, nullptr));
        var_level.resize(num_types, std::vector<int>(num_vars, unassigned));
        var_reason[type].resize(num_vars, nullptr);
        var_level[type].resize(num_vars, unassigned);
    }

    /** Decide variable at a new decision level.
     *
     * The caller is responsible for setting new @p var value in the appropriate
     * `model()`.
     *
     * @param var newly decided variable
     */
    inline void decide(Variable var)
    {
        assert(var.type() < var_level.size());
        assert(var.type() < var_reason.size());
        assert(var.type() < var_models.size());

        assigned_stack.emplace_back(std::vector<Assignment>{Assignment{var, /*reason=*/nullptr}});
        var_level[var.type()][var.ord()] = decision_level();
        var_reason[var.type()][var.ord()] = nullptr;

        recent_variables.clear();
        recent_variables.push_back(Assignment{var, /*reason=*/nullptr});
    }

    /** Propagate variable @p var due to clause @p reason at decision level @p
     * level
     *
     * @param var variable to propagate
     * @param reason reason clause for the propagation or `nullptr` if this is a
     * semantic propagation
     * @param level decision level at which @p var is propagated (in `[0,
     * decision_level()]` range)
     */
    inline void propagate(Variable var, Clause* reason, int level)
    {
        assert(0 <= level && level <= decision_level());
        assert(var.type() < var_level.size());
        assert(var.type() < var_reason.size());
        assert(var.type() < var_models.size());

        assigned_stack[level].push_back(Assignment{var, reason});
        var_level[var.type()][var.ord()] = level;
        var_reason[var.type()][var.ord()] = reason;

        recent_variables.push_back(Assignment{var, reason});
    }

    /** Make all variables decided or propagated at levels > @p level
     * unassigned.
     *
     * @param level decision level to backtrack to
     */
    inline void backtrack(int level)
    {
        assert(0 <= level);
        recent_variables.clear();

        for (; decision_level() > level; assigned_stack.pop_back())
        {
            for (auto [var, _] : assigned_stack[decision_level()])
            {
                var_level[var.type()][var.ord()] = unassigned;
                var_reason[var.type()][var.ord()] = nullptr;
                var_models[var.type()]->clear(var.ord());
            }
        }

        assert(level == decision_level());
    }

    /** Check if some variable is assigned.
     *
     * @return true iff no variable is assigned in this trail
     */
    inline bool empty() const { return assigned_stack.size() == 1 && assigned_stack[0].empty(); }

    /** Make all variables unassigned.
     */
    inline void clear()
    {
        for (auto& list : var_reason)
        {
            for (auto& value : list)
            {
                value = nullptr;
            }
        }

        for (auto& list : var_level)
        {
            for (auto& value : list)
            {
                value = unassigned;
            }
        }

        for (auto& model : var_models)
        {
            if (model)
            {
                model->clear();
            }
        }

        assigned_stack.clear();
        assigned_stack.emplace_back();
        recent_variables.clear();
    }

    /** Get recently assigned variables.
     * 
     * Variables assigned between the last `backtrack()`, `clear()`, or `decide()`
     * call and this call. The decided variable is also part of recent variables.
     * 
     * @return range of recently assigned variables
     */
    inline auto const& recent() const { return recent_variables; }

private:
    // level in `var_level` of unassigned variables
    inline static constexpr int unassigned = -1;

    // map decision level -> list of decisions/propagations at that level
    std::vector<std::vector<Assignment>> assigned_stack;
    // map variable type -> variable ordinal -> reason clause (redundant data
    // for fast random access)
    std::vector<std::vector<Clause const*>> var_reason;
    // map variable type -> variable ordinal -> decision level (redundant data
    // for fast random access)
    std::vector<std::vector<int>> var_level;
    // models managed by this trail
    std::vector<std::unique_ptr<Model_base>> var_models;
    // list of recently propagated variables
    std::vector<Assignment> recent_variables;
};

} // namespace perun

#endif // PERUN_TRAIL_H_