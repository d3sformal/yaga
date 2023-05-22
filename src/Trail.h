#ifndef YAGA_TRAIL_H_
#define YAGA_TRAIL_H_

#include <cassert>
#include <memory>
#include <optional>
#include <tuple>
#include <vector>

#include "Clause.h"
#include "Literal.h"
#include "Model.h"
#include "Variable.h"

namespace yaga {

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

    inline Trail() : trail(1) {}

    // get current decision level
    inline int decision_level() const { return static_cast<int>(trail.size()) - 1; }

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

    /** Get variables assigned at current decision level.
     * 
     * Note, that level of variables in this list can be lower than `decision_level()`.
     * 
     * @return range of variables added to the trail at current decision level
     */
    inline auto const& recent() const { return trail.back(); }

    /** Get variables assigned at @p level
     * 
     * Note, that decision level of variables in this list can be lower than @p level
     * 
     * @param level decision level
     * @return variables added to the trail at level @p level
     */
    inline auto const& assigned(int level) const { return trail[level]; }

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

    /** Get base model instance for variables of type @p type
     * 
     * @param type type of variables
     * @return partial model of variables of type @p type
     */
    inline Model_base const& model(Variable::Type type) const { return *var_models[type]; }

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

        trail.emplace_back(std::vector<Assignment>{Assignment{var, /*reason=*/nullptr}});
        var_level[var.type()][var.ord()] = decision_level();
        var_reason[var.type()][var.ord()] = nullptr;
    }

    /** Propagate variable @p var due to clause @p reason at decision level @p level
     *
     * @param var variable to propagate
     * @param reason reason clause for the propagation or `nullptr` if this is a semantic
     * propagation
     * @param level decision level at which @p var is propagated (in `[0, decision_level()]`
     * range)
     */
    inline void propagate(Variable var, Clause* reason, int level)
    {
        assert(0 <= level && level <= decision_level());
        assert(var.type() < var_level.size());
        assert(var.type() < var_reason.size());
        assert(var.type() < var_models.size());

        for (int i = level; i <= decision_level(); ++i)
        {
            trail[i].push_back(Assignment{var, reason});
        }
        var_level[var.type()][var.ord()] = level;
        var_reason[var.type()][var.ord()] = reason;
    }

    /** Make all variables decided or propagated at levels > @p level unassigned.
     *
     * @param level decision level to backtrack to
     */
    inline void backtrack(int level)
    {
        assert(0 <= level);

        for (; decision_level() > level; trail.pop_back())
        {
            for (auto assignment : trail[decision_level()])
            {
                if (var_level[assignment.var.type()][assignment.var.ord()] > level)
                {
                    var_level[assignment.var.type()][assignment.var.ord()] = unassigned;
                    var_reason[assignment.var.type()][assignment.var.ord()] = nullptr;
                    var_models[assignment.var.type()]->clear(assignment.var.ord());
                }
            }
        }
        assert(level == decision_level());
    }

    /** Check if some variable is assigned.
     *
     * @return true iff no variable is assigned in this trail
     */
    inline bool empty() const { return trail.size() == 1 && trail[0].empty(); }

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

        trail.clear();
        trail.emplace_back();
    }

private:
    // level in `var_level` of unassigned variables
    inline static constexpr int unassigned = -1;

    // map decision level -> list of decisions/propagations made at that level
    std::vector<std::vector<Assignment>> trail;
    // map variable type -> variable ordinal -> reason clause (redundant data
    // for fast random access)
    std::vector<std::vector<Clause const*>> var_reason;
    // map variable type -> variable ordinal -> decision level
    std::vector<std::vector<int>> var_level;
    // models managed by this trail
    std::vector<std::unique_ptr<Model_base>> var_models;
};

} // namespace yaga

#endif // YAGA_TRAIL_H_