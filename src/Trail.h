#ifndef PERUN_TRAIL_H_
#define PERUN_TRAIL_H_

#include <vector>
#include <memory>
#include <cassert>
#include <optional>
#include <tuple>

#include "Variable.h"
#include "Literal.h"
#include "Clause.h"
#include "Model.h"

namespace perun {

class Trail {
public:
    struct Assignment {
        // assigned variable
        Variable var;
        // reason clause for the assignment or nullptr if this is a decision/semantic propagation
        Clause* reason;

        // convert to pair so we can tie the properties
        inline operator std::pair<Variable, Clause*>() const { return {var, reason}; }
    };

    inline Trail() : assigned_(1) {}

    // get current decision level
    inline int decision_level() const { return static_cast<int>(assigned_.size()) - 1; }

    /** Get decision level of a variable
     * 
     * @param var queried variable
     * @return level at which @p var was decided/propagated or non if @p var does not have a value 
     * in this trail
     */
    inline std::optional<int> decision_level(Variable var) const 
    { 
        return level_[var.type()][var.ord()] < 0 ? std::optional<int>{} : level_[var.type()][var.ord()]; 
    }

    /** Get reason why @p var was propagated
     * 
     * @param var queried variable
     * @return reason clause which lead to propagation of @p var or nullptr if there is no such 
     * clause in this trail
     */
    inline const Clause* reason(Variable var) const { return reason_[var.type()][var.ord()]; }

    /** Get a list of variables together with reason clause assigned at decision level @p level
     * 
     * @param level decision level
     * @return list of variables assigned at decision level @p level
     */
    inline const auto& assigned(int level) const { return assigned_[level]; }

    /** Add a new partial model for type @p type to this trail
     * 
     * @tparam T type of elements stored in the model
     * @param type type of variables
     * @return reference to the managed model
     */
    template<typename T>
    inline Model<T>& add_model(Variable::Type type)
    {
        if (type >= models_.size())
        {
            models_.resize(static_cast<int>(type) + 1);
        }
        auto model = std::make_unique<Model<T>>();
        auto ptr = model.get();
        models_[type] = std::move(model);
        return *ptr;
    }

    /** Get partial model for variable @p type 
     * 
     * @tparam T type of values in the model
     * @param type type of variables
     * @return partial model for @p type managed by this trail
     */
    template<typename T>
    inline Model<T>& model(Variable::Type type) { return dynamic_cast<Model<T>&>(*models_[type]); }

    template<typename T>
    inline const Model<T>& model(Variable::Type type) const { return dynamic_cast<Model<T>&>(*models_[type]); }

    // get model for each type in this trail
    inline auto models() const 
    {
        int type = 0;
        std::vector<std::pair<Variable::Type, const Model_base*>> models;
        for (const auto& model : models_)
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
        assert(type < models_.size());

        models_[type]->resize(num_vars);
        reason_.resize(type + 1, std::vector<const Clause*>(num_vars, nullptr));
        level_.resize(type + 1, std::vector<int>(num_vars, UNASSIGNED));
    }

    /** Decide variable at a new decision level. 
     * 
     * The caller is responsible for setting new @p var value in the appropriate `model()`.
     * 
     * @param var newly decided variable
     */
    inline void decide(Variable var)
    {
        assert(var.type() < level_.size());
        assert(var.type() < reason_.size());
        assert(var.type() < models_.size());

        assigned_.emplace_back(std::vector<Assignment>{Assignment{var, nullptr}});
        level_[var.type()][var.ord()] = decision_level();
        reason_[var.type()][var.ord()] = nullptr;
    }

    /** Propagate variable @p var due to clause @p reason at decision level @p level
     * 
     * @param var variable to propagate
     * @param reason reason clause for the propagation or `nullptr` if this is a semantic propagation
     * @param level decision level at which @p var is propagated (in `[0, decision_level()]` range)
     */
    inline void propagate(Variable var, Clause* reason, int level)
    {
        assert(0 <= level && level <= decision_level());
        assert(var.type() < level_.size());
        assert(var.type() < reason_.size());
        assert(var.type() < models_.size());

        assigned_[level].push_back(Assignment{var, reason});
        level_[var.type()][var.ord()] = level;
        reason_[var.type()][var.ord()] = reason;
    }

    /** Make all variables decided or propagated at levels > @p level unassigned.
     * 
     * @param level decision level to backtrack to
     */
    inline void backtrack(int level)
    {
        assert(0 <= level);

        for (; decision_level() > level; assigned_.pop_back())
        {
            for (auto [var, _] : assigned_[decision_level()])
            {
                level_[var.type()][var.ord()] = UNASSIGNED;
                reason_[var.type()][var.ord()] = nullptr;
                models_[var.type()]->clear(var.ord());
            }
        }

        assert(level == decision_level());
    }

    /** Check if some variable is assigned.
     * 
     * @return true iff at least one variable is assigned in this trail
     */
    inline bool empty() const { return assigned_.size() == 1 && assigned_[0].size() == 0; }
private:
    // level in `level_` of unassigned variables
    inline static constexpr int UNASSIGNED = -1;

    // map decision level -> list of decisions/propagations at that level 
    std::vector<std::vector<Assignment>> assigned_;
    // map variable type -> variable ordinal -> reason clause (redundant data for fast random access)
    std::vector<std::vector<const Clause*>> reason_;
    // map variable type -> variable ordinal -> decision level (redundant data for fast random access)
    std::vector<std::vector<int>> level_;
    // models managed by this trail
    std::vector<std::unique_ptr<Model_base>> models_; 
};

}

#endif // PERUN_TRAIL_H_