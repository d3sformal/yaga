#include "Generalized_vsids.h"

namespace perun {

void Generalized_vsids::on_variable_resize(Variable::Type type, int num_vars)
{
    if (vsids.size() <= static_cast<std::size_t>(type))
    {
        vsids.resize(type + 1);
    }
    vsids[type].resize(num_vars, 0.0f);
}

void Generalized_vsids::on_init(Database& db, Trail&)
{
    for (auto& scores : vsids)
    {
        for (auto& score : scores)
        {
            score = 0.0f;
        }
    }

    for (auto clause_list : {&db.asserted(), &db.learned()})
    {
        for (auto& clause : *clause_list)
        {
            for (auto lit : clause)
            {
                bump(lit.var().ord());
            }
        }
    }
}

void Generalized_vsids::on_learned_clause(Database&, Trail&, Clause const& learned)
{
    for (auto lit : learned)
    {
        bump(lit.var().ord());
    }
    decay();
}

void Generalized_vsids::on_conflict_resolved(Database&, Trail&, Clause const& other)
{
    for (auto lit : other)
    {
        bump(lit.var().ord());
    }
}

std::optional<Variable> Generalized_vsids::pick(Database&, Trail& trail)
{
    // decide variables with implied value first (i.e., variable `x` s.t. `L <= x <= U` and `L = U`)
    auto models = lra->relevant_models(trail);
    for (int var_ord = 0; var_ord < static_cast<int>(models.owned().num_vars()); ++var_ord)
    {
        if (!models.owned().is_defined(var_ord))
        {
            auto& bounds = lra->find_bounds(var_ord);
            if (bounds.lower_bound(models).value() == bounds.upper_bound(models).value())
            {
                return Variable{var_ord, Variable::rational};
            }
        }
    }

    // find variable with the best VSIDS score
    std::optional<Variable> best_var;
    float best_score = -1.f;

    for (std::size_t type = 0; type < vsids.size(); ++type)
    {
        Variable var{0, static_cast<Variable::Type>(type)};
        for (auto score : vsids[type])
        {
            if (!trail.decision_level(var) && score > best_score)
            {
                best_score = score;
                best_var = var;
            }
            var = Variable{var.ord() + 1, var.type()};
        }
    }
    return best_var;
}

} // namespace perun