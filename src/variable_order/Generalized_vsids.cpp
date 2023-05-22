#include "Generalized_vsids.h"

namespace yaga {

void Generalized_vsids::on_variable_resize(Variable::Type type, int num_vars)
{
    if (vsids.size() <= static_cast<std::size_t>(type))
    {
        vsids.resize(type + 1);
    }
    int var_ord = static_cast<int>(vsids[type].size());
    vsids[type].resize(num_vars, 0.0f);

    for (; var_ord < num_vars; ++var_ord)
    {
        variables.push(Variable{var_ord, type}, 0.0f);
    }
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

void Generalized_vsids::on_before_backtrack(Database&, Trail& trail, int level)
{
    decay();

    for (int i = trail.decision_level(); i > level; --i)
    {
        for (auto [var, _] : trail.assigned(i))
        {
            if (!variables.contains(var) && trail.decision_level(var).value() > level)
            {
                variables.push(var, score(var));
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
}

void Generalized_vsids::on_conflict_resolved(Database&, Trail&, Clause const& other)
{
    for (auto lit : other)
    {
        bump(lit.var().ord());
    }
}

bool Generalized_vsids::is_before(Variable lhs, Variable rhs) const
{
    return score(lhs) > score(rhs);
}

std::optional<Variable> Generalized_vsids::pick(Database&, Trail& trail)
{
    // remove assigned variables from the top of the variables priority queue
    while (!variables.empty() && trail.decision_level(variables.top()))
    {
        variables.pop();
    }

    if (variables.empty())
    {
        return {}; // none, all variables are assigned
    }
    return variables.top();
}

} // namespace yaga