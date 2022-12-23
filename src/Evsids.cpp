#include "Evsids.h"

namespace perun {

void Evsids::on_variable_resize(Variable::Type type, int num_vars)
{
    if (type == Variable::boolean)
    {
        vsids.resize(num_vars, 0.0f);
    }
}

void Evsids::on_init(Database& db, Trail&)
{
    for (auto& score : vsids)
    {
        score = 0.0f;
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

void Evsids::on_conflict_resolved(Database&, Trail&, Clause const& other)
{
    for (auto lit : other)
    {
        bump(lit.var().ord());
    }
}

void Evsids::on_learned_clause(Database&, Trail&, Clause* learned)
{
    for (auto lit : *learned)
    {
        bump(lit.var().ord());
    }
    decay();
}

std::optional<Variable> Evsids::pick(Database&, Trail& trail)
{
    auto const& model = trail.model<bool>(Variable::boolean);

    int best_var = -1;       // none
    float best_score = -1.f; // replace this score even if the best score is 0

    for (int i = 0; i < static_cast<int>(vsids.size()); ++i)
    {
        if (!model.is_defined(i) && score(i) > best_score)
        {
            best_score = score(i);
            best_var = i;
        }
    }

    if (best_var < 0)
    {
        return {}; // no unassigned variables
    }
    return Variable{best_var, Variable::boolean};
}

} // namespace perun