#include "First_unassigned.h"

namespace perun {

bool First_unassigned::is_before(Variable lhs, Variable rhs) const
{
    return lhs.type() < rhs.type() || (lhs.type() == rhs.type() && lhs.ord() < rhs.ord());
}

std::optional<Variable> First_unassigned::pick(Database&, Trail& trail)
{
    auto models = trail.models();

    for (auto [type, model] : models)
    {
        if (!var_type || var_type == type)
        {
            for (int i = 0; i < static_cast<int>(model->num_vars()); ++i)
            {
                if (!model->is_defined(i))
                {
                    return Variable{i, type};
                }
            }
        }
    }
    return {};
}

} // namespace perun