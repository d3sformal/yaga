#include "First_unassigned.h"

namespace perun {

std::optional<Variable> First_unassigned::pick(Database&, Trail& trail)
{
    for (auto [type, model] : trail.models())
    {
        for (int i = 0; i < static_cast<int>(model->num_vars()); ++i)
        {
            if (!model->is_defined(i))
            {
                return Variable{i, type};
            }
        }
    }
    return {};
}

} // namespace perun