#include "Smallest_range_first.h"

namespace perun {

std::optional<Variable> Smallest_range_first::pick(Database&, Trail& trail)
{
    auto const& models = lra->relevant_models(trail);

    int best_var = -1; // none
    auto best_range = std::numeric_limits<std::int64_t>::max();

    for (int i = 0; i < static_cast<int>(models.owned().num_vars()); ++i)
    {
        if (models.owned().is_defined(i))
        {
            continue; // skip assigned variables
        }

        auto& bounds = lra->find_bounds(i);
        auto ub = bounds.upper_bound(models).value();
        auto lb = bounds.lower_bound(models).value();
        auto range = static_cast<std::int64_t>(ub.numerator()) * lb.denominator() - static_cast<std::int64_t>(lb.numerator()) * ub.denominator();
        if (range < best_range)
        {
            best_var = i;
            best_range = range;
        }
    }

    if (best_var < 0)
    {
        return {}; // all variables are assigned
    }
    return Variable{best_var, Variable::rational};
}

}