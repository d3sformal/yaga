#include "Theory.h"

namespace perun {

void Theory::on_before_backtrack(Database&, Trail&, int)
{
    current_level = -1; // make the next assigned() call reset current_level
    next_index = 0;
}

Theory::Trail_subrange Theory::assigned(Trail const& trail)
{
    auto skip = trail.decision_level() == current_level ? next_index : 0;
    current_level = trail.decision_level();
    next_index = trail.assigned(trail.decision_level()).size();
    return trail.assigned(trail.decision_level()) | std::views::drop(skip);
}

}