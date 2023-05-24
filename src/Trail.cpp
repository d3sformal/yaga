#include "Trail.h"
#include "Event_dispatcher.h"

namespace yaga {

void Trail::resize(Variable::Type type, int num_vars)
{
    assert(type < var_models.size());

    var_models[type]->resize(num_vars);
    int num_types = std::max<int>(static_cast<int>(var_reason.size()), type + 1);
    var_reason.resize(num_types, std::vector<Clause const*>(num_vars, nullptr));
    var_level.resize(num_types, std::vector<int>(num_vars, unassigned));
    var_reason[type].resize(num_vars, nullptr);
    var_level[type].resize(num_vars, unassigned);
    // notify all listeners that the number of variables has changed
    dispatcher.on_variable_resize(type, num_vars);
}

}