#include "Uninterpreted_functions.h"

namespace yaga {

std::vector<Clause> yaga::Uninterpreted_functions::propagate(Database&, Trail&) {
    return {};
}

void yaga::Uninterpreted_functions::decide(yaga::Database&, yaga::Trail&, yaga::Variable) {

}

} // namespace yaga