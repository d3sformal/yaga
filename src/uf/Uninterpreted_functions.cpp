//
// Created by milan on 16.01.24.
//
#include "Uninterpreted_functions.h"

namespace yaga {

std::vector<Clause> yaga::Uninterpreted_functions::propagate(Database&, Trail&) {
    printf("uf::propagate\n");
    return {};
}

void yaga::Uninterpreted_functions::decide(yaga::Database&, yaga::Trail&, yaga::Variable) {

}

} // namespace yaga