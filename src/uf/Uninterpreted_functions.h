//
// Created by milan on 16.01.24.
//

#ifndef YAGA_UNINTERPRETED_FUNCTIONS_H
#define YAGA_UNINTERPRETED_FUNCTIONS_H

#include "Theory.h"

namespace yaga{

class Uninterpreted_functions : public Theory {

    std::vector<Clause> propagate(Database&, Trail&) override;

    void decide(Database&, Trail&, Variable) override;

};

} // namespace yaga

#endif // YAGA_UNINTERPRETED_FUNCTIONS_H
