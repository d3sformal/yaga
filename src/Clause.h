#ifndef PERUN_CLAUSE_H_
#define PERUN_CLAUSE_H_

#include <vector>

#include "Literal.h"

namespace perun {

// disjunction of literals
using Clause = std::vector<Literal>;

}

#endif // PERUN_CLAUSE_H_