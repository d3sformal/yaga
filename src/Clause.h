#ifndef PERUN_CLAUSE_H
#define PERUN_CLAUSE_H

#include <vector>

#include "Literal.h"

namespace perun {

/** Disjunction of literals
 */
using Clause = std::vector<Literal>;

} // namespace perun

#endif // PERUN_CLAUSE_H