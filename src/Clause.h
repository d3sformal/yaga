#ifndef YAGA_CLAUSE_H
#define YAGA_CLAUSE_H

#include <vector>

#include "Literal.h"

namespace yaga {

/** Disjunction of literals
 */
using Clause = std::vector<Literal>;

} // namespace yaga

#endif // YAGA_CLAUSE_H