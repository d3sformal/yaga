#ifndef YAGA_SOLVER_WRAPPER_H
#define YAGA_SOLVER_WRAPPER_H

#include <vector>

#include "Solver_answer.h"
#include "Term_manager.h"

namespace yaga::parser
{

class Solver_wrapper
{
    terms::Term_manager& term_manager;

public:
    explicit Solver_wrapper(terms::Term_manager& term_manager) : term_manager(term_manager) {}

    Solver_answer check(std::vector<terms::term_t> const& assertions);
};

}

#endif // YAGA_SOLVER_WRAPPER_H
