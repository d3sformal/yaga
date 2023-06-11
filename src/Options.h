#ifndef YAGA_OPTIONS_H
#define YAGA_OPTIONS_H

#include "Bool_theory.h"

namespace yaga {

/** Solver options parsed from the command line.
 */
struct Options {
    /** If true, the LRA plugin will decide rational variables with only one allowed value first.
     * 
     * For example, if 0 <= x and x <= 0 are on the trail, we will decide x before any other 
     * variable.
     */
    bool prop_rational = false;

    /** If true, the LRA plugin will derive new bounds using Fourier-Motzkin elimination.
     */
    bool deduce_bounds = false;

    /** If true, the program will print solver counters like the number of conflicts.
     */
    bool print_stats = false;

    /** Value selection strategy for boolean variables.
     */
    Phase phase = Phase::positive;
};

}

#endif // YAGA_OPTIONS_H