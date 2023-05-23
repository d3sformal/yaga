# Yaga

MCSat SMT solver developed at MFF UK, mainly by M. Blicha, D. Hanák, and J. Kofroň (in alphabetic order).

## Build

### Prerequisities
* C++ compiler (`gcc`, `clang`) with C++20 support
* `cmake` version at least 3.17
* `flex` version at least 2.6

To build Yaga, run the following commands:

1. `mkdir build-release`
2. `cd build-release`
3. `cmake -DCMAKE_BUILD_TYPE=Release ..`
4. `make` 

You can use a different build system in step `3`. For example, `cmake -DCMAKE_BUILD_TYPE=Release -G Ninja ..` creates build files for the [Ninja build system](https://ninja-build.org/) which you can use in the 4th step by running `ninja` instead of `make`.

Building the project creates `test`, `sat` and `smt` executables. The `sat` utility implements a SAT solver using core of the MCSat framework and a plugin for boolean variables. It has one command line argument which is a path to a CNF formula in the [DIMACS format](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/SATLINK____DIMACS).
The `smt` utility implements an SMT solver capable of solving problem in quantifier-free linear real arithmetic (QF_LRA logic in SMT-LIB terminology).
It has one command line argument which is a path to a SMT-LIB2 file.
Yaga supports a subset of SMT-LIB2 language that covers all non-incremental benchmarks in SMT-LIB for QF_LRA.
    

# Description
Yaga is an MCSat based [3] SMT solver. Currently, we implemented plugins for boolean and
rational variables which can be used to decide problems in quantifier-free linear real arithmetic.
The boolean plugin uses the typical mechanism of watched literals [6] to perform boolean constraint
propagation. The plugin for linear real arithmetic uses a similar mechanism of watched variables
to keep track of variable bounds [5]. The last checked variable in each clause or a linear constraint
is cached. Search for a non-falsified literal or an unassigned rational variable always starts from the
last position. Additionally, we use the following heuristics:

* Variable order. Yaga uses a generalization of the VSIDS heuristic implementation from
MiniSat [8]. Variable score is increased for each variable involved in conflict derivation. 
Variables of all types (i.e., boolean and rational variables) are ranked using this heuristic.
* Restart scheme. We use a simplified restart scheme from the Glucose solver [1]. The solver
maintains an exponential average of glucose level (LBD) of all learned clauses [2] and an
exponential LBD average of recently learned clauses. Yaga restarts when the recent LBD
average exceeds the global average by some threshold.
* Clause deletion. Yaga deletes subsumed learned clauses on restart [4].
* Clause minimization. Learned clauses are minimized using self-subsuming resolution introduced in MiniSat [8].
* Value caching. Similarly to phase-saving heuristics used in SAT solvers [7], Yaga caches
values of decided rational variables [5]. It preferably uses cached values for rational variables.
If a cached value is not available, the solver tries to find a small integer or a fraction with a
small denominator which is a power of two.
* Bound caching. We keep a stack of variable bounds for each rational variable. When the
solver backtracks, it lazily removes obsolete bounds from the stack. Bounds computed at a
decision level lower than the backtrack level do not have to be recomputed.

## References
1. Gilles Audemard and Laurent Simon. On the Glucose SAT solver. International Journal on Artificial Intelligence Tools, 27(01):1840001, 2018.
2. Armin Biere. Weaknesses of CDCL solvers. In Fields Institute Workshop on Theoretical Foundations of SAT Solving, 2016.
3. Leonardo De Moura and Dejan Jovanovic. A model-constructing satisfiability calculus. In Verification, Model Checking, and Abstract Interpretation: 14th International Conference, VMCAI 2013, Rome, Italy, January 20-22, 2013. Proceedings 14, pages 1–12. Springer, 2013.
4. Niklas Een and Armin Biere. Effective preprocessing in SAT through variable and clause elimination. SAT, 3569:61–75, 2005.
5. Dejan Jovanovic, Clark Barrett, and Leonardo De Moura. The design and implementation of the model constructing satisfiability calculus. In 2013 Formal Methods in Computer-Aided Design, pages 173–180. IEEE, 2013.
6. Matthew W Moskewicz, Conor F Madigan, Ying Zhao, Lintao Zhang, and Sharad Malik. Chaff: Engineering an efficient SAT solver. In Proceedings of the 38th annual Design Automation Conference, pages 530–535, 2001.
7. Knot Pipatsrisawat and Adnan Darwiche. A lightweight component caching scheme for satisfiability solvers. In Theory and Applications of Satisfiability Testing–SAT 2007: 10th International Conference, Lisbon, Portugal, May 28–31, 2007. Proceedings 10, pages 294–299. Springer, 2007.
