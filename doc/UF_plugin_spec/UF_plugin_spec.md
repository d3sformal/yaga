# 1. Basic Information
## Description and Focus of the Software Work
The aim of the work is to extend the Yaga SMT solver, developed at the Department of Distributed and Reliable Systems at the Faculty of Mathematics and Physics, Charles University, to accept a broader range of input formulas—specifically, formulas containing uninterpreted function symbols. The solver is based on the innovative MCSat approach, described in [2].

## Technologies Used
The plugin, like the previous parts of the solver, will be written in C++ and will use its standard libraries.

# 2. Brief Description of the Software Work

The existing Yaga SMT solver, created upon [1], currently decides clauses containing Boolean variables and real variables only. This work aims to extend the solver's functionality to clauses with uninterpreted function symbols, as stated in section IV.C of [1].

## Main Functions
The main functions of the solver plugins, as outlined in the reference article and as already implemented in other plugins within the solver, are three: assigning new values to variables, detecting conflicts related to the corresponding theory, and propagating literals. For deciding on function symbols, only the congruence rule is used, implemented using the 1-variable watchlist mechanism.

## Motivational Example of Use
The solver will be provided with a set of clauses containing, among other things, function symbols. For example, for the input `f(0)=1`, the solver would respond with sat (satisfiable), while for the input `(f(0)=1 & f(0)=0)`, the output would be unsat (unsatisfiable).

## Application Environment
The solver can be compiled by any C++ compiler and subsequently run on any platform supported by the respective compiler.

## Limitations of the Work
The implementation will adhere to the existing conventions of the Yaga solver, in terms of object naming, code structuring, documentation comments, etc.

# 3. External Interface
## User Interface, Inputs, and Outputs
The entire Yaga SMT solver is a command-line application. The solver input is a text file with clauses, whose format adheres to the SMT-LIB standard [3]. The output is information about the satisfiability of the input set of clauses: sat or unsat, optionally including selected statistics about the solver run.

## Interface with Software
The plugin will be an extension of the Yaga SMT solver, in which plugins for real linear arithmetic and Boolean variables are already implemented. The solver is ready for extension using plugins in terms of defining the `Theory` class, which individual plugins implement. The solver core communicates with the plugin using this interface. Part of the interface includes event listeners for some events within the solver (backtracking trail, assigning new variables, etc.), and further methods `decide` and `propagate`, which are used for assigning values to variables, resp. propagating literals.

Within the solver, a clause database is already implemented, with which the plugin will also communicate. In addition, it will use a formula parser, which is also already implemented within the solver. However, the functions of both mentioned parts may need to be extended to accept formulas containing function symbols.

# 4. Detailed Description of Functionality
The plugin should decide on function symbols based on the congruence rule (Ackermann expansion rule). The implementation will use the 1-variable watchlist mechanism—for each term with a function symbol, we maintain one remaining argument in the watchlist that has not yet been assigned a value. After assigning all arguments, conflict detection and propagation occur.

## Conflict Detection
Based on the input set of clauses and the current content of the trail, the plugin searches for a so-called _conflict clause_, i.e., a clause that is evaluated as false in the current trail. In the case of this plugin, these are clauses that contradict the rule of congruence. If the plugin detects such a clause, it passes it to the solver core, which then resolves the conflict and performs backtracking (i.e., removing several top-level elements from the trail).

## Propagation of Literals
Based on the aforementioned 1-variable watchlist mechanism, it checks whether literals containing function symbols can be evaluated (as true or false). In such cases, they can be propagated—i.e., added to the end of the trail as semantic propagation. Based on these, constraint propagation of the solver core can take place.

## Assigning Values to Variables
Unlike the other plugins, the responsibility of the plugin for the theory of uninterpreted functions is not assigning values to individual variables. Each created term acquires a value either of a real number or a Boolean value (true/false), and thus the assignment of such a value is realized by the correposonding (Bool / LRA) plugin.

# 5. Other (Non-Functional) Requirements
## Requirements for Extensibility and Integrability
Part of the project will also be a set of tests that will verify the correct functionality of the plugin using mock-ups of other parts of the solver—the core, clause database, and parser.


# References
1. Dejan Jovanovic, Clark Barrett, and Leonardo De Moura. The design and implementation of the model constructing satisfiability calculus. In 2013 Formal Methods in Computer-Aided Design, pages 173–180. IEEE, 2013.
2. Leonardo De Moura and Dejan Jovanovic. A model-constructing satisfiability calculus. In Verification, Model Checking, and Abstract Interpretation: 14th International Conference, VMCAI 2013, Rome, Italy, January 20-22, 2013. Proceedings 14, pages 1–12. Springer, 2013.
3. Clark Barrett, Pascal Fontaine, and Cesare Tinelli. The SMT-LIB Standard: Version 2.6. Department of Computer Science, The University of Iowa. 2017. https://smtlib.cs.uiowa.edu/language.shtml
