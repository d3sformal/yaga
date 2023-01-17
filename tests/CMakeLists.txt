target_include_directories(test PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(test PRIVATE
    Bool_theory_test.cpp
    Bounds_test.cpp
    Conflict_analysis_test.cpp
    Evsids_test.cpp
    Fraction_test.cpp
    Glucose_restart_test.cpp
    Linear_arithmetic_test.cpp
    Linear_constraints_test.cpp
    Lra_test.cpp
    Luby_restart_test.cpp
    Solver_test.cpp
    Subsumption_test.cpp
)