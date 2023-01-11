target_include_directories(perun PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(perun PRIVATE
    Bool_theory.cpp
    Conflict_analysis.cpp
    Evsids.cpp
    Linear_arithmetic.cpp
    Solver.cpp
    Subsumption.cpp
)