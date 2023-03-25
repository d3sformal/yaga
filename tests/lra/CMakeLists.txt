target_include_directories(test PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(test PRIVATE
    Bounds_test.cpp
    Fraction_test.cpp
    Linear_arithmetic_test.cpp
    Linear_constraints_test.cpp
    Lra_test.cpp
    Lra_conflict_analysis_test.cpp
    Smtlib_parser_test.cpp
    Variable_bounds_test.cpp
)