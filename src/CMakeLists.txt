target_include_directories(perun PUBLIC ${CMAKE_CURRENT_LIST_DIR})

add_subdirectory(bool)
add_subdirectory(lra)
add_subdirectory(variable_order)
add_subdirectory(terms)

target_sources(perun PRIVATE
    Conflict_analysis.cpp
    Solver.cpp
    Subsumption.cpp
    Theory.cpp
    Theory_combination.cpp
)