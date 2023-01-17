target_include_directories(perun PUBLIC ${CMAKE_CURRENT_LIST_DIR})

add_subdirectory(bool)
add_subdirectory(lra)

target_sources(perun PRIVATE
    Conflict_analysis.cpp
    Evsids.cpp
    First_unassigned.cpp
    Solver.cpp
    Subsumption.cpp
    Theory_combination.cpp
)