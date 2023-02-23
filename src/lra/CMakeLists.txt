target_include_directories(perun PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(perun PRIVATE
    Arithmetic_conflict_analysis.cpp
    Linear_arithmetic.cpp
)