target_include_directories(perun PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(perun PRIVATE
    Evsids.cpp
    First_unassigned.cpp
    Smallest_range_first.cpp
)