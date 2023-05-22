target_include_directories(yaga PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(yaga PRIVATE
    Evsids.cpp
    First_unassigned.cpp
    Generalized_vsids.cpp
    Variable_priority_queue.cpp
)