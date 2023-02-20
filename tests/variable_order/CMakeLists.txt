target_include_directories(test PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(test PRIVATE
    Evsids_test.cpp
    Generalized_vsids_test.cpp
    Variable_priority_queue_test.cpp
)