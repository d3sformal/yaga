target_include_directories(perun PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(perun PRIVATE
    Terms.cpp
    Term_hash_table.cpp
    Term_manager.cpp
)