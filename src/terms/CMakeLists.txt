target_include_directories(yaga PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(yaga PRIVATE
    Terms.cpp
    Term_hash_table.cpp
    Term_manager.cpp
    Term_visitor.h
)