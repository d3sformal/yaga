#ifndef YAGA_TERM_VISITOR_H
#define YAGA_TERM_VISITOR_H

#include <unordered_set>

#include "Term_manager.h"

namespace yaga::terms
{

template<typename TConfig> class Visitor
{
    Term_manager const& term_manager;
    TConfig& config;
    std::unordered_set<int32_t> processed;

public:
    Visitor(Term_manager const& term_manager, TConfig& config) : term_manager(term_manager), config(config) {}

    void reset()
    {
        processed.clear();
        config.reset();
    }

    void visit(std::span<const term_t> roots)
    {
        for (term_t root : roots)
        {
            if (processed.count(term_manager.index_of(root)) == 0)
            {
                visit(root);
            }
        }
    }

    void visit(term_t root)
    {
        struct DFSEntry {
            explicit DFSEntry(term_t term) : term(term) {}
            term_t term;
            unsigned int next_child = 0;
        };

        std::vector<DFSEntry> worklist;

        worklist.emplace_back(root);
        while (!worklist.empty())
        {
            auto& current_entry = worklist.back();
            term_t current = current_entry.term;
            auto children = term_manager.get_args(current);
            if (current_entry.next_child < children.size()) {
                term_t next_child = children[current_entry.next_child];
                ++current_entry.next_child;
                if (processed.find(term_manager.index_of(next_child)) == processed.end()) {
                    worklist.emplace_back(next_child);
                }
                continue;
            }
            // If we are here, we have already processed all children
            assert(processed.count(term_manager.index_of(current)) == 0);
            config.visit(current);
            processed.insert(term_manager.index_of(current));
            worklist.pop_back();
        }
    }
};

class Default_visitor_config {
public:
    virtual void visit(term_t) { } // don't do anything
    virtual void reset() { } // don't do anything
};

}
#endif // YAGA_TERM_VISITOR_H
