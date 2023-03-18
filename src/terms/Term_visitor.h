#ifndef PERUN_TERM_VISITOR_H
#define PERUN_TERM_VISITOR_H

#include <unordered_set>

#include "Terms.h"

namespace perun::terms
{

template<typename TConfig> class Visitor
{
    Term_table const& term_table;
    TConfig& config;
    std::unordered_set<term_t> processed;

public:
    Visitor(Term_table const& term_table, TConfig& config) : term_table(term_table), config(config) {}

    void reset()
    {
        processed.clear();
        config.reset();
    }

    void visit(std::span<const term_t> roots)
    {
        for (term_t root : roots)
        {
            visit(root);
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
            auto children = term_table.get_args(current);
            if (current_entry.next_child < children.size()) {
                term_t next_child = children[current_entry.next_child];
                ++current_entry.next_child;
                if (processed.find(next_child) == processed.end()) {
                    worklist.emplace_back(next_child);
                }
                continue;
            }
            // If we are here, we have already processed all children
            assert(processed.count(current) == 0);
            config.visit(current);
            processed.insert(current);
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
#endif // PERUN_TERM_VISITOR_H
