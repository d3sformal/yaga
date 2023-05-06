#ifndef PERUN_TERM_REWRITER_H
#define PERUN_TERM_REWRITER_H

#include <unordered_set>
#include <unordered_map>

#include "Term_manager.h"

namespace perun::terms {

template<typename TConfig> class Rewriter {

protected:
    Term_manager & tm;
    TConfig & cfg;

public:
    Rewriter(Term_manager & tm, TConfig & cfg) : tm(tm), cfg(cfg) {}

    term_t rewrite(term_t root) {
        struct DFSEntry {
            explicit DFSEntry(term_t term) : term(term) {}
            term_t term;
            unsigned int next_child = 0;
        };

        std::unordered_map<term_t, term_t> substitutions;
        std::unordered_set<term_t> processed;
        std::vector<DFSEntry> toProcess;
        std::vector<term_t> aux_args;
        auto is_processed = [&processed](term_t term) { return processed.find(term) != processed.end(); };

        toProcess.emplace_back(root);
        while (not toProcess.empty())
        {
            auto & current_entry = toProcess.back();
            term_t current_term = current_entry.term;
            assert(not is_processed(current_term));
            auto children = tm.get_args(current_term);
            if (current_entry.next_child < children.size())
            {
                term_t next_child = children[current_entry.next_child];
                ++current_entry.next_child;
                if (is_processed(next_child)) { toProcess.emplace_back(next_child); }
                continue;
            }
            // If we are here, we have already processed all children
            assert(substitutions.count(current_term) == 0);
            bool needs_change = false;
            for (term_t child : children)
            {
                auto it = substitutions.find(child);
                bool child_changed = it != substitutions.end();
                needs_change |= child_changed;
                term_t newChild = child_changed ? it->second : child;
                assert(tm.get_type(child) == tm.get_type(newChild));
                aux_args.push_back(newChild);
            }
            term_t newTerm = needs_change ? tm.mk_term(tm.get_kind(current_term), aux_args) : current_term;
            aux_args.clear();
            term_t rewritten = cfg.rewrite(newTerm);
            if (rewritten != newTerm or needs_change) {
                assert(tm.get_type(current_term) == tm.get_type(rewritten));
                substitutions.insert({current_term, rewritten});
            }
            processed.insert(current_term);
            toProcess.pop_back();
        }

        auto it = substitutions.find(root);
        return it == substitutions.end() ? root : it->second;
    }
};

class DefaultRewriterConfig
{
public:
    virtual term_t rewrite(term_t term) { return term; } // don't do anything
};

using subst_map_t = std::unordered_map<term_t, term_t>;

class VarSubstituteConfig : public DefaultRewriterConfig
{
    Term_manager& tm;
    subst_map_t const& subst_map;

public:
    VarSubstituteConfig(Term_manager& tm, subst_map_t const& subst_map) : tm(tm), subst_map(subst_map) {}

    term_t rewrite(term_t term) override
    {
        if (not is_negated(term) and tm.get_kind(term) == Kind::UNINTERPRETED_TERM)
        {
            if (auto it = subst_map.find(term); it != subst_map.end())
            {
                return it->second;
            }
        }
        return term;
    }
};

term_t simultaneous_variable_substitution(Term_manager& tm, subst_map_t const& map, term_t term)
{
    VarSubstituteConfig config(tm, map);
    Rewriter<VarSubstituteConfig> rewriter(tm, config);
    return rewriter.rewrite(term);
}

} // namespace perun::terms

#endif // PERUN_TERM_REWRITER_H
