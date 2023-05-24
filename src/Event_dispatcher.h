#ifndef YAGA_EVENT_DISPATCHER_H
#define YAGA_EVENT_DISPATCHER_H

#include <vector>
#include <ranges>

#include "Event_listener.h"

namespace yaga {

/** Container of objects of type `Event_listener` which calls events on all registered listeners.
 */
class Event_dispatcher : public Event_listener {
public:
    virtual ~Event_dispatcher() = default;

    /** Calls the on init event in all registered listeners.
     *
     * @param db clause database
     * @param trail current solver trail
     */
    void on_init(Database& db, Trail& trail) override
    {
        for (auto&& listener : listeners)
        {
            listener->on_init(db, trail);
        }
    }

    /** Calls the variable resize event in all registered listeners.
     *
     * @param type type of variables
     * @param num_vars new number of variables
     */
    void on_variable_resize(Variable::Type type, int num_vars) override
    {
        for (auto&& listener : listeners)
        {
            listener->on_variable_resize(type, num_vars);
        }
    }

    /** Calls the event in all registers listeners.
     *
     * @param db clause database
     * @param trail current solver trail before backtracking
     * @param decision_level decision level to backtrack to
     */
    void on_before_backtrack(Database& db, Trail& trail, int decision_level) override
    {
        for (auto&& listener : listeners)
        {
            listener->on_before_backtrack(db, trail, decision_level);
        }
    }

    /** Calls the event in all registered listeners.
     *
     * @param db clause database
     * @param trail current solver trail
     * @param learned reference to the newly learned clause in @p db
     */
    void on_learned_clause(Database& db, Trail& trail, Clause const& learned) override
    {
        for (auto&& listener : listeners)
        {
            listener->on_learned_clause(db, trail, learned);
        }
    }

    /** Calls the event in all registers listeners.
     *
     * @param db clause database
     * @param trail current solver trail
     * @param other_clause clause that is resolved with current conflict clause
     */
    void on_conflict_resolved(Database& db, Trail& trail, Clause const& other_clause) override
    {
        for (auto&& listener : listeners)
        {
            listener->on_conflict_resolved(db, trail, other_clause);
        }
    }

    /** Calls the event in all registered listeners.
     *
     * @param db clause database
     * @param trail current solver trail after restart
     */
    void on_restart(Database& db, Trail& trail) override 
    {
        for (auto&& listener : listeners)
        {
            listener->on_restart(db, trail);
        }
    }

    /** Add @p listener to the list of listeners.
     * 
     * @param listener new listener to add
     */
    void add(Event_listener* listener) { listeners.push_back(listener); }

    /** Remove @p listener from the list of listeners.
     * 
     * If @p listener is not registers in this dispatcher, this method does nothing.
     * 
     * @param listener listener to remove
     */
    void remove(Event_listener* listener)
    {
        auto it = std::ranges::find(listeners, listener);
        if (it != listeners.end())
        {
            listeners.erase(it);
        }
    }
private:
    std::vector<Event_listener*> listeners;
};

}

#endif // YAGA_EVENT_DISPATCHER_H