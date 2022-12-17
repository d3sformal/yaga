#ifndef PERUN_RESTART_H_
#define PERUN_RESTART_H_

#include "Database.h"
#include "Trail.h"
#include "Event_listener.h"

namespace perun {

class Restart : public Event_listener {
public:
    virtual ~Restart() = default;

    /** Check whether the solver should restart
     * 
     * @return true iff the solver should restart
     */
    virtual bool should_restart() const = 0;
};

class No_restart final : public Restart {
public:
    virtual ~No_restart() = default;
    bool should_restart() const override { return false; }
};

class Luby_restart final : public Restart {
public:
    virtual ~Luby_restart() = default;
    inline Luby_restart() { next(); }

    void on_learned_clause(Database&, Trail&, Clause*) override { --countdown_; }
    void on_restart(Database&, Trail&) override { next(); }
    bool should_restart() const override { return countdown_ <= 0; }

    // generate a luby sequence element given a 1-based element index
    inline int luby(std::uint32_t index) const 
    {
        for (std::uint32_t mask = -1; (index & (index + 1)) != 0; index -= mask)
        {
            for (; mask >= index; mask >>= 1)
            {
            }
        }
        return (index + 1) >> 1;
    }

private:
    // countdown to the next restart
    int countdown_ = 0;
    // current luby sequence index
    int index_ = 0;
    // restart multiplier 
    int mult_ = 550;

    inline void next() { countdown_ = luby(++index_) * mult_; }
};

}

#endif // PERUN_RESTART_H_