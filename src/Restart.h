#ifndef PERUN_RESTART_H_
#define PERUN_RESTART_H_

#include "Database.h"
#include "Trail.h"

namespace perun {

class Restart {
public:
    virtual ~Restart() = default;
    virtual void on_learned_clause(Database&, Trail&, Clause*) {}
    virtual void on_restart(Database&, Trail&) {}

    /** Check whether the solver should restart
     * 
     * @return true iff the solver should restart
     */
    virtual bool should_restart() const = 0;
};

class No_restart final : public Restart {
public:
    virtual ~No_restart() = default;
    bool should_restart() const override;
};

}

#endif // PERUN_RESTART_H_