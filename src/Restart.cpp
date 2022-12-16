#include "Restart.h"

namespace perun {

bool No_restart::should_restart() const 
{
    return false;
}

void Luby_restart::on_learned_clause(Database&, Trail&, Clause*)
{
    --countdown_;
}

void Luby_restart::on_restart(Database&, Trail&)
{
    next();
}

bool Luby_restart::should_restart() const
{
    return countdown_ <= 0;
}

}