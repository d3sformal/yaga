#include "Luby_restart.h"

namespace perun {

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