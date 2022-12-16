#include "Restart.h"

namespace perun {

bool No_restart::should_restart() const 
{
    return false;
}

}