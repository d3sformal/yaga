#include "Yaga.h"

namespace yaga {

void Propositional::setup(Solver& solver) const
{
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.set_theory<Bool_theory>();
    solver.set_restart_policy<Glucose_restart>();
    solver.set_variable_order<Evsids>();
}

void Qf_lra::setup(Solver& solver) const
{
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Rational>(Variable::rational, 0);
    auto& theories = solver.set_theory<Theory_combination>();
    theories.add_theory<Bool_theory>();
    auto& lra = theories.add_theory<Linear_arithmetic>();
    solver.set_restart_policy<Glucose_restart>();
    solver.set_variable_order<Generalized_vsids>(lra);
}

Yaga::Yaga(Initializer const& initializer) { init(initializer); }

void Yaga::init(Initializer const& init)
{
    smt.db().learned().clear();
    smt.db().asserted().clear();
    init.setup(smt);

    // find the LRA plugin so we can add linear constraints
    lra = nullptr;
    if (auto combination = dynamic_cast<Theory_combination*>(smt.theory()))
    {
        for (auto theory : combination->theories())
        {
            if (auto plugin = dynamic_cast<Linear_arithmetic*>(theory))
            {
                lra = plugin;
                break;
            }
        }
    }
}

Variable Yaga::make(Variable::Type type)
{
    auto num_vars = static_cast<int>(smt.trail().model(type).num_vars());
    smt.trail().resize(type, num_vars + 1);
    return Variable{num_vars, type};
}

Literal Yaga::make_bool()
{
    return Literal{make(Variable::boolean).ord()};
}

}