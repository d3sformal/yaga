#include "Yaga.h"

namespace yaga {

void Propositional::setup(Solver& solver, Options const& options) const
{
    solver.trail().set_model<bool>(Variable::boolean, 0);
    auto& bcp = solver.set_theory<Bool_theory>();
    bcp.set_phase(options.phase);
    solver.set_restart_policy<Glucose_restart>();
    solver.set_variable_order<Evsids>();
}

void Qf_lra::setup(Solver& solver, Options const& options) const
{
    solver.trail().set_model<bool>(Variable::boolean, 0);
    solver.trail().set_model<Rational>(Variable::rational, 0);
    // create plugins
    auto& theories = solver.set_theory<Theory_combination>();
    auto& bcp = theories.add_theory<Bool_theory>();
    bcp.set_phase(options.phase);

    Linear_arithmetic::Options lra_options;
    lra_options.prop_rational = options.prop_rational;
    lra_options.prop_bounds = options.deduce_bounds;
    auto& lra = theories.add_theory<Linear_arithmetic>();
    lra.set_options(lra_options);

    theories.add_theory<Uninterpreted_functions>();

    // add heuristics
    solver.set_restart_policy<Glucose_restart>();
    solver.set_variable_order<Generalized_vsids>(lra);
}

Yaga::Yaga(Initializer const& initializer, Options const& options) { init(initializer, options); }

void Yaga::init(Initializer const& init, Options const& options)
{
    smt.db().learned().clear();
    smt.db().asserted().clear();
    init.setup(smt, options);

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