#include <span>

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

void Qf_uflra::setup(Solver& solver, Options const& options) const
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

    auto& uf = theories.add_theory<Uninterpreted_functions>(solver.tm());

    // add heuristics
    solver.set_restart_policy<Glucose_restart>();
    solver.set_variable_order<Generalized_vsids>(lra);
}

Yaga::Yaga(Initializer const& initializer, Options const& options, terms::Term_manager const& tm) : smt(tm) { init(initializer, options); }

void Yaga::init(Initializer const& init, Options const& options)
{
    smt.db().learned().clear();
    smt.db().asserted().clear();
    init.setup(smt, options);

    // find the LRA and UF plugins so we can add linear constraints and function applications
    lra = nullptr;
    if (auto combination = dynamic_cast<Theory_combination*>(smt.theory()))
    {
        for (auto theory : combination->theories())
        {
            if (auto lraPlugin = dynamic_cast<Linear_arithmetic*>(theory))
            {
                lra = lraPlugin;
            } else if (auto ufPlugin = dynamic_cast<Uninterpreted_functions*>(theory)) {
                uf = ufPlugin;
                uf->register_solver(this);
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

Variable Yaga::make_function_application(Variable::Type type, terms::term_t app_term)
{
    Variable result = make(type);
    uf->register_application_term(result, app_term);
    return result;
}

Literal Yaga::make_bool()
{
    return Literal{make(Variable::boolean).ord()};
}

void Yaga::propagate_mapping(std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, int> >  mapping) {
    uf->register_mapping(mapping);
}

void Yaga::propagate_mapping(std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, Literal> >  mapping) {
    uf->register_mapping(mapping);
}

std::unordered_map<terms::term_t, Uninterpreted_functions::function_value_map_t>& Yaga::get_function_model() {
    return uf->get_model();
}

}