#include "Linear_polynomial.h"

namespace yaga::utils {

void Linear_polynomial::add(Linear_polynomial && x) {
    for (std::size_t i = 0; i < x.vars.size(); ++i)
    {
        int var = x.vars[i];
        auto found = std::find(vars.begin(), vars.end(), var);
        if (found != vars.end()) {
            auto ix = std::distance(vars.begin(), found);
            coef[ix] += x.coef[i];
            if (coef[ix] == 0) {
                coef.erase(coef.begin() + ix);
                vars.erase(vars.begin() + ix);
            }
        } else {
            vars.push_back(var);
            coef.push_back(x.coef[i]);
        }
    }

    constant += x.constant;
}

void Linear_polynomial::sub(Linear_polynomial&& x) {
    // Negate the other polynomial ( *= -1 ).
    for (std::size_t i = 0; i < x.coef.size(); ++i)
    {
        x.coef[i] *= (-1);
    }
    x.constant *= (-1);

    // Then add it.
    add(std::move(x));
}

void Linear_polynomial::negate()
{
    for (auto& c : coef)
    {
        c = -c;
    }
    constant = -constant;
}

void Linear_polynomial::sort(Trail& trail) {
    using poly_element = std::pair<int, Rational>;
    std::vector<poly_element> to_sort;
    for (std::size_t i = 0; i < vars.size(); ++i)
    {
        to_sort.push_back({vars[i], coef[i]});
    }

    std::sort(to_sort.begin(), to_sort.end(), [&](poly_element a, poly_element b){
        Variable a_var(a.first, Variable::rational);
        Variable b_var(b.first, Variable::rational);
        return trail.decision_level(a_var) > trail.decision_level(b_var);
    });

    for (std::size_t i = 0; i < to_sort.size(); ++i)
    {
        vars[i] = to_sort[i].first;
        coef[i] = to_sort[i].second;
    }
}

void Linear_polynomial::subtract_var(Variable v)
{
    assert(std::ranges::find(vars, v.ord()) == vars.end());
    this->vars.push_back(v.ord());
    this->coef.emplace_back(-1);
}

}