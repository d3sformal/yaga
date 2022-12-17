#ifndef PERUN_EVSIDS_H_
#define PERUN_EVSIDS_H_

#include <vector>

#include "Clause.h"
#include "Literal.h"
#include "Variable.h"
#include "Variable_order.h"

namespace perun {

class Evsids final : public Variable_order {
public:
    virtual ~Evsids() = default;

    void on_init(Database& db, Trail& trail) override;
    void on_variable_resize(Variable::Type type, int num_vars) override;
    void on_learned_clause(Database& db, Trail& trail, Clause* learned) override;
    void on_conflict_resolved(Database& db, Trail& trail, const Clause& other) override;
    std::optional<Variable> pick(Database& db, Trail& trail) override;

    // get current score of a boolean variable
    inline float score(int var_ord) const { return score_[var_ord]; }
private:
    // map boolean variable ordinal -> VSIDS score 
    std::vector<float> score_;
    // score grow factor (inverse dacay factor)
    float grow_ = 1.05f;
    // current variable increment value when it is bumped
    float inc_ = 1.0f;

    // when a score exceeds this threshold, all scores are rescaled
    inline static const float score_threshold = 1e35f;

    inline void rescale() 
    {
        for (auto& score : score_)
        {
            score /= score_threshold;
        }
        inc_ /= score_threshold;
    }

    inline void decay() { inc_ *= grow_; }

    inline void bump(int var_ord)
    {
        score_[var_ord] += inc_;
        if (score_[var_ord] >= score_threshold)
        {
            rescale();
        }
    }
};

}

#endif // PERUN_EVSIDS_H_