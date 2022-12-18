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

class Glucose_restart final : public Restart {
public:
    virtual ~Glucose_restart() = default;

    inline Glucose_restart() { countdown_ = min_num_conflicts_; }

    void on_restart(Database&, Trail&) override { countdown_ = min_num_conflicts_; }

    void on_learned_clause(Database&, Trail& trail, Clause* learned) override 
    {
        --countdown_;
        std::vector<int> levels(learned->size());
        auto it = levels.begin();
        for (auto lit : *learned)
        {
            *it++ = trail.decision_level(lit.var()).value();
        }
        add_glucose(std::distance(levels.begin(), std::unique(levels.begin(), levels.end())));
    }

    bool should_restart() const override { return countdown_ <= 0 && fast_ >= threshold_ * slow_; }

    // get value of the slow moving average
    inline float slow() const { return slow_; }
    // get value of the fast moving average
    inline float fast() const { return fast_; }

    // set minimal number of conflicts before a restart
    inline Glucose_restart& set_min_conflicts(int min_conflicts)
    {
        countdown_ = min_num_conflicts_ = min_conflicts;
        return *this;
    }

    // set exponent for the slow moving average
    inline Glucose_restart& set_slow_exp(int exp)
    {
        slow_exp_ = exp;
        return *this;
    }

    // set exponent for the fast moving average
    inline Glucose_restart& set_fast_exp(int exp)
    {
        fast_exp_ = exp;
        return *this;
    }
private:
    int countdown_ = 0;
    // slow moving exponential average
    float slow_ = 0.f;
    // fast moving exponential average
    float fast_ = 0.f;
    // exponent for the slow exponential average
    int slow_exp_ = 13; 
    // exponent for the fast exponential average
    int fast_exp_ = 5;
    // minimal number of conflicts before a restart
    int min_num_conflicts_ = 50;

    // by how much does the fast average have to exceed the slow average in order to restart
    inline static const float threshold_ = 1.3f;

    inline void add_glucose(int lbd) 
    {
        slow_ += (lbd - slow_) / static_cast<float>(1 << slow_exp_);
        fast_ += (lbd - fast_) / static_cast<float>(1 << fast_exp_);
    }
};

}

#endif // PERUN_RESTART_H_