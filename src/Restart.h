#ifndef YAGA_RESTART_H
#define YAGA_RESTART_H

#include "Database.h"
#include "Event_listener.h"
#include "Trail.h"

namespace yaga {

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

    /** Returns false
     *
     * @return always false
     */
    bool should_restart() const override { return false; }
};

/** Restart policy based on Luby sequence.
 */
class Luby_restart final : public Restart {
public:
    virtual ~Luby_restart() = default;

    inline Luby_restart() { next(); }

    /** Mark that a conflict has occurred.
     *
     * @param db clause database
     * @param trail current solver trail
     * @param learned learned clause
     */
    void on_learned_clause(Database&, Trail&, Clause const&) override { --countdown; }

    /** Reset countdown to the next restart to the next element of Luby
     * sequence.
     *
     * @param db clause database
     * @param trail current solver trail
     */
    void on_restart(Database&, Trail&) override { next(); }

    /** Check whether the solver should restart
     *
     * @return true iff number of conflicts since the last restart exceeded
     * current limit
     */
    bool should_restart() const override { return countdown <= 0; }

    /** Generate a luby sequence element given a 1-based element index
     *
     * @param index 1-based element index
     * @return Luby sequence element at position @p index
     */
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
    int countdown = 0;
    // current luby sequence index
    int index = 0;
    // restart multiplier
    int mult = 550;

    inline void next() { countdown = luby(++index) * mult; }
};

/** Dynamic restart policy based on clause glucose (LBD - number of distinct
 * decision levels in a clause)
 *
 * Implementation as described in "Weaknesses of CDCL Solvers", Armin Biere
 */
class Glucose_restart final : public Restart {
public:
    virtual ~Glucose_restart() = default;

    inline Glucose_restart() { countdown = min_num_conflicts; }

    /** Reset minimal number of clauses needed for restart.
     *
     * @param db clause database
     * @param trail current solver trail
     */
    void on_restart(Database&, Trail&) override { countdown = min_num_conflicts; }

    /** Compute glucose (LBD) of @p learned and udpate global and moving LBD
     * average.
     *
     * @param db clause database
     * @param trail current solver trail
     * @param learned newly learned clause
     */
    void on_learned_clause(Database&, Trail& trail, Clause const& learned) override
    {
        --countdown;
        std::vector<int> levels(learned.size());
        auto it = levels.begin();
        for (auto lit : learned)
        {
            *it++ = trail.decision_level(lit.var()).value();
        }
        std::sort(levels.begin(), levels.end());
        add_glucose(std::distance(levels.begin(), std::unique(levels.begin(), levels.end())));
    }

    /** Check whether the solver should restart
     *
     * @return true iff moving average of LBDs exceeds global average of LBDs by
     * some threshold
     */
    bool should_restart() const override { return countdown <= 0 && fast() >= threshold * slow(); }

    /** Get value of slow moving exponential average of LBDs
     *
     * @return slow moving exponential average of LBDs
     */
    inline float slow() const { return slow_ema; }

    /** Get value of fast moving exponential average of LBDs
     *
     * @return fast moving exponential average of LBDs
     */
    inline float fast() const { return fast_ema; }

    /** Set minimal number of conflict before a restart
     *
     * @param min_conflicts minimal number of conflicts before restart
     * @return this
     */
    inline Glucose_restart& set_min_conflicts(int min_conflicts)
    {
        countdown = min_num_conflicts = min_conflicts;
        return *this;
    }

    /** Set exponent for the slow moving LBD average
     *
     * @param min_conflicts minimal number of conflicts before restart
     * @return this
     */
    inline Glucose_restart& set_slow_exp(int exp)
    {
        slow_exp = exp;
        return *this;
    }

    /** Set exponent for the fast moving LBD average
     *
     * @param min_conflicts minimal number of conflicts before restart
     * @return this
     */
    inline Glucose_restart& set_fast_exp(int exp)
    {
        fast_exp = exp;
        return *this;
    }

private:
    int countdown = 0;
    // slow moving exponential average
    float slow_ema = 0.f;
    // fast moving exponential average
    float fast_ema = 0.f;
    // exponent for the slow exponential average
    int slow_exp = 13;
    // exponent for the fast exponential average
    int fast_exp = 5;
    // minimal number of conflicts before a restart
    int min_num_conflicts = 50;

    // by how much does the fast average have to exceed the slow average in
    // order to restart
    inline static float const threshold = 1.3f;

    // recompute slow/fast averages of LDBs
    inline void add_glucose(int lbd)
    {
        slow_ema += (lbd - slow_ema) / static_cast<float>(1 << slow_exp);
        fast_ema += (lbd - fast_ema) / static_cast<float>(1 << fast_exp);
    }
};

} // namespace yaga

#endif // YAGA_RESTART_H