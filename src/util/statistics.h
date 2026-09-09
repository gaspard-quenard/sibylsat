#ifndef SIBYLSAT_STATISTICS_H
#define SIBYLSAT_STATISTICS_H

#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <map>
#include <vector>

/** Encoding phases to which generated clauses are attributed. */
enum class EncodingStage {
    ACTION_CONSTRAINTS,
    ACTION_EFFECTS,
    AT_LEAST_ONE_ELEMENT,
    AT_MOST_ONE_ELEMENT,
    DIRECT_FRAME_AXIOMS,
    EXPANSIONS,
    FACT_VARIABLE_ENCODING,
    FORBIDDEN_OPERATIONS,
    INDIRECT_FRAME_AXIOMS,
    PREDECESSORS,
    Q_CONSTANT_EQUALITY,
    Q_FACT_SEMANTICS,
    Q_TYPE_CONSTRAINTS,
    REDUCTION_CONSTRAINTS,
    SUBSTITUTION_CONSTRAINTS,
    ASSUMPTIONS,
    PLAN_LENGTH_COUNTING,
    MUTEXES,
    COUNT
};

/** Independently accumulated wall-clock measurements. */
enum class TimingStage {
    GROUNDING,
    MUTEX_COMPUTATION,
    EXPANSION,
    ENCODING,
    SOLVER,
    TOTAL
};

/** Collects statistics for one invocation of the planner. */
class Statistics {
public:
    using Count = std::uint64_t;
    using Duration = std::chrono::nanoseconds;

    Statistics() = default;
    Statistics(const Statistics&) = delete;
    Statistics& operator=(const Statistics&) = delete;
    Statistics(Statistics&&) = delete;
    Statistics& operator=(Statistics&&) = delete;

    void beginPosition();
    void endPosition();

    /** Attribute subsequently generated clauses to this phase until end(). */
    void begin(EncodingStage stage);
    void end(EncodingStage stage);

    void beginTiming(TimingStage stage);
    void endTiming(TimingStage stage);
    Duration getTiming(TimingStage stage) const;

    void recordLiteral() { ++_num_literals; }
    void recordClause() { ++_num_clauses; }
    void recordAssumption() { ++_num_assumptions; }
    void clearAssumptionCount() { _num_assumptions = 0; }

    Count getNumClauses() const { return _num_clauses; }
    Count getNumLiterals() const { return _num_literals; }
    Count getNumAssumptions() const { return _num_assumptions; }

    void print() const;

    /**
     * Discard measurements from an abandoned search while retaining
     * preprocessing measurements and the running whole-invocation timer.
     */
    void resetSearchStatistics();

private:
    using Clock = std::chrono::steady_clock;
    static constexpr std::size_t NUM_ENCODING_STAGES = static_cast<std::size_t>(EncodingStage::COUNT);

    static std::size_t stageIndex(EncodingStage stage);
    static const char* stageName(EncodingStage stage);
    static const char* timingName(TimingStage stage);

    Count _num_clauses = 0;
    Count _num_literals = 0;
    Count _num_assumptions = 0;
    Count _previous_num_clauses = 0;
    Count _previous_num_literals = 0;
    Count _num_clauses_at_stage_start = 0;

    std::array<Count, NUM_ENCODING_STAGES> _num_clauses_per_stage{};
    std::vector<EncodingStage> _current_stages;
    std::map<TimingStage, Clock::time_point> _active_timings;
    std::map<TimingStage, Duration> _elapsed_times;
};

#endif
