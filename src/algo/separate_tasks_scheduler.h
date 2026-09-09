#ifndef SEPARATE_TASKS_SCHEDULER_H
#define SEPARATE_TASKS_SCHEDULER_H

#include <chrono>
#include <string>
#include <vector>

#include "util/bitvec.h"
#include "util/domain_settings_manager.h"
#include "util/hashmap.h"

class Encoding;
class FactAnalysis;
class HtnInstance;
class Position;

/**
 * Solves the initial task network incrementally in consecutive batches.
 *
 * After each successful batch, the scheduler remembers the selected SAT
 * variables and the state at the new task boundary. Domain settings determine
 * whether solved batches are committed permanently or retained as assumptions
 * that may be relaxed after a later failure.
 */
class SeparateTasksScheduler {
private:
    HtnInstance& _htn;
    FactAnalysis& _facts;

    const int _initial_task_count;
    int _solved_task_count = 0;
    int _target_task_count = 1;
    int _next_batch_size = 1;
    int _solved_position_count = 0;

    std::string _domain_name;
    DomainSettingsManager _settings_manager;
    bool _commit_solved_tasks_permanently;
    bool _restart_planner = false;

    BitVec _initial_positive_facts;
    BitVec _initial_negative_facts;
    BitVec _positive_facts_after_solved_tasks;
    BitVec _negative_facts_after_solved_tasks;

    std::chrono::high_resolution_clock::time_point _batch_start_time;
    long long _previous_batch_duration_ms = 0;

    std::vector<NodeHashSet<int>> _solved_task_snapshots;
    std::vector<int> _solved_position_count_history;
    std::vector<int> _batch_size_history;

    void saveSolvedBatch(Encoding& encoding, const std::vector<Position*>& leaves, int solvedPositionCount);
    void adaptNextBatchSize();
    void updateBoundaryState(Encoding& encoding, const std::vector<Position*>& leaves, int solvedPositionCount);
    void replaySelectedActions(Encoding& encoding, const std::vector<Position*>& leaves, int solvedPositionCount);
    void accumulatePossibleEffects(const std::vector<Position*>& leaves, int solvedPositionCount);

public:
    SeparateTasksScheduler(HtnInstance& htn, FactAnalysis& facts, const std::string& domainFilename);

    /** Display progress through the initial task network. */
    void displayProgress() const;

    /** Reapply the latest solved-prefix snapshot as clauses or assumptions. */
    void applySolvedTaskConstraints(Encoding& encoding);

    /** Return the exclusive frontier boundary for primitive-plan assumptions. */
    int getPrimitiveAssumptionBoundary(int frontierSize) const;

    /**
     * Record a successfully solved batch and choose the next target.
     * @return true when the entire initial task network has been solved.
     */
    bool updateAfterSolved(Encoding& encoding, const std::vector<Position*>& leaves);

    /** Relax saved batches after an abstract-plan failure, or request a restart for a permanently committed prefix. */
    bool handleAbstractPlanFailure(Encoding& encoding);

    int getSolvedPositionCount() const { return _solved_position_count; }
    bool commitsSolvedTasksPermanently() const { return _commit_solved_tasks_permanently; }
    const BitVec& getPositiveFactsAfterSolvedTasks() const { return _positive_facts_after_solved_tasks; }
    const BitVec& getNegativeFactsAfterSolvedTasks() const { return _negative_facts_after_solved_tasks; }
    bool mustRestartPlanner() const { return _restart_planner; }
};

#endif
