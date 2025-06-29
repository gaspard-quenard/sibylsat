#ifndef SEPARATE_TASKS_SCHEDULER_H
#define SEPARATE_TASKS_SCHEDULER_H

#include <chrono>
#include <string>
#include <vector>
#include "sat/encoding.h"
#include "data/layer.h"         
#include "util/domain_settings_manager.h" 
#include "util/log.h"

class SeparateTasksScheduler {

    private:
    int    _num_init_tasks_resolved;      // How many tasks have been solved so far.
    int    _init_task_network_size;       // Total number of initial tasks.
    int    _current_task_index;          // Next task index to try.
    int    _num_tasks_to_solve;           // Number of tasks to solve in the next iteration.
    int    _num_pos_done;               // Number of positions already solved.
    bool   _tcp_exponential_resolving;   // Whether to adjust _num_tasks_to_solve exponentially.
    bool   _add_tasks_as_clauses;         // Whether to add tasks accomplished as clauses or assumptions.
    const USigSet _init_state;          // Initial state of the HTN instance.
    HtnInstance& _htn;            // Reference to the HTN instance.
    USigSet _reachable_state_pos_after_tasks_accomplished; // State after tasks accomplished (used for fact analysis).
    USigSet _reachable_state_neg_after_tasks_accomplished; // State after tasks accomplished (used for fact analysis).
    

    BitVec _init_state_pos_bitvec;       // Bit vector for positive initial state facts.
    BitVec _init_state_neg_bitvec;       // Bit vector for negative initial state facts.
    BitVec _reachable_state_pos_after_tasks_accomplished_bitvec; // Bit vector for reachable state after tasks accomplished (used for fact analysis).
    BitVec _reachable_state_neg_after_tasks_accomplished_bitvec; // Bit vector for reachable state after tasks accomplished (used for fact analysis).

    std::string _domain_name;           // Name of the domain.
    DomainSettingsManager _settings_manager;  // Individual domain settings manager. Here, it indicate for each domain whether their tasks are independent or not.
    
    std::chrono::high_resolution_clock::time_point _init_time_spend_to_solve_tasks;
    long long _last_time_spend_to_solve_tasks;
    
    std::vector<NodeHashSet<int>> _vars_tasks_accomplished;     // Snapshots of SAT variables (tasks solved).
    std::vector<int> _num_pos_done_at_each_step;                // Positions done at each step.
    std::vector<int> _num_tasks_solved_at_each_step;            // Number of tasks solved in each step.
    
    int    _num_failed_sat;             // Counter for failed SAT attempts.
    bool   _restart_planner;           // Flag to indicate that the planner must be restarted.

//     enum class Phase { EXPLORE, SEARCH };   // current optimisation stage
// Phase      _phase             = Phase::EXPLORE;

// size_t     _lo_batch          = 1;      // lower edge of the current bracket
// size_t     _hi_batch          = 1;      // upper edge of the current bracket
// size_t     _best_batch        = 1;      // batch size that gave best throughput so far
// double     _best_tp           = 0.0;    // “best throughput” (tasks / ms)

// static constexpr double EPS   = 0.03;   // 3 % improvement threshold
/* -------------------------------------------- */


public:
    /**
     * Constructor.
     *
     * @param htn The HTN instance.
     */
    SeparateTasksScheduler(HtnInstance& htn);

    /**
     * Display an advancement/progress bar showing how many tasks have been solved.
     */
    void displayAdvancementBar() const;


    void updateReachableStateAfterTasksAccomplished(Encoding &enc, const std::vector<Layer*> &layers, int layerIdx, int solvePositions);

    /**
     * If there are previously saved snapshots of SAT variables (from solved tasks),
     * add them as assumptions in the encoding.
     *
     * @param enc The encoding object.
     */
    void addAssumptionsForSolvedTasks(Encoding &enc);

    /**
     * Given the current layer size, compute the position until which to add assumptions.
     *
     * @param layerSize The size of the current layer.
     * @return The computed index (assumptions_until).
     */
    int getAssumptionsUntil(int layerSize) const;

    int getPositionsDone(int layerSize) const {
        return _num_pos_done;
    }

    const bool addTasksAsClauses() const {
        return _add_tasks_as_clauses;
    }

    /**
     * When a SAT call has solved the current batch of tasks, update the scheduler state.
     * This method saves a snapshot of the SAT variables and adjusts the number of tasks to solve next.
     *
     * @param enc The encoding object (to extract the snapshot).
     * @param layers The vector of layers.
     * @param layerIdx The current layer index.
     * @return True if all initial tasks have been solved; false otherwise.
     */
    bool updateAfterSolved(Encoding &enc, const std::vector<Layer*> &layers, int layerIdx);


    const USigSet& getReachableStatePosAfterTasksAccomplished() const {
        return _reachable_state_pos_after_tasks_accomplished;
    }
    const USigSet& getReachableStateNegAfterTasksAccomplished() const {
        return _reachable_state_neg_after_tasks_accomplished;
    }

    const BitVec& getReachableStatePosAfterTasksAccomplishedBitVec() const {
        return _reachable_state_pos_after_tasks_accomplished_bitvec;
    }
    const BitVec& getReachableStateNegAfterTasksAccomplishedBitVec() const {
        return _reachable_state_neg_after_tasks_accomplished_bitvec;
    }

    /**
     * In case the virtual plan cannot be found, relax the previously added assumptions.
     * Depending on the setting, this may trigger a restart of the full planner.
     *
     * @param enc The encoding object.
     * @return True if a virtual plan was eventually found; false otherwise.
     */
    bool handleVirtualPlanFailure(Encoding &enc, int layerSize);

    /**
     * @return True if the scheduler indicates that the full planner must be restarted.
     */
    bool mustRestartPlanner() const;
};

#endif // SEPARATE_TASKS_SCHEDULER_H
