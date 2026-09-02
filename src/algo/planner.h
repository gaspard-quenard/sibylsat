
#ifndef DOMPASCH_TREE_REXX_PLANNER_H
#define DOMPASCH_TREE_REXX_PLANNER_H
 
#include "util/params.h"
#include "data/position.h"
#include "data/htn_instance.h"
#include "algo/plan_writer.h"
#include "algo/precondition_inference.h"
#include "algo/separate_tasks_scheduler.h"
#include "algo/tree_expander.h"
#include "sat/encoding.h"
#include <optional>

typedef std::pair<std::vector<PlanItem>, std::vector<PlanItem>> Plan;

/**
 * How the search tree is grown each iteration.
 */
enum class ExpansionMode {
    BFS,      // Expand every leaf of the current frontier.
    SIBYLSAT  // Expand only the leaves selected from the last abstract plan.
};

/**
 * What kind of solution the SAT solver is asked for.
 */
enum class SolveMode {
    SATISFICING,  // Any primitive plan.
    OPTIMAL       // A primitive plan whose cost matches the best abstract plan.
};

/**
 * The orthogonal search options that determine the planner's behaviour.
 */
struct SearchMode {
    ExpansionMode expansion;
    SolveMode solve;
    bool separateTasks;
};

class Planner {

private:
    Parameters& _params;
    HtnInstance& _htn_instance;
    TreeExpander _tree_expander;
    Position*& _root_position;
    std::vector<Position*>& _leaf_positions;
    FactAnalysis& _analysis;
    MethodEffectAnalysis& _method_effects;
    Encoding _encoding;
    std::unique_ptr<RetroactivePruning> _pruning;
    PlanWriter _plan_writer;

    const bool _use_sibylsat_expansion;
    std::vector<Position*> _sibylsat_nodes_to_develop;

    // For optimal planning
    const bool _optimal;
    std::optional<TDG> _tdg;

    const bool _separate_tasks;
    std::unique_ptr<SeparateTasksScheduler> _separate_tasks_scheduler;
    
    float _optimization_factor;

public:
    Planner(Parameters& params, HtnInstance& htn);
    int findPlan();
    void optimizeCurrentPlan();

    const bool mustRestartPlanner() const {
        return _separate_tasks_scheduler != nullptr && _separate_tasks_scheduler->mustRestartPlanner();
    }

private:
    /**
     * Build the initial search tree (root + goal leaves) and encode it.
     */
    void initializeSearchTree();

    /**
     * Derive the search mode from the command-line parameters.
     */
    SearchMode determineSearchMode() const;

    /**
     * Configure the planner components that depend on the search mode
     * (TDG, pruning, separate-tasks scheduler, mutex cleanup).
     */
    void configure();

    void printTreeStatistics() const { _tree_expander.printStatistics(); }

    /**
     * Grow the search tree and encode the new frontier, according to the
     * expansion mode (BFS expands all leaves, SibylSat only the selected ones).
     */
    void expandAndEncode(SearchMode mode);

    /**
     * Ask the SAT solver for a solution of the current search tree.
     * Returns true if a solution was found.
     */
    bool solveCurrentTree(SearchMode mode);

    /**
     * After a failed solve, decide which leaves to expand next.
     * Returns false if the problem is proven impossible.
     */
    bool selectNextLeavesToDevelop(SearchMode mode);

    /**
     * Extract, optimize and output the found plan.
     */
    int outputSolution();

    /**
     * Launch two SAT calls:
     * 1) The first one looks for the best primitive plan in the search tree, and returns its cost.
     * 2) The second one looks for the best abstract plan in the search tree, and returns its cost.

     * Then compare the cost of the best primitive plan to the cost of the best abstract plan.
     * The plan is globally optimal if its cost is equal to the cost of the best abstract plan in the search tree.
     * Return true if the plan is globally optimal, false otherwise.
     * If the plan is not globally optimal, fill `_sibylsat_nodes_to_develop` with the leaves 
     * which contains a method in the optimal abstract plan.
     */
    bool findGloballyOptimalSolutionInSearchTree();

    /**
     * Launch a SAT call on the search tree for any primitive plan.
     * Return true if a primitive plan is found, false otherwise.
     */
    bool findPrimitiveSolutionInSearchTree();

    /**
     * Solve the current search tree incrementally, task by task, using the
     * separate-tasks scheduler. Returns true if all initial tasks are solved.
     */
    bool solveWithSeparateTasks();

    /**
     * Launch a SAT call on the search tree for any abstract plan and select the leaves whose
     * reductions must be expanded next (any leaves which contains a reduction in the abstract plan). 
     * Return false if no abstract plan is found, true otherwise.
     */
    bool findAbstractPlanInSearchTree();

    /**
     * Fill `_sibylsat_nodes_to_develop` from an abstract plan, optionally
     * restricted to its first `leafLimit` leaves.
     */
    void collectLeavesToDevelopFromAbstractPlan(const std::vector<PlanItem>& abstractPlan, int leafLimit = -1);

    /**
     * In optimal mode, set a MaxSat cost for each operation of the current leaves of the search tree which correspond to 
     * an admissible cost of those operations (which is found using the TDG heuristics).
     */
    void setSoftLitsForCurrentLeaves();

};

#endif
