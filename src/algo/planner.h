
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

class Planner {

private:
    Parameters& _params;
    HtnInstance& _htn;
    TreeExpander _tree_expander;
    Position*& _root_position;
    std::vector<Position*>& _leaf_positions;
    FactAnalysis& _analysis;
    Encoding _enc;
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
    Planner(Parameters& params, HtnInstance& htn)
            : _params(params),
              _htn(htn),
              _tree_expander(_params, _htn),
              _root_position(_tree_expander.getRootPositionRef()),
              _leaf_positions(_tree_expander.getLeafPositions()),
              _analysis(_tree_expander.getAnalysis()),
              _enc(_params, _htn, _analysis, _root_position, _leaf_positions),
              _pruning(std::make_unique<RetroactivePruning>(_enc)),
              _plan_writer(_htn, _params),
              _use_sibylsat_expansion(_params.isNonzero("sibylsat")),
              _optimal(_params.isNonzero("optimal")),
              _separate_tasks(_params.isNonzero("separateTasks")
                      && _htn.getInitReduction().getSubtasks().size() > 1
                      && _use_sibylsat_expansion
                      && !_optimal),
              _optimization_factor(_params.getFloatParam("of")) {
        PreconditionInference::infer(_htn, _analysis, PreconditionInference::MinePrecMode(_params.getIntParam("mp")));
        if (_htn.getParams().isNonzero("mutex") && _analysis.checkGroundingFacts()) {
            _htn._sas_plus->cleanMutexGroupsWithPandaPiGrounderPreprocessingFacts(_analysis.getGroundPosFacts());
        }
        if (_optimal) {
            _tdg.emplace(_htn);
            _tree_expander.attachTDG(*_tdg);
        }
        _tree_expander.attachPruning(*_pruning);
        if (_separate_tasks) {
            _separate_tasks_scheduler = std::make_unique<SeparateTasksScheduler>(_htn);
            _tree_expander.attachSeparateTasksScheduler(*_separate_tasks_scheduler);
        }
    }
    int findPlan();
    void optimizeCurrentPlan();

    const bool mustRestartPlanner() const {
        return _separate_tasks_scheduler != nullptr && _separate_tasks_scheduler->mustRestartPlanner();
    }

private:
    void initializeSearchTree() {
        // Create the initial search tree with only the root and the goal node as leaves.
        _tree_expander.createInitialLeaves();

        // Encode the root method
        _enc.encode(*_leaf_positions[0]);
        // Encode the goal node
        _enc.encode(*_leaf_positions[1]);
    }

    void printTreeStatistics() const { _tree_expander.printStatistics(); }

    /**
     * Expand the given leaves in the search tree.
     */
    TreeExpander::ExpansionResult expandLeaves(const std::vector<Position*>& leavesToExpand);

    /**
     * Encode the new leaves into a SAT formula after an expansion step.
     */
    void encodeLeaves(const TreeExpander::ExpansionResult& expansion);

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
