
#ifndef DOMPASCH_TREE_REXX_PLANNER_H
#define DOMPASCH_TREE_REXX_PLANNER_H
 
#include "util/names.h"
#include "util/params.h"
#include "util/hashmap.h"
#include "data/position.h"
#include "data/htn_instance.h"
#include "algo/instantiator.h"
#include "algo/arg_iterator.h"
#include "algo/precondition_inference.h"
#include "algo/minres.h"
#include "algo/fact_analysis.h"
#include "algo/retroactive_pruning.h"
#include "algo/domination_resolver.h"
#include "algo/plan_writer.h"
#include "algo/tree_expander.h"
#include "sat/encoding.h"
#include "data/tdg.h"
#include "algo/separate_tasks_scheduler.h"
#include <optional>

typedef std::pair<std::vector<PlanItem>, std::vector<PlanItem>> Plan;

class Planner {

public:
    typedef std::function<bool(const USignature&, bool)> StateEvaluator;

private:
    Parameters& _params;
    HtnInstance& _htn;

    Position* _root_position = nullptr;
    std::vector<Position*> _leaf_positions;

    FactAnalysis _analysis;
    Instantiator _instantiator;
    Encoding _enc;
    Statistics& _stats;
    MinRES _minres;
    RetroactivePruning _pruning;
    DominationResolver _domination_resolver;
    PlanWriter _plan_writer;
    size_t _depth = 0;

    const int _verbosity;

    const bool _use_sibylsat_expansion;
    std::vector<Position*> _sibylsat_nodes_to_develop;

    // For optimal planning
    const bool _optimal;
    std::optional<TDG> _tdg;
    size_t _last_number_of_soft_lits = 0;
    std::unordered_set<int> _soft_lits;

    // For separate tasks
    const bool _separate_tasks;
    std::unique_ptr<SeparateTasksScheduler> _separate_tasks_scheduler;
    
    bool _nonprimitive_support;
    float _optimization_factor;

    Plan _plan;

    // statistics
    size_t _num_instantiated_positions = 0;
    size_t _num_instantiated_actions = 0;
    size_t _num_instantiated_reductions = 0;

    TreeExpander _tree_expander;

public:
    Planner(Parameters& params, HtnInstance& htn) : _params(params), _htn(htn), _stats(Statistics::getInstance()),
            _verbosity(params.getIntParam("v")),
            _analysis(_htn, true, _htn.getParams().isNonzero("optimal")), 
            _use_sibylsat_expansion(_params.isNonzero("sibylsat")),
            _optimal(_params.isNonzero("optimal")),
            _separate_tasks(_params.isNonzero("separateTasks") && _htn.getInitReduction().getSubtasks().size() > 1 && _use_sibylsat_expansion && !_optimal),
            _instantiator(params, htn, _analysis), 
            _enc(_params, _htn, _analysis, _root_position, _leaf_positions), 
            _minres(_htn), 
            _pruning(_enc),
            _domination_resolver(_htn),
            _plan_writer(_htn, _params),
            _nonprimitive_support(_params.isNonzero("nps")), 
            _optimization_factor(_params.getFloatParam("of")),
            _tree_expander(
                    _params,
                    _htn,
                    _root_position,
                    _leaf_positions,
                    _analysis,
                    _instantiator,
                    _enc,
                    _stats,
                    _pruning,
                    _domination_resolver,
                    _tdg,
                    _separate_tasks_scheduler,
                    _depth,
                    _use_sibylsat_expansion,
                    _separate_tasks,
                    _nonprimitive_support,
                    _optimal,
                    _num_instantiated_positions,
                    _num_instantiated_actions,
                    _num_instantiated_reductions) {

        // Mine additional preconditions for reductions from their subtasks
        PreconditionInference::infer(_htn, _analysis, PreconditionInference::MinePrecMode(_params.getIntParam("mp")));

        if (_htn.getParams().isNonzero("mutex") && _analysis.checkGroundingFacts()) {
            _htn._sas_plus->cleanMutexGroupsWithPandaPiGrounderPreprocessingFacts(_analysis.getGroundPosFacts());
        }

        if (_optimal) {
            // Construct the TDG and infer the admissible values for each tasks and methods
            _tdg.emplace(_htn);
        }

        if (_separate_tasks) {
            // Initialize the separate tasks scheduler
            _separate_tasks_scheduler = std::make_unique<SeparateTasksScheduler>(/*htn=*/ htn);
        }
    }
    int findPlan();
    void optimizeCurrentPlan();

    const bool mustRestartPlanner() const { 
        return (_separate_tasks && _separate_tasks_scheduler->mustRestartPlanner());
    }

private:
    /**
     * Expand the given leaves in the search tree.
     */
    void expandLeaves(const std::vector<Position*>& leavesToExpand);

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

    void setSoftLitsForCurrentLeaves();

    void printStatistics();

};

#endif
