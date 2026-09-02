#include <algorithm>
#include <assert.h> 

#include "planner.h"
#include "util/log.h"
#include "util/names.h"
#include "sat/plan_optimizer.h"

Planner::Planner(Parameters& params, HtnInstance& htn)
        : _params(params),
          _htn_instance(htn),
          _tree_expander(_params, _htn_instance),
          _root_position(_tree_expander.getRootPositionRef()),
          _leaf_positions(_tree_expander.getLeafPositions()),
          _analysis(_tree_expander.getAnalysis()),
          _method_effects(_tree_expander.getMethodEffects()),
          _encoding(_params, _htn_instance, _analysis, _root_position, _leaf_positions),
          _pruning(std::make_unique<RetroactivePruning>(_encoding)),
          _plan_writer(_htn_instance, _params),
          _use_sibylsat_expansion(_params.isNonzero("sibylsat")),
          _optimal(_params.isNonzero("optimal")),
          _separate_tasks(_params.isNonzero("separateTasks")
                  && _htn_instance.getInitReduction().getSubtasks().size() > 1
                  && _use_sibylsat_expansion
                  && !_optimal),
          _optimization_factor(_params.getFloatParam("of")) {
    configure();
}

void Planner::configure() {
    PreconditionInference::infer(_htn_instance, _method_effects,
            PreconditionInference::MinePrecMode(_params.getIntParam("mp")));
    if (_htn_instance.getParams().isNonzero("mutex")) {
        _htn_instance._sas_plus->cleanMutexGroupsWithPandaPiGrounderPreprocessingFacts(
                _analysis.getGroundPosFacts());
    }
    if (_optimal) {
        _tdg.emplace(_htn_instance);
        _tree_expander.attachTDG(*_tdg);
    }
    _tree_expander.attachPruning(*_pruning);
    if (_separate_tasks) {
        _separate_tasks_scheduler = std::make_unique<SeparateTasksScheduler>(_htn_instance);
    }
}

SearchMode Planner::determineSearchMode() const {
    return {
        _use_sibylsat_expansion ? ExpansionMode::SIBYLSAT : ExpansionMode::BFS,
        _optimal ? SolveMode::OPTIMAL : SolveMode::SATISFICING,
        _separate_tasks
    };
}

int Planner::findPlan() {

    int iteration = 0;
    Log::i("Iteration %i.\n", iteration);

    // Build the initial search tree before entering the search loop.
    initializeSearchTree();

    const SearchMode mode = determineSearchMode();
    const int maxIterations = _params.getIntParam("D");

    if (mode.expansion == ExpansionMode::SIBYLSAT) {
        // Only develop the leaf which contains the _top_method
        _sibylsat_nodes_to_develop.push_back(_leaf_positions[0]);
    }

    // Main loop of the search. We keep expanding the search tree until we find a solution,
    // or reach the maximum iteration limit.
    while (true) {

        iteration++;
        Log::i("Iteration %i.\n", iteration);

        if (maxIterations != 0 && iteration > maxIterations) {
            Log::e("Reached maximum iteration limit (%i). Stopping search.\n", maxIterations);
            return 1;
        }

        if (mode.separateTasks) {
            _separate_tasks_scheduler->displayAdvancementBar();
        }

        // Grow the search tree and encode the new frontier.
        expandAndEncode(mode);

        // Check if this search tree contains a solution.
        if (solveCurrentTree(mode)) {
            return outputSolution();
        }

        // Decide which leaves to expand next (or detect impossibility).
        if (!selectNextLeavesToDevelop(mode)) {
            Log::w("No success. Exiting.\n");
            return 1;
        }
    }
}

void Planner::initializeSearchTree() {
    // Create the initial search tree with only the root and the goal node as leaves.
    _tree_expander.createInitialLeaves();

    // Encode the root method
    _encoding.encode(*_leaf_positions[0]);
    // Encode the goal node
    _encoding.encode(*_leaf_positions[1]);
}

void Planner::expandAndEncode(SearchMode mode) {
    // Select the leaves to expand: in SibylSat mode only the leaves selected
    // from the last abstract plan; in BFS mode every leaf of the frontier.
    FlatHashSet<Position*> leavesToExpand;
    if (mode.expansion == ExpansionMode::SIBYLSAT) {
        leavesToExpand.insert(_sibylsat_nodes_to_develop.begin(), _sibylsat_nodes_to_develop.end());
    } else {
        leavesToExpand.insert(_leaf_positions.begin(), _leaf_positions.end());
    }

    // Grow the search tree by expanding the selected leaves.
    _tree_expander.expandLeaves(leavesToExpand);

    // The separate-tasks boundary tells the encoding which carried leaves were
    // already encoded in a previous call (so they must be skipped).
    _encoding.setActiveFrontierStart(_tree_expander.getActiveFrontierStart());

    // Encode the new frontier before querying the SAT solver on it.
    _encoding.encodeAllLeaves();
}

bool Planner::solveCurrentTree(SearchMode mode) {
    return mode.solve == SolveMode::OPTIMAL
            ? findGloballyOptimalSolutionInSearchTree()
            : findPrimitiveSolutionInSearchTree();
}

bool Planner::selectNextLeavesToDevelop(SearchMode mode) {
    if (mode.solve == SolveMode::OPTIMAL) {
        // The optimal solve already filled _sibylsat_nodes_to_develop.
        return true;
    }
    if (mode.expansion == ExpansionMode::SIBYLSAT) {
        // A failed primitive solve is followed by an abstract plan extraction
        // to decide which leaves should be expanded next.
        return findAbstractPlanInSearchTree();
    }
    // BFS: all leaves are expanded, nothing to select.
    return true;
}

int Planner::outputSolution() {
    const size_t currentExpansionIteration = _leaf_positions.front()->getCreationIteration();
    Log::i("Found a solution after %i expansion iterations.\n", (int) currentExpansionIteration);
    if (_optimization_factor != 0) {
        optimizeCurrentPlan();
    }

    // Extract the plan from the SAT solver and output it.
    Plan plan = _encoding.extractPlan();
    _plan_writer.outputPlan(plan);
    printTreeStatistics();
    return 0;
}

bool Planner::findGloballyOptimalSolutionInSearchTree() {
    _encoding.clearSoftLits();
    Log::i("Add weight for each operation of the current leaves\n");
    setSoftLitsForCurrentLeaves();

    const int result = _encoding.solve();
    if (result != 10) {
        Log::e("No solution possible !\n");
        exit(1);
    }

    const int bestAbstractObjectiveValue = _encoding.getObjectiveValue();
    collectLeavesToDevelopFromAbstractPlan(_encoding.extractAbstractPlan());
    if (_sibylsat_nodes_to_develop.empty()) {
        Log::i("The plan is primitive\n");
        return true;
    }

    Log::i("The plan is not primitive. Number of leaves to develop: %zu/%zu\n",
            _sibylsat_nodes_to_develop.size(), _leaf_positions.size());
    Log::i("Objective value of the best abstract plan: %d\n", bestAbstractObjectiveValue);

    _encoding.addAssumptionsPrimPlan();
    const int primitiveResult = _encoding.solve();
    if (primitiveResult != 10) {
        return false;
    }

    const int bestPrimitiveObjectiveValue = _encoding.getObjectiveValue();
    Log::i("Found a primitive plan with objective value %d\n", bestPrimitiveObjectiveValue);
    if (bestPrimitiveObjectiveValue == bestAbstractObjectiveValue) {
        Log::i("The primitive plan is globally optimal\n");
        return true;
    }

    Log::i("The primitive plan is not optimal (%d > %d)\n",
            bestPrimitiveObjectiveValue, bestAbstractObjectiveValue);
    return false;
}

bool Planner::findPrimitiveSolutionInSearchTree() {
    if (_separate_tasks) {
        return solveWithSeparateTasks();
    }

    _encoding.addAssumptionsPrimPlan();
    return _encoding.solve() == 10;
}

bool Planner::solveWithSeparateTasks() {
    _separate_tasks_scheduler->addAssumptionsForSolvedTasks(_encoding);

    const int assumptionsUntil =
            _separate_tasks_scheduler->getAssumptionsUntil(_leaf_positions.size());
    _encoding.addAssumptionsPrimPlan(/*permanent=*/false, /*assumptions_until=*/assumptionsUntil);
    if (_encoding.solve() != 10) {
        return false;
    }

    if (_separate_tasks_scheduler->updateAfterSolved(_encoding, _leaf_positions)) {
        Log::i("Solved the problem for all tasks\n");
        return true;
    }

    if (_separate_tasks_scheduler->addTasksAsClauses()) {
        // Shift the analysis "initial state" to the post-task boundary state so that
        // resetReachability() naturally starts from there in the next expansion.
        _analysis.updateInitialState(
            _separate_tasks_scheduler->getReachableStatePosFactsAfterTasksAccomplished(),
            _separate_tasks_scheduler->getReachableStateNegFactsAfterTasksAccomplished()
        );
        // Tell the expander where to start the next expansion (boundary position).
        _tree_expander.setActiveFrontierStart(
            _separate_tasks_scheduler->getPositionsDone()
        );
    }

    return false;
}

bool Planner::findAbstractPlanInSearchTree() {
    Log::i("Failed to find a primitive solution... Trying to find an abstract plan...\n");

    if (_separate_tasks) {
        _separate_tasks_scheduler->addAssumptionsForSolvedTasks(_encoding);
    }

    bool foundAbstractPlan = _encoding.solve() == 10;
    if (!foundAbstractPlan && _separate_tasks) {
        foundAbstractPlan = _separate_tasks_scheduler->handleAbstractPlanFailure(_encoding);
    }

    if (!foundAbstractPlan) {
        Log::w("No abstract plan found. Problem is impossible ! Exiting.\n");
        return false;
    }

    Log::i("Found an abstract plan\n");
    const int leafLimit =
            _separate_tasks ? _separate_tasks_scheduler->getAssumptionsUntil(_leaf_positions.size()) : -1;
    collectLeavesToDevelopFromAbstractPlan(_encoding.extractAbstractPlan(), leafLimit);
    Log::i("Number of leaves to develop: %zu\n", _sibylsat_nodes_to_develop.size());
    return true;
}

void Planner::collectLeavesToDevelopFromAbstractPlan(const std::vector<PlanItem>& abstractPlan, int leafLimit) {
    const size_t currentExpansionIteration = _leaf_positions.front()->getCreationIteration();
    _sibylsat_nodes_to_develop.clear();
    const size_t maxLeafIndex =
            leafLimit < 0 ? _leaf_positions.size() : std::min(_leaf_positions.size(), static_cast<size_t>(leafLimit));
    for (size_t leafIndex = 0; leafIndex < abstractPlan.size() && leafIndex < maxLeafIndex; leafIndex++) {
        const PlanItem& item = abstractPlan[leafIndex];
        if (item.id == -1) {
            continue;
        }
        if (_htn_instance.isReduction(item.reduction)) {
            Log::d("  Reduction %s is true at expansion iteration %i, leaf %zu\n",
                    TOSTR(item.reduction), currentExpansionIteration, leafIndex);
            _sibylsat_nodes_to_develop.push_back(_leaf_positions[leafIndex]);
        }
    }
}

void Planner::optimizeCurrentPlan() {
    PlanOptimizer optimizer(_htn_instance, _leaf_positions, _encoding);
    Plan optimizedPlan;
    const int upperBound = _leaf_positions.empty() ? 0 : static_cast<int>(_leaf_positions.size()) - 1;
    Log::i("Optimize the current frontier with plan length upper bound %d\n", upperBound);
    optimizer.optimizePlan(upperBound, optimizedPlan, PlanOptimizer::ConstraintAddition::TRANSIENT);
}

void Planner::setSoftLitsForCurrentLeaves() {
    int name_id_prim = _htn_instance.nameId("__PRIMITIVE___");
    int name_id_blank = 1;

    for (size_t pos_idx = 0; pos_idx + 1 < _leaf_positions.size(); pos_idx++) {
        Position& pos = *_leaf_positions[pos_idx];

        // Iterate over all action and reductions of the position and their respective SAT var
        for (const auto& [op, aVar] : pos.getVariableTable(VarType::OP)) {
            // If op is blank action, pass
            if (op._name_id == name_id_blank) continue;

            // If this is a repetition of a blank action, pass
            if (_htn_instance.isActionRepetition(op._name_id) && _htn_instance.getActionFromRepetition(op._name_id).getNameId() == name_id_blank) continue;

            // If it is the __PRIM__ operator, pass
            if (op._name_id == name_id_prim) continue;
            int var = aVar;
            int heuristicValue = 0;

            // If it is an action, set the weight to 1 since for now, we cannot indicate specific weight for actions in HDDL
            if (_htn_instance.isAction(op)) {
                // If it is a macro action, then its heuristic value is the number of actions in the macro action
                if (_htn_instance.isMacroTask(op._name_id)) {
                    heuristicValue = _htn_instance.numActionsInMacro(op._name_id);
                } else {
                    // Otherwise, it is 1
                    heuristicValue = 1;
                }
            } else {
                // Get the heuristic value of the best grounding of this lifted operator
                heuristicValue = pos.getHeuristicValue(op);
            }
            
            // Set the weight of the lifted operator
            if (heuristicValue > 0) {
                // printf("%d -%d 0\n", heuristicValue, aVar);
                Log::d("Add soft lit for op %s (%d) with heuristic value %d\n", TOSTR(op), var, heuristicValue);
                _encoding.addSoftLit(var, heuristicValue);
            }
        }
    }
}
