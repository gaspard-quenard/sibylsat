
#include <algorithm>
#include <assert.h> 

#include "planner.h"
#include "util/log.h"
#include "util/names.h"
#include "sat/plan_optimizer.h"

int Planner::findPlan() {

    int iteration = 0;
    Log::i("Iteration %i.\n", iteration);

    // Build the initial search tree before entering the search loop.
    initializeSearchTree();

    const int maxIterations = _params.getIntParam("D");
    bool solved = false;

    if (_use_sibylsat_expansion) {
        // Only develop the leaf which contains the _top_method
        _sibylsat_nodes_to_develop.push_back(_leaf_positions[0]);
    }

    // Main loop of the search. We keep expanding the search tree until we find a solution, or reach the maximum iteration limit
    while (!solved) {

        iteration++;
        Log::i("Iteration %i.\n", iteration);

        if (maxIterations != 0 && iteration > maxIterations) {
            Log::e("Reached maximum iteration limit (%i). Stopping search.\n", maxIterations);
            break;
        }

        if (_separate_tasks) {
            _separate_tasks_scheduler->displayAdvancementBar();
        }

        const std::vector<Position*>& leavesToExpand =
                _use_sibylsat_expansion ? _sibylsat_nodes_to_develop : _leaf_positions;

        // Grow the search tree by expanding the leaves selected for this iteration.
        const TreeExpander::ExpansionResult expansion = expandLeaves(leavesToExpand);

        // Encode the new frontier before querying the SAT solver on it.
        encodeLeaves(expansion);

        // Then check if this search tree contains a solution (or a globally optimal solution if the optimal flag is on).
        solved = _optimal ? findGloballyOptimalSolutionInSearchTree() : findPrimitiveSolutionInSearchTree();
        if (solved) {
            break;
        }

        // In SibylSat mode, a failed primitive solve is followed by an abstract
        // plan extraction to decide which leaves should be expanded next.
        if (!_optimal && _use_sibylsat_expansion && !findAbstractPlanInSearchTree()) {
            break;
        }
    }

    if (!solved) {
        Log::w("No success. Exiting.\n");
        return 1;
    }

    const size_t currentDepth = _leaf_positions.front()->getLayerIndex();
    Log::i("Found a solution at depth %i.\n", (int) currentDepth);
    if (_optimization_factor != 0) {
        optimizeCurrentPlan();
    }

    // Extract the plan from the SAT solver and output it.
    Plan plan = _enc.extractPlan();
    _plan_writer.outputPlan(plan);
    printTreeStatistics();
    return 0;
}

TreeExpander::ExpansionResult Planner::expandLeaves(const std::vector<Position*>& leavesToExpand) {
    return _tree_expander.expandLeaves(leavesToExpand);
}

void Planner::encodeLeaves(const TreeExpander::ExpansionResult& expansion) {
    Statistics& stats = Statistics::getInstance();
    const size_t currentDepth = _leaf_positions.front()->getLayerIndex();

    Log::i("Collected %i relevant facts at this depth\n", _analysis.getRelevantFactsBitVec().count());
    Log::i("Encoding ...\n");
    _enc.setNewInitPos(expansion.newInitPos);

    stats.beginTiming(TimingStage::ENCODING);
    if (expansion.expandAll) {
        for (Position* leaf : _leaf_positions) {
            Log::v("- Position (%i,%i)\n", currentDepth, leaf->getPositionIndex());
            _enc.encode(*leaf);
        }
    } else {
        Log::i("New leaf count: %zu\n", _leaf_positions.size());
        for (size_t leafIndex = 0; leafIndex < _leaf_positions.size(); leafIndex++) {
            switch (expansion.leafEncodingActions[leafIndex]) {
            case TreeExpander::LeafEncodingAction::NONE:
                break;
            case TreeExpander::LeafEncodingAction::FULL:
                _enc.encode(*_leaf_positions[leafIndex]);
                break;
            case TreeExpander::LeafEncodingAction::NEW_RELEVANTS:
                _enc.encodeNewRelevantsFacts(*_leaf_positions[leafIndex]);
                break;
            case TreeExpander::LeafEncodingAction::EFFECTS_AND_FRAME:
                _enc.encodeOnlyEffsAndFrameAxioms(*_leaf_positions[leafIndex]);
                break;
            case TreeExpander::LeafEncodingAction::PROPAGATE_RELEVANTS:
                _enc.propagateRelevantsFacts(*_leaf_positions[leafIndex]);
                break;
            }
        }
    }
    stats.endTiming(TimingStage::ENCODING);

    for (size_t leafIndex = 0; leafIndex < _leaf_positions.size(); leafIndex++) {
        _leaf_positions[leafIndex]->setLeftPosition(leafIndex > 0 ? _leaf_positions[leafIndex - 1] : nullptr);
    }

    if (!expansion.expandAll) {
        for (Position* node : expansion.expandedNodes) {
            Log::v("Freeing position %zu of depth %zu\n", node->getPositionIndex(), node->getLayerIndex());
            node->clearFullPos();
        }
        for (Position* leaf : _leaf_positions) {
            leaf->clearDecodings();
        }
    }
}

bool Planner::findGloballyOptimalSolutionInSearchTree() {
    _enc.clearSoftLits();
    Log::i("Add weight for each operation of the current leaves\n");
    setSoftLitsForCurrentLeaves();

    const int result = _enc.solve();
    if (result != 10) {
        Log::e("No solution possible !\n");
        exit(1);
    }

    const int bestAbstractObjectiveValue = _enc.getObjectiveValue();
    collectLeavesToDevelopFromAbstractPlan(_enc.extractAbstractPlan());
    if (_sibylsat_nodes_to_develop.empty()) {
        Log::i("The plan is primitive\n");
        return true;
    }

    Log::i("The plan is not primitive. Number of leaves to develop: %zu/%zu\n",
            _sibylsat_nodes_to_develop.size(), _leaf_positions.size());
    Log::i("Objective value of the best abstract plan: %d\n", bestAbstractObjectiveValue);

    _enc.addAssumptionsPrimPlan();
    const int primitiveResult = _enc.solve();
    if (primitiveResult != 10) {
        return false;
    }

    const int bestPrimitiveObjectiveValue = _enc.getObjectiveValue();
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
        _separate_tasks_scheduler->addAssumptionsForSolvedTasks(_enc);
    }

    const int assumptionsUntil =
            _separate_tasks ? _separate_tasks_scheduler->getAssumptionsUntil(_leaf_positions.size()) : -1;
    _enc.addAssumptionsPrimPlan(/*permanent=*/false, /*assumptions_until=*/assumptionsUntil);
    if (_enc.solve() != 10) {
        return false;
    }

    if (!_separate_tasks) {
        return true;
    }

    if (_separate_tasks_scheduler->updateAfterSolved(_enc, _leaf_positions)) {
        Log::i("Solved the problem for all tasks\n");
        return true;
    }

    if (_separate_tasks_scheduler->addTasksAsClauses()) {
        // Shift the analysis "initial state" to the post-task boundary state so that
        // resetReachability() naturally starts from there in the next expansion.
        _analysis.updateInitialState(
            _separate_tasks_scheduler->getReachableStatePosAfterTasksAccomplishedBitVec(),
            _separate_tasks_scheduler->getReachableStateNegAfterTasksAccomplishedBitVec()
        );
        // Tell the expander where to start the next expansion (boundary position).
        _tree_expander.setExpansionBoundary(
            _separate_tasks_scheduler->getPositionsDone(_leaf_positions.size())
        );
    }

    return false;
}

bool Planner::findAbstractPlanInSearchTree() {
    const size_t currentDepth = _leaf_positions.front()->getLayerIndex();
    Log::i("Failed to find a solution at depth %i. Trying to find an abstract plan...\n", currentDepth);

    if (_separate_tasks) {
        _separate_tasks_scheduler->addAssumptionsForSolvedTasks(_enc);
    }

    bool foundAbstractPlan = _enc.solve() == 10;
    if (!foundAbstractPlan && _separate_tasks) {
        foundAbstractPlan = _separate_tasks_scheduler->handleAbstractPlanFailure(_enc, _leaf_positions.size());
    }

    if (!foundAbstractPlan) {
        Log::w("No abstract plan found. Problem is impossible ! Exiting.\n");
        return false;
    }

    Log::i("Found an abstract plan\n");
    const int leafLimit =
            _separate_tasks ? _separate_tasks_scheduler->getAssumptionsUntil(_leaf_positions.size()) : -1;
    collectLeavesToDevelopFromAbstractPlan(_enc.extractAbstractPlan(), leafLimit);
    Log::i("Number of leaves to develop: %zu\n", _sibylsat_nodes_to_develop.size());
    return true;
}

void Planner::collectLeavesToDevelopFromAbstractPlan(const std::vector<PlanItem>& abstractPlan, int leafLimit) {
    const size_t currentDepth = _leaf_positions.front()->getLayerIndex();
    _sibylsat_nodes_to_develop.clear();
    const size_t maxLeafIndex =
            leafLimit < 0 ? _leaf_positions.size() : std::min(_leaf_positions.size(), static_cast<size_t>(leafLimit));
    for (size_t leafIndex = 0; leafIndex < abstractPlan.size() && leafIndex < maxLeafIndex; leafIndex++) {
        const PlanItem& item = abstractPlan[leafIndex];
        if (item.id == -1) {
            continue;
        }
        if (_htn.isReduction(item.reduction)) {
            Log::d("  Reduction %s is true at depth %i, leaf %zu\n", TOSTR(item.reduction), currentDepth, leafIndex);
            _sibylsat_nodes_to_develop.push_back(_leaf_positions[leafIndex]);
        }
    }
}

void Planner::optimizeCurrentPlan() {
    PlanOptimizer optimizer(_htn, _leaf_positions, _enc);
    Plan optimizedPlan;
    const int upperBound = _leaf_positions.empty() ? 0 : static_cast<int>(_leaf_positions.size()) - 1;
    Log::i("Optimize the current depth with plan length upper bound %d\n", upperBound);
    optimizer.optimizePlan(upperBound, optimizedPlan, PlanOptimizer::ConstraintAddition::TRANSIENT);
}

void Planner::setSoftLitsForCurrentLeaves() {
    int name_id_prim = _htn.nameId("__PRIMITIVE___");
    int name_id_blank = 1;

    for (size_t pos_idx = 0; pos_idx + 1 < _leaf_positions.size(); pos_idx++) {
        Position& pos = *_leaf_positions[pos_idx];

        // Iterate over all action and reductions of the position and their respective SAT var
        for (const auto& [op, aVar] : pos.getVariableTable(VarType::OP)) {
            // If op is blank action, pass
            if (op._name_id == name_id_blank) continue;

            // If this is a repetition of a blank action, pass
            if (_htn.isActionRepetition(op._name_id) && _htn.getActionFromRepetition(op._name_id).getNameId() == name_id_blank) continue;

            // If it is the __PRIM__ operator, pass
            if (op._name_id == name_id_prim) continue;
            int var = aVar;
            int heuristicValue = 0;

            // If it is an action, set the weight to 1 since for now, we cannot indicate specific weight for actions in HDDL
            if (_htn.isAction(op)) {
                // If it is a macro action, then its heuristic value is the number of actions in the macro action
                if (_htn.isMacroTask(op._name_id)) {
                    heuristicValue = _htn.numActionsInMacro(op._name_id);
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
                _enc.addSoftLit(var, heuristicValue);
            }
        }
    }
}

