
#include <assert.h> 

#include "planner.h"
#include "util/log.h"
#include "sat/plan_optimizer.h"

int Planner::findPlan() {
    
    int iteration = 0;
    Log::i("Iteration %i.\n", iteration);

    createInitialLeaves();

    const int maxIterations = _params.getIntParam("D");
    bool solved = false;

    if (_use_sibylsat_expansion) {
        // Only develop the leaf which contains the _top_method
        _sibylsat_nodes_to_develop.push_back(_leaf_positions[0]);
    }
    
    // Main loop of the search. We keep expanding the tree until we find a solution, or reach the maximum depth limit
    while (!solved) {

        iteration++;      
        Log::i("Iteration %i.\n", iteration);

        if (maxIterations != 0 && iteration > maxIterations) {
            Log::e("Reached maximum depth limit (%i). Stopping search.\n", maxIterations);
            break;
        }

        if (_separate_tasks) {
            _separate_tasks_scheduler->displayAdvancementBar();
        }

        expandCurrentLeaves();

        solved = _optimal ? findGloballyOptimalSolutionInCurrentTree() : findPrimitiveSolutionInCurrentTree();
        if (solved) {
            break;
        }

        if (!_optimal && _use_sibylsat_expansion && !findAbstractPlanToDevelop()) {
            break;
        }
    }

    if (!solved) {
        Log::w("No success. Exiting.\n");
        return 1;
    }

    Log::i("Found a solution at depth %i.\n", (int) _depth);
    if (_optimization_factor != 0) {
        optimizeCurrentPlan();
    }

    _plan = _enc.extractPlan();
    _plan_writer.outputPlan(_plan);
    printStatistics();    
    return 0;
}

void Planner::expandCurrentLeaves() {
    if (_use_sibylsat_expansion) {
        expandLeaves(_sibylsat_nodes_to_develop);
    } else {
        expandLeaves(_leaf_positions);
    }
}

bool Planner::findGloballyOptimalSolutionInCurrentTree() {
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

bool Planner::findPrimitiveSolutionInCurrentTree() {
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

    return false;
}

bool Planner::findAbstractPlanToDevelop() {
    Log::i("Failed to find a solution at depth %i. Trying to find an abstract plan...\n", _depth);

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
    _sibylsat_nodes_to_develop.clear();
    const size_t maxLeafIndex =
            leafLimit < 0 ? _leaf_positions.size() : std::min(_leaf_positions.size(), static_cast<size_t>(leafLimit));
    for (size_t leafIndex = 0; leafIndex < abstractPlan.size() && leafIndex < maxLeafIndex; leafIndex++) {
        const PlanItem& item = abstractPlan[leafIndex];
        if (item.id == -1) {
            continue;
        }
        if (_htn.isReduction(item.reduction)) {
            Log::d("  Reduction %s is true at depth %i, leaf %zu\n", TOSTR(item.reduction), _depth, leafIndex);
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

    _last_number_of_soft_lits = 0;

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
                    _last_number_of_soft_lits++;
            }
        }
    }
}


void Planner::printStatistics() {
    Log::i("# number of depths: %zu\n", _depth + 1);
    Log::i("# instantiated positions: %i\n", _num_instantiated_positions);
    Log::i("# instantiated actions: %i\n", _num_instantiated_actions);
    Log::i("# instantiated reductions: %i\n", _num_instantiated_reductions);
    Log::i("# introduced pseudo-constants: %i\n", _htn.getNumberOfQConstants());
    Log::i("# retroactive prunings: %i\n", _pruning.getNumRetroactivePunings());
    Log::i("# retroactively pruned operations: %i\n", _pruning.getNumRetroactivelyPrunedOps());
    Log::i("# dominated operations: %i\n", _domination_resolver.getNumDominatedOps());
}
