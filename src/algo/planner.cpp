
#include <assert.h> 

#include "planner.h"
#include "util/log.h"
#include "util/signal_manager.h"
#include "util/timer.h"
#include "sat/plan_optimizer.h"

int terminateSatCall(void* state) {return ((Planner*) state)->getTerminateSatCall();}

int Planner::findPlan() {

    // _stats.beginTiming(TimingStage::PLANNER);
    
    int iteration = 0;
    Log::i("Iteration %i.\n", iteration);

    createInitialLeaves();

    // Bounds on depth to solve / explore
    int firstSatCallIteration = _params.getIntParam("d");
    int maxIterations = _params.getIntParam("D");
    _sat_time_limit = _params.getFloatParam("stl");

    bool solved = false;
    bool solvedVirtualPlan = false;
    _enc.setTerminateCallback(this, terminateSatCall);
    if (iteration >= firstSatCallIteration) {
        _enc.addAssumptionsPrimPlan();
        int result = _enc.solve();
        if (result == 0) {
            Log::w("Solver was interrupted. Discarding time limit for next solving attempts.\n");
            _sat_time_limit = 0;
        }
        solved = result == 10;
    } 

    if (_use_sibylsat_expansion) {
        // Only develop the position which contains the _top_method
        _sibylsat_positions_to_develop.insert(0);
    }
    
    // Next depths
    while (!solved && (maxIterations == 0 || iteration < maxIterations)) {

        if (iteration >= firstSatCallIteration) {

            _enc.printFailedVars();

            if (_params.isNonzero("cs")) { // check solvability
                Log::i("Not solved at depth %i with assumptions\n", _depth);

                // Attempt to solve formula again, now without assumptions
                // (is usually simple; if it fails, we know the entire problem is unsolvable)
                int result = _enc.solve();
                if (result == 20) {
                    Log::w("Unsolvable at depth %i even without assumptions!\n", _depth);
                    break;
                } else {
                    Log::i("Not proven unsolvable - expanding by another layer\n");
                }
            } else {
                Log::i("Unsolvable at depth %i -- expanding.\n", _depth);
            }
        }

        iteration++;      
        Log::i("Iteration %i.\n", iteration);

        if (_separate_tasks) {
            _separate_tasks_scheduler->displayAdvancementBar();
        }
        
        if (_use_sibylsat_expansion) {
            // Only develop the positions where the associate reduction is true in the last virtual plan
            expandSelectedLeaves(_sibylsat_positions_to_develop);
        } else {
            // Lilotane: Breadth first expansion
            expandAllLeaves();
        }

        if (_optimal) {
            // Clear current soft literals in the formula...
            _enc.clearSoftLits();
            //... and add the new ones
            Log::i("Add weight for each operation of the current leaves\n");
            setSoftLitsForCurrentLeaves();

            // Now, find the optimal abstract plan in this new set of leaves
            int objective_value_best_plan = 0;
            int result = _enc.solve();
            if (result == 0) {
                Log::w("Solver was interrupted. Discarding time limit for next solving attempts.\n");
                _sat_time_limit = 0;
            }
            solved = result == 10;
            if (solved) {
                objective_value_best_plan = _enc.getObjectiveValue();
                std::vector<PlanItem> virtualPlan = _enc.extractVirtualPlan();

                // Check if the virtual plan is primitive
                // In case it is, we can stop the search. Otherwise, we can already deduce the next positions to develop
                bool planIsPrimitive = true;
                _sibylsat_positions_to_develop.clear();
                int pos = -1;
                for (const PlanItem& item : virtualPlan) {
                    pos++;
                    if (item.id == -1) continue;
                    if (_htn.isReduction(item.reduction)) {
                        planIsPrimitive = false;
                        _sibylsat_positions_to_develop.insert(pos);
                    }
                }
                if (planIsPrimitive) {
                    Log::i("The plan is primitive\n");
                    break;
                } else {
                    Log::i("The plan is not primitive. Number of positions to develop: %zu/%zu\n", 
                            _sibylsat_positions_to_develop.size(), _leaf_positions.size());
                }
            } else {
                Log::e("No solution possible !\n");
                exit(1);
            }

            Log::i("Objective value of the best abstract plan: %d\n", objective_value_best_plan);
            // Now, add the assumption to only look for a primitive plan, and check if the primitive plan
            // has an objective value equal or less than the best plan
            _enc.addAssumptionsPrimPlan();
            result = _enc.solve();
            if (result == 0) {
                Log::w("Solver was interrupted. Discarding time limit for next solving attempts.\n");
                _sat_time_limit = 0;
            }
            solved = result == 10;
            if (solved) {
                Log::i("Found a primitive plan with objective value %d\n", _enc.getObjectiveValue());
                int objective_value_best_primitive_plan = _enc.getObjectiveValue();
                if (objective_value_best_primitive_plan == objective_value_best_plan) {
                    Log::i("The primitive plan is optimal\n");
                    solved = true;
                    break;
                } else {
                    Log::i("The primitive plan is not optimal (%d > %d)\n", objective_value_best_primitive_plan, objective_value_best_plan);
                    solved = false;
                }
            }
        } else {
            if (iteration >= firstSatCallIteration) {

                if (_separate_tasks) {
                    _separate_tasks_scheduler->addAssumptionsForSolvedTasks(_enc);
                }

                // In case, we try to solve the init tasks separately, we only need the assumptions of primtive plan for the K first tasks
                int assumptions_until = _separate_tasks ? _separate_tasks_scheduler->getAssumptionsUntil(_leaf_positions.size()) : -1;
                _enc.addAssumptionsPrimPlan(/*permanent=*/false, /*assumptions_until=*/assumptions_until);
                int result = _enc.solve();
                if (result == 0) {
                    Log::w("Solver was interrupted. Discarding time limit for next solving attempts.\n");
                    _sat_time_limit = 0;
                }
                solved = result == 10;
            } 
            if (_separate_tasks && solved) {
                if (_separate_tasks_scheduler->updateAfterSolved(_enc, _leaf_positions)) {
                    Log::i("Solved the problem for all tasks\n");
                    break;
                } else {
                    solved = false;
                }
            }

            if (_use_sibylsat_expansion && !solved) {
                Log::i("Failed to find a solution at depth %i. Trying to find a virtual plan...\n", _depth);

                if (_separate_tasks) {
                    _separate_tasks_scheduler->addAssumptionsForSolvedTasks(_enc);
                }
                // Find a virtual plan to develop
                int result = _enc.solve();
                if (result == 0) {
                    Log::w("Solver was interrupted. Discarding time limit for next solving attempts.\n");
                    _sat_time_limit = 0;
                }
                solvedVirtualPlan = result == 10;

                if (!solvedVirtualPlan && _separate_tasks) {
                    solvedVirtualPlan = _separate_tasks_scheduler->handleVirtualPlanFailure(_enc, _leaf_positions.size());
                }

                if (!solvedVirtualPlan) {
                     Log::w("No virtual plan found. Problem is impossible ! Exiting.\n");
                     break;
                }

                Log::i("Found a virtual plan\n");

                // Extract the virtual plan and use it to determinate which positions need to be developed
                // Iterate the last layer and get the op holding at the position. If it is a reduction, we need to develop it
                _sibylsat_positions_to_develop.clear();
                int pos_to_develop_limit = _separate_tasks ? _separate_tasks_scheduler->getAssumptionsUntil(_leaf_positions.size()) : -1;
                for (size_t pos = 0; pos < _leaf_positions.size(); pos++) {
                    if (_separate_tasks && pos >= pos_to_develop_limit) {
                        break;
                    }
                    const USignature& opSig = _enc.getOpHoldingAt(*_leaf_positions[pos]);
                    // Log::i("Position %zu: %s\n", pos, TOSTR(opSig));
                    if (_htn.isReduction(opSig)) {
                        Log::d("  Reduction %s is true at depth %i, position %i\n", TOSTR(opSig), _depth, pos);
                        _sibylsat_positions_to_develop.insert(pos);
                    }
                }
                Log::i("Number of positions to develop: %zu\n", _sibylsat_positions_to_develop.size());
            }
        }
    }

    if (!solved) {
        if (iteration >= firstSatCallIteration) _enc.printFailedVars();
        Log::w("No success. Exiting.\n");
        return 1;
    }

    Log::i("Found a solution at depth %i.\n", (int) _depth);
    _time_at_first_plan = Timer::elapsedSeconds();

    improvePlan(iteration);

    // _stats.endTiming(TimingStage::PLANNER);

    _plan_writer.outputPlan(_plan);
    printStatistics();    
    return 0;
}

void Planner::improvePlan(int& iteration) {

    // Compute extra layers after initial solution as desired
    PlanOptimizer optimizer(_htn, _leaf_positions, _enc);
    int maxIterations = _params.getIntParam("D");
    int extraLayers = _params.getIntParam("el");
    int upperBound = _leaf_positions.size()-1;
    if (extraLayers != 0) {

        // Extract initial plan (for anytime purposes)
        _plan = _enc.extractPlan();
        _has_plan = true;
        upperBound = optimizer.getPlanLength(std::get<0>(_plan));
        Log::i("Initial plan at most shallow layer has length %i\n", upperBound);
        
        if (extraLayers == -1) {

            // Indefinitely increase bound and solve until program is interrupted or max depth reached
            size_t el = 1;
            do {
                // Extra layers without solving
                for (size_t x = 0; x < el && (maxIterations == 0 || iteration < maxIterations); x++) {
                    iteration++;      
                    Log::i("Iteration %i. (extra)\n", iteration);
                    expandAllLeaves();
                }
                // Solve again (to get another plan)
                _enc.addAssumptionsPrimPlan();
                int result = _enc.solve();
                if (result != 10) break;
                // Extract plan at layer, update bound
                auto thisLayerPlan = _enc.extractPlan();
                int newLength = optimizer.getPlanLength(std::get<0>(thisLayerPlan));
                // Update plan only if it is better than any previous plan
                if (newLength < upperBound || !_has_plan) {
                    upperBound = newLength;
                    _plan = thisLayerPlan;
                    _has_plan = true;
                }
                Log::i("Initial plan at depth %i has length %i\n", iteration, newLength);
                // Optimize
                optimizer.optimizePlan(upperBound, _plan, PlanOptimizer::ConstraintAddition::TRANSIENT);
                // Double number of extra layers in next iteration
                el *= 2;
            } while (maxIterations == 0 || iteration < maxIterations);

        } else {
            // Extra layers without solving
            for (int x = 0; x < extraLayers; x++) {
                iteration++;      
                Log::i("Iteration %i. (extra)\n", iteration);
                expandAllLeaves();
            }

            // Solve again (to get another plan)
            _enc.addAssumptionsPrimPlan();
            _enc.solve();
        }
    }

    if (extraLayers != -1) {
        if (_optimization_factor != 0) {

            // Extract plan at final layer, update bound
            auto finalLayerPlan = _enc.extractPlan();
            int newLength = optimizer.getPlanLength(std::get<0>(finalLayerPlan));
            // Update plan only if it is better than any previous plan
            if (newLength < upperBound || !_has_plan) {
                upperBound = newLength;
                _plan = finalLayerPlan;
                _has_plan = true;
            }
            Log::i("Initial plan at final leaves has length %i\n", newLength);
            // Optimize
            optimizer.optimizePlan(upperBound, _plan, PlanOptimizer::ConstraintAddition::PERMANENT);

        } else {
            // Just extract plan
            _plan = _enc.extractPlan();
            _has_plan = true;
        }
    }
}

// Tree expansion and instantiation logic lives in planner_expansion.cpp.

void Planner::clearDonePositions(int offset) {
    (void) offset;
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
                // TODO If op is a repetition, get the original action instead (to keep the same heuristic value)
                // if (_htn.isActionRepetition(op._name_id)) {
                //     // Get the action from the repetiion

                //     // Get the parent action
                //      pos.getPredecessors().at(op)
                // }
                    _enc.addSoftLit(var, heuristicValue);
                    _last_number_of_soft_lits++;
            }
        }
    }
}

void Planner::checkTermination() {
    bool exitSet = SignalManager::isExitSet();
    bool cancelOpt = cancelOptimization();
    if (exitSet) {
        if (_has_plan) {
            Log::i("Termination signal caught - printing last found plan.\n");
            _plan_writer.outputPlan(_plan);
        } else {
            Log::i("Termination signal caught.\n");
        }
    } else if (cancelOpt) {
        Log::i("Cancelling optimization according to provided limit.\n");
        _plan_writer.outputPlan(_plan);
    } else if (_time_at_first_plan == 0 
            && _init_plan_time_limit > 0
            && Timer::elapsedSeconds() > _init_plan_time_limit) {
        Log::i("Time limit to find an initial plan exceeded.\n");
        exitSet = true;
    }
    if (exitSet || cancelOpt) {
        printStatistics();
        Log::i("Exiting happily.\n");
        exit(0);
    }
}

bool Planner::cancelOptimization() {
    return _time_at_first_plan > 0 &&
            _optimization_factor > 0 &&
            Timer::elapsedSeconds() > (1+_optimization_factor) * _time_at_first_plan;
}

int Planner::getTerminateSatCall() {
    // Breaking out of first SAT call after some time
    if (_sat_time_limit > 0 &&
        _enc.getTimeSinceSatCallStart() > _sat_time_limit) {
        return 1;
    }
    // Termination due to initial planning time limit (-T)
    if (_time_at_first_plan == 0 &&
        _init_plan_time_limit > 0 &&
        Timer::elapsedSeconds() > _init_plan_time_limit) {
        return 1;
    }
    // Plan length optimization limit hit
    if (cancelOptimization()) {
        return 1;
    }
    // Termination by interruption signal
    if (SignalManager::isExitSet()) return 1;
    return 0;
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
