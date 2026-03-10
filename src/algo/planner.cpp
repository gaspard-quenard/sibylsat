
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

void Planner::incrementPosition(const Position& pos) {
    _num_instantiated_actions += pos.getActions().size();
    _num_instantiated_reductions += pos.getReductions().size();
    _pos++; _num_instantiated_positions++;
}

void Planner::refreshLeafMetadata() {
    for (size_t pos = 0; pos < _leaf_positions.size(); pos++) {
        _leaf_positions[pos]->setPos(_depth, pos);
    }
}

void Planner::createInitialLeaves() {

    const int initSize = 2;
    Log::i("Creating initial leaves of size %i\n", initSize);
    _depth = 0;
    _pos = 0;

    _root_position = new Position();
    _root_position->setPos(-1, 0);

    Position* rootReductionPosition = new Position();
    rootReductionPosition->setParentPosition(_root_position);
    Position* goalPosition = new Position();
    goalPosition->setParentPosition(_root_position);

    _leaf_positions = {rootReductionPosition, goalPosition};
    refreshLeafMetadata();

    rootReductionPosition->setOriginalLayerIdx(_depth);
    rootReductionPosition->setOriginalPos(_pos);

    /***** DEPTH 0, POSITION 0 ******/

    for (USignature& rSig : _instantiator.getApplicableInstantiations(_htn.getInitReduction())) {
        auto rOpt = createValidReduction(*rootReductionPosition, rSig, USignature());
        if (rOpt) {
            auto& r = rOpt.value();
            USignature sig = r.getSignature();
            rootReductionPosition->addReduction(sig);
            rootReductionPosition->addAxiomaticOp(sig);
            rootReductionPosition->addExpansionSize(r.getSubtasks().size());
        }
    }
    addPreconditionConstraints(*rootReductionPosition);
    initializeNextEffectsBitVec(*rootReductionPosition);

    incrementPosition(*rootReductionPosition);

    /***** DEPTH 0, POSITION 1 ******/

    createNextPosition(*goalPosition, /*parent=*/nullptr, /*parentPos=*/0, rootReductionPosition);

    Action goalAction = _htn.getGoalAction();
    USignature goalSig = goalAction.getSignature();
    goalPosition->addAction(goalSig);
    goalPosition->addAxiomaticOp(goalSig);
    addPreconditionConstraints(*goalPosition);
    goalPosition->setPos(_depth, _pos);
    goalPosition->setOriginalLayerIdx(_depth);
    goalPosition->setOriginalPos(_pos);

    rootReductionPosition->clearAfterInstantiation();
    goalPosition->clearAfterInstantiation();

    _enc.encode(*rootReductionPosition);
    _enc.encode(*goalPosition);
}

void Planner::expandAllLeaves() {

    std::vector<Position*> currentLeaves = _leaf_positions;
    size_t nextLeafCount = 0;
    for (Position* leaf : currentLeaves) {
        nextLeafCount += leaf->getMaxExpansionSize();
    }

    _depth++;
    _pos = 0;
    _leaf_positions.clear();
    _leaf_positions.reserve(nextLeafCount);
    Log::i("New leaf count: %zu\n", nextLeafCount);

    Log::i("Instantiating ...\n");
    _stats.beginTiming(TimingStage::EXPANSION);
    for (_old_pos = 0; _old_pos < currentLeaves.size(); _old_pos++) {
        Position& above = *currentLeaves[_old_pos];
        size_t maxOffset = above.getMaxExpansionSize();

        for (size_t offset = 0; offset < maxOffset; offset++) {
            Position* current = new Position();
            current->setParentPosition(&above);
            _leaf_positions.push_back(current);
            current->setPos(_depth, _pos);
            Position* left = _pos > 0 ? _leaf_positions[_pos-1] : nullptr;
            createNextPosition(*current, &above, _old_pos, left);
            Log::v("  Instantiation done. (r=%i a=%i qf=%i supp=%i)\n",
                    current->getReductions().size(),
                    current->getActions().size(),
                    current->getQFacts().size(),
                    current->getPosFactSupportsId().size() + current->getNegFactSupportsId().size());
            if (_pos > 0) {
                _leaf_positions[_pos-1]->clearAfterInstantiation();
            }

            incrementPosition(*current);
            checkTermination();
        }
    }
    if (_pos > 0) {
        _leaf_positions[_pos-1]->clearAfterInstantiation();
    }
    _stats.endTiming(TimingStage::EXPANSION);
    Log::i("Collected %i relevant facts at this depth\n", _analysis.getRelevantFactsBitVec().count());

    Log::i("Encoding ...\n");
    _stats.beginTiming(TimingStage::ENCODING);
    for (Position* leaf : _leaf_positions) {
        Log::v("- Position (%i,%i)\n", _depth, leaf->getPositionIndex());
        _enc.encode(*leaf);
    }
    _stats.endTiming(TimingStage::ENCODING);
}

void Planner::expandSelectedLeaves(const FlatHashSet<int>& positionsToDevelop) {

    std::vector<Position*> currentLeaves = _leaf_positions;
    std::vector<size_t> nextLeafStarts(currentLeaves.size(), 0);

    _stats.beginTiming(TimingStage::EXPANSION);

    size_t nextLeafCount = currentLeaves.size();
    for (int pos: positionsToDevelop) {
        Position& oldPos = *currentLeaves[pos];
        nextLeafCount += oldPos.getMaxExpansionSize() - 1;
    }

    _depth++;
    _pos = 0;
    _leaf_positions.clear();
    _leaf_positions.reserve(nextLeafCount);
    Log::i("New leaf count: %zu\n", nextLeafCount);

    int num_pos_developed = 0;
    bool all_pos_developed = false;
    bool left_pos_is_developed = false;

    int num_position_already_done = _separate_tasks ? _separate_tasks_scheduler->getPositionsDone(currentLeaves.size()) : 0;
    if (num_position_already_done > 0) {
        Log::i("Propagating initial state facts for positions already done (%i)\n", num_position_already_done);
        Position tmpInitialPosition;
        tmpInitialPosition.setPos(_depth, 0);
        propagateInitialState(tmpInitialPosition, *currentLeaves[0]);
        const BitVec& reachable_state_pos_after_tasks_accomplished = _separate_tasks_scheduler->getReachableStatePosAfterTasksAccomplishedBitVec();
        const BitVec& reachable_state_neg_after_tasks_accomplished = _separate_tasks_scheduler->getReachableStateNegAfterTasksAccomplishedBitVec();
        _analysis.setReachableFactsBitVec(
            reachable_state_pos_after_tasks_accomplished,
            reachable_state_neg_after_tasks_accomplished
        );
        if (_separate_tasks_scheduler->addTasksAsClauses()) {
            _enc.setNewInitPos(num_position_already_done);

            for (_old_pos = 0; _old_pos < num_position_already_done; _old_pos++) {
                nextLeafStarts[_old_pos] = _pos;
                Position* carriedLeaf = currentLeaves[_old_pos];
                carriedLeaf->setPos(_depth, _pos);
                _leaf_positions.push_back(carriedLeaf);
                _pos++;
            }
        }
        Log::i("Done !\n");
    }

    int init_pos_expanding = _separate_tasks && _separate_tasks_scheduler->addTasksAsClauses() ? num_position_already_done : 0;

    Log::i("Instantiating ...\n");

    for (_old_pos = init_pos_expanding; _old_pos < currentLeaves.size(); _old_pos++)  {

        nextLeafStarts[_old_pos] = _pos;

        if (!positionsToDevelop.count(_old_pos)) {

            Position* newPosPtr = currentLeaves[_old_pos];
            newPosPtr->setPos(_depth, _pos);
            _leaf_positions.push_back(newPosPtr);
            Position& newPos = *newPosPtr;

            if (_pos == 0) {
                propagateInitialState(newPos, *currentLeaves[0]);
            } else if (_separate_tasks_scheduler
                && _depth > 0
                && _pos == _separate_tasks_scheduler->getPositionsDone(currentLeaves.size())
                && _separate_tasks_scheduler->addTasksAsClauses()) {
                for (int i = 0; i < _htn.getNumPositiveGroundFacts(); i++) {
                    const USignature& sig = _htn.getGroundPositiveFact(i);
                    if (_analysis.isReachableBitVec(i, /*negated=*/false)) {
                        newPos.addTrueFact(sig);
                    } else {
                        newPos.addFalseFact(sig);
                    }
                }
            } else {
                Position& leftPos = *_leaf_positions[_pos - 1];

                if (left_pos_is_developed) {
                    newPos.clearFactSupportsId();
                    createNextPositionFromLeft(newPos, leftPos);
                } else if (!all_pos_developed) {
                    createNextPositionFromLeftSimplified(newPos);
                }
            }

            left_pos_is_developed = false;
            _pos++;
        } else {
            size_t expansion_size = 1;
            for (const auto& method : currentLeaves[_old_pos]->getReductions()) {
                const Reduction& subR = _htn.getOpTable().getReduction(method);
                expansion_size = std::max(expansion_size, subR.getSubtasks().size());
            }

            currentLeaves[_old_pos]->setExpansionSize(expansion_size);

            for (size_t offset = 0; offset < expansion_size; offset++) {
                Position* current = new Position();
                current->setParentPosition(currentLeaves[_old_pos]);
                _leaf_positions.push_back(current);
                current->setPos(_depth, _pos);
                Position* left = _pos > 0 ? _leaf_positions[_pos-1] : nullptr;
                createNextPosition(*current, currentLeaves[_old_pos], _old_pos, left);
                incrementPosition(*current);
            }

            num_pos_developed++;
            left_pos_is_developed = true;
            if (num_pos_developed == positionsToDevelop.size()) {
                all_pos_developed = true;
            }
        }
    }

    _stats.endTiming(TimingStage::EXPANSION);

    Log::i("Collected %i relevant facts at this depth\n", _analysis.getRelevantFactsBitVec().count());
    Log::i("New leaf count: %zu (%d)\n", _leaf_positions.size(), _pos);

    int init_pos_encoding = _separate_tasks && _separate_tasks_scheduler->addTasksAsClauses() ? num_position_already_done : 0;
    Log::i("Encoding ...\n");
    _stats.beginTiming(TimingStage::ENCODING);
    bool encodeOnlyEffsAndFA = false;
    for (_old_pos = init_pos_encoding; _old_pos < currentLeaves.size(); _old_pos++) {

        if (_old_pos == init_pos_encoding && !positionsToDevelop.count(_old_pos)) {
            _enc.encodeNewRelevantsFacts(*_leaf_positions[nextLeafStarts[init_pos_encoding]]);
        }

        if (positionsToDevelop.count(_old_pos)) {
            size_t newPos = nextLeafStarts[_old_pos];
            size_t maxOffset = currentLeaves[_old_pos]->getMaxExpansionSize();
            for (size_t offset = 0; offset < maxOffset; offset++) {
                _enc.encode(*_leaf_positions[newPos + offset]);
            }
            encodeOnlyEffsAndFA = true;

        } else if (encodeOnlyEffsAndFA) {
            _enc.encodeOnlyEffsAndFrameAxioms(*_leaf_positions[nextLeafStarts[_old_pos]]);
            encodeOnlyEffsAndFA = false;
        }
        else if (_old_pos != init_pos_encoding) {
            _enc.propagateRelevantsFacts(*_leaf_positions[nextLeafStarts[_old_pos]]);
        }
    }
    _stats.endTiming(TimingStage::ENCODING);

    for (int pos : positionsToDevelop) {
        Log::v("Freeing position %d of depth %d\n", pos, _depth - 1);
        currentLeaves[pos]->clearFullPos();
    }
    for (Position* leaf : _leaf_positions) {
        leaf->clearDecodings();
    }
}

void Planner::createNextPosition(Position& newPos, Position* parent, size_t parentPos, Position* left) {
    // Useful informations for sibylsat expansion
    newPos.setPos(_depth, _pos);
    if (parent != nullptr) {
        newPos.setAbovePos(parentPos);
        newPos.setParentPosition(parent);
    }
    newPos.setOriginalLayerIdx(_depth);
    newPos.setOriginalPos(_pos);
    newPos.initFactChangesBitVec(_htn.getNumPositiveGroundFacts());

    // Set up all facts that may hold at this position.
    if (_pos == 0) {
        assert(parent != nullptr || _depth == 0);
        if (_depth > 0) {
            propagateInitialState(newPos, *parent);
        }
    }  
    else if (_separate_tasks_scheduler 
                && _depth > 0
                && _pos == _separate_tasks_scheduler->getPositionsDone(_leaf_positions.size())
                && _separate_tasks_scheduler->addTasksAsClauses()) {
                    // Only need to indicate the true facts and false facts of the 'new' initial state
                    // Log::i("Propagating initial state facts for position %i\n", _pos);
                    for (int i = 0; i < _htn.getNumPositiveGroundFacts(); i++) {
                        const USignature& sig = _htn.getGroundPositiveFact(i);
                        if (_analysis.isReachableBitVec(i, /*negated=*/false)) {
                            // Log::i("Adding true fact %s at position %i\n", TOSTR(sig), _pos);
                            newPos.addTrueFact(sig);
                        } else {
                            // Log::i("Adding false fact %s at position %i\n", TOSTR(sig), _pos);
                            newPos.addFalseFact(sig);
                        }
                    }
            }
    else if (left != nullptr) {
        createNextPositionFromLeft(newPos, *left);
    }

    // Generate this new position's content based on the facts and the position above.
    if (parent != nullptr) {
        createNextPositionFromAbove(newPos, *parent);
    }

    // Eliminate operations which are dominated by another operation
    if (_params.isNonzero("edo")) 
        _domination_resolver.eliminateDominatedOperations(newPos);


    // In preparation for the upcoming position,
    // add all effects of the actions and reductions occurring HERE
    // as (initially false) facts to THIS position. 
    // Already done in create next position from left for sibylsat expansion
    if (!_use_sibylsat_expansion) { 
        _stats.beginTiming(TimingStage::EXPANSION_INITIALIZED_NEXT_EFFECTS);
        initializeNextEffectsBitVec(newPos);
        _stats.endTiming(TimingStage::EXPANSION_INITIALIZED_NEXT_EFFECTS);
    }
}

void Planner::createNextPositionFromAbove(Position& newPos, Position& above) {
    // _stats.beginTiming(TimingStage::EXPANSION_ABOVE);
    //eliminateInvalidParentsAtCurrentState(offset);
    propagateActions(newPos, above);
    propagateReductions(newPos, above);
    addPreconditionConstraints(newPos);

    // if (offset == 0) {
    //     Position& above = (*_frontiers[_depth-1])[_old_pos];
    //     for (const int mutexGroup : above.getGroupMutexEncoded()) {
    //         newPos.addGroupMutexEncoded(mutexGroup);
    //     }
    // }
    // _stats.endTiming(TimingStage::EXPANSION_ABOVE);
}

void Planner::createNextPositionFromLeft(Position& newPos, Position& left) {
    // _stats.beginTiming(TimingStage::EXPANSION_LEFT);
    // Log::i("Creating position (%i,%i) from left position (%i,%i)\n", 
            // _depth, _pos, left.getLayerIndex(), left.getPositionIndex());
    assert(left.getLayerIndex() == newPos.getLayerIndex());
    assert(left.getPositionIndex()+1 == newPos.getPositionIndex());

    // Propagate fact changes from operations from previous position
    USigSet actionsToRemove;
    const USigSet* ops[2] = {&left.getActions(), &left.getReductions()};
    bool isAction = true;
    for (const auto& set : ops) {
        for (const auto& aSig : *set) {

            bool repeatedAction = isAction && _htn.isActionRepetition(aSig._name_id);

            // for (const Signature& fact : _analysis.getPossibleFactChanges(aSig)) {
            //     Log::i("Possible fact changes for %s: %s\n", TOSTR(aSig), TOSTR(fact));
            //     if (isAction && !addEffect(
            //             repeatedAction ? aSig.renamed(_htn.getActionNameFromRepetition(aSig._name_id)) : aSig, 
            //             fact, 
            //             repeatedAction ? EffectMode::DIRECT_NO_QFACT : EffectMode::DIRECT)) {
                    
            //         // Impossible direct effect: forbid action retroactively.
            //         Log::w("Retroactively prune action %s due to impossible effect %s\n", TOSTR(aSig), TOSTR(fact));
            //         actionsToRemove.insert(aSig);

            //         // Also remove any virtualized actions corresponding to this action
            //         USignature repSig = aSig.renamed(_htn.getRepetitionNameOfAction(aSig._name_id));
            //         if (left.hasAction(repSig)) actionsToRemove.insert(repSig);
                    
            //         break;
            //     }
            //     if (!isAction && !addEffect(aSig, fact, EffectMode::INDIRECT)) {
            //         // Impossible indirect effect: ignore.
            //     }
            // }
            // _analysis.eraseCachedPossibleFactChanges(aSig);

            // Do the same with BitVec
            // First, get all ground pfc of this 
            BitVec groundEffPos = _analysis.getPossibleGroundFactChanges(aSig, /*negated=*/false);
            BitVec groundEffNeg = _analysis.getPossibleGroundFactChanges(aSig, /*negated=*/true);
            const SigSet& pseudoEff = _analysis.getPossiblePseudoGroundFactChanges(aSig);
            // _stats.beginTiming(TimingStage::EXPANSION_LEFT_GROUND);

            addGroundEffectBitVec(newPos, aSig, groundEffPos, /*negated=*/false, isAction ? EffectMode::DIRECT : EffectMode::INDIRECT);
            addGroundEffectBitVec(newPos, aSig, groundEffNeg, /*negated=*/true, isAction ? EffectMode::DIRECT : EffectMode::INDIRECT);

            
            // _stats.endTiming(TimingStage::EXPANSION_LEFT_GROUND);
            // _stats.beginTiming(TimingStage::EXPANSION_LEFT_PSEUDO);
            for (const Signature& pseudoPred : pseudoEff) {
                // Log::i("Get pseudo ground fact changes for %s: %s\n", TOSTR(aSig), TOSTR(pseudoPred));
                if (isAction && !addPseudoGroundEffect(
                        newPos,
                        left,
                        repeatedAction ? aSig.renamed(_htn.getActionNameFromRepetition(aSig._name_id)) : aSig, 
                        pseudoPred,
                        repeatedAction ? EffectMode::DIRECT_NO_QFACT : EffectMode::DIRECT)) {
                    
                    // Impossible direct effect: forbid action retroactively.
                    Log::w("3_ Retroactively prune action %s due to impossible effect %s\n", TOSTR(aSig), TOSTR(pseudoPred));
                    actionsToRemove.insert(aSig);
                    break;
                }
                if (!isAction && !addPseudoGroundEffect(newPos, left, aSig, pseudoPred, EffectMode::INDIRECT)) {
                    // Impossible indirect effect: ignore.
                }
            }
            // _stats.endTiming(TimingStage::EXPANSION_LEFT_PSEUDO);

        }
        isAction = false;
    }

    for (const auto& aSig : actionsToRemove) {
        _pruning.prune(aSig, left);
    }

    // To debug, print reachable facts
    // Log::i("Reachable facts after creating position (%i,%i):\n", _depth, _pos);
    // Log::i("Classical:\n");
    // _analysis.printReachableFacts();
    // Log::i("BitVec:\n");
    // _analysis.printReachableFactsBitVec();
    int a = 0;
    // _stats.endTiming(TimingStage::EXPANSION_LEFT);
}



// Just update the analysis
void Planner::createNextPositionFromLeftSimplified(Position& newPos) {
    // _stats.beginTiming(TimingStage::EXPANSION_LEFT_SIMPLFIED);
    const BitVec& pos_facts_changed = newPos.getFactChangeBitVec(/*negated=*/false);
    const BitVec& neg_facts_changed = newPos.getFactChangeBitVec(/*negated=*/true);
    _analysis.addMultipleReachableFactsBitVec(pos_facts_changed, /*negated=*/false);
    _analysis.addMultipleReachableFactsBitVec(neg_facts_changed, /*negated=*/true);
    // _stats.endTiming(TimingStage::EXPANSION_LEFT_SIMPLFIED);
}


void Planner::addPreconditionConstraints(Position& pos) {
    for (const auto& aSig : pos.getActions()) {
        const Action& a = _htn.getOpTable().getAction(aSig);
        // Add preconditions of action
        bool isRepetition = _htn.isActionRepetition(aSig._name_id);
        addPreconditionsAndConstraints(pos, aSig, a.getPreconditions(), isRepetition);
    }
    for (const auto& rSig : pos.getReductions()) {
        // Add preconditions of reduction
        addPreconditionsAndConstraints(pos, rSig, _htn.getOpTable().getReduction(rSig).getPreconditions(), /*isRepetition=*/false);
    }
}

void Planner::addPreconditionsAndConstraints(Position& pos, const USignature& op, const SigSet& preconditions, bool isRepetition) {
    USignature constrOp = isRepetition ? USignature(_htn.getActionNameFromRepetition(op._name_id), op._args) : op;

    // Log::i("Starting preconditions for op %s\n", TOSTR(op));
    for (const Signature& fact : preconditions) {
        // Log::i("  Precondition %s\n", TOSTR(fact));
        // auto cOpt2 = addPrecondition(op, fact, !isRepetition);
        auto cOpt = addPreconditionBitVec(pos, op, fact, !isRepetition);
        // if (cOpt && cOpt2 && *cOpt != *cOpt2) {
        //     Log::e("Inconsistency in precondition constraints for %s\n", 
        //         TOSTR(op));
        // }
        if (cOpt) pos.addSubstitutionConstraint(constrOp, std::move(cOpt.value()));
    }
    if (!isRepetition) addQConstantTypeConstraints(pos, op);

    if (!pos.getSubstitutionConstraints().count(op)) return;

    // Merge substitution constraints as far as possible
    auto& constraints = pos.getSubstitutionConstraints().at(op);
    //Log::d("MERGE? %i constraints\n", constraints.size());
    for (size_t i = 0; i < constraints.size(); i++) {
        for (size_t j = i+1; j < constraints.size(); j++) {
            auto& iTree = constraints[i];
            auto& jTree = constraints[j];
            if (iTree.canMerge(jTree)) {
                //Log::d("MERGE %s %i,%i sizes %i,%i\n", 
                //    iTree.getPolarity() == SubstitutionConstraint::ANY_VALID ? "ANY_VALID" : "NO_INVALID", 
                //    i, j, iTree.getEncodedSize(), jTree.getEncodedSize());
                iTree.merge(std::move(jTree));
                //Log::d("MERGED: new size %i\n", iTree.getEncodedSize());
                if (j+1 < constraints.size()) 
                    constraints[j] = std::move(constraints.back());
                constraints.erase(constraints.begin()+constraints.size()-1);
                j--;
            }
        }
    }
}

std::optional<SubstitutionConstraint> Planner::addPreconditionBitVec(Position& pos, const USignature& op, const Signature& fact, bool addQFact) {

    // Log::i("Adding precondition %s for op %s\n", TOSTR(fact), TOSTR(op));
    const USignature& factAbs = fact.getUnsigned();


    if (!_htn.hasQConstants(factAbs)) {
        
         if (_htn.isEqualityPredicate(factAbs._name_id)) {
            bool equality_is_correct = fact._negated ? factAbs._args[0] != factAbs._args[1] : factAbs._args[0] == factAbs._args[1];
            assert(equality_is_correct || Log::e("Precondition %s not reachable!\n", TOSTR(fact)));
            if (equality_is_correct && !fact._negated) {
                int predId = _htn.getGroundFactId(factAbs, fact._negated);
                // Log::i("Adding equality precondition %s for op %s with predId %i\n", TOSTR(factAbs), TOSTR(op), predId);
                initializeFactBitVec(pos, predId);
                // if (!_analysis.isRelevantBitVec(predId)) {
                //     Log::i("1 ADDING RELEVANT FACT BITVEC %s by %s\n", TOSTR(factAbs), TOSTR(op));
                // }
                _analysis.addRelevantFactBitVec(predId);
            }
            return std::optional<SubstitutionConstraint>();
         }

        int predId = _htn.getGroundFactId(factAbs, fact._negated);
        if (predId < 0) {
            Log::e("Precondition %s not reachable!\n", TOSTR(fact));
            return std::optional<SubstitutionConstraint>();
        }
        assert(_analysis.isReachableBitVec(predId, fact._negated) || Log::e("Precondition %s not reachable!\n", TOSTR(fact)));

        if (_analysis.isReachableBitVec(predId, !fact._negated)) {
            // Negated prec. is reachable: not statically resolvable
            initializeFactBitVec(pos, predId);
            // if (!_analysis.isRelevantBitVec(predId)) {
            //     Log::i("2 ADDING RELEVANT FACT BITVEC %s by %s\n", TOSTR(factAbs), TOSTR(op));
            // }
            // Log::i("1 ADDING RELEVANT FACT BITVEC %s\n", TOSTR(factAbs));
            _analysis.addRelevantFactBitVec(predId);
        }
        return std::optional<SubstitutionConstraint>();
    }
    
    std::vector<int> sorts = _htn.getOpSortsForCondition(factAbs, op);
    std::vector<int> sortedArgIndices = SubstitutionConstraint::getSortedSubstitutedArgIndices(_htn, factAbs._args, sorts);
    std::vector<int> involvedQConsts(sortedArgIndices.size());
    for (size_t i = 0; i < sortedArgIndices.size(); i++) involvedQConsts[i] = factAbs._args[sortedArgIndices[i]];
    SubstitutionConstraint c(involvedQConsts);

    bool staticallyResolvable = true;
    USigSet relevants;
    FlatHashSet<int> relevantsPredIds;
    
    auto eligibleArgs = _htn.getEligibleArgs(factAbs, sorts);

    auto polarity = SubstitutionConstraint::UNDECIDED;
    // Special case if it is an equality fact. Since I do not store all their possible values in ground facts as it could be very large,
    if (_htn.isEqualityPredicate(factAbs._name_id)) {
        // Log::i("This is an equality fact %s\n", TOSTR(factAbs));

        if (!_htn.hasQConstants(factAbs)) return std::optional<SubstitutionConstraint>();

        for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, eligibleArgs)) {

            // Log::i("(BitVec) Decoded fact %s from %s\n", TOSTR(decFactAbs), TOSTR(factAbs));

            bool is_true = fact._negated ? decFactAbs._args[0] != decFactAbs._args[1] : decFactAbs._args[0] == decFactAbs._args[1];
            // Can the decoded fact occur as is?
            if (is_true) {
                if (polarity != SubstitutionConstraint::NO_INVALID)
                    c.addValid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
            } else {
                // Fact cannot hold here
                if (polarity != SubstitutionConstraint::ANY_VALID)
                    c.addInvalid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
            }
        }
        c.fixPolarity();
        return std::optional<SubstitutionConstraint>(std::move(c));
    } 
    else if (_htn.isStaticPredicate(factAbs._name_id)) { // Works, but it is a lot slower with AssemblyHierarchical
        // We can directly add all the correct paths
        BitVec result = ArgIterator2::getFullInstantiation2(factAbs, /*negated=*/false, _htn, sorts); // Get all the statics predicates that can be merged with this fact
        c.fixPolarity(fact._negated ? SubstitutionConstraint::NO_INVALID : SubstitutionConstraint::ANY_VALID);
        for (int predId: result) {
            const USignature& decFactAbs = _htn.getGroundPositiveFact(predId);

            if (fact._negated) {
                c.addInvalid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
            }
            else {
                c.addValid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
            }
        }
        return std::optional<SubstitutionConstraint>(std::move(c));
    }


    size_t totalSize = 1; for (auto& args : eligibleArgs) totalSize *= args.size();
    size_t sampleSize = 25;
    bool doSample = totalSize > 2*sampleSize;
    if (doSample) {
        size_t valids = 0;
        // Check out a random sample of the possible decoded objects
        for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, eligibleArgs, sampleSize)) {
            int predId = _htn.getGroundFactId(decFactAbs, fact._negated);

            if (predId >=0 && _analysis.isReachableBitVec(predId, fact._negated)) valids++;
        }
        polarity = valids < sampleSize/2 ? SubstitutionConstraint::ANY_VALID : SubstitutionConstraint::NO_INVALID;
        c.fixPolarity(polarity);
    }

    // TODO, do a better job there !
    // BitVec result = ArgIterator2::getFullInstantiation2(factAbs, _htn, sorts);
    // if (doSample) {
    //     size_t valids = 0;
    //     size_t num_pred = result.count();
    //     // Make an and over the reachble predicate
    //     result.and_with(_analysis.getReachableFactsBitVec(fact._negated));
    //     size_t num_correct = result.count();

    //     bool take_valid = num_correct > num_pred / 2;

    //     polarity = take_valid ? SubstitutionConstraint::ANY_VALID : SubstitutionConstraint::NO_INVALID;
    //     c.fixPolarity(polarity);
    // }

    // For each fact decoded from the q-fact:
    for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, eligibleArgs)) {
    // for (size_t predId: result) {

        // Log::i("(BitVec) Decoded fact %s from %s\n", TOSTR(decFactAbs), TOSTR(factAbs));

        // const USignature& decFactAbs = _htn.getGroundPositiveFact(predId);
        int predId = _htn.getGroundFactId(decFactAbs, fact._negated);

        // bool equality_pred_true = _htn.isEqualityPredicate(decFactAbs._name_id) && fact._negated ? decFactAbs._args[0] != decFactAbs._args[1] : decFactAbs._args[0] == decFactAbs._args[1];

        // Can the decoded fact occur as is?
        if (predId >= 0 && _analysis.isReachableBitVec(predId, fact._negated)) {
            if (polarity != SubstitutionConstraint::NO_INVALID)
                c.addValid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
        } else {
            // Fact cannot hold here
            if (polarity != SubstitutionConstraint::ANY_VALID)
                c.addInvalid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
            continue;
        }

        // If the fact is reachable, is it even invariant?
        // if (_analysis.isInvariant(decFactAbs, fact._negated)) {
        if (_analysis.isInvariantBitVec(predId, fact._negated)) {
            // Yes! This precondition is trivially satisfied 
            // with above substitution restrictions
            continue;
        }

        staticallyResolvable = false;
        // relevants.insert(decFactAbs);
        relevantsPredIds.insert(predId);
    }

    if (!staticallyResolvable) {
        if (addQFact) pos.addQFact(factAbs);
        // for (const USignature& decFactAbs : relevants) {
        for (const int& predId : relevantsPredIds) {
            const USignature& decFactAbs = _htn.getGroundPositiveFact(predId);
            // Decoded fact may be new - initialize as necessary
            // initializeFact(pos, decFactAbs);
            initializeFactBitVec(pos, predId);
            if (addQFact) pos.addQFactDecoding(factAbs, decFactAbs, fact._negated);
            // Log::i("2 ADDING RELEVANT FACT BITVEC %s\n", TOSTR(decFactAbs));
            // if (!_analysis.isRelevantBitVec(predId)) {
            //     _analysis.printReachableFactsBitVec();
            //     Log::i("3 ADDING RELEVANT FACT BITVEC %s by %s\n", TOSTR(decFactAbs), TOSTR(op));
            // }
            _analysis.addRelevantFactBitVec(predId);
        }
    } // else : encoding the precondition is not necessary!
    if (!doSample) c.fixPolarity();
    return std::optional<SubstitutionConstraint>(std::move(c));
}


void Planner::addGroundEffectBitVec(Position& pos, const USignature& opSig, BitVec effects, bool negated, EffectMode mode) 
{
    if (effects.count() == 0) return; // No effect to add

    // Remove all invariant ground facts from the effects
    _analysis.removeInvariantGroundFactsBitVec(effects, negated);
    if (mode != INDIRECT) {
        // Log::i("AddGroundEffect: add Relevant fact %s for op %s\n", TOSTR(effects), TOSTR(opSig));
        _analysis.addMultipleRelevantFactsBitVec(effects);
    }

    // Indicate for the position that all those effects are fact changes possible
    pos.addMultipleFactChangesBitVec(effects, negated);

    // Indicate that all those effects are reachable facts
    _analysis.addMultipleReachableFactsBitVec(effects, negated);

    // Now, we would need to have a better way to handle the support of the facts
    // For now, iterate over the bits and add the support for each fact
    for (int predId: effects) {
        const USignature& factAbs = _htn.getGroundPositiveFact(predId);
        Signature fact = factAbs.toSignature(negated);
        if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
            pos.addFactSupportId(predId, negated, opSig);
        } else {
            pos.touchFactSupportId(predId, negated);
        }
    }   
}


bool Planner::addGroundEffect(Position& pos, const USignature& opSig, int predId, bool negated, EffectMode mode) {
    assert(pos.getPositionIndex() > 0);

    // Log::i("Adding ground effect %s for op %s\n", TOSTR(_htn.getGroundPositiveFact(predId)), TOSTR(opSig));

    // Invariant fact? --> no need to encode
    if (_analysis.isInvariantBitVec(predId, negated)) return true;

    if (mode != INDIRECT) {
        _analysis.addRelevantFactBitVec(predId);
    }

    // Change this later...
    const USignature& factAbs = _htn.getGroundPositiveFact(predId);
    Signature fact = factAbs.toSignature(negated);

    // Depending on whether fact supports are encoded for primitive ops only,
    // add the ground fact to the op's support accordingly
    if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
        // pos.addFactSupport(fact, opSig);
        pos.addFactSupportId(predId, negated, opSig);
    } else {
        // Remember that there is some (unspecified) support for this fact
        pos.touchFactSupportId(predId, negated);
    }
    pos.addFactChangeBitVec(predId, negated);
    
    // Log::i("Adding reachable fact %s for op %s\n", TOSTR(fact), TOSTR(opSig));
    _analysis.addReachableFactBitVec(predId, negated);
    return true;
}


bool Planner::addPseudoGroundEffect(Position& pos, Position& left, const USignature& opSig, const Signature& fact, EffectMode mode) {
    assert(pos.getPositionIndex() > 0);
    USignature factAbs = fact.getUnsigned();
    bool isQFact = _htn.hasQConstants(factAbs);

    if (!isQFact) {
        // Fully ground, need to call the addGroundEffect instead
        // But first, we need to get the predId of the fact. It annoy me that we use a map for that, but I have no other idea there...
        int a = 0;
        int predId = _htn.getGroundFactId(factAbs, fact._negated);
        if (predId == -1) return false; // Not a valid fact, cannot add it
        return addGroundEffect(pos, opSig, predId, fact._negated, mode);
    }

    // Create the full set of valid decodings for this qfact
    std::vector<int> sorts = _htn.getOpSortsForCondition(factAbs, opSig);
    std::vector<int> sortedArgIndices = SubstitutionConstraint::getSortedSubstitutedArgIndices(_htn, factAbs._args, sorts);
    const bool isConstrained = left.getSubstitutionConstraints().count(opSig);
    
    std::vector<int> involvedQConsts(sortedArgIndices.size());
    for (size_t i = 0; i < sortedArgIndices.size(); i++) involvedQConsts[i] = factAbs._args[sortedArgIndices[i]];
    std::vector<SubstitutionConstraint*> fittingConstrs, otherConstrs;
    if (isConstrained) {
        for (auto& c : left.getSubstitutionConstraints().at(opSig)) {
            if (c.getInvolvedQConstants() == involvedQConsts) fittingConstrs.push_back(&c);
            else if (c.getPolarity() == SubstitutionConstraint::NO_INVALID || c.involvesSupersetOf(involvedQConsts)) 
                otherConstrs.push_back(&c);
        }
    }
    
    bool anyGood = false;
    bool staticallyResolvable = true;
    bool existNegativeEffWhichCanConflitWithPosEff = false; // Compute it for each action in preprocessing
    // Iterate over the effect of the action to check if a negative effect as the same name_id as this positive eff
    // TODO could be done in preprocessing...
    if (!fact._negated && (_htn.isAction(opSig) || (_use_sibylsat_expansion && mode == DIRECT))) {
        const SigSet& effects = _htn.isAction(opSig) ? _htn.getOpTable().getAction(opSig).getEffects() : _htn.getOpTable().getReduction(opSig).getEffects();
        for (const Signature& negFact : effects) {
            // Log::i("Effect: %s\n", TOSTR(negFact));
            if (negFact._negated && negFact._usig._name_id == fact._usig._name_id) {
                existNegativeEffWhichCanConflitWithPosEff = true;
                break;
            }
        }
    }
    bool isPositiveEffOfAction = (_htn.isAction(opSig) || (_use_sibylsat_expansion && mode == DIRECT)) && !fact._negated;

    // for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, _htn.getEligibleArgs(factAbs, sorts))) {
    BitVec result = ArgIterator2::getFullInstantiation2(factAbs, fact._negated, _htn, sorts);
    for (int predId: result) {
        const USignature& decFactAbs = _htn.getGroundPositiveFact(predId);
        // int predId = _htn.getGroundFactId(decFactAbs);
        // if (predId < 0) {
            // continue;
        // }

        // Log::i("Can be ground to %s\n", TOSTR(decFactAbs));
    
        auto path = SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices);

        // Check if this decoding is known to be invalid due to some precondition
        if (isConstrained) {
            bool isValid = true;
            for (const auto& c : fittingConstrs) {
                if (!c->isValid(path, /*sameReference=*/true)) {
                    isValid = false;
                    break;
                }
            }
            if (isValid) for (const auto& c : otherConstrs) {
                if (!c->isValid(path, /*sameReference=*/false)) {
                    isValid = false;
                    break;
                }
            }
            if (!isValid) continue;
        }

        anyGood = true;
        // if (_analysis.isInvariant(decFactAbs, fact._negated)) {
        if (_analysis.isInvariantBitVec(predId, fact._negated)) {

            if (isPositiveEffOfAction && existNegativeEffWhichCanConflitWithPosEff && staticallyResolvable) {
                // Need to encode at least one positive effect or there will be only the negative effect of the action encoded
                Log::d("Eff: %c %s of %s hold trivially but must be added for correct encoding\n", fact._negated ? '-' : '+', TOSTR(decFactAbs), TOSTR(opSig));
            } else {
                continue;
            }
        }

        // Valid effect decoding
        _analysis.addReachableFactBitVec(predId, /*negated=*/fact._negated);
        if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
            pos.addIndirectFactSupportId(predId, fact._negated, opSig, path);
        } else {
            pos.touchFactSupportId(predId, fact._negated);
        }
        pos.addFactChangeBitVec(predId, fact._negated);
        if (mode != INDIRECT) {
            if (mode == DIRECT) pos.addQFactDecoding(factAbs, decFactAbs, fact._negated);
            // _analysis.addRelevantFact(decFactAbs);
            // Log::i("Adding relevant fact %s\n", TOSTR(decFactAbs));
            // if (!_analysis.isRelevantBitVec(predId)) {
                // Log::i("5 ADDING RELEVANT FACT BITVEC %s by %s\n", TOSTR(decFactAbs), TOSTR(opSig));
            // }
            
            _analysis.addRelevantFactBitVec(predId);
        }
        staticallyResolvable = false;
    }
    // Not a single valid decoding of the effect? -> Invalid effect.
    if (!anyGood) return false;

    if (!staticallyResolvable && mode == DIRECT) pos.addQFact(factAbs);
    
    return true;
}




void Planner::propagateInitialState(Position& newPos, const Position& above) {
    assert(newPos.getLayerIndex() > 0);
    assert(newPos.getPositionIndex() == 0);

    _analysis.resetReachability();

    // Propagate TRUE facts
    for (const int predId : above.getTrueFactsIds()) {
        const USignature& predFact = _htn.getGroundPositiveFact(predId);
        newPos.addTrueFact(predFact);
        newPos.addTrueFactId(predId);
        _analysis.addInitializedFactBitVec(predId);
    }
    for (const int predId : above.getFalseFactsIds()) {
        const USignature& predFact = _htn.getGroundPositiveFact(predId);
        newPos.addFalseFact(predFact);
        newPos.addFalseFactId(predId);
        _analysis.addInitializedFactBitVec(predId);
    }

}

void Planner::propagateActions(Position& newPos, Position& above) {
    size_t offset = newPos.getOffset();
    // Check validity of actions at above position
    std::vector<USignature> actionsToPrune;
    size_t numActionsBefore = above.getActions().size();
    for (const auto& aSig : above.getActions()) {
        const Action& a = _htn.getOpTable().getAction(aSig);

        // Can the action occur here w.r.t. the current state?
        // bool valid = _analysis.hasValidPreconditions(a.getPreconditions())
                // && _analysis.hasValidPreconditions(a.getExtraPreconditions());


        bool valid = _analysis.hasValidPreconditionsBitVec(a.getPreconditions())
                && _analysis.hasValidPreconditionsBitVec(a.getExtraPreconditions());

        // if (valid != validWithBitVec) {
        //     Log::e("1_ Inconsistency in preconditions for action %s: %s vs %s\n", 
        //         TOSTR(aSig), valid ? "valid" : "invalid", validWithBitVec ? "valid" : "invalid");
        //     _analysis.printReachableFacts();
        //     _analysis.printReachableFactsBitVec();

        //     bool valid_pred = _analysis.hasValidPreconditionsBitVec(a.getPreconditions());
        //     bool valid_extra_pred = _analysis.hasValidPreconditionsBitVec(a.getExtraPreconditions());


        //     exit(1);
        // }

        // If not: forbid the action, i.e., its parent action
        if (!valid) {
            Log::i("Retroactively prune action %s@(%i,%i): no children at offset %i\n",
                TOSTR(aSig), above.getLayerIndex(), above.getPositionIndex(), offset);
            actionsToPrune.push_back(aSig);
        }
    }

    // Prune invalid actions at above position
    for (const auto& aSig : actionsToPrune) {
        _pruning.prune(aSig, above);
    }
    assert(above.getActions().size() == numActionsBefore - actionsToPrune.size() 
        || Log::e("%i != %i-%i\n", above.getActions().size(), numActionsBefore, actionsToPrune.size()));

    // Propagate remaining (valid) actions from above
    for (const auto& aSig : above.getActions()) {
        if (offset < 1) {
            // proper action propagation
            assert(_htn.isFullyGround(aSig));
            if (_params.isNonzero("aar") && !_htn.isActionRepetition(aSig._name_id)) {
                // Virtualize child of action
                USignature vChildSig = _htn.getRepetitionOfAction(aSig);
                newPos.addAction(vChildSig);
                newPos.addExpansion(aSig, vChildSig);
            } else {
                // Treat as a normal action
                newPos.addAction(aSig);
                newPos.addExpansion(aSig, aSig);
            }
        } else {
            // action expands to "blank" at non-zero offsets
            const USignature& blankSig = _htn.getBlankActionSig();
            newPos.addAction(blankSig);
            newPos.addExpansion(aSig, blankSig);
        }
    }
}

void Planner::propagateReductions(Position& newPos, Position& above) {
    size_t offset = newPos.getOffset();
    NodeHashMap<USignature, USigSet, USignatureHasher> subtaskToParents;
    NodeHashSet<USignature, USignatureHasher> reductionsWithChildren;

    // Collect all possible subtasks and remember their possible parents
    for (const auto& rSig : above.getReductions()) {

        const Reduction r = _htn.getOpTable().getReduction(rSig);
        
        if (offset < r.getSubtasks().size()) {
            // Proper expansion
            const USignature& subtask = r.getSubtasks()[offset];
            subtaskToParents[subtask].insert(rSig);
        } else {
            // Blank
            reductionsWithChildren.insert(rSig);
            const USignature& blankSig = _htn.getBlankActionSig();
            newPos.addAction(blankSig);
            newPos.addExpansion(rSig, blankSig);
        }
    }

    // Iterate over all possible subtasks
    for (const auto& [subtask, parents] : subtaskToParents) {

        // Log::i("For subtask %s@(%i,%i) at offset %i, found %zu parents\n", 
                // TOSTR(subtask), _depth-1, _old_pos, offset, parents.size());

        // Calculate all possible actions fitting the subtask.
        auto allActions = instantiateAllActionsOfTask(newPos, subtask);

        // Any reduction(s) fitting the subtask?
        for (const USignature& subRSig : instantiateAllReductionsOfTask(newPos, subtask)) {

            if (_htn.isAction(subRSig)) {
                // Actually an action, not a reduction: remember for later
                allActions.push_back(subRSig);
                continue;
            }

            const Reduction& subR = _htn.getOpTable().getReduction(subRSig);
            
            assert(_htn.isReduction(subRSig) && subRSig == subR.getSignature() && _htn.isFullyGround(subRSig));

            newPos.addReduction(subRSig);
            newPos.addExpansionSize(subR.getSubtasks().size());

            if (_optimal) {
                // Find the admissible tdg heuristic value for this reduction
                int heuristicValue = _tdg->getBestHeuristicValue(subRSig);
                Log::d("Set the heuristic value of %s to %d\n", TOSTR(subRSig), heuristicValue);
                newPos.setHeuristicValue(subRSig, heuristicValue);
            }

            for (const auto& rSig : parents) {
                reductionsWithChildren.insert(rSig);
                newPos.addExpansion(rSig, subRSig);
            }
        }

        // Any action(s) fitting the subtask?
        for (const USignature& aSig : allActions) {

            assert(_htn.isFullyGround(aSig));
            newPos.addAction(aSig);

            for (const auto& rSig : parents) {
                reductionsWithChildren.insert(rSig);
                newPos.addExpansion(rSig, aSig);
            }
        }
    }

    // Check if any reduction has no valid children at all
    std::vector<USignature> reductionsWithNoChildren;
    for (const auto& rSig : above.getReductions()) {
        if (!reductionsWithChildren.count(rSig)) {
            reductionsWithNoChildren.push_back(rSig);
        }
    }

    // Prune invalid reductions at above position
    for (const auto& rSig : reductionsWithNoChildren) {
        Log::i("Retroactively prune reduction %s@(%i,%i): no children at offset %i\n", 
                    TOSTR(rSig), above.getLayerIndex(), above.getPositionIndex(), offset);
        _pruning.prune(rSig, above);
    }
}

std::vector<USignature> Planner::instantiateAllActionsOfTask(Position& pos, const USignature& task) {
    std::vector<USignature> result;

    if (!_htn.isAction(task)) return result;
    
    for (USignature& sig : _instantiator.getApplicableInstantiations(_htn.toAction(task._name_id, task._args))) {
        // Log::i("Instantiate action %s\n", TOSTR(sig));

        // Log::i("ADDACTION %s ?\n", TOSTR(sig));
        Action action = _htn.toAction(sig._name_id, sig._args);

        // Rename any remaining variables in each action as unique q-constants,
        action = _htn.replaceVariablesWithQConstants(
            action,
            _analysis.getReducedArgumentDomains(action),
            pos.getLayerIndex(),
            pos.getPositionIndex());

        // Remove any contradictory ground effects that were just created
        action.removeInconsistentEffects();

        // Check validity
        if (!_htn.isFullyGround(action.getSignature())) continue;
        if (!_htn.hasConsistentlyTypedArgs(sig)) continue;
        // if (!_analysis.hasValidPreconditions(action.getPreconditions())) {
        if (!_analysis.hasValidPreconditionsBitVec(action.getPreconditions())) {
            // Same result with bitvec ?
            // if (_analysis.hasValidPreconditionsBitVec(action.getPreconditions())) {
                // Log::e("2_ Inconsistency in preconditions for action %s: %s vs %s\n", 
                    // TOSTR(action.getSignature()), "valid", "invalid");
                // _analysis.printReachableFacts();
                // _analysis.printReachableFactsBitVec();
                // exit(1);
            // }

            continue;
        }
        // if (!_analysis.hasValidPreconditions(action.getExtraPreconditions())) {
        if (!_analysis.hasValidPreconditionsBitVec(action.getExtraPreconditions())) {
            // Same result with bitvec ?
            // if (_analysis.hasValidPreconditionsBitVec(action.getExtraPreconditions())) {
                // Log::e("Inconsistency in extra preconditions for action %s: %s vs %s\n", 
                    // TOSTR(action.getSignature()), "valid", "invalid");
                // exit(1);
            // }
            continue;
        }
        
        // Action is valid
        sig = action.getSignature();
        _htn.getOpTable().addAction(action);
        result.push_back(action.getSignature());
    }
    return result;
}

std::vector<USignature> Planner::instantiateAllReductionsOfTask(Position& pos, const USignature& task) {
    std::vector<USignature> result;

    if (!_htn.hasReductions(task._name_id)) return result;

    // Filter and minimally instantiate methods
    // applicable in current (super)state
    for (int redId : _htn.getReductionIdsOfTaskId(task._name_id)) {
        Reduction r = _htn.getReductionTemplate(redId);

        if (_htn.isReductionPrimitivizable(redId)) {
            const Action& a = _htn.getReductionPrimitivization(redId);

            std::vector<Substitution> subs = Substitution::getAll(r.getTaskArguments(), task._args);
            for (const Substitution& s : subs) {
                USignature primSig = a.getSignature().substitute(s);
                for (const auto& sig : instantiateAllActionsOfTask(pos, primSig)) {
                    result.push_back(sig);
                }
            }
            continue;
        }

        std::vector<Substitution> subs = Substitution::getAll(r.getTaskArguments(), task._args);
        for (const Substitution& s : subs) {
            for (const auto& entry : s) assert(entry.second != 0);

            Reduction rSub = r.substituteRed(s);
            USignature origSig = rSub.getSignature();
            if (!_htn.hasConsistentlyTypedArgs(origSig)) continue;
            
            for (USignature& red : _instantiator.getApplicableInstantiations(rSub)) {
                auto rOpt = createValidReduction(pos, red, task);
                if (rOpt) result.push_back(rOpt.value().getSignature());
            }
        }
    }
    return result;
}

std::optional<Reduction> Planner::createValidReduction(Position& pos, const USignature& sig, const USignature& task) {
    std::optional<Reduction> rOpt;

    // Rename any remaining variables in each action as new, unique q-constants 
    Reduction red = _htn.toReduction(sig._name_id, sig._args);
    auto domains = _analysis.getReducedArgumentDomains(red);
    red = _htn.replaceVariablesWithQConstants(red, domains, pos.getLayerIndex(), pos.getPositionIndex());

    // Check validity
    bool isValid = true;
    if (task._name_id >= 0 && red.getTaskSignature() != task) isValid = false;
    else if (!_htn.isFullyGround(red.getSignature())) isValid = false;
    else if (!_htn.hasConsistentlyTypedArgs(red.getSignature())) isValid = false;
    // else if (!_analysis.hasValidPreconditions(red.getPreconditions())) {
    else if (!_analysis.hasValidPreconditionsBitVec(red.getPreconditions())) {
        // Same result with bitvec ?
        // if (_analysis.hasValidPreconditionsBitVec(red.getPreconditions())) {
            // Log::e("Inconsistency in preconditions for reduction %s: %s vs %s\n", 
                // TOSTR(red.getSignature()), "valid", "invalid");
            // exit(1);
        // }
        isValid = false;
    }
    // else if (!_analysis.hasValidPreconditions(red.getExtraPreconditions())) {
    else if (!_analysis.hasValidPreconditionsBitVec(red.getExtraPreconditions())) {
        // if (_analysis.hasValidPreconditionsBitVec(red.getExtraPreconditions())) {
            // Log::e("Inconsistency in extra preconditions for reduction %s: %s vs %s\n", 
                // TOSTR(red.getSignature()), "valid", "invalid");
            // exit(1);
        // }
        isValid = false;
    }

    if (isValid) {
        _htn.getOpTable().addReduction(red);
        rOpt.emplace(red);
    }
    return rOpt;
}

void Planner::initializeNextEffectsBitVec(Position& newPos) {
    // For each possible operation effect:
    const USigSet* ops[2] = {&newPos.getActions(), &newPos.getReductions()};
    bool isAction = true;
    for (const auto& set : ops) {
        for (const auto& aSig : *set) {
            // const SigSet& pfc = _analysis.getPossibleFactChanges(aSig, FactAnalysis::FULL, isAction ? FactAnalysis::ACTION : FactAnalysis::REDUCTION);
            // for (const Signature& eff : pfc) {

            //     if (!_htn.hasQConstants(eff._usig)) {
            //         // New ground fact: set before the action may happen
            //         if (_analysis.checkGroundingFacts() && !_analysis.isInGroundFacts(eff)) {
            //             continue;
            //         }
            //         initializeFact(newPos, eff._usig); 
            //     } else {
            //         std::vector<int> sorts = _htn.getOpSortsForCondition(eff._usig, aSig);
            //         for (const USignature& decEff : _htn.decodeObjects(eff._usig, _htn.getEligibleArgs(eff._usig, sorts))) {           
            //             // New ground fact: set before the action may happen
            //             if (_analysis.checkGroundingFacts() && !_analysis.isInGroundFacts(decEff, eff._negated)) {
            //                 continue;
            //             }
            //             initializeFact(newPos, decEff);
            //         }
            //     }
            // }
            // const SigSet& pfc = _analysis.getPossibleFactChanges(aSig, FactAnalysis::FULL, isAction ? FactAnalysis::ACTION : FactAnalysis::REDUCTION);
            const BitVec& groundEffPos = _analysis.getPossibleGroundFactChanges(aSig, /*negated=*/false);
            const BitVec& groundEffNeg = _analysis.getPossibleGroundFactChanges(aSig, /*negated=*/true);
            const SigSet& pseudoEff = _analysis.getPossiblePseudoGroundFactChanges(aSig);
            for (size_t predId : groundEffPos) {
                initializeFactBitVec(newPos, predId);
            }
            for (size_t predId : groundEffNeg) {
                initializeFactBitVec(newPos, predId);
            }
            for (const Signature& eff : pseudoEff) {
                if (!_htn.hasQConstants(eff._usig)) {
                    int predId = _htn.getGroundFactId(eff._usig, eff._negated);
                    if (predId > 0) {
                        // Log::i("(BitVec) Initialize fact %s for action %s\n", TOSTR(eff._usig), TOSTR(aSig));
                        initializeFactBitVec(newPos, predId);
                        continue;
                    }
                }
                BitVec groundEffPos = ArgIterator2::getFullInstantiation2(eff._usig, eff._negated, _htn, _htn.getOpSortsForCondition(eff._usig, aSig));
                
                for (size_t predId : groundEffPos) {
                    const USignature& fact = _htn.getGroundPositiveFact(predId);
                    // Log::i("(BitVec) Initialize fact %s for action %s\n", TOSTR(fact), TOSTR(aSig));
                    initializeFactBitVec(newPos, predId);
                }
            }
        }
        isAction = false;
    }
}

void Planner::initializeFactBitVec(Position& newPos, const int predId) {

    const USignature& fact = _htn.getGroundPositiveFact(predId);

    // Has the fact already been defined? -> Not new!
    if (_analysis.isInitializedBitVec(predId)) return;

    _analysis.addInitializedFactBitVec(predId);

    // if (_analysis.isReachable(fact, /*negated=*/true)) newPos.addFalseFact(fact);
    if (_analysis.isReachableBitVec(predId, /*negated=*/true)) {
        newPos.addFalseFact(fact);
        newPos.addFalseFactId(predId);
    }
    else { 
        newPos.addTrueFact(fact);
        newPos.addTrueFactId(predId);
    }
}

void Planner::addQConstantTypeConstraints(Position& pos, const USignature& op) {
    // Add type constraints for q constants
    std::vector<TypeConstraint> cs = _htn.getQConstantTypeConstraints(op);
    // Add to this position's data structure
    for (const TypeConstraint& c : cs) {
        pos.addQConstantTypeConstraint(op, c);
    }
}

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
