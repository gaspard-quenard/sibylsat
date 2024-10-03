
#include <assert.h> 

#include "planner.h"
#include "util/log.h"
#include "util/signal_manager.h"
#include "util/timer.h"
#include "sat/plan_optimizer.h"

int terminateSatCall(void* state) {return ((Planner*) state)->getTerminateSatCall();}

int Planner::findPlan() {
    
    int iteration = 0;
    Log::i("Iteration %i.\n", iteration);

    createFirstLayer();

    // Bounds on depth to solve / explore
    int firstSatCallIteration = _params.getIntParam("d");
    int maxIterations = _params.getIntParam("D");
    _sat_time_limit = _params.getFloatParam("stl");

    bool solved = false;
    bool solvedVirtualPlan = false;
    _enc.setTerminateCallback(this, terminateSatCall);
    if (iteration >= firstSatCallIteration) {
        _enc.addAssumptions(_layer_idx);
        int result = _enc.solve();
        if (result == 0) {
            Log::w("Solver was interrupted. Discarding time limit for next solving attempts.\n");
            _sat_time_limit = 0;
        }
        solved = result == 10;
    } 

    if (_use_sibylsat_expansion) {
        // Only develop the position which contains the _top_method
        sibylsat_positions_to_develop.insert(0);
    }
    
    // Next layers
    while (!solved && (maxIterations == 0 || iteration < maxIterations)) {

        if (iteration >= firstSatCallIteration) {

            _enc.printFailedVars(*_layers.back());

            if (_params.isNonzero("cs")) { // check solvability
                Log::i("Not solved at layer %i with assumptions\n", _layer_idx);

                // Attempt to solve formula again, now without assumptions
                // (is usually simple; if it fails, we know the entire problem is unsolvable)
                int result = _enc.solve();
                if (result == 20) {
                    Log::w("Unsolvable at layer %i even without assumptions!\n", _layer_idx);
                    break;
                } else {
                    Log::i("Not proven unsolvable - expanding by another layer\n");
                }
            } else {
                Log::i("Unsolvable at layer %i -- expanding.\n", _layer_idx);
            }
        }

        iteration++;      
        Log::i("Iteration %i.\n", iteration);
        
        if (_use_sibylsat_expansion) {
            // Only develop the positions where the associate reduction is true in the last virtual plan
            createNextLayerUsingSibylSat(sibylsat_positions_to_develop);
        } else {
            // Lilotane: Breadth first expansion
            createNextLayer();
        }
        

        if (iteration >= firstSatCallIteration) {
            _enc.addAssumptions(_layer_idx);
            int result = _enc.solve();
            if (result == 0) {
                Log::w("Solver was interrupted. Discarding time limit for next solving attempts.\n");
                _sat_time_limit = 0;
            }
            solved = result == 10;
        } 

        if (_use_sibylsat_expansion && !solved) {
            Log::i("Failed to find a solution at layer %i. Trying to find a virtual plan...\n", _layer_idx);
            // Find a virtual plan to develop
            int result = _enc.solve();
            if (result == 0) {
                Log::w("Solver was interrupted. Discarding time limit for next solving attempts.\n");
                _sat_time_limit = 0;
            }
            solvedVirtualPlan = result == 10;
            if (!solvedVirtualPlan) {
                Log::w("No virtual plan found. Problem is impossible ! Exiting.\n");
                break;
            }

            Log::i("Found a virtual plan\n");

            // Extract the virtual plan and use it to determinate which positions need to be developed
            std::vector<PlanItem> virtualPlan = _enc.extractVirtualPlan();
            sibylsat_positions_to_develop.clear();
            int pos = -1;
            for (const PlanItem& item : virtualPlan) {
                pos++;
                if (item.id == -1) continue;
                else if (_htn.isReduction(item.reduction)) {
                    if (_verbosity >= Log::V2_INFORMATION) {
                        const USignature& rSig = _enc.getOpHoldingInLayerPos(_layer_idx, pos);
                        Log::d("  Reduction %s is true in layer %i, position %i\n", TOSTR(rSig), _layer_idx, pos);
                    }
                    sibylsat_positions_to_develop.insert(pos);
                }
            }

        }
    }

    if (!solved) {
        if (iteration >= firstSatCallIteration) _enc.printFailedVars(*_layers.back());
        Log::w("No success. Exiting.\n");
        return 1;
    }

    Log::i("Found a solution at layer %i.\n", _layers.size()-1);
    _time_at_first_plan = Timer::elapsedSeconds();

    improvePlan(iteration);

    _plan_writer.outputPlan(_plan);
    printStatistics();    
    return 0;
}

void Planner::improvePlan(int& iteration) {

    // Compute extra layers after initial solution as desired
    PlanOptimizer optimizer(_htn, _layers, _enc);
    int maxIterations = _params.getIntParam("D");
    int extraLayers = _params.getIntParam("el");
    int upperBound = _layers.back()->size()-1;
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
                    createNextLayer();
                }
                // Solve again (to get another plan)
                _enc.addAssumptions(_layer_idx);
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
                Log::i("Initial plan at layer %i has length %i\n", iteration, newLength);
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
                createNextLayer();
            }

            // Solve again (to get another plan)
            _enc.addAssumptions(_layer_idx);
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
            Log::i("Initial plan at final layer has length %i\n", newLength);
            // Optimize
            optimizer.optimizePlan(upperBound, _plan, PlanOptimizer::ConstraintAddition::PERMANENT);

        } else {
            // Just extract plan
            _plan = _enc.extractPlan();
            _has_plan = true;
        }
    }
}

void Planner::incrementPosition() {
    _num_instantiated_actions += _layers[_layer_idx]->at(_pos).getActions().size();
    _num_instantiated_reductions += _layers[_layer_idx]->at(_pos).getReductions().size();
    _pos++; _num_instantiated_positions++;
}

void Planner::createFirstLayer() {

    // Initial layer of size 2 (top level reduction + goal action)
    int initSize = 2;
    Log::i("Creating initial layer of size %i\n", initSize);
    _layer_idx = 0;
    _pos = 0;
    _layers.push_back(new Layer(0, initSize));
    Layer& initLayer = (*_layers[0]);
    initLayer[_pos].setPos(_layer_idx, _pos);
    // Useful informations for sibylsat expansion
    initLayer[_pos].setOriginalLayerIdx(_layer_idx);
    initLayer[_pos].setOriginalPos(_pos);
    
    
    
    /***** LAYER 0, POSITION 0 ******/

    // Instantiate all possible init. reductions
    for (USignature& rSig : _instantiator.getApplicableInstantiations(_htn.getInitReduction())) {
        auto rOpt = createValidReduction(rSig, USignature());
        if (rOpt) {
            auto& r = rOpt.value();
            USignature sig = r.getSignature();
            initLayer[_pos].addReduction(sig);
            initLayer[_pos].addAxiomaticOp(sig);
            initLayer[_pos].addExpansionSize(r.getSubtasks().size());
        }
    }
    addPreconditionConstraints();
    initializeNextEffects();
    
    incrementPosition();

    /***** LAYER 0, POSITION 1 ******/

    createNextPosition(); // position 1

    // Create virtual goal action
    Action goalAction = _htn.getGoalAction();
    USignature goalSig = goalAction.getSignature();
    initLayer[_pos].addAction(goalSig);
    initLayer[_pos].addAxiomaticOp(goalSig);
    addPreconditionConstraints();
    // Useful informations for sibylsat expansion
    initLayer[_pos].setOriginalLayerIdx(_layer_idx);
    initLayer[_pos].setOriginalPos(_pos);
    
    
    /***** LAYER 0 END ******/

    initLayer[0].clearAfterInstantiation();
    initLayer[1].clearAfterInstantiation();

    _pos = 0;
    _enc.encode(_layer_idx, _pos++);
    _enc.encode(_layer_idx, _pos++);
    initLayer.consolidate();
}

void Planner::createNextLayer() {

    _layers.push_back(new Layer(_layers.size(), _layers.back()->getNextLayerSize()));
    Layer& newLayer = *_layers.back();
    Log::i("New layer size: %i\n", newLayer.size());
    Layer& oldLayer = (*_layers[_layer_idx]);
    _layer_idx++;
    _pos = 0;

    // Instantiate new layer
    Log::i("Instantiating ...\n");
    for (_old_pos = 0; _old_pos < oldLayer.size(); _old_pos++) {
        size_t newPos = oldLayer.getSuccessorPos(_old_pos);
        size_t maxOffset = oldLayer[_old_pos].getMaxExpansionSize();

        // Instantiate each new position induced by the old position
        for (size_t offset = 0; offset < maxOffset; offset++) {
            //Log::d("%i,%i,%i,%i\n", _old_pos, newPos, offset, newLayer.size());
            assert(_pos == newPos + offset);
            Log::v("- Position (%i,%i)\n", _layer_idx, _pos);

            assert(newPos+offset < newLayer.size());

            createNextPosition();
            Log::v("  Instantiation done. (r=%i a=%i qf=%i supp=%i)\n", 
                    (*_layers[_layer_idx])[_pos].getReductions().size(),
                    (*_layers[_layer_idx])[_pos].getActions().size(),
                    (*_layers[_layer_idx])[_pos].getQFacts().size(),
                    (*_layers[_layer_idx])[_pos].getPosFactSupports().size() + (*_layers[_layer_idx])[_pos].getNegFactSupports().size()
            );
            if (_pos > 0) _layers[_layer_idx]->at(_pos-1).clearAfterInstantiation();

            incrementPosition();
            checkTermination();
        }
    }
    if (_pos > 0) _layers[_layer_idx]->at(_pos-1).clearAfterInstantiation();

    Log::i("Collected %i relevant facts at this layer\n", _analysis.getRelevantFacts().size());

    // Encode new layer
    Log::i("Encoding ...\n");
    for (_old_pos = 0; _old_pos < oldLayer.size(); _old_pos++) {
        size_t newPos = oldLayer.getSuccessorPos(_old_pos);
        size_t maxOffset = oldLayer[_old_pos].getMaxExpansionSize();
        for (size_t offset = 0; offset < maxOffset; offset++) {
            _pos = newPos + offset;
            Log::v("- Position (%i,%i)\n", _layer_idx, _pos);
            _enc.encode(_layer_idx, _pos);
            clearDonePositions(offset);
        }
    }

    newLayer.consolidate();
}


void Planner::createNextLayerUsingSibylSat(const FlatHashSet<int>& positionsToDevelop) {

    Layer& oldLayer = (*_layers[_layer_idx]);


    // Find the size of the next layer with the known position to develop
    int size_new_layer = _layers.back()->size();

    for (int pos: positionsToDevelop) {
        Position& oldPos = oldLayer[pos];
        size_new_layer += oldPos.getMaxExpansionSize() - 1;
    }

    // We need to set where the next position will be for each position of the old layer
    oldLayer.clearSuccessorPositions();

    // Create the new layer
    _layers.push_back(new Layer(_layers.size(), size_new_layer));
    Log::i("New layer size: %i\n", size_new_layer);

     // Get the new layer
    Layer& newLayer = *_layers.back();

    _layer_idx++;
    _pos = 0;


    // Instantiate new layer
    Log::i("Instantiating ...\n");
    int num_pos_developed = 0;
    bool all_pos_developed = false;
    bool left_pos_is_developed = false;

    for (_old_pos = 0; _old_pos < oldLayer.size(); _old_pos++)  {

        oldLayer.pushSuccessorPosition(_pos);

        if (!positionsToDevelop.count(_old_pos)) {

            // Report the position to the new layer
            Position* pointerPos = _layers[_layer_idx - 1]->getPointerPos(_old_pos);
            newLayer.updatePos(_pos, pointerPos);

            // Update layer and position 
            newLayer[_pos].setPos(_layer_idx, _pos);

            if (_pos == 0) {
                propagateInitialState();
            } else {
                // Add the effects of the left position
                Position& leftPos = newLayer[_pos - 1];

                if (left_pos_is_developed) {
                    // Left posititon has updated its frame axioms, we need to update the effects
                    Position& newPos = newLayer[_pos];
                    newPos.clearFactSupports();
                    createNextPositionFromLeft(leftPos);
                } else if (!all_pos_developed) {
                    createNextPositionFromLeftSimplified(leftPos);
                }     
            }

            left_pos_is_developed = false;
            _pos++;
        } else {
            // Find the expansion size of this position
            size_t expansion_size = 1;
            
            for (const auto& method : oldLayer[_old_pos].getReductions()) {
                const Reduction& subR = _htn.getOpTable().getReduction(method);
                expansion_size = std::max(expansion_size, subR.getSubtasks().size());
            }

            // Set the max expansion size of the position
            oldLayer[_old_pos].setExpansionSize(expansion_size);

            for (int offset = 0; offset < expansion_size; offset++) {

                createNextPosition();

                incrementPosition();
            }

            num_pos_developed++;
            left_pos_is_developed = true;
            if (num_pos_developed == positionsToDevelop.size()) {
                all_pos_developed = true;
            }
        }
    }

    Log::i("Collected %i relevant facts at this layer\n", _analysis.getRelevantFacts().size());

    // Encode new layer
    Log::i("Encoding ...\n");
    bool encodeOnlyEffsAndFA = false;
    for (_old_pos = 0; _old_pos < oldLayer.size(); _old_pos++) {

        // Log::v("Layer: %d, pos: %d/%d\n", _layer_idx, _old_pos, oldLayer.size());

        if (_old_pos == 0 && !positionsToDevelop.count(_old_pos)) {
            // Encode the new relevant facts
            _enc.encodeNewRelevantsFacts(newLayer[0]);
        }

        if (positionsToDevelop.count(_old_pos)) {
            size_t newPos = oldLayer.getSuccessorPos(_old_pos);
            size_t maxOffset = oldLayer[_old_pos].getMaxExpansionSize();
            for (size_t offset = 0; offset < maxOffset; offset++) {
                _pos = newPos + offset;
                Log::v("- Position (%i,%i)\n", _layer_idx, _pos);
                _enc.encode(_layer_idx, _pos);
            }
            encodeOnlyEffsAndFA = true;

        } else if (encodeOnlyEffsAndFA) {
            // We still to have to encode the frame axioms for the current position (as it was not done in the previouses position encoded). Then we will have totally encoded the current position
            size_t newPos = oldLayer.getSuccessorPos(_old_pos);
            Log::v("- Position (%i,%i) (Only for Frame axioms)\n", _layer_idx, newPos);
            _enc.encodeOnlyEffsAndFrameAxioms(_layer_idx, newPos);
            encodeOnlyEffsAndFA = false;
        } 
        else if (_old_pos != 0) {
            // propagate all the new relevant facts at this position
            size_t _pos = oldLayer.getSuccessorPos(_old_pos);
            Log::v(" - Position (%i,%i): Propagate new relevant facts\n", _layer_idx, _pos);
            size_t newPos = oldLayer.getSuccessorPos(_old_pos);
            _enc.propagateRelevantsFacts(_layer_idx, newPos);
        }
    } 

    // Free some memory from the above layer: old pos which have been decomposed into new positions
    for (int pos : positionsToDevelop) {
        Log::v("Freeing position %d of layer %d\n", pos, _layer_idx - 1);
        oldLayer[pos].clearFullPos();    
    }
    for (int _new_pos = 0; _new_pos < newLayer.size(); _new_pos++) {
        newLayer[_new_pos].clearDecodings();
    }
    
}

void Planner::createNextPosition() {

    Position& newPos = (*_layers[_layer_idx])[_pos];
    // Useful informations for sibylsat expansion
    newPos.setAbovePos(_old_pos);
    newPos.setOriginalLayerIdx(_layer_idx);
    newPos.setOriginalPos(_pos);

    // Set up all facts that may hold at this position.
    if (_pos == 0) {
        propagateInitialState();
    } else {
        Position& left = (*_layers[_layer_idx])[_pos-1];
        createNextPositionFromLeft(left);
    }

    // Generate this new position's content based on the facts and the position above.
    if (_layer_idx > 0) {
        createNextPositionFromAbove();
    }

    // Eliminate operations which are dominated by another operation
    if (_params.isNonzero("edo")) 
        _domination_resolver.eliminateDominatedOperations(_layers[_layer_idx]->at(_pos));

    // In preparation for the upcoming position,
    // add all effects of the actions and reductions occurring HERE
    // as (initially false) facts to THIS position. 

    // Already done in create next position from left for sibylsat expansion
    if (!_use_sibylsat_expansion) { 
        initializeNextEffects();
    }
}

void Planner::createNextPositionFromAbove() {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    newPos.setPos(_layer_idx, _pos);
    int offset = _pos - (*_layers[_layer_idx-1]).getSuccessorPos(_old_pos);
    //eliminateInvalidParentsAtCurrentState(offset);
    propagateActions(offset);
    propagateReductions(offset);
    addPreconditionConstraints();

    // if (offset == 0) {
    //     Position& above = (*_layers[_layer_idx-1])[_old_pos];
    //     for (const int mutexGroup : above.getGroupMutexEncoded()) {
    //         newPos.addGroupMutexEncoded(mutexGroup);
    //     }
    // }
}

void Planner::createNextPositionFromLeft(Position& left) {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    newPos.setPos(_layer_idx, _pos);
    assert(left.getLayerIndex() == _layer_idx);
    assert(left.getPositionIndex() == _pos-1);

    // Propagate fact changes from operations from previous position
    USigSet actionsToRemove;
    const USigSet* ops[2] = {&left.getActions(), &left.getReductions()};
    bool isAction = true;
    for (const auto& set : ops) {
        for (const auto& aSig : *set) {

            bool repeatedAction = isAction && _htn.isActionRepetition(aSig._name_id);

            for (const Signature& fact : _analysis.getPossibleFactChanges(aSig)) {
                if (isAction && !addEffect(
                        repeatedAction ? aSig.renamed(_htn.getActionNameFromRepetition(aSig._name_id)) : aSig, 
                        fact, 
                        repeatedAction ? EffectMode::DIRECT_NO_QFACT : EffectMode::DIRECT)) {
                    
                    // Impossible direct effect: forbid action retroactively.
                    Log::w("Retroactively prune action %s due to impossible effect %s\n", TOSTR(aSig), TOSTR(fact));
                    actionsToRemove.insert(aSig);

                    // Also remove any virtualized actions corresponding to this action
                    USignature repSig = aSig.renamed(_htn.getRepetitionNameOfAction(aSig._name_id));
                    if (left.hasAction(repSig)) actionsToRemove.insert(repSig);
                    
                    break;
                }
                if (!isAction && !addEffect(aSig, fact, EffectMode::INDIRECT)) {
                    // Impossible indirect effect: ignore.
                }
            }
            _analysis.eraseCachedPossibleFactChanges(aSig);
        }
        isAction = false;
    }

    for (const auto& aSig : actionsToRemove) {
        _pruning.prune(aSig, _layer_idx, _pos-1);
    }
}



// Just update the analysis
void Planner::createNextPositionFromLeftSimplified(Position& left) {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    assert(left.getLayerIndex() == _layer_idx);
    assert(left.getPositionIndex() == _pos-1);

    for (const auto& [fact, opSigs] : newPos.getPosFactSupports()) _analysis.addReachableFact(fact, /*negated=*/false);
    for (const auto& [fact, opSigs] : newPos.getNegFactSupports()) _analysis.addReachableFact(fact, /*negated=*/true);
    for (const auto& [fact, opSigs] : newPos.getPosIndirectFactSupports()) _analysis.addReachableFact(fact, /*negated=*/false);
    for (const auto& [fact, opSigs] : newPos.getNegIndirectFactSupports()) _analysis.addReachableFact(fact, /*negated=*/true);
}


void Planner::addPreconditionConstraints() {
    Position& newPos = _layers[_layer_idx]->at(_pos);

    for (const auto& aSig : newPos.getActions()) {
        const Action& a = _htn.getOpTable().getAction(aSig);
        // Add preconditions of action
        bool isRepetition = _htn.isActionRepetition(aSig._name_id);
        addPreconditionsAndConstraints(aSig, a.getPreconditions(), isRepetition);
    }

    for (const auto& rSig : newPos.getReductions()) {
        // Add preconditions of reduction
        addPreconditionsAndConstraints(rSig, _htn.getOpTable().getReduction(rSig).getPreconditions(), /*isRepetition=*/false);
    }
}

void Planner::addPreconditionsAndConstraints(const USignature& op, const SigSet& preconditions, bool isRepetition) {
    Position& newPos = _layers[_layer_idx]->at(_pos);
    
    USignature constrOp = isRepetition ? USignature(_htn.getActionNameFromRepetition(op._name_id), op._args) : op;

    for (const Signature& fact : preconditions) {
        auto cOpt = addPrecondition(op, fact, !isRepetition);
        if (cOpt) newPos.addSubstitutionConstraint(constrOp, std::move(cOpt.value()));
    }
    if (!isRepetition) addQConstantTypeConstraints(op);

    if (!newPos.getSubstitutionConstraints().count(op)) return;

    // Merge substitution constraints as far as possible
    auto& constraints = newPos.getSubstitutionConstraints().at(op);
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

std::optional<SubstitutionConstraint> Planner::addPrecondition(const USignature& op, const Signature& fact, bool addQFact) {

    Position& pos = (*_layers[_layer_idx])[_pos];
    const USignature& factAbs = fact.getUnsigned();

    if (!_htn.hasQConstants(factAbs)) { 
        assert(_analysis.isReachable(fact) || Log::e("Precondition %s not reachable!\n", TOSTR(fact)));
                
        if (_analysis.isReachable(factAbs, !fact._negated)) {
            // Negated prec. is reachable: not statically resolvable
            initializeFact(pos, factAbs);
            _analysis.addRelevantFact(factAbs);
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
    
    auto eligibleArgs = _htn.getEligibleArgs(factAbs, sorts);

    auto polarity = SubstitutionConstraint::UNDECIDED;
    size_t totalSize = 1; for (auto& args : eligibleArgs) totalSize *= args.size();
    size_t sampleSize = 25;
    bool doSample = totalSize > 2*sampleSize;
    if (doSample) {
        size_t valids = 0;
        // Check out a random sample of the possible decoded objects
        for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, eligibleArgs, sampleSize)) {
            if (_analysis.isReachable(decFactAbs, fact._negated)) valids++;
        }
        polarity = valids < sampleSize/2 ? SubstitutionConstraint::ANY_VALID : SubstitutionConstraint::NO_INVALID;
        c.fixPolarity(polarity);
    }

    // For each fact decoded from the q-fact:
    for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, eligibleArgs)) {

        // Can the decoded fact occur as is?
        if (_analysis.isReachable(decFactAbs, fact._negated)) {
            if (polarity != SubstitutionConstraint::NO_INVALID)
                c.addValid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
        } else {
            // Fact cannot hold here
            if (polarity != SubstitutionConstraint::ANY_VALID)
                c.addInvalid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
            continue;
        }

        // If the fact is reachable, is it even invariant?
        if (_analysis.isInvariant(decFactAbs, fact._negated)) {
            // Yes! This precondition is trivially satisfied 
            // with above substitution restrictions
            continue;
        }

        staticallyResolvable = false;
        relevants.insert(decFactAbs);
    }

    if (!staticallyResolvable) {
        if (addQFact) pos.addQFact(factAbs);
        for (const USignature& decFactAbs : relevants) {
            // Decoded fact may be new - initialize as necessary
            initializeFact(pos, decFactAbs);
            if (addQFact) pos.addQFactDecoding(factAbs, decFactAbs, fact._negated);
            _analysis.addRelevantFact(decFactAbs);
        }
    } // else : encoding the precondition is not necessary!

    if (!doSample) c.fixPolarity();
    return std::optional<SubstitutionConstraint>(std::move(c));
}

bool Planner::addEffect(const USignature& opSig, const Signature& fact, EffectMode mode) {
    Position& pos = (*_layers[_layer_idx])[_pos];
    assert(_pos > 0);
    Position& left = (*_layers[_layer_idx])[_pos-1];
    USignature factAbs = fact.getUnsigned();
    bool isQFact = _htn.hasQConstants(factAbs);

    if (!isQFact) {

        if (_analysis.checkGroundingFacts() && !_analysis.isInGroundFacts(fact._usig, fact._negated)) {
            // No need to encode
            return true;
        }

        // Invariant fact? --> no need to encode
        if (_analysis.isInvariant(fact)) return true;

        if (mode != INDIRECT) _analysis.addRelevantFact(factAbs);

        // Depending on whether fact supports are encoded for primitive ops only,
        // add the ground fact to the op's support accordingly
        if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
            pos.addFactSupport(fact, opSig);
        } else {
            // Remember that there is some (unspecified) support for this fact
            pos.touchFactSupport(fact);
        }
        
        _analysis.addReachableFact(fact);
        return true;
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

    for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, _htn.getEligibleArgs(factAbs, sorts))) {

        if (_analysis.checkGroundingFacts() && !_analysis.isInGroundFacts(decFactAbs, fact._negated)) {
            // Preprocessing fact cannot be true
            continue;
        }  

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
        if (_analysis.isInvariant(decFactAbs, fact._negated)) {

            if (_analysis.checkGroundingFacts() && isPositiveEffOfAction && existNegativeEffWhichCanConflitWithPosEff && staticallyResolvable) {
                // Need to encode at least one positive effect or there will be only the negative effect of the action encoded
                Log::d("Eff: %c %s of %s hold trivially but must be added for correct encoding\n", fact._negated ? '-' : '+', TOSTR(decFactAbs), TOSTR(opSig));
            } else {
                continue;
            }
        }

        // Valid effect decoding
        _analysis.addReachableFact(decFactAbs, /*negated=*/fact._negated);
        if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
            pos.addIndirectFactSupport(decFactAbs, fact._negated, opSig, path);
        } else {
            pos.touchFactSupport(decFactAbs, fact._negated);
        }
        if (mode != INDIRECT) {
            if (mode == DIRECT) pos.addQFactDecoding(factAbs, decFactAbs, fact._negated);
            _analysis.addRelevantFact(decFactAbs);
        }
        staticallyResolvable = false;
    }
    // Not a single valid decoding of the effect? -> Invalid effect.
    if (!anyGood) return false;

    if (!staticallyResolvable && mode == DIRECT) pos.addQFact(factAbs);
    
    return true;
}

void Planner::propagateInitialState() {
    assert(_layer_idx > 0);
    assert(_pos == 0);

    Position& newPos = (*_layers[_layer_idx])[0];
    Position& above = (*_layers[_layer_idx-1])[0];

    _analysis.resetReachability();

    // Propagate TRUE facts
    for (const USignature& fact : above.getTrueFacts()) {
        newPos.addTrueFact(fact);
        _analysis.addInitializedFact(fact);
    }
    for (const USignature& fact : above.getFalseFacts()) {
        newPos.addFalseFact(fact);
        _analysis.addInitializedFact(fact);
    }
}

void Planner::propagateActions(size_t offset) {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    Position& above = (*_layers[_layer_idx-1])[_old_pos];

    // Check validity of actions at above position
    std::vector<USignature> actionsToPrune;
    size_t numActionsBefore = above.getActions().size();
    for (const auto& aSig : above.getActions()) {
        const Action& a = _htn.getOpTable().getAction(aSig);

        // Can the action occur here w.r.t. the current state?
        bool valid = _analysis.hasValidPreconditions(a.getPreconditions())
                && _analysis.hasValidPreconditions(a.getExtraPreconditions());

        // If not: forbid the action, i.e., its parent action
        if (!valid) {
            Log::i("Retroactively prune action %s@(%i,%i): no children at offset %i\n", TOSTR(aSig), _layer_idx-1, _old_pos, offset);
            actionsToPrune.push_back(aSig);
        }
    }

    // Prune invalid actions at above position
    for (const auto& aSig : actionsToPrune) {
        _pruning.prune(aSig, _layer_idx-1, _old_pos);
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

void Planner::propagateReductions(size_t offset) {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    Position& above = (*_layers[_layer_idx-1])[_old_pos];

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

        // Calculate all possible actions fitting the subtask.
        auto allActions = instantiateAllActionsOfTask(subtask);

        // Any reduction(s) fitting the subtask?
        for (const USignature& subRSig : instantiateAllReductionsOfTask(subtask)) {

            if (_htn.isAction(subRSig)) {
                // Actually an action, not a reduction: remember for later
                allActions.push_back(subRSig);
                continue;
            }

            const Reduction& subR = _htn.getOpTable().getReduction(subRSig);
            
            assert(_htn.isReduction(subRSig) && subRSig == subR.getSignature() && _htn.isFullyGround(subRSig));
            
            newPos.addReduction(subRSig);
            newPos.addExpansionSize(subR.getSubtasks().size());

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
    for (const auto& rSig : above.getReductions()) {
        if (!reductionsWithChildren.count(rSig)) {
            Log::i("Retroactively prune reduction %s@(%i,%i): no children at offset %i\n", 
                    TOSTR(rSig), _layer_idx-1, _old_pos, offset);
            _pruning.prune(rSig, _layer_idx-1, _old_pos);
        }
    }
}

std::vector<USignature> Planner::instantiateAllActionsOfTask(const USignature& task) {
    std::vector<USignature> result;

    if (!_htn.isAction(task)) return result;
    
    for (USignature& sig : _instantiator.getApplicableInstantiations(_htn.toAction(task._name_id, task._args))) {
        //Log::d("ADDACTION %s ?\n", TOSTR(action.getSignature()));
        Action action = _htn.toAction(sig._name_id, sig._args);

        // Rename any remaining variables in each action as unique q-constants,
        action = _htn.replaceVariablesWithQConstants(action, _analysis.getReducedArgumentDomains(action), _layer_idx, _pos);

        // Remove any contradictory ground effects that were just created
        action.removeInconsistentEffects();

        // Check validity
        if (!_htn.isFullyGround(action.getSignature())) continue;
        if (!_htn.hasConsistentlyTypedArgs(sig)) continue;
        if (!_analysis.hasValidPreconditions(action.getPreconditions())) continue;
        if (!_analysis.hasValidPreconditions(action.getExtraPreconditions())) continue;
        
        // Action is valid
        sig = action.getSignature();
        _htn.getOpTable().addAction(action);
        result.push_back(action.getSignature());
    }
    return result;
}

std::vector<USignature> Planner::instantiateAllReductionsOfTask(const USignature& task) {
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
                for (const auto& sig : instantiateAllActionsOfTask(primSig)) {
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
                auto rOpt = createValidReduction(red, task);
                if (rOpt) result.push_back(rOpt.value().getSignature());
            }
        }
    }
    return result;
}

std::optional<Reduction> Planner::createValidReduction(const USignature& sig, const USignature& task) {
    std::optional<Reduction> rOpt;

    // Rename any remaining variables in each action as new, unique q-constants 
    Reduction red = _htn.toReduction(sig._name_id, sig._args);
    auto domains = _analysis.getReducedArgumentDomains(red);
    red = _htn.replaceVariablesWithQConstants(red, domains, _layer_idx, _pos);

    // Check validity
    bool isValid = true;
    if (task._name_id >= 0 && red.getTaskSignature() != task) isValid = false;
    else if (!_htn.isFullyGround(red.getSignature())) isValid = false;
    else if (!_htn.hasConsistentlyTypedArgs(red.getSignature())) isValid = false;
    else if (!_analysis.hasValidPreconditions(red.getPreconditions())) isValid = false;
    else if (!_analysis.hasValidPreconditions(red.getExtraPreconditions())) isValid = false;

    if (isValid) {
        _htn.getOpTable().addReduction(red);
        rOpt.emplace(red);
    }
    return rOpt;
}

void Planner::initializeNextEffects() {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    
    // For each possible operation effect:
    const USigSet* ops[2] = {&newPos.getActions(), &newPos.getReductions()};
    bool isAction = true;
    for (const auto& set : ops) {
        for (const auto& aSig : *set) {
            const SigSet& pfc = _analysis.getPossibleFactChanges(aSig, FactAnalysis::FULL, isAction ? FactAnalysis::ACTION : FactAnalysis::REDUCTION);
            for (const Signature& eff : pfc) {

                if (!_htn.hasQConstants(eff._usig)) {
                    // New ground fact: set before the action may happen
                    if (_analysis.checkGroundingFacts() && !_analysis.isInGroundFacts(eff)) {
                        continue;
                    }
                    initializeFact(newPos, eff._usig); 
                } else {
                    std::vector<int> sorts = _htn.getOpSortsForCondition(eff._usig, aSig);
                    for (const USignature& decEff : _htn.decodeObjects(eff._usig, _htn.getEligibleArgs(eff._usig, sorts))) {           
                        // New ground fact: set before the action may happen
                        if (_analysis.checkGroundingFacts() && !_analysis.isInGroundFacts(decEff, eff._negated)) {
                            continue;
                        }
                        initializeFact(newPos, decEff);
                    }
                }
            }
        }
        isAction = false;
    }
}

void Planner::initializeFact(Position& newPos, const USignature& fact) {
    assert(!_htn.hasQConstants(fact));

    // Has the fact already been defined? -> Not new!
    if (_analysis.isInitialized(fact)) return;

    _analysis.addInitializedFact(fact);

    if (_analysis.isReachable(fact, /*negated=*/true)) newPos.addFalseFact(fact);
    else newPos.addTrueFact(fact);
}

void Planner::addQConstantTypeConstraints(const USignature& op) {
    // Add type constraints for q constants
    std::vector<TypeConstraint> cs = _htn.getQConstantTypeConstraints(op);
    // Add to this position's data structure
    for (const TypeConstraint& c : cs) {
        (*_layers[_layer_idx])[_pos].addQConstantTypeConstraint(op, c);
    }
}

void Planner::clearDonePositions(int offset) {

    Position* positionToClearLeft = nullptr;
    if (_pos == 0 && _layer_idx > 0) {
        positionToClearLeft = &_layers.at(_layer_idx-1)->last();
    } else if (_pos > 0) positionToClearLeft = &_layers.at(_layer_idx)->at(_pos-1);
    if (positionToClearLeft != nullptr) {
        Log::v("  Freeing some memory of (%i,%i) ...\n", positionToClearLeft->getLayerIndex(), positionToClearLeft->getPositionIndex());
        positionToClearLeft->clearAtPastPosition();
    }

    if (_layer_idx == 0 || offset > 0) return;
    
    Position* positionToClearAbove = nullptr;
    if (_old_pos == 0) {
        // Clear rightmost position of "above above" layer
        if (_layer_idx > 1) positionToClearAbove = &_layers.at(_layer_idx-2)->at(_layers.at(_layer_idx-2)->size()-1);
    } else {
        // Clear previous parent position of "above" layer
        positionToClearAbove = &_layers.at(_layer_idx-1)->at(_old_pos-1);
    }
    if (positionToClearAbove != nullptr) {
        Log::v("  Freeing most memory of (%i,%i) ...\n", positionToClearAbove->getLayerIndex(), positionToClearAbove->getPositionIndex());
        positionToClearAbove->clearAtPastLayer();
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
    _enc.printStatistics();
    Log::i("# instantiated positions: %i\n", _num_instantiated_positions);
    Log::i("# instantiated actions: %i\n", _num_instantiated_actions);
    Log::i("# instantiated reductions: %i\n", _num_instantiated_reductions);
    Log::i("# introduced pseudo-constants: %i\n", _htn.getNumberOfQConstants());
    Log::i("# retroactive prunings: %i\n", _pruning.getNumRetroactivePunings());
    Log::i("# retroactively pruned operations: %i\n", _pruning.getNumRetroactivelyPrunedOps());
    Log::i("# dominated operations: %i\n", _domination_resolver.getNumDominatedOps());
    Log::i("Number layers: %i\n", _layers.size());

    if (_params.isNonzero("mutex")) {
        Log::i("Time spend to compute mutex predicates: %i ms\n", _htn.getTimeComputingMutex());
        Log::i("Time spend to encode mutex predicates: %i ms\n", _enc.getTimeSpendOnMutexes());
    }

    if (_analysis.checkGroundingFacts()) {
        Log::i("Time spend to ground facts: %i ms\n", _analysis.getGroundingTime());
    }
}
