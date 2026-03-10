#include <assert.h>

#include "planner.h"
#include "util/log.h"

void Planner::incrementPosition(const Position& pos) {
    _num_instantiated_actions += pos.getActions().size();
    _num_instantiated_reductions += pos.getReductions().size();
    _num_instantiated_positions++;
}

void Planner::refreshLeafMetadata() {
    for (size_t pos = 0; pos < _leaf_positions.size(); pos++) {
        _leaf_positions[pos]->setPos(_depth, pos);
    }
}

void Planner::refreshLeafLeftPositions() {
    for (size_t pos = 0; pos < _leaf_positions.size(); pos++) {
        _leaf_positions[pos]->setLeftPosition(pos > 0 ? _leaf_positions[pos - 1] : nullptr);
    }
}

void Planner::createInitialLeaves() {

    const int initSize = 2;
    Log::i("Creating initial leaves of size %i\n", initSize);
    _depth = 0;

    _root_position = new Position();
    _root_position->setPos(-1, 0);

    Position* rootReductionPosition = new Position();
    rootReductionPosition->setParentPosition(_root_position);
    rootReductionPosition->setLeftPosition(nullptr);
    Position* goalPosition = new Position();
    goalPosition->setParentPosition(_root_position);
    goalPosition->setLeftPosition(rootReductionPosition);

    _leaf_positions = {rootReductionPosition, goalPosition};
    refreshLeafMetadata();

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

    createNextPosition(*goalPosition, /*parent=*/nullptr, rootReductionPosition);

    Action goalAction = _htn.getGoalAction();
    USignature goalSig = goalAction.getSignature();
    goalPosition->addAction(goalSig);
    goalPosition->addAxiomaticOp(goalSig);
    addPreconditionConstraints(*goalPosition);
    goalPosition->setPos(_depth, 1);

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
    size_t nextPos = 0;
    _leaf_positions.clear();
    _leaf_positions.reserve(nextLeafCount);
    Log::i("New leaf count: %zu\n", nextLeafCount);

    Log::i("Instantiating ...\n");
    _stats.beginTiming(TimingStage::EXPANSION);
    for (size_t oldPos = 0; oldPos < currentLeaves.size(); oldPos++) {
        Position& above = *currentLeaves[oldPos];
        size_t maxOffset = above.getMaxExpansionSize();

        for (size_t offset = 0; offset < maxOffset; offset++) {
            Position* current = new Position();
            current->setParentPosition(&above);
            _leaf_positions.push_back(current);
            current->setPos(_depth, nextPos);
            Position* left = nextPos > 0 ? _leaf_positions[nextPos - 1] : nullptr;
            current->setLeftPosition(left);
            createNextPosition(*current, &above, left);
            Log::v("  Instantiation done. (r=%i a=%i qf=%i supp=%i)\n",
                    current->getReductions().size(),
                    current->getActions().size(),
                    current->getQFacts().size(),
                    current->getPosFactSupportsId().size() + current->getNegFactSupportsId().size());
            if (nextPos > 0) {
                _leaf_positions[nextPos - 1]->clearAfterInstantiation();
            }

            incrementPosition(*current);
            nextPos++;
            checkTermination();
        }
    }
    if (nextPos > 0) {
        _leaf_positions[nextPos - 1]->clearAfterInstantiation();
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
    refreshLeafLeftPositions();
}

void Planner::expandSelectedLeaves(const FlatHashSet<int>& positionsToDevelop) {
    enum class LeafEncodingAction { NONE, FULL, NEW_RELEVANTS, EFFECTS_AND_FRAME, PROPAGATE_RELEVANTS };

    std::vector<Position*> currentLeaves = _leaf_positions;

    _stats.beginTiming(TimingStage::EXPANSION);

    size_t nextLeafCount = currentLeaves.size();
    for (int pos: positionsToDevelop) {
        Position& oldPos = *currentLeaves[pos];
        nextLeafCount += oldPos.getMaxExpansionSize() - 1;
    }
    std::vector<LeafEncodingAction> encodingActions;
    encodingActions.reserve(nextLeafCount);

    _depth++;
    size_t nextPos = 0;
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

            for (int oldPos = 0; oldPos < num_position_already_done; oldPos++) {
                Position* carriedLeaf = currentLeaves[oldPos];
                carriedLeaf->setPos(_depth, nextPos);
                _leaf_positions.push_back(carriedLeaf);
                encodingActions.push_back(LeafEncodingAction::NONE);
                nextPos++;
            }
        }
        Log::i("Done !\n");
    }

    size_t initPosExpanding = _separate_tasks && _separate_tasks_scheduler->addTasksAsClauses() ? num_position_already_done : 0;
    size_t initPosEncoding = _separate_tasks && _separate_tasks_scheduler->addTasksAsClauses() ? num_position_already_done : 0;
    bool needsEffectsAndFrame = false;

    Log::i("Instantiating ...\n");

    for (size_t oldPos = initPosExpanding; oldPos < currentLeaves.size(); oldPos++)  {

        if (!positionsToDevelop.count(oldPos)) {

            Position* newPosPtr = currentLeaves[oldPos];
            newPosPtr->setPos(_depth, nextPos);
            _leaf_positions.push_back(newPosPtr);
            Position& newPos = *newPosPtr;

            if (nextPos == 0) {
                propagateInitialState(newPos, *currentLeaves[0]);
            } else if (_separate_tasks_scheduler
                && _depth > 0
                && nextPos == (size_t) _separate_tasks_scheduler->getPositionsDone(currentLeaves.size())
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
                Position& leftPos = *_leaf_positions[nextPos - 1];

                if (left_pos_is_developed) {
                    newPos.clearFactSupportsId();
                    createNextPositionFromLeft(newPos, leftPos);
                } else if (!all_pos_developed) {
                    createNextPositionFromLeftSimplified(newPos);
                }
            }

            left_pos_is_developed = false;
            encodingActions.push_back(
                oldPos == initPosEncoding ? LeafEncodingAction::NEW_RELEVANTS
                : needsEffectsAndFrame ? LeafEncodingAction::EFFECTS_AND_FRAME
                : LeafEncodingAction::PROPAGATE_RELEVANTS);
            needsEffectsAndFrame = false;
            nextPos++;
        } else {
            size_t expansion_size = 1;
            for (const auto& method : currentLeaves[oldPos]->getReductions()) {
                const Reduction& subR = _htn.getOpTable().getReduction(method);
                expansion_size = std::max(expansion_size, subR.getSubtasks().size());
            }

            currentLeaves[oldPos]->setExpansionSize(expansion_size);

            for (size_t offset = 0; offset < expansion_size; offset++) {
                Position* current = new Position();
                current->setParentPosition(currentLeaves[oldPos]);
                _leaf_positions.push_back(current);
                current->setPos(_depth, nextPos);
                Position* left = nextPos > 0 ? _leaf_positions[nextPos - 1] : nullptr;
                current->setLeftPosition(left);
                createNextPosition(*current, currentLeaves[oldPos], left);
                incrementPosition(*current);
                encodingActions.push_back(LeafEncodingAction::FULL);
                nextPos++;
            }

            num_pos_developed++;
            left_pos_is_developed = true;
            needsEffectsAndFrame = true;
            if (num_pos_developed == positionsToDevelop.size()) {
                all_pos_developed = true;
            }
        }
    }

    _stats.endTiming(TimingStage::EXPANSION);

    Log::i("Collected %i relevant facts at this depth\n", _analysis.getRelevantFactsBitVec().count());
    Log::i("New leaf count: %zu (%zu)\n", _leaf_positions.size(), nextPos);

    Log::i("Encoding ...\n");
    _stats.beginTiming(TimingStage::ENCODING);
    for (size_t pos = 0; pos < _leaf_positions.size(); pos++) {
        switch (encodingActions[pos]) {
        case LeafEncodingAction::NONE:
            break;
        case LeafEncodingAction::FULL:
            _enc.encode(*_leaf_positions[pos]);
            break;
        case LeafEncodingAction::NEW_RELEVANTS:
            _enc.encodeNewRelevantsFacts(*_leaf_positions[pos]);
            break;
        case LeafEncodingAction::EFFECTS_AND_FRAME:
            _enc.encodeOnlyEffsAndFrameAxioms(*_leaf_positions[pos]);
            break;
        case LeafEncodingAction::PROPAGATE_RELEVANTS:
            _enc.propagateRelevantsFacts(*_leaf_positions[pos]);
            break;
        }
    }
    _stats.endTiming(TimingStage::ENCODING);
    refreshLeafLeftPositions();

    for (int pos : positionsToDevelop) {
        Log::v("Freeing position %d of depth %d\n", pos, _depth - 1);
        currentLeaves[pos]->clearFullPos();
    }
    for (Position* leaf : _leaf_positions) {
        leaf->clearDecodings();
    }
}

void Planner::createNextPosition(Position& newPos, Position* parent, Position* left) {
    size_t pos = newPos.getPositionIndex();

    newPos.setPos(_depth, pos);
    if (parent != nullptr) {
        newPos.setParentPosition(parent);
    }
    newPos.initFactChangesBitVec(_htn.getNumPositiveGroundFacts());

    if (pos == 0) {
        assert(parent != nullptr || _depth == 0);
        if (_depth > 0) {
            propagateInitialState(newPos, *parent);
        }
    }  
    else if (_separate_tasks_scheduler 
                && _depth > 0
                && pos == (size_t) _separate_tasks_scheduler->getPositionsDone(_leaf_positions.size())
                && _separate_tasks_scheduler->addTasksAsClauses()) {
                    for (int i = 0; i < _htn.getNumPositiveGroundFacts(); i++) {
                        const USignature& sig = _htn.getGroundPositiveFact(i);
                        if (_analysis.isReachableBitVec(i, /*negated=*/false)) {
                            newPos.addTrueFact(sig);
                        } else {
                            newPos.addFalseFact(sig);
                        }
                    }
            }
    else if (left != nullptr) {
        createNextPositionFromLeft(newPos, *left);
    }

    if (parent != nullptr) {
        createNextPositionFromAbove(newPos, *parent);
    }

    if (_params.isNonzero("edo")) {
        _domination_resolver.eliminateDominatedOperations(newPos);
    }

    if (!_use_sibylsat_expansion) { 
        _stats.beginTiming(TimingStage::EXPANSION_INITIALIZED_NEXT_EFFECTS);
        initializeNextEffectsBitVec(newPos);
        _stats.endTiming(TimingStage::EXPANSION_INITIALIZED_NEXT_EFFECTS);
    }
}

void Planner::createNextPositionFromAbove(Position& newPos, Position& above) {
    propagateActions(newPos, above);
    propagateReductions(newPos, above);
    addPreconditionConstraints(newPos);
}

void Planner::createNextPositionFromLeft(Position& newPos, Position& left) {
    assert(left.getLayerIndex() == newPos.getLayerIndex());
    assert(left.getPositionIndex()+1 == newPos.getPositionIndex());

    USigSet actionsToRemove;
    const USigSet* ops[2] = {&left.getActions(), &left.getReductions()};
    bool isAction = true;
    for (const auto& set : ops) {
        for (const auto& aSig : *set) {

            bool repeatedAction = isAction && _htn.isActionRepetition(aSig._name_id);

            BitVec groundEffPos = _analysis.getPossibleGroundFactChanges(aSig, /*negated=*/false);
            BitVec groundEffNeg = _analysis.getPossibleGroundFactChanges(aSig, /*negated=*/true);
            const SigSet& pseudoEff = _analysis.getPossiblePseudoGroundFactChanges(aSig);

            addGroundEffectBitVec(newPos, aSig, groundEffPos, /*negated=*/false, isAction ? EffectMode::DIRECT : EffectMode::INDIRECT);
            addGroundEffectBitVec(newPos, aSig, groundEffNeg, /*negated=*/true, isAction ? EffectMode::DIRECT : EffectMode::INDIRECT);

            for (const Signature& pseudoPred : pseudoEff) {
                if (isAction && !addPseudoGroundEffect(
                        newPos,
                        left,
                        repeatedAction ? aSig.renamed(_htn.getActionNameFromRepetition(aSig._name_id)) : aSig, 
                        pseudoPred,
                        repeatedAction ? EffectMode::DIRECT_NO_QFACT : EffectMode::DIRECT)) {
                    
                    Log::w("3_ Retroactively prune action %s due to impossible effect %s\n", TOSTR(aSig), TOSTR(pseudoPred));
                    actionsToRemove.insert(aSig);
                    break;
                }
                if (!isAction && !addPseudoGroundEffect(newPos, left, aSig, pseudoPred, EffectMode::INDIRECT)) {
                }
            }

        }
        isAction = false;
    }

    for (const auto& aSig : actionsToRemove) {
        _pruning.prune(aSig, left);
    }
}

void Planner::createNextPositionFromLeftSimplified(Position& newPos) {
    const BitVec& pos_facts_changed = newPos.getFactChangeBitVec(/*negated=*/false);
    const BitVec& neg_facts_changed = newPos.getFactChangeBitVec(/*negated=*/true);
    _analysis.addMultipleReachableFactsBitVec(pos_facts_changed, /*negated=*/false);
    _analysis.addMultipleReachableFactsBitVec(neg_facts_changed, /*negated=*/true);
}

void Planner::addPreconditionConstraints(Position& pos) {
    for (const auto& aSig : pos.getActions()) {
        const Action& a = _htn.getOpTable().getAction(aSig);
        bool isRepetition = _htn.isActionRepetition(aSig._name_id);
        addPreconditionsAndConstraints(pos, aSig, a.getPreconditions(), isRepetition);
    }
    for (const auto& rSig : pos.getReductions()) {
        addPreconditionsAndConstraints(pos, rSig, _htn.getOpTable().getReduction(rSig).getPreconditions(), /*isRepetition=*/false);
    }
}

void Planner::addPreconditionsAndConstraints(Position& pos, const USignature& op, const SigSet& preconditions, bool isRepetition) {
    USignature constrOp = isRepetition ? USignature(_htn.getActionNameFromRepetition(op._name_id), op._args) : op;

    for (const Signature& fact : preconditions) {
        auto cOpt = addPreconditionBitVec(pos, op, fact, !isRepetition);
        if (cOpt) pos.addSubstitutionConstraint(constrOp, std::move(cOpt.value()));
    }
    if (!isRepetition) addQConstantTypeConstraints(pos, op);

    if (!pos.getSubstitutionConstraints().count(op)) return;

    auto& constraints = pos.getSubstitutionConstraints().at(op);
    for (size_t i = 0; i < constraints.size(); i++) {
        for (size_t j = i+1; j < constraints.size(); j++) {
            auto& iTree = constraints[i];
            auto& jTree = constraints[j];
            if (iTree.canMerge(jTree)) {
                iTree.merge(std::move(jTree));
                if (j+1 < constraints.size()) {
                    constraints[j] = std::move(constraints.back());
                }
                constraints.erase(constraints.begin()+constraints.size()-1);
                j--;
            }
        }
    }
}

std::optional<SubstitutionConstraint> Planner::addPreconditionBitVec(Position& pos, const USignature& op, const Signature& fact, bool addQFact) {

    const USignature& factAbs = fact.getUnsigned();

    if (!_htn.hasQConstants(factAbs)) {
        
         if (_htn.isEqualityPredicate(factAbs._name_id)) {
            bool equality_is_correct = fact._negated ? factAbs._args[0] != factAbs._args[1] : factAbs._args[0] == factAbs._args[1];
            assert(equality_is_correct || Log::e("Precondition %s not reachable!\n", TOSTR(fact)));
            if (equality_is_correct && !fact._negated) {
                int predId = _htn.getGroundFactId(factAbs, fact._negated);
                initializeFactBitVec(pos, predId);
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
            initializeFactBitVec(pos, predId);
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
    FlatHashSet<int> relevantsPredIds;
    
    auto eligibleArgs = _htn.getEligibleArgs(factAbs, sorts);

    auto polarity = SubstitutionConstraint::UNDECIDED;
    if (_htn.isEqualityPredicate(factAbs._name_id)) {
        if (!_htn.hasQConstants(factAbs)) return std::optional<SubstitutionConstraint>();

        for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, eligibleArgs)) {
            bool is_true = fact._negated ? decFactAbs._args[0] != decFactAbs._args[1] : decFactAbs._args[0] == decFactAbs._args[1];
            if (is_true) {
                if (polarity != SubstitutionConstraint::NO_INVALID) {
                    c.addValid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
                }
            } else {
                if (polarity != SubstitutionConstraint::ANY_VALID) {
                    c.addInvalid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
                }
            }
        }
        c.fixPolarity();
        return std::optional<SubstitutionConstraint>(std::move(c));
    } 
    else if (_htn.isStaticPredicate(factAbs._name_id)) {
        BitVec result = ArgIterator2::getFullInstantiation2(factAbs, /*negated=*/false, _htn, sorts);
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
        for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, eligibleArgs, sampleSize)) {
            int predId = _htn.getGroundFactId(decFactAbs, fact._negated);

            if (predId >=0 && _analysis.isReachableBitVec(predId, fact._negated)) valids++;
        }
        polarity = valids < sampleSize/2 ? SubstitutionConstraint::ANY_VALID : SubstitutionConstraint::NO_INVALID;
        c.fixPolarity(polarity);
    }

    for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, eligibleArgs)) {
        int predId = _htn.getGroundFactId(decFactAbs, fact._negated);

        if (predId >= 0 && _analysis.isReachableBitVec(predId, fact._negated)) {
            if (polarity != SubstitutionConstraint::NO_INVALID) {
                c.addValid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
            }
        } else {
            if (polarity != SubstitutionConstraint::ANY_VALID) {
                c.addInvalid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
            }
            continue;
        }

        if (_analysis.isInvariantBitVec(predId, fact._negated)) {
            continue;
        }

        staticallyResolvable = false;
        relevantsPredIds.insert(predId);
    }

    if (!staticallyResolvable) {
        if (addQFact) pos.addQFact(factAbs);
        for (const int& predId : relevantsPredIds) {
            const USignature& decFactAbs = _htn.getGroundPositiveFact(predId);
            initializeFactBitVec(pos, predId);
            if (addQFact) pos.addQFactDecoding(factAbs, decFactAbs, fact._negated);
            _analysis.addRelevantFactBitVec(predId);
        }
    }
    if (!doSample) c.fixPolarity();
    return std::optional<SubstitutionConstraint>(std::move(c));
}


void Planner::addGroundEffectBitVec(Position& pos, const USignature& opSig, BitVec effects, bool negated, EffectMode mode) 
{
    if (effects.count() == 0) return;

    _analysis.removeInvariantGroundFactsBitVec(effects, negated);
    if (mode != INDIRECT) {
        _analysis.addMultipleRelevantFactsBitVec(effects);
    }

    pos.addMultipleFactChangesBitVec(effects, negated);
    _analysis.addMultipleReachableFactsBitVec(effects, negated);

    for (int predId: effects) {
        if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
            pos.addFactSupportId(predId, negated, opSig);
        } else {
            pos.touchFactSupportId(predId, negated);
        }
    }   
}


bool Planner::addGroundEffect(Position& pos, const USignature& opSig, int predId, bool negated, EffectMode mode) {
    assert(pos.getPositionIndex() > 0);

    if (_analysis.isInvariantBitVec(predId, negated)) return true;

    if (mode != INDIRECT) {
        _analysis.addRelevantFactBitVec(predId);
    }

    if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
        pos.addFactSupportId(predId, negated, opSig);
    } else {
        pos.touchFactSupportId(predId, negated);
    }
    pos.addFactChangeBitVec(predId, negated);
    
    _analysis.addReachableFactBitVec(predId, negated);
    return true;
}


bool Planner::addPseudoGroundEffect(Position& pos, Position& left, const USignature& opSig, const Signature& fact, EffectMode mode) {
    assert(pos.getPositionIndex() > 0);
    USignature factAbs = fact.getUnsigned();
    bool isQFact = _htn.hasQConstants(factAbs);

    if (!isQFact) {
        int predId = _htn.getGroundFactId(factAbs, fact._negated);
        if (predId == -1) return false;
        return addGroundEffect(pos, opSig, predId, fact._negated, mode);
    }

    std::vector<int> sorts = _htn.getOpSortsForCondition(factAbs, opSig);
    std::vector<int> sortedArgIndices = SubstitutionConstraint::getSortedSubstitutedArgIndices(_htn, factAbs._args, sorts);
    const bool isConstrained = left.getSubstitutionConstraints().count(opSig);
    
    std::vector<int> involvedQConsts(sortedArgIndices.size());
    for (size_t i = 0; i < sortedArgIndices.size(); i++) involvedQConsts[i] = factAbs._args[sortedArgIndices[i]];
    std::vector<SubstitutionConstraint*> fittingConstrs, otherConstrs;
    if (isConstrained) {
        for (auto& c : left.getSubstitutionConstraints().at(opSig)) {
            if (c.getInvolvedQConstants() == involvedQConsts) fittingConstrs.push_back(&c);
            else if (c.getPolarity() == SubstitutionConstraint::NO_INVALID || c.involvesSupersetOf(involvedQConsts)) {
                otherConstrs.push_back(&c);
            }
        }
    }
    
    bool anyGood = false;
    bool staticallyResolvable = true;
    bool existNegativeEffWhichCanConflitWithPosEff = false;
    if (!fact._negated && (_htn.isAction(opSig) || (_use_sibylsat_expansion && mode == DIRECT))) {
        const SigSet& effects = _htn.isAction(opSig) ? _htn.getOpTable().getAction(opSig).getEffects() : _htn.getOpTable().getReduction(opSig).getEffects();
        for (const Signature& negFact : effects) {
            if (negFact._negated && negFact._usig._name_id == fact._usig._name_id) {
                existNegativeEffWhichCanConflitWithPosEff = true;
                break;
            }
        }
    }
    bool isPositiveEffOfAction = (_htn.isAction(opSig) || (_use_sibylsat_expansion && mode == DIRECT)) && !fact._negated;

    BitVec result = ArgIterator2::getFullInstantiation2(factAbs, fact._negated, _htn, sorts);
    for (int predId: result) {
        const USignature& decFactAbs = _htn.getGroundPositiveFact(predId);
        auto path = SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices);

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
        if (_analysis.isInvariantBitVec(predId, fact._negated)) {

            if (isPositiveEffOfAction && existNegativeEffWhichCanConflitWithPosEff && staticallyResolvable) {
                Log::d("Eff: %c %s of %s hold trivially but must be added for correct encoding\n", fact._negated ? '-' : '+', TOSTR(decFactAbs), TOSTR(opSig));
            } else {
                continue;
            }
        }

        _analysis.addReachableFactBitVec(predId, /*negated=*/fact._negated);
        if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
            pos.addIndirectFactSupportId(predId, fact._negated, opSig, path);
        } else {
            pos.touchFactSupportId(predId, fact._negated);
        }
        pos.addFactChangeBitVec(predId, fact._negated);
        if (mode != INDIRECT) {
            if (mode == DIRECT) pos.addQFactDecoding(factAbs, decFactAbs, fact._negated);
            _analysis.addRelevantFactBitVec(predId);
        }
        staticallyResolvable = false;
    }
    if (!anyGood) return false;

    if (!staticallyResolvable && mode == DIRECT) pos.addQFact(factAbs);
    
    return true;
}


void Planner::propagateInitialState(Position& newPos, const Position& above) {
    assert(newPos.getLayerIndex() > 0);
    assert(newPos.getPositionIndex() == 0);

    _analysis.resetReachability();

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
    std::vector<USignature> actionsToPrune;
    size_t numActionsBefore = above.getActions().size();
    for (const auto& aSig : above.getActions()) {
        const Action& a = _htn.getOpTable().getAction(aSig);

        bool valid = _analysis.hasValidPreconditionsBitVec(a.getPreconditions())
                && _analysis.hasValidPreconditionsBitVec(a.getExtraPreconditions());

        if (!valid) {
            Log::i("Retroactively prune action %s@(%i,%i): no children at offset %i\n",
                TOSTR(aSig), above.getLayerIndex(), above.getPositionIndex(), offset);
            actionsToPrune.push_back(aSig);
        }
    }

    for (const auto& aSig : actionsToPrune) {
        _pruning.prune(aSig, above);
    }
    assert(above.getActions().size() == numActionsBefore - actionsToPrune.size() 
        || Log::e("%i != %i-%i\n", above.getActions().size(), numActionsBefore, actionsToPrune.size()));

    for (const auto& aSig : above.getActions()) {
        if (offset < 1) {
            assert(_htn.isFullyGround(aSig));
            if (_params.isNonzero("aar") && !_htn.isActionRepetition(aSig._name_id)) {
                USignature vChildSig = _htn.getRepetitionOfAction(aSig);
                newPos.addAction(vChildSig);
                newPos.addExpansion(aSig, vChildSig);
            } else {
                newPos.addAction(aSig);
                newPos.addExpansion(aSig, aSig);
            }
        } else {
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

    for (const auto& rSig : above.getReductions()) {

        const Reduction r = _htn.getOpTable().getReduction(rSig);
        
        if (offset < r.getSubtasks().size()) {
            const USignature& subtask = r.getSubtasks()[offset];
            subtaskToParents[subtask].insert(rSig);
        } else {
            reductionsWithChildren.insert(rSig);
            const USignature& blankSig = _htn.getBlankActionSig();
            newPos.addAction(blankSig);
            newPos.addExpansion(rSig, blankSig);
        }
    }

    for (const auto& [subtask, parents] : subtaskToParents) {
        auto allActions = instantiateAllActionsOfTask(newPos, subtask);

        for (const USignature& subRSig : instantiateAllReductionsOfTask(newPos, subtask)) {

            if (_htn.isAction(subRSig)) {
                allActions.push_back(subRSig);
                continue;
            }

            const Reduction& subR = _htn.getOpTable().getReduction(subRSig);
            
            assert(_htn.isReduction(subRSig) && subRSig == subR.getSignature() && _htn.isFullyGround(subRSig));

            newPos.addReduction(subRSig);
            newPos.addExpansionSize(subR.getSubtasks().size());

            if (_optimal) {
                int heuristicValue = _tdg->getBestHeuristicValue(subRSig);
                Log::d("Set the heuristic value of %s to %d\n", TOSTR(subRSig), heuristicValue);
                newPos.setHeuristicValue(subRSig, heuristicValue);
            }

            for (const auto& rSig : parents) {
                reductionsWithChildren.insert(rSig);
                newPos.addExpansion(rSig, subRSig);
            }
        }

        for (const USignature& aSig : allActions) {

            assert(_htn.isFullyGround(aSig));
            newPos.addAction(aSig);

            for (const auto& rSig : parents) {
                reductionsWithChildren.insert(rSig);
                newPos.addExpansion(rSig, aSig);
            }
        }
    }

    std::vector<USignature> reductionsWithNoChildren;
    for (const auto& rSig : above.getReductions()) {
        if (!reductionsWithChildren.count(rSig)) {
            reductionsWithNoChildren.push_back(rSig);
        }
    }

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
        Action action = _htn.toAction(sig._name_id, sig._args);

        action = _htn.replaceVariablesWithQConstants(
            action,
            _analysis.getReducedArgumentDomains(action),
            pos.getLayerIndex(),
            pos.getPositionIndex());

        action.removeInconsistentEffects();

        if (!_htn.isFullyGround(action.getSignature())) continue;
        if (!_htn.hasConsistentlyTypedArgs(sig)) continue;
        if (!_analysis.hasValidPreconditionsBitVec(action.getPreconditions())) {
            continue;
        }
        if (!_analysis.hasValidPreconditionsBitVec(action.getExtraPreconditions())) {
            continue;
        }
        
        sig = action.getSignature();
        _htn.getOpTable().addAction(action);
        result.push_back(action.getSignature());
    }
    return result;
}

std::vector<USignature> Planner::instantiateAllReductionsOfTask(Position& pos, const USignature& task) {
    std::vector<USignature> result;

    if (!_htn.hasReductions(task._name_id)) return result;

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

    Reduction red = _htn.toReduction(sig._name_id, sig._args);
    auto domains = _analysis.getReducedArgumentDomains(red);
    red = _htn.replaceVariablesWithQConstants(red, domains, pos.getLayerIndex(), pos.getPositionIndex());

    bool isValid = true;
    if (task._name_id >= 0 && red.getTaskSignature() != task) isValid = false;
    else if (!_htn.isFullyGround(red.getSignature())) isValid = false;
    else if (!_htn.hasConsistentlyTypedArgs(red.getSignature())) isValid = false;
    else if (!_analysis.hasValidPreconditionsBitVec(red.getPreconditions())) {
        isValid = false;
    }
    else if (!_analysis.hasValidPreconditionsBitVec(red.getExtraPreconditions())) {
        isValid = false;
    }

    if (isValid) {
        _htn.getOpTable().addReduction(red);
        rOpt.emplace(red);
    }
    return rOpt;
}

void Planner::initializeNextEffectsBitVec(Position& newPos) {
    const USigSet* ops[2] = {&newPos.getActions(), &newPos.getReductions()};
    bool isAction = true;
    for (const auto& set : ops) {
        for (const auto& aSig : *set) {
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
                        initializeFactBitVec(newPos, predId);
                        continue;
                    }
                }
                BitVec groundEffPos = ArgIterator2::getFullInstantiation2(eff._usig, eff._negated, _htn, _htn.getOpSortsForCondition(eff._usig, aSig));
                
                for (size_t predId : groundEffPos) {
                    initializeFactBitVec(newPos, predId);
                }
            }
        }
        isAction = false;
    }
}

void Planner::initializeFactBitVec(Position& newPos, const int predId) {

    const USignature& fact = _htn.getGroundPositiveFact(predId);

    if (_analysis.isInitializedBitVec(predId)) return;

    _analysis.addInitializedFactBitVec(predId);

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
    std::vector<TypeConstraint> cs = _htn.getQConstantTypeConstraints(op);
    for (const TypeConstraint& c : cs) {
        pos.addQConstantTypeConstraint(op, c);
    }
}
