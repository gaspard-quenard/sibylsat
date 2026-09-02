#include <algorithm>
#include <assert.h>

#include "tree_expander.h"
#include "util/log.h"

TreeExpander::TreeExpander(Parameters& params, HtnInstance& htn)
        : _params(params),
          _htn(htn),
          _stats(Statistics::getInstance()),
          _analysis(_htn),
          _method_effects(_htn, _analysis),
          _domination_resolver(_htn),
          _use_sibylsat_expansion(_params.isNonzero("sibylsat")),
          _nonprimitive_support(_params.isNonzero("nps")),
          _optimal(_params.isNonzero("optimal")) {}

size_t TreeExpander::getNumRetroactivePrunings() const {
    return _pruning == nullptr ? 0 : _pruning->getNumRetroactivePunings();
}

size_t TreeExpander::getNumRetroactivelyPrunedOps() const {
    return _pruning == nullptr ? 0 : _pruning->getNumRetroactivelyPrunedOps();
}

void TreeExpander::incrementPosition(const Position& pos) {
    _num_instantiated_actions += pos.getActions().size();
    _num_instantiated_reductions += pos.getReductions().size();
    _num_instantiated_positions++;
}

bool TreeExpander::isPotentiallyApplicable(const HtnOp& op) {
    return _analysis.hasValidPreconditions(op.getPreconditions()) &&
           _analysis.hasValidPreconditions(op.getExtraPreconditions()) &&
           _htn.hasSomeInstantiation(op.getSignature());
}

size_t TreeExpander::computeExpansionSize(const Position& position) const {
    size_t expansionSize = 1;
    for (const USignature& reduction : position.getReductions()) {
        expansionSize = std::max(
                expansionSize,
                _htn.getOpTable().getReduction(reduction).getSubtasks().size());
    }
    return expansionSize;
}

void TreeExpander::createInitialLeaves() {

    const int initSize = 2;
    Log::i("Creating initial leaves of size %i\n", initSize);
    _depth = 0;

    _root_position = new Position();
    _root_position->setPos(-1);

    Position* rootReductionPosition = new Position();
    rootReductionPosition->setPos(_depth);
    rootReductionPosition->setParentPosition(_root_position);
    rootReductionPosition->setLeftPosition(nullptr);

    Position* goalPosition = new Position();
    goalPosition->setParentPosition(_root_position);

    _leaf_positions = {rootReductionPosition, goalPosition};
    for (size_t i = 0; i < _leaf_positions.size(); i++) {
        _leaf_positions[i]->setFrontierIndex(i);
        _leaf_positions[i]->setLeftPosition(i > 0 ? _leaf_positions[i - 1] : nullptr);
        _leaf_positions[i]->setFreshInCurrentLayer(true);
    }

    /***** DEPTH 0, POSITION 0 ******/

    const Reduction& initReduction = _htn.getInitReduction();
    if (isPotentiallyApplicable(initReduction)) {
        USignature rSig = initReduction.getSignature();
        auto rOpt = createValidReduction(*rootReductionPosition, rSig, USignature());
        if (rOpt) {
            auto& r = rOpt.value();
            USignature sig = r.getSignature();
            rootReductionPosition->addReduction(sig);
        }
    }
    addPreconditionConstraints(*rootReductionPosition);

    incrementPosition(*rootReductionPosition);
    computeOutgoingEffects(*rootReductionPosition);

    /***** DEPTH 0, POSITION 1 ******/

    createNextPosition(*goalPosition, /*parent=*/nullptr, rootReductionPosition);

    Action goalAction = _htn.getGoalAction();
    USignature goalSig = goalAction.getSignature();
    goalPosition->addAction(goalSig);
    addPreconditionConstraints(*goalPosition);
}

void TreeExpander::printStatistics() const {
    Log::i("# number of depths: %zu\n", _depth + 1);
    Log::i("# instantiated positions: %i\n", _num_instantiated_positions);
    Log::i("# instantiated actions: %i\n", _num_instantiated_actions);
    Log::i("# instantiated reductions: %i\n", _num_instantiated_reductions);
    Log::i("# introduced pseudo-constants: %i\n", _htn.getNumberOfQConstants());
    Log::i("# retroactive prunings: %i\n", getNumRetroactivePrunings());
    Log::i("# retroactively pruned operations: %i\n", getNumRetroactivelyPrunedOps());
    Log::i("# dominated operations: %i\n", _domination_resolver.getNumDominatedOps());
}

void TreeExpander::expandLeaves(const FlatHashSet<Position*>& leavesToExpand) {
    std::vector<Position*> currentLeaves = std::move(_leaf_positions);

    std::vector<size_t> expansionSizes(currentLeaves.size(), /*init_val=*/1);
    size_t nextLeafCount = 0;
    for (size_t leafIndex = 0; leafIndex < currentLeaves.size(); leafIndex++) {
        if (leavesToExpand.count(currentLeaves[leafIndex])) {
            expansionSizes[leafIndex] = computeExpansionSize(*currentLeaves[leafIndex]);
        }
        nextLeafCount += expansionSizes[leafIndex];
    }

    _depth++;
    _leaf_positions.reserve(nextLeafCount);
    Log::i("New leaf count: %zu\n", nextLeafCount);

    // All leaves of the new frontier start as "not fresh"; expandLeaf marks
    // newly created positions as fresh so the encoding can tell them apart.
    for (Position* leaf : currentLeaves) {
        leaf->setFreshInCurrentLayer(false);
    }

    _stats.beginTiming(TimingStage::EXPANSION);
    _analysis.resetReachability();

    // Leaves before _expansion_start_index were already solved in a previous SAT call and
    // are carried into the new layer unchanged.
    const size_t carriedPrefixSize = _expansion_start_index;
    if (carriedPrefixSize > 0) {
        Log::i("Carrying %zu already-solved leaf positions into the new layer\n", carriedPrefixSize);
        for (size_t leafIndex = 0; leafIndex < carriedPrefixSize; leafIndex++) {
            carryLeaf(*currentLeaves[leafIndex]);
        }
    }

    Log::i("Instantiating ...\n");

    for (size_t leafIndex = carriedPrefixSize; leafIndex < currentLeaves.size(); leafIndex++)  {
        Position* currentLeaf = currentLeaves[leafIndex];
        if (leavesToExpand.count(currentLeaf)) {
            expandLeaf(*currentLeaf, expansionSizes[leafIndex]);
        } else {
            carryLeaf(*currentLeaf);
        }
    }

    // The ordering of the new frontier defines each leaf's frontier index.
    // Keep carried leaves' previous-layer left neighbour until encoding is
    // complete: it is needed as leftOfAbove by incremental frame axioms.
    for (size_t i = 0; i < _leaf_positions.size(); i++) {
        _leaf_positions[i]->setFrontierIndex(i);
    }

    _stats.endTiming(TimingStage::EXPANSION);
}

void TreeExpander::expandLeaf(Position& parent, size_t expansionSize) {
    for (size_t childIndex = 0; childIndex < expansionSize; childIndex++) {
        Position* child = new Position();
        child->setFreshInCurrentLayer(true);
        Position* left = _leaf_positions.empty() ? nullptr : _leaf_positions.back();
        _leaf_positions.push_back(child);
        createNextPosition(*child, &parent, left);

        Log::v("  Instantiation done. (r=%i a=%i qf=%i)\n",
                child->getReductions().size(),
                child->getActions().size(),
                child->getQFacts().size());

        incrementPosition(*child);
        computeOutgoingEffects(*child);
    }
}

void TreeExpander::carryLeaf(Position& leaf) {
    _leaf_positions.push_back(&leaf);
    applyOutgoingEffects(leaf);
}

void TreeExpander::createNextPosition(Position& newPos, Position* parent, Position* left) {
    newPos.setPos(_depth);
    if (parent != nullptr) {
        newPos.setParentPosition(parent);
    }
    newPos.setLeftPosition(left);
    newPos.getOutgoingEffects().reset(_htn.getNumPositiveGroundFacts());

    if (parent != nullptr) {
        createNextPositionFromParent(newPos, *parent);
    }

    if (_params.isNonzero("edo")) {
        _domination_resolver.eliminateDominatedOperations(newPos);
    }

}

void TreeExpander::createNextPositionFromParent(Position& newPos, Position& parent) {
    propagateActions(newPos, parent);
    propagateReductions(newPos, parent);
    addPreconditionConstraints(newPos);
}

void TreeExpander::computeOutgoingEffects(Position& position) {
    OutgoingEffects& effects = position.getOutgoingEffects();
    effects.reset(_htn.getNumPositiveGroundFacts());

    USigSet operationsToRemove;
    const USigSet* ops[2] = {&position.getActions(), &position.getReductions()};
    bool isAction = true;
    for (const auto& set : ops) {
        for (const auto& aSig : *set) {

            bool repeatedAction = isAction && _htn.isActionRepetition(aSig._name_id);

            BitVec groundEffPos = _method_effects.getGroundEffects(aSig, /*negated=*/false);
            BitVec groundEffNeg = _method_effects.getGroundEffects(aSig, /*negated=*/true);
            const SigSet instantiatedEffects = _method_effects.instantiateEffects(aSig);

            addGroundEffect(effects, aSig, groundEffPos, /*negated=*/false, isAction ? EffectMode::DIRECT : EffectMode::INDIRECT);
            addGroundEffect(effects, aSig, groundEffNeg, /*negated=*/true, isAction ? EffectMode::DIRECT : EffectMode::INDIRECT);

            for (const Signature& effect : instantiatedEffects) {
                if (isAction && !addPseudoGroundEffect(
                        effects,
                        position,
                        repeatedAction ? aSig.renamed(_htn.getActionNameFromRepetition(aSig._name_id)) : aSig, 
                        effect,
                        repeatedAction ? EffectMode::DIRECT_NO_QFACT : EffectMode::DIRECT)) {
                    
                    Log::w("3_ Retroactively prune action %s due to impossible effect %s\n", TOSTR(aSig), TOSTR(effect));
                    operationsToRemove.insert(aSig);
                    break;
                }
                if (!isAction) {
                    addPseudoGroundEffect(effects, position, aSig, effect, EffectMode::INDIRECT);
                }
            }

        }
        isAction = false;
    }

    pruneImpossibleOperations(position, operationsToRemove);
}

void TreeExpander::pruneImpossibleOperations(Position& position, const USigSet& operationsToRemove) {
    for (const auto& aSig : operationsToRemove) {
        assert(_pruning != nullptr);
        _pruning->prune(aSig, position);
    }
}

void TreeExpander::applyOutgoingEffects(const Position& position) {
    const OutgoingEffects& effects = position.getOutgoingEffects();
    _analysis.addMultipleReachableFacts(effects.getFactChanges(/*negated=*/false), /*negated=*/false);
    _analysis.addMultipleReachableFacts(effects.getFactChanges(/*negated=*/true), /*negated=*/true);
}

void TreeExpander::addPreconditionConstraints(Position& pos) {
    for (const auto& aSig : pos.getActions()) {
        const Action& a = _htn.getOpTable().getAction(aSig);
        bool isRepetition = _htn.isActionRepetition(aSig._name_id);
        addPreconditionsAndConstraints(pos, aSig, a.getPreconditions(), isRepetition);
    }
    for (const auto& rSig : pos.getReductions()) {
        addPreconditionsAndConstraints(pos, rSig, _htn.getOpTable().getReduction(rSig).getPreconditions(), /*isRepetition=*/false);
    }
}

void TreeExpander::addPreconditionsAndConstraints(Position& pos, const USignature& op, const SigSet& preconditions, bool isRepetition) {
    USignature constrOp = isRepetition ? USignature(_htn.getActionNameFromRepetition(op._name_id), op._args) : op;

    for (const Signature& fact : preconditions) {
        auto cOpt = addPrecondition(pos, op, fact, !isRepetition);
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

std::optional<SubstitutionConstraint> TreeExpander::addPrecondition(Position& pos, const USignature& op, const Signature& fact, bool addQFact) {

    const USignature& factAbs = fact.getUnsigned();

    if (!_htn.hasQConstants(factAbs)) {
        
         if (_htn.isEqualityPredicate(factAbs._name_id)) {
            bool equality_is_correct = fact._negated ? factAbs._args[0] != factAbs._args[1] : factAbs._args[0] == factAbs._args[1];
            assert(equality_is_correct || Log::e("Precondition %s not reachable!\n", TOSTR(fact)));
            if (equality_is_correct && !fact._negated) {
                int predId = _htn.getGroundFactId(factAbs, fact._negated);
                _analysis.addRelevantFact(predId);
            }
            return std::optional<SubstitutionConstraint>();
         }

        int predId = _htn.getGroundFactId(factAbs, fact._negated);
        if (predId < 0) {
            Log::e("Precondition %s not reachable!\n", TOSTR(fact));
            return std::optional<SubstitutionConstraint>();
        }
        assert(_analysis.isReachable(predId, fact._negated) || Log::e("Precondition %s not reachable!\n", TOSTR(fact)));

        if (_analysis.isReachable(predId, !fact._negated)) {
            _analysis.addRelevantFact(predId);
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
        BitVec result = _htn.getMatchingGroundFactIds(factAbs, /*negated=*/false, sorts);
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

            if (predId >=0 && _analysis.isReachable(predId, fact._negated)) valids++;
        }
        polarity = valids < sampleSize/2 ? SubstitutionConstraint::ANY_VALID : SubstitutionConstraint::NO_INVALID;
        c.fixPolarity(polarity);
    }

    for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, eligibleArgs)) {
        int predId = _htn.getGroundFactId(decFactAbs, fact._negated);

        if (predId >= 0 && _analysis.isReachable(predId, fact._negated)) {
            if (polarity != SubstitutionConstraint::NO_INVALID) {
                c.addValid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
            }
        } else {
            if (polarity != SubstitutionConstraint::ANY_VALID) {
                c.addInvalid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
            }
            continue;
        }

        if (_analysis.isInvariant(predId, fact._negated)) {
            continue;
        }

        staticallyResolvable = false;
        relevantsPredIds.insert(predId);
    }

    if (!staticallyResolvable) {
        if (addQFact) pos.addQFact(factAbs);
        for (const int& predId : relevantsPredIds) {
            const USignature& decFactAbs = _htn.getGroundPositiveFact(predId);
            if (addQFact) pos.addQFactDecoding(factAbs, decFactAbs, fact._negated);
            _analysis.addRelevantFact(predId);
        }
    }
    if (!doSample) c.fixPolarity();
    return std::optional<SubstitutionConstraint>(std::move(c));
}


void TreeExpander::addGroundEffect(OutgoingEffects& outgoing, const USignature& opSig, BitVec effects, bool negated, EffectMode mode)
{
    if (effects.count() == 0) return;

    _analysis.removeInvariantGroundFacts(effects, negated);
    if (mode != INDIRECT) {
        _analysis.addMultipleRelevantFacts(effects);
    }

    outgoing.addFactChanges(effects, negated);
    _analysis.addMultipleReachableFacts(effects, negated);

    for (int predId: effects) {
        if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
            outgoing.addSupport(predId, negated, opSig);
        } else {
            outgoing.touchSupport(predId, negated);
        }
    }   
}


bool TreeExpander::addGroundEffect(OutgoingEffects& outgoing, const USignature& opSig, int predId, bool negated, EffectMode mode) {
    if (_analysis.isInvariant(predId, negated)) return true;

    if (mode != INDIRECT) {
        _analysis.addRelevantFact(predId);
    }

    if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
        outgoing.addSupport(predId, negated, opSig);
    } else {
        outgoing.touchSupport(predId, negated);
    }
    outgoing.addFactChange(predId, negated);
    
    _analysis.addReachableFact(predId, negated);
    return true;
}


bool TreeExpander::addPseudoGroundEffect(
        OutgoingEffects& outgoing,
        Position& position,
        const USignature& opSig,
        const Signature& fact,
        EffectMode mode) {
    USignature factAbs = fact.getUnsigned();
    bool isQFact = _htn.hasQConstants(factAbs);

    if (!isQFact) {
        int predId = _htn.getGroundFactId(factAbs, fact._negated);
        if (predId == -1) return false;
        return addGroundEffect(outgoing, opSig, predId, fact._negated, mode);
    }

    std::vector<int> sorts = _htn.getOpSortsForCondition(factAbs, opSig);
    std::vector<int> sortedArgIndices = SubstitutionConstraint::getSortedSubstitutedArgIndices(_htn, factAbs._args, sorts);
    const bool isConstrained = position.getSubstitutionConstraints().count(opSig);
    
    std::vector<int> involvedQConsts(sortedArgIndices.size());
    for (size_t i = 0; i < sortedArgIndices.size(); i++) involvedQConsts[i] = factAbs._args[sortedArgIndices[i]];
    std::vector<SubstitutionConstraint*> fittingConstrs, otherConstrs;
    if (isConstrained) {
        for (auto& c : position.getSubstitutionConstraints().at(opSig)) {
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

    BitVec result = _htn.getMatchingGroundFactIds(factAbs, fact._negated, sorts);
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
        if (_analysis.isInvariant(predId, fact._negated)) {

            if (isPositiveEffOfAction && existNegativeEffWhichCanConflitWithPosEff && staticallyResolvable) {
                Log::d("Eff: %c %s of %s hold trivially but must be added for correct encoding\n", fact._negated ? '-' : '+', TOSTR(decFactAbs), TOSTR(opSig));
            } else {
                continue;
            }
        }

        _analysis.addReachableFact(predId, /*negated=*/fact._negated);
        if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
            outgoing.addIndirectSupport(predId, fact._negated, opSig, path);
        } else {
            outgoing.touchSupport(predId, fact._negated);
        }
        outgoing.addFactChange(predId, fact._negated);
        if (mode != INDIRECT) {
            if (mode == DIRECT) outgoing.addQFactDecoding(factAbs, decFactAbs, fact._negated);
            _analysis.addRelevantFact(predId);
        }
        staticallyResolvable = false;
    }
    if (!anyGood) return false;

    if (!staticallyResolvable && mode == DIRECT) outgoing.addQFact(factAbs);
    
    return true;
}

void TreeExpander::propagateActions(Position& newPos, Position& parent) {
    size_t offset = newPos.getOffset();
    std::vector<USignature> actionsToPrune;
    size_t numActionsBefore = parent.getActions().size();
    for (const auto& aSig : parent.getActions()) {
        const Action& a = _htn.getOpTable().getAction(aSig);

        bool valid = _analysis.hasValidPreconditions(a.getPreconditions())
                && _analysis.hasValidPreconditions(a.getExtraPreconditions());

        if (!valid) {
            Log::i("Retroactively prune action %s@(%i,%i): no children at offset %i\n",
                TOSTR(aSig), parent.getLayerIndex(), parent.getPositionIndex(), offset);
            actionsToPrune.push_back(aSig);
        }
    }

    for (const auto& aSig : actionsToPrune) {
        assert(_pruning != nullptr);
        _pruning->prune(aSig, parent);
    }
    assert(parent.getActions().size() == numActionsBefore - actionsToPrune.size()
        || Log::e("%i != %i-%i\n", parent.getActions().size(), numActionsBefore, actionsToPrune.size()));

    for (const auto& aSig : parent.getActions()) {
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

void TreeExpander::propagateReductions(Position& newPos, Position& parent) {
    size_t offset = newPos.getOffset();
    NodeHashMap<USignature, USigSet, USignatureHasher> subtaskToParents;
    NodeHashSet<USignature, USignatureHasher> reductionsWithChildren;

    for (const auto& rSig : parent.getReductions()) {

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

            if (_optimal) {
                assert(_tdg != nullptr);
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
    for (const auto& rSig : parent.getReductions()) {
        if (!reductionsWithChildren.count(rSig)) {
            reductionsWithNoChildren.push_back(rSig);
        }
    }

    for (const auto& rSig : reductionsWithNoChildren) {
        Log::i("Retroactively prune reduction %s@(%i,%i): no children at offset %i\n", 
                    TOSTR(rSig), parent.getLayerIndex(), parent.getPositionIndex(), offset);
        assert(_pruning != nullptr);
        _pruning->prune(rSig, parent);
    }
}

std::vector<USignature> TreeExpander::instantiateAllActionsOfTask(Position& pos, const USignature& task) {
    std::vector<USignature> result;

    if (!_htn.isAction(task)) return result;

    Action action = _htn.toAction(task._name_id, task._args);
    if (!isPotentiallyApplicable(action)) return result;

    const USignature originalSig = action.getSignature();
    action = _htn.replaceVariablesWithQConstants(
        action,
        _analysis.getReducedArgumentDomains(action),
        pos.getLayerIndex(),
        pos.getPositionIndex());

    action.removeInconsistentEffects();

    if (!_htn.isFullyGround(action.getSignature())) return result;
    if (!_htn.hasConsistentlyTypedArgs(originalSig)) return result;
    if (!_analysis.hasValidPreconditions(action.getPreconditions())) {
        return result;
    }
    if (!_analysis.hasValidPreconditions(action.getExtraPreconditions())) {
        return result;
    }

    _htn.getOpTable().addAction(action);
    result.push_back(action.getSignature());
    return result;
}

std::vector<USignature> TreeExpander::instantiateAllReductionsOfTask(Position& pos, const USignature& task) {
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
            if (!isPotentiallyApplicable(rSub)) continue;

            auto rOpt = createValidReduction(pos, rSub.getSignature(), task);
            if (rOpt) result.push_back(rOpt.value().getSignature());
        }
    }
    return result;
}

std::optional<Reduction> TreeExpander::createValidReduction(Position& pos, const USignature& sig, const USignature& task) {
    std::optional<Reduction> rOpt;

    Reduction red = _htn.toReduction(sig._name_id, sig._args);
    auto domains = _analysis.getReducedArgumentDomains(red);
    red = _htn.replaceVariablesWithQConstants(red, domains, pos.getLayerIndex(), pos.getPositionIndex());

    bool isValid = true;
    if (task._name_id >= 0 && red.getTaskSignature() != task) isValid = false;
    else if (!_htn.isFullyGround(red.getSignature())) isValid = false;
    else if (!_htn.hasConsistentlyTypedArgs(red.getSignature())) isValid = false;
    else if (!_analysis.hasValidPreconditions(red.getPreconditions())) {
        isValid = false;
    }
    else if (!_analysis.hasValidPreconditions(red.getExtraPreconditions())) {
        isValid = false;
    }

    if (isValid) {
        _htn.getOpTable().addReduction(red);
        rOpt.emplace(red);
    }
    return rOpt;
}

void TreeExpander::addQConstantTypeConstraints(Position& pos, const USignature& op) {
    std::vector<TypeConstraint> cs = _htn.getQConstantTypeConstraints(op);
    for (const TypeConstraint& c : cs) {
        pos.addQConstantTypeConstraint(op, c);
    }
}
