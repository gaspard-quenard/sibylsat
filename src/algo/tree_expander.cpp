#include <algorithm>
#include <cassert>

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
    return _pruning == nullptr ? 0 : _pruning->getNumRetroactivePrunings();
}

size_t TreeExpander::getNumRetroactivelyPrunedOps() const {
    return _pruning == nullptr ? 0 : _pruning->getNumRetroactivelyPrunedOps();
}

void TreeExpander::recordInstantiatedPosition(const Position& position) {
    _num_instantiated_actions += position.getActions().size();
    _num_instantiated_reductions += position.getReductions().size();
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
    constexpr size_t initialLeafCount = 2;
    Log::i("Creating initial leaves of size %zu\n", initialLeafCount);
    _expansion_iteration = 0;

    _root_position = new Position();

    Position* rootReductionPosition = new Position(_expansion_iteration, _root_position);
    Position* goalPosition = new Position(_expansion_iteration, _root_position);

    _leaf_positions = {rootReductionPosition, goalPosition};
    for (size_t i = 0; i < _leaf_positions.size(); i++) {
        _leaf_positions[i]->setFrontierIndex(i);
        _leaf_positions[i]->setLeftPosition(i > 0 ? _leaf_positions[i - 1] : nullptr);
        _leaf_positions[i]->setCreatedInLastExpansion(true);
    }

    const Reduction& initReduction = _htn.getInitReduction();
    auto initReductionSig = instantiateAndRegisterReduction(initReduction, std::nullopt, rootReductionPosition->getPositionId());
    if (initReductionSig) rootReductionPosition->addReduction(initReductionSig.value());
    preparePreconditionEncoding(*rootReductionPosition);

    recordInstantiatedPosition(*rootReductionPosition);
    computeOutgoingEffects(*rootReductionPosition);
    addOutgoingEffectsToReachability(*rootReductionPosition);

    // The artificial goal has no effects, but the encoding reads its outgoing bit vectors.
    goalPosition->getOutgoingEffects().reset(_htn.getNumPositiveGroundFacts());

    const USignature goalSig = _htn.getGoalAction().getSignature();
    goalPosition->addAction(goalSig);
    preparePreconditionEncoding(*goalPosition);
}

void TreeExpander::printStatistics() const {
    Log::i("# expansion iterations: %zu\n", _expansion_iteration + 1);
    Log::i("# instantiated positions: %zu\n", _num_instantiated_positions);
    Log::i("# instantiated actions: %zu\n", _num_instantiated_actions);
    Log::i("# instantiated reductions: %zu\n", _num_instantiated_reductions);
    Log::i("# introduced pseudo-constants: %zu\n", _htn.getNumberOfQConstants());
    Log::i("# retroactive prunings: %zu\n", getNumRetroactivePrunings());
    Log::i("# retroactively pruned operations: %zu\n", getNumRetroactivelyPrunedOps());
    Log::i("# dominated operations: %zu\n", _domination_resolver.getNumDominatedOps());
}

void TreeExpander::expandLeaves(const FlatHashSet<Position*>& leavesToExpand) {
    std::vector<Position*> currentLeaves = std::move(_leaf_positions);
    const size_t carriedPrefixSize = _active_frontier_start;
    assert(carriedPrefixSize <= currentLeaves.size());

    std::vector<size_t> expansionSizes(currentLeaves.size(), /*init_val=*/1);
    size_t nextLeafCount = carriedPrefixSize;
    for (size_t leafIndex = carriedPrefixSize; leafIndex < currentLeaves.size(); leafIndex++) {
        if (leavesToExpand.count(currentLeaves[leafIndex])) {
            expansionSizes[leafIndex] = computeExpansionSize(*currentLeaves[leafIndex]);
        }
        nextLeafCount += expansionSizes[leafIndex];
    }

    _expansion_iteration++;
    _leaf_positions.reserve(nextLeafCount);
    Log::i("New leaf count: %zu\n", nextLeafCount);

    // Positions from the previous frontier are not new in this expansion.
    for (Position* leaf : currentLeaves) {
        leaf->setCreatedInLastExpansion(false);
    }

    _stats.beginTiming(TimingStage::EXPANSION);
    _analysis.resetReachability();

    // Leaves before _active_frontier_start were already solved in a previous SAT call and
    // are carried into the new frontier unchanged.
    if (carriedPrefixSize > 0) {
        Log::i("Carrying %zu already-solved leaf positions into the new frontier\n", carriedPrefixSize);
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

    for (size_t i = 0; i < _leaf_positions.size(); i++) {
        _leaf_positions[i]->setFrontierIndex(i);
    }

    _stats.endTiming(TimingStage::EXPANSION);
}

void TreeExpander::expandLeaf(Position& parent, size_t expansionSize) {
    for (size_t childIndex = 0; childIndex < expansionSize; childIndex++) {
        Position* child = new Position(_expansion_iteration, &parent);
        child->setCreatedInLastExpansion(true);
        Position* left = _leaf_positions.empty() ? nullptr : _leaf_positions.back();
        _leaf_positions.push_back(child);
        child->setLeftPosition(left);
        populateChildFromParent(*child, parent);

        if (_params.isNonzero("edo")) {
            _domination_resolver.eliminateDominatedOperations(*child);
        }

        Log::v("  Instantiation done. (r=%zu a=%zu qf=%zu)\n",
                child->getReductions().size(),
                child->getActions().size(),
                child->getQFacts().size());

        recordInstantiatedPosition(*child);
        computeOutgoingEffects(*child);
        addOutgoingEffectsToReachability(*child);
    }
}

void TreeExpander::carryLeaf(Position& leaf) {
    _leaf_positions.push_back(&leaf);
    addOutgoingEffectsToReachability(leaf);
}

void TreeExpander::populateChildFromParent(Position& child, Position& parent) {
    assert(child.getParentPosition() == &parent);
    propagateParentActions(child, parent);
    expandParentReductions(child, parent);
    preparePreconditionEncoding(child);
}

void TreeExpander::computeOutgoingEffects(Position& position) {
    OutgoingEffects& effects = position.getOutgoingEffects();
    effects.reset(_htn.getNumPositiveGroundFacts());

    USigSet actionsToPrune;
    for (const USignature& actionSig : position.getActions()) {
        if (!addActionOutgoingEffects(effects, position, actionSig)) actionsToPrune.insert(actionSig);
    }
    for (const USignature& reductionSig : position.getReductions()) {
        addReductionOutgoingEffects(effects, position, reductionSig);
    }

    pruneImpossibleActions(position, actionsToPrune);
}

bool TreeExpander::addActionOutgoingEffects(OutgoingEffects& effects, Position& position, const USignature& actionSig) {
    const SigSet& actionEffects = _htn.getOpTable().getAction(actionSig).getEffects();

    const bool repeatedAction = _htn.isActionRepetition(actionSig._name_id);
    const USignature effectOwnerSig = repeatedAction ? actionSig.renamed(_htn.getActionNameFromRepetition(actionSig._name_id)) : actionSig;
    const EffectMode mode = repeatedAction ? EffectMode::REPEATED_ACTION_EFFECT : EffectMode::ACTION_EFFECT;
    for (const Signature& effect : actionEffects) {
        if (addInstantiatedEffect(effects, position, effectOwnerSig, effect, mode)) continue;

        Log::w("Retroactively prune action %s due to impossible effect %s\n", TOSTR(actionSig), TOSTR(effect));
        return false;
    }
    return true;
}

void TreeExpander::addReductionOutgoingEffects(OutgoingEffects& effects, Position& position, const USignature& reductionSig) {
    const BitVec& argumentIndependentPositiveEffects = _method_effects.getArgumentIndependentGroundEffects(reductionSig, /*negated=*/false);
    const BitVec& argumentIndependentNegativeEffects = _method_effects.getArgumentIndependentGroundEffects(reductionSig, /*negated=*/true);
    const SigSet argumentDependentEffects = _method_effects.instantiateArgumentDependentEffects(reductionSig);

    addGroundEffect(effects, reductionSig, argumentIndependentPositiveEffects, /*negated=*/false, EffectMode::POSSIBLE_METHOD_EFFECT);
    addGroundEffect(effects, reductionSig, argumentIndependentNegativeEffects, /*negated=*/true, EffectMode::POSSIBLE_METHOD_EFFECT);
    for (const Signature& effect : argumentDependentEffects) {
        addInstantiatedEffect(effects, position, reductionSig, effect, EffectMode::POSSIBLE_METHOD_EFFECT);
    }
}

void TreeExpander::pruneImpossibleActions(Position& position, const USigSet& actionsToPrune) {
    for (const USignature& actionSig : actionsToPrune) {
        assert(_pruning != nullptr);
        _pruning->prune(actionSig, position);
    }
}

void TreeExpander::addOutgoingEffectsToReachability(const Position& position) {
    const OutgoingEffects& effects = position.getOutgoingEffects();
    _analysis.addMultipleReachableFacts(effects.getFactChanges(/*negated=*/false), /*negated=*/false);
    _analysis.addMultipleReachableFacts(effects.getFactChanges(/*negated=*/true), /*negated=*/true);
}

void TreeExpander::preparePreconditionEncoding(Position& position) {
    for (const USignature& actionSig : position.getActions()) {
        const Action& action = _htn.getOpTable().getAction(actionSig);
        prepareOperationPreconditions(position, action, _htn.isActionRepetition(actionSig._name_id));
    }
    for (const USignature& reductionSig : position.getReductions()) {
        const Reduction& reduction = _htn.getOpTable().getReduction(reductionSig);
        prepareOperationPreconditions(position, reduction, /*isRepeatedAction=*/false);
    }
}

/**
 * Prepares the information needed to encode an operation's preconditions.
 * Ground preconditions identify dynamic facts that need SAT variables, while
 * Q-constant preconditions also contribute allowed or forbidden substitutions.
 */
void TreeExpander::prepareOperationPreconditions(Position& position, const HtnOp& operation, bool isRepeatedAction) {
    const USignature operationSig = operation.getSignature();
    // Repetition effects are decoded using the original action signature.
    const USignature constraintOwnerSig = isRepeatedAction
        ? operationSig.renamed(_htn.getActionNameFromRepetition(operationSig._name_id))
        : operationSig;

    for (const Signature& precondition : operation.getPreconditions()) {
        auto constraint = analyzePrecondition(position, operationSig, precondition, !isRepeatedAction);
        if (constraint) position.addSubstitutionConstraint(constraintOwnerSig, std::move(*constraint));
    }
    if (!isRepeatedAction) addQConstantTypeConstraints(position, operationSig);
    mergeCompatibleConstraints(position, constraintOwnerSig);
}

void TreeExpander::mergeCompatibleConstraints(Position& position, const USignature& operationSig) {
    auto constraintsIt = position.getSubstitutionConstraints().find(operationSig);
    if (constraintsIt == position.getSubstitutionConstraints().end()) return;

    auto& constraints = constraintsIt->second;
    for (size_t i = 0; i < constraints.size(); i++) {
        for (size_t j = i + 1; j < constraints.size();) {
            if (!constraints[i].canMerge(constraints[j])) {
                j++;
                continue;
            }
            constraints[i].merge(std::move(constraints[j]));
            if (j + 1 < constraints.size()) constraints[j] = std::move(constraints.back());
            constraints.pop_back();
        }
    }
}

std::optional<SubstitutionConstraint> TreeExpander::analyzePrecondition(Position& position, const USignature& operationSig, const Signature& precondition, bool registerDynamicQFact) {
    const USignature& unsignedPrecondition = precondition.getUnsigned();
    if (!_htn.hasQConstants(unsignedPrecondition)) {
        analyzeGroundPrecondition(precondition);
        return std::nullopt;
    }

    const std::vector<int> sorts = _htn.getConditionSortsFromOperation(unsignedPrecondition, operationSig);
    const std::vector<int> qArgumentIndices = SubstitutionConstraint::getQArgumentIndicesByDomainSize(_htn, unsignedPrecondition._args, sorts);

    if (_htn.isEqualityPredicate(unsignedPrecondition._name_id)) {
        return buildEqualityPreconditionConstraint(precondition, sorts, qArgumentIndices);
    }
    if (_htn.isStaticPredicate(unsignedPrecondition._name_id)) {
        return buildStaticPreconditionConstraint(precondition, sorts, qArgumentIndices);
    }
    const std::vector<std::vector<int>> eligibleArguments = _htn.getCandidateArgumentDomains(unsignedPrecondition, sorts);
    return buildFluentPreconditionConstraint(position, precondition, eligibleArguments, qArgumentIndices, registerDynamicQFact);
}

void TreeExpander::analyzeGroundPrecondition(const Signature& precondition) {
    const USignature& fact = precondition.getUnsigned();
    if (_htn.isEqualityPredicate(fact._name_id)) {
        const bool holds = precondition._negated ? fact._args[0] != fact._args[1] : fact._args[0] == fact._args[1];
        assert(holds || Log::e("Precondition %s not reachable!\n", TOSTR(precondition)));
        if (holds && !precondition._negated) {
            const int factId = _htn.getGroundFactId(fact, /*negated=*/false);
            _analysis.addRelevantFact(factId);
        }
        return;
    }

    const int factId = _htn.getGroundFactId(fact, precondition._negated);
    if (factId < 0) {
        Log::e("Precondition %s not reachable!\n", TOSTR(precondition));
        return;
    }
    assert(_analysis.isReachable(factId, precondition._negated) || Log::e("Precondition %s not reachable!\n", TOSTR(precondition)));
    // A fact needs a SAT variable only when both truth values remain reachable.
    if (_analysis.isReachable(factId, !precondition._negated)) _analysis.addRelevantFact(factId);
}

SubstitutionConstraint TreeExpander::buildEqualityPreconditionConstraint(const Signature& precondition, const std::vector<int>& sorts, const std::vector<int>& qArgumentIndices) {
    const USignature& fact = precondition.getUnsigned();
    SubstitutionConstraint constraint(collectQConstants(fact, qArgumentIndices));

    // Equality needs every candidate assignment because equality facts are not fully grounded in the fact table.
    for (const USignature& decoding : _htn.enumerateCandidateDecodings(fact, sorts)) {
        const bool holds = precondition._negated ? decoding._args[0] != decoding._args[1] : decoding._args[0] == decoding._args[1];
        const auto path = SubstitutionConstraint::toAssignmentPath(fact._args, decoding._args, qArgumentIndices);
        if (holds) constraint.allow(path);
        else constraint.forbid(path);
    }
    constraint.chooseRepresentation();
    return constraint;
}

SubstitutionConstraint TreeExpander::buildStaticPreconditionConstraint(const Signature& precondition, const std::vector<int>& sorts, const std::vector<int>& qArgumentIndices) {
    const USignature& fact = precondition.getUnsigned();
    SubstitutionConstraint constraint(collectQConstants(fact, qArgumentIndices));
    constraint.chooseRepresentation(precondition._negated ? SubstitutionConstraint::FORBIDDEN_ASSIGNMENTS : SubstitutionConstraint::ALLOWED_ASSIGNMENTS);

    // Static predicates only need facts present in the indexed ground-fact table.
    const BitVec matchingPositiveFacts = _htn.findMatchingGroundFactIds(fact, /*negated=*/false, sorts);
    for (int factId : matchingPositiveFacts) {
        const USignature& decoding = _htn.getGroundPositiveFact(factId);
        const auto path = SubstitutionConstraint::toAssignmentPath(fact._args, decoding._args, qArgumentIndices);
        if (precondition._negated) constraint.forbid(path);
        else constraint.allow(path);
    }
    return constraint;
}

SubstitutionConstraint TreeExpander::buildFluentPreconditionConstraint(Position& position, const Signature& precondition, const std::vector<std::vector<int>>& eligibleArguments, const std::vector<int>& qArgumentIndices, bool registerDynamicQFact) {
    const USignature& fact = precondition.getUnsigned();
    SubstitutionConstraint constraint(collectQConstants(fact, qArgumentIndices));
    FlatHashSet<int> stateDependentFactIds;

    size_t numDecodings = 1;
    for (const auto& arguments : eligibleArguments) numDecodings *= arguments.size();

    // Sampling selects the smaller allowed/forbidden representation. Every decoding is still examined below.
    constexpr size_t sampleSize = 25;
    const bool chooseRepresentationFromSample = numDecodings > 2 * sampleSize;
    auto representation = SubstitutionConstraint::UNDECIDED;
    if (chooseRepresentationFromSample) {
        size_t numReachableSamples = 0;
        for (const USignature& decoding : _htn.sampleCandidateDecodings(fact, eligibleArguments, sampleSize)) {
            const int factId = _htn.getGroundFactId(decoding, precondition._negated);
            if (factId >= 0 && _analysis.isReachable(factId, precondition._negated)) numReachableSamples++;
        }
        representation = numReachableSamples < sampleSize / 2 ? SubstitutionConstraint::ALLOWED_ASSIGNMENTS : SubstitutionConstraint::FORBIDDEN_ASSIGNMENTS;
        constraint.chooseRepresentation(representation);
    }

    // Reachability determines valid substitutions. Non-invariant decodings also need SAT fact variables.
    for (const USignature& decoding : _htn.enumerateCandidateDecodings(fact, eligibleArguments)) {
        const int factId = _htn.getGroundFactId(decoding, precondition._negated);
        const bool reachable = factId >= 0 && _analysis.isReachable(factId, precondition._negated);
        const auto path = SubstitutionConstraint::toAssignmentPath(fact._args, decoding._args, qArgumentIndices);

        if (!reachable) {
            if (representation != SubstitutionConstraint::ALLOWED_ASSIGNMENTS) constraint.forbid(path);
            continue;
        }
        if (representation != SubstitutionConstraint::FORBIDDEN_ASSIGNMENTS) constraint.allow(path);
        if (!_analysis.isInvariant(factId, precondition._negated)) stateDependentFactIds.insert(factId);
    }

    if (!stateDependentFactIds.empty()) {
        if (registerDynamicQFact) position.addQFact(fact);
        for (int factId : stateDependentFactIds) {
            const USignature& decoding = _htn.getGroundPositiveFact(factId);
            if (registerDynamicQFact) position.addQFactDecoding(fact, decoding, precondition._negated);
            _analysis.addRelevantFact(factId);
        }
    }
    if (!chooseRepresentationFromSample) constraint.chooseRepresentation();
    return constraint;
}

std::vector<int> TreeExpander::collectQConstants(const USignature& fact, const std::vector<int>& qArgumentIndices) const {
    std::vector<int> qConstants;
    qConstants.reserve(qArgumentIndices.size());
    for (int argumentIndex : qArgumentIndices) qConstants.push_back(fact._args[argumentIndex]);
    return qConstants;
}

void TreeExpander::addGroundEffect(OutgoingEffects& outgoing, const USignature& opSig, BitVec effects, bool negated, EffectMode mode) {
    if (effects.count() == 0) return;

    _analysis.removeInvariantGroundFacts(effects, negated);
    if (mode != EffectMode::POSSIBLE_METHOD_EFFECT) {
        _analysis.addMultipleRelevantFacts(effects);
    }

    outgoing.addFactChanges(effects, negated);

    for (int factId : effects) {
        if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
            outgoing.addSupport(factId, negated, opSig);
        } else {
            outgoing.touchSupport(factId, negated);
        }
    }
}

void TreeExpander::addGroundEffect(OutgoingEffects& outgoing, const USignature& opSig, int factId, bool negated, EffectMode mode) {
    if (_analysis.isInvariant(factId, negated)) return;

    if (mode != EffectMode::POSSIBLE_METHOD_EFFECT) {
        _analysis.addRelevantFact(factId);
    }

    if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
        outgoing.addSupport(factId, negated, opSig);
    } else {
        outgoing.touchSupport(factId, negated);
    }
    outgoing.addFactChange(factId, negated);
}

bool TreeExpander::isEffectDecodingAllowed(const std::vector<IntPair>& assignmentPath, const std::vector<const SubstitutionConstraint*>& sameQConstantConstraints, const std::vector<const SubstitutionConstraint*>& relatedConstraints) const {
    for (const SubstitutionConstraint* constraint : sameQConstantConstraints) {
        if (!constraint->isValid(assignmentPath, /*sameReference=*/true)) return false;
    }
    for (const SubstitutionConstraint* constraint : relatedConstraints) {
        if (!constraint->isValid(assignmentPath, /*sameReference=*/false)) return false;
    }
    return true;
}

bool TreeExpander::hasNegativeEffectOnPredicate(const USignature& actionSig, int predicateId) const {
    const SigSet& actionEffects = _htn.getOpTable().getAction(actionSig).getEffects();
    for (const Signature& actionEffect : actionEffects) {
        if (actionEffect._negated && actionEffect._usig._name_id == predicateId) return true;
    }
    return false;
}

bool TreeExpander::addInstantiatedEffect(OutgoingEffects& outgoing, Position& position, const USignature& opSig, const Signature& effect, EffectMode mode) {
    const USignature& unsignedEffect = effect.getUnsigned();
    if (!_htn.hasQConstants(unsignedEffect)) {
        const int factId = _htn.getGroundFactId(unsignedEffect, effect._negated);
        if (factId < 0) return false;
        addGroundEffect(outgoing, opSig, factId, effect._negated, mode);
        return true;
    }

    const std::vector<int> effectSorts = _htn.getConditionSortsFromOperation(unsignedEffect, opSig);
    const std::vector<int> qArgumentIndices = SubstitutionConstraint::getQArgumentIndicesByDomainSize(_htn, unsignedEffect._args, effectSorts);
    const std::vector<int> effectQConstants = collectQConstants(unsignedEffect, qArgumentIndices);

    std::vector<const SubstitutionConstraint*> sameQConstantConstraints;
    std::vector<const SubstitutionConstraint*> relatedConstraints;
    const auto constraintsIt = position.getSubstitutionConstraints().find(opSig);
    if (constraintsIt != position.getSubstitutionConstraints().end()) {
        for (const SubstitutionConstraint& constraint : constraintsIt->second) {
            if (constraint.getQConstants() == effectQConstants) {
                sameQConstantConstraints.push_back(&constraint);
            } else if (constraint.getRepresentation() == SubstitutionConstraint::FORBIDDEN_ASSIGNMENTS || constraint.involvesSupersetOf(effectQConstants)) {
                relatedConstraints.push_back(&constraint);
            }
        }
    }

    const bool isPositiveActionEffect = _htn.isAction(opSig) && !effect._negated;
    const bool hasConflictingNegativeEffect = isPositiveActionEffect && hasNegativeEffectOnPredicate(opSig, effect._usig._name_id);
    bool hasValidDecoding = false;
    bool requiresQFactEncoding = false;

    const BitVec matchingFactIds = _htn.findMatchingGroundFactIds(unsignedEffect, effect._negated, effectSorts);
    for (int factId : matchingFactIds) {
        const USignature& decoding = _htn.getGroundPositiveFact(factId);
        const std::vector<IntPair> assignmentPath = SubstitutionConstraint::toAssignmentPath(unsignedEffect._args, decoding._args, qArgumentIndices);
        if (!isEffectDecodingAllowed(assignmentPath, sameQConstantConstraints, relatedConstraints)) continue;

        hasValidDecoding = true;
        if (_analysis.isInvariant(factId, effect._negated)) {
            // A positive invariant still needs encoding if this action can also delete the predicate.
            if (!isPositiveActionEffect || !hasConflictingNegativeEffect || requiresQFactEncoding) continue;
            Log::d("Eff: %c %s of %s holds trivially but must be added for correct encoding\n", effect._negated ? '-' : '+', TOSTR(decoding), TOSTR(opSig));
        }

        if (_nonprimitive_support || _htn.isAction(opSig) || _use_sibylsat_expansion) {
            outgoing.addIndirectSupport(factId, effect._negated, opSig, assignmentPath);
        } else {
            outgoing.touchSupport(factId, effect._negated);
        }
        outgoing.addFactChange(factId, effect._negated);
        if (mode != EffectMode::POSSIBLE_METHOD_EFFECT) {
            if (mode == EffectMode::ACTION_EFFECT) outgoing.addQFactDecoding(unsignedEffect, decoding, effect._negated);
            _analysis.addRelevantFact(factId);
        }
        requiresQFactEncoding = true;
    }

    if (!hasValidDecoding) return false;
    if (requiresQFactEncoding && mode == EffectMode::ACTION_EFFECT) outgoing.addQFact(unsignedEffect);
    return true;
}

void TreeExpander::propagateParentActions(Position& child, Position& parent) {
    const size_t childOffset = child.getOffset();
    if (childOffset > 0) {
        const USignature& blankActionSig = _htn.getBlankActionSig();
        if (!parent.getActions().empty()) child.addAction(blankActionSig);

        for (const auto& actionSig : parent.getActions()) {
            child.addExpansion(actionSig, blankActionSig);
        }
        return;
    }

    std::vector<USignature> actionsToPrune;
    const size_t numParentActionsBeforePruning = parent.getActions().size();
    for (const auto& actionSig : parent.getActions()) {
        const Action& action = _htn.getOpTable().getAction(actionSig);

        const bool hasValidPreconditions =
            _analysis.hasValidPreconditions(action.getPreconditions())
            && _analysis.hasValidPreconditions(action.getExtraPreconditions());

        if (!hasValidPreconditions) {
            Log::i("Retroactively prune action %s@(%zu,%zu): no children at offset %zu\n",
                TOSTR(actionSig), parent.getCreationIteration(), parent.getPositionId(), childOffset);
            actionsToPrune.push_back(actionSig);
        }
    }

    for (const auto& actionSig : actionsToPrune) {
        assert(_pruning != nullptr);
        _pruning->prune(actionSig, parent);
    }
    assert(parent.getActions().size() == numParentActionsBeforePruning - actionsToPrune.size()
        || Log::e("%zu != %zu-%zu\n", parent.getActions().size(),
            numParentActionsBeforePruning, actionsToPrune.size()));

    for (const auto& actionSig : parent.getActions()) {
        assert(_htn.isFullyGround(actionSig));
        if (_params.isNonzero("aar") && !_htn.isActionRepetition(actionSig._name_id)) {
            USignature repetitionSig = _htn.getRepetitionOfAction(actionSig);
            child.addAction(repetitionSig);
            child.addExpansion(actionSig, repetitionSig);
        } else {
            child.addAction(actionSig);
            child.addExpansion(actionSig, actionSig);
        }
    }
}

void TreeExpander::expandParentReductions(Position& child, Position& parent) {
    const size_t childOffset = child.getOffset();
    const size_t originPositionId = child.getPositionId();
    const USignature& blankActionSig = _htn.getBlankActionSig();
    NodeHashMap<USignature, USigSet, USignatureHasher> parentReductionsBySubtask;
    std::vector<USignature> reductionsWithNoChildren;

    for (const auto& parentReductionSig : parent.getReductions()) {
        const Reduction& parentReduction = _htn.getOpTable().getReduction(parentReductionSig);

        if (childOffset < parentReduction.getSubtasks().size()) {
            const USignature& subtask = parentReduction.getSubtasks()[childOffset];
            parentReductionsBySubtask[subtask].insert(parentReductionSig);
        } else {
            // Pad reductions shorter than the expanded width with blank actions.
            child.addAction(blankActionSig);
            child.addExpansion(parentReductionSig, blankActionSig);
        }
    }

    // Instantiate each distinct subtask once, then link it to every parent reduction exposing it.
    for (const auto& [subtask, parentReductionSigs] : parentReductionsBySubtask) {
        const auto instantiatedActionSigs = instantiateActionsOfTask(subtask, originPositionId);
        const auto instantiatedReductionSigs = instantiateReductionsOfTask(subtask, originPositionId);

        if (instantiatedActionSigs.empty() && instantiatedReductionSigs.empty()) {
            reductionsWithNoChildren.insert(reductionsWithNoChildren.end(), parentReductionSigs.begin(), parentReductionSigs.end());
            continue;
        }

        for (const USignature& childReductionSig : instantiatedReductionSigs) {
            assert(_htn.isReduction(childReductionSig));
            const Reduction& childReduction = _htn.getOpTable().getReduction(childReductionSig);
            assert(childReductionSig == childReduction.getSignature());
            assert(_htn.isFullyGround(childReductionSig));

            child.addReduction(childReductionSig);

            if (_optimal) {
                assert(_tdg != nullptr);
                const int heuristicValue = _tdg->getBestHeuristicValue(childReductionSig);
                Log::d("Set the heuristic value of %s to %d\n", TOSTR(childReductionSig), heuristicValue);
                child.setHeuristicValue(childReductionSig, heuristicValue);
            }

            for (const auto& parentReductionSig : parentReductionSigs) {
                child.addExpansion(parentReductionSig, childReductionSig);
            }
        }

        for (const USignature& childActionSig : instantiatedActionSigs) {
            assert(_htn.isFullyGround(childActionSig));
            child.addAction(childActionSig);

            for (const auto& parentReductionSig : parentReductionSigs) {
                child.addExpansion(parentReductionSig, childActionSig);
            }
        }
    }

    for (const auto& parentReductionSig : reductionsWithNoChildren) {
        Log::i("Retroactively prune reduction %s@(%zu,%zu): no children at offset %zu\n",
            TOSTR(parentReductionSig), parent.getCreationIteration(),
            parent.getPositionId(), childOffset);
        assert(_pruning != nullptr);
        _pruning->prune(parentReductionSig, parent);
    }
}

std::optional<USignature> TreeExpander::instantiateAndRegisterAction(const USignature& actionSig, size_t originPositionId) {
    Action action = _htn.toAction(actionSig._name_id, actionSig._args);
    if (!isPotentiallyApplicable(action)) return std::nullopt;

    const USignature originalSig = action.getSignature();
    auto argumentDomains = _analysis.computeReachableArgumentDomains(action);
    if (!argumentDomains) return std::nullopt;
    auto instantiatedAction = _htn.instantiateWithQConstants(action, argumentDomains.value(), originPositionId);
    if (!instantiatedAction) return std::nullopt;
    action = std::move(instantiatedAction.value());

    action.removeInconsistentEffects();

    assert(_htn.isFullyGround(action.getSignature()));
    if (!_htn.isFullyGround(action.getSignature())) return std::nullopt;
    if (!_htn.hasConsistentlyTypedArgs(originalSig)) return std::nullopt;
    if (!_analysis.hasValidPreconditions(action.getPreconditions())) return std::nullopt;
    if (!_analysis.hasValidPreconditions(action.getExtraPreconditions())) return std::nullopt;

    _htn.getOpTable().addAction(action);
    return action.getSignature();
}

std::vector<USignature> TreeExpander::instantiateActionsOfTask(const USignature& task, size_t originPositionId) {
    std::vector<USignature> result;

    if (_htn.isAction(task)) {
        auto actionSig = instantiateAndRegisterAction(task, originPositionId);
        if (actionSig) result.push_back(std::move(actionSig.value()));
        return result;
    }

    if (!_htn.hasReductions(task._name_id)) return result;

    // An abstract task may have actions created from primitivizable methods that accomplish the task.
    for (int reductionId : _htn.getReductionIdsOfTaskId(task._name_id)) {
        if (!_htn.isReductionPrimitivizable(reductionId)) continue;

        const Reduction& reduction = _htn.getReductionTemplate(reductionId);
        const Action& primitivizedAction = _htn.getReductionPrimitivization(reductionId);

        auto substitution = Substitution::fromArgumentMapping(reduction.getTaskArguments(), task._args);
        if (!substitution) continue;

        const USignature primitivizedActionSig = primitivizedAction.getSignature().substitute(substitution.value());
        auto actionSig = instantiateAndRegisterAction(primitivizedActionSig, originPositionId);
        if (actionSig) result.push_back(std::move(actionSig.value()));
    }
    return result;
}

std::vector<USignature> TreeExpander::instantiateReductionsOfTask(const USignature& task, size_t originPositionId) {
    std::vector<USignature> result;

    if (!_htn.hasReductions(task._name_id)) return result;

    for (int reductionId : _htn.getReductionIdsOfTaskId(task._name_id)) {
        if (_htn.isReductionPrimitivizable(reductionId)) continue;

        const Reduction& reduction = _htn.getReductionTemplate(reductionId);

        auto substitution = Substitution::fromArgumentMapping(reduction.getTaskArguments(), task._args);
        if (!substitution) continue;

        Reduction substitutedReduction = reduction.substituteRed(substitution.value());
        auto instantiatedReductionSig = instantiateAndRegisterReduction(std::move(substitutedReduction), task, originPositionId);
        if (instantiatedReductionSig) result.push_back(instantiatedReductionSig.value());
    }
    return result;
}

std::optional<USignature> TreeExpander::instantiateAndRegisterReduction(Reduction reduction, const std::optional<USignature>& expectedTask, size_t originPositionId) {
    if (!_htn.hasConsistentlyTypedArgs(reduction.getSignature())) return std::nullopt;
    if (!isPotentiallyApplicable(reduction)) return std::nullopt;

    auto argumentDomains = _analysis.computeReachableArgumentDomains(reduction);
    if (!argumentDomains) return std::nullopt;
    auto instantiatedReduction = _htn.instantiateWithQConstants(reduction, argumentDomains.value(), originPositionId);
    if (!instantiatedReduction) return std::nullopt;
    reduction = std::move(instantiatedReduction.value());

    if (expectedTask && reduction.getTaskSignature() != expectedTask.value()) return std::nullopt;
    assert(_htn.isFullyGround(reduction.getSignature()));
    if (!_htn.isFullyGround(reduction.getSignature())) return std::nullopt;
    if (!_analysis.hasValidPreconditions(reduction.getPreconditions())) return std::nullopt;
    if (!_analysis.hasValidPreconditions(reduction.getExtraPreconditions())) return std::nullopt;

    _htn.getOpTable().addReduction(reduction);
    return reduction.getSignature();
}

void TreeExpander::addQConstantTypeConstraints(Position& position, const USignature& operationSig) {
    const std::vector<TypeConstraint> constraints = _htn.getQConstantTypeConstraints(operationSig);
    for (const TypeConstraint& constraint : constraints) {
        position.addQConstantTypeConstraint(operationSig, constraint);
    }
}
