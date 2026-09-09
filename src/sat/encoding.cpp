
#include <algorithm>
#include <queue>

#include "sat/encoding.h"
#include "sat/literal_tree.h"
#include "sat/binary_amo.h"
#include "sat/dnf2cnf.h"
#include "util/log.h"

Position* Encoding::getCurrentFrontierLeft(const Position& pos) const {
    size_t frontierIndex = pos.getFrontierIndex();
    if (frontierIndex == 0 || frontierIndex >= _leaf_positions.size()) {
        return nullptr;
    }
    return _leaf_positions[frontierIndex - 1];
}

Position* Encoding::getPreviousFrontierLeft(const Position& pos, size_t expansionIteration) const {
    const Position* node = &pos;
    while (node->getParentPosition() != nullptr) {
        Position* parent = node->getParentPosition();
        if (node->getOffset() > 0) {
            Position* predecessor = parent->getChildrenPositions()[node->getOffset() - 1];

            // Follow the rightmost branch that had already been created before
            // this expansion. Children created now replace their parent only in
            // the new frontier, so the parent itself belongs to the old one.
            while (true) {
                Position* previousDescendant = nullptr;
                for (auto it = predecessor->getChildrenPositions().rbegin(); it != predecessor->getChildrenPositions().rend(); ++it) {
                    if ((*it)->getCreationIteration() < expansionIteration) {
                        previousDescendant = *it;
                        break;
                    }
                }
                if (previousDescendant == nullptr) return predecessor;
                predecessor = previousDescendant;
            }
        }
        node = parent;
    }
    return nullptr;
}

Position* Encoding::getParentExcludingRoot(const Position& pos) const {
    Position* parent = pos.getParentPosition();
    return parent == _root_position ? nullptr : parent;
}

bool Encoding::wasCreatedInCurrentExpansion(const Position& pos, size_t expansionIteration) const {
    return pos.getCreationIteration() == expansionIteration;
}

bool Encoding::isPrimitiveReduction(const USignature& reduction) const {
    return _htn.getOpTable().getReduction(reduction).getSubtasks().empty();
}

bool Encoding::hasPrimitiveCandidates(const Position& pos) const {
    if (!pos.getActions().empty()) return true;

    // Selecting a reduction with no children also makes the position primitive.
    return std::any_of(pos.getReductions().begin(), pos.getReductions().end(), [&](const USignature& reduction) {
        return isPrimitiveReduction(reduction);
    });
}

bool Encoding::hasNonprimitiveCandidates(const Position& pos) const {
    return std::any_of(pos.getReductions().begin(), pos.getReductions().end(), [&](const USignature& reduction) {
        return !isPrimitiveReduction(reduction);
    });
}

void Encoding::StateQFacts::add(const Position& position) {
    for (const USignature& fact : position.getQFacts()) {
        qFacts.insert(fact);
        if (position.hasQFactDecodings(fact, /*negated=*/false)) {
            const USigSet& decodings = position.getQFactDecodings(fact, /*negated=*/false);
            positiveDecodings[fact].insert(decodings.begin(), decodings.end());
        }
        if (position.hasQFactDecodings(fact, /*negated=*/true)) {
            const USigSet& decodings = position.getQFactDecodings(fact, /*negated=*/true);
            negativeDecodings[fact].insert(decodings.begin(), decodings.end());
        }
    }
}

void Encoding::StateQFacts::add(const OutgoingEffects& effects) {
    for (const USignature& fact : effects.getQFacts()) {
        qFacts.insert(fact);
        if (effects.hasQFactDecodings(fact, /*negated=*/false)) {
            const USigSet& decodings = effects.getQFactDecodings(fact, /*negated=*/false);
            positiveDecodings[fact].insert(decodings.begin(), decodings.end());
        }
        if (effects.hasQFactDecodings(fact, /*negated=*/true)) {
            const USigSet& decodings = effects.getQFactDecodings(fact, /*negated=*/true);
            negativeDecodings[fact].insert(decodings.begin(), decodings.end());
        }
    }
}

bool Encoding::StateQFacts::hasDecodings(const USignature& fact, bool negated) const {
    const auto& decodings = negated ? negativeDecodings : positiveDecodings;
    return decodings.count(fact);
}

bool Encoding::StateQFacts::hasAnyDecodings(const USignature& fact) const {
    return hasDecodings(fact, /*negated=*/false)
            || hasDecodings(fact, /*negated=*/true);
}

const USigSet& Encoding::StateQFacts::getDecodings(const USignature& fact, bool negated) const {
    const auto& decodings = negated ? negativeDecodings : positiveDecodings;
    assert(decodings.count(fact));
    return decodings.at(fact);
}

Encoding::StateQFacts Encoding::collectStateQFacts(const Position& position, const Position* incoming) const {
    StateQFacts stateQFacts;
    stateQFacts.add(position);
    if (incoming != nullptr
            && position.getFrontierIndex() != 0
            && position.getFrontierIndex() != _active_frontier_start) {
        stateQFacts.add(incoming->getOutgoingEffects());
    }
    return stateQFacts;
}

int Encoding::findReusableQFactVariable(
        const USignature& qfact,
        const Position& position,
        const StateQFacts& stateQFacts,
        const Position* source,
        const StateQFacts& sourceStateQFacts) const {
    if (source == nullptr) return 0;

    const int qfactVar = source->getVariableOrZero(VarType::FACT, qfact);
    if (qfactVar == 0) return 0;

    for (bool negated : {false, true}) {
        if (!stateQFacts.hasDecodings(qfact, negated)) continue;
        if (!sourceStateQFacts.hasDecodings(qfact, negated)) return 0;

        const USigSet& sourceDecodings = sourceStateQFacts.getDecodings(qfact, negated);
        for (const USignature& decoding : stateQFacts.getDecodings(qfact, negated)) {
            const int factVar = position.getVariableOrZero(VarType::FACT, decoding);
            const int sourceFactVar = source->getVariableOrZero(VarType::FACT, decoding);
            if (!sourceDecodings.count(decoding)
                    || factVar == 0
                    || sourceFactVar == 0
                    || factVar != sourceFactVar) {
                return 0;
            }
        }
    }
    return qfactVar;
}

Encoding::EncodingEnvironment Encoding::buildFreshPositionEnvironment(Position& pos) const {
    Encoding::EncodingEnvironment env;
    env.incoming = getCurrentFrontierLeft(pos);
    env.parent = getParentExcludingRoot(pos);
    env.reusePredecessor = env.parent == nullptr ? nullptr : getPreviousFrontierLeft(*env.parent, pos.getCreationIteration());
    env.reuseFactsFrom = pos.getOffset() == 0 ? env.parent : nullptr;
    return env;
}

Encoding::EncodingEnvironment Encoding::buildExistingTransitionEnvironment(Position& source, Position& destination, size_t expansionIteration) const {
    Encoding::EncodingEnvironment env;
    env.incoming = &source;
    env.parent = getParentExcludingRoot(destination);
    env.reusePredecessor = getPreviousFrontierLeft(destination, expansionIteration);
    env.reuseFactsFrom = &destination;
    return env;
}

Encoding::EncodingEnvironment Encoding::buildRelevantFactPropagationEnvironment(Position& source, Position& destination, size_t expansionIteration) const {
    Encoding::EncodingEnvironment env;
    env.incoming = &source;
    env.parent = getParentExcludingRoot(destination);
    env.reusePredecessor = getPreviousFrontierLeft(destination, expansionIteration);
    env.reuseFactsFrom = destination.getOffset() == 0 ? env.parent : nullptr;
    return env;
}

void Encoding::encodeAllLeaves() {
    Statistics& stats = Statistics::getInstance();

    Log::i("Collected %i relevant facts at this expansion iteration\n", _analysis.getRelevantFacts().count());
    Log::i("Encoding ...\n");

    size_t currentExpansionIteration = 0;
    for (Position* leaf : _leaf_positions) {
        currentExpansionIteration = std::max(currentExpansionIteration, leaf->getCreationIteration());
    }
    const bool hasCarriedPositions = std::any_of(_leaf_positions.begin(), _leaf_positions.end(), [&](const Position* leaf) {
        return !wasCreatedInCurrentExpansion(*leaf, currentExpansionIteration);
    });

    stats.beginTiming(TimingStage::ENCODING);
    Log::i("Frontier size: %zu\n", _leaf_positions.size());

    // Reuse parent state variables before encoding any fresh position. This also
    // ensures that newly relevant facts are attached to the existing state at
    // the start of the active frontier whenever possible.
    for (size_t leafIndex = _active_frontier_start; leafIndex < _leaf_positions.size(); leafIndex++) {
        Position& position = *_leaf_positions[leafIndex];
        if (wasCreatedInCurrentExpansion(position, currentExpansionIteration)) {
            reuseParentFactVariables(position, buildFreshPositionEnvironment(position));
        }
    }
    const BitVec newlyRelevantFactIds = encodeRelevantFactsAtFrontierStart(*_leaf_positions[_active_frontier_start]);

    // The SAT formula is monotonic: old clauses remain valid. A fresh position
    // needs its complete encoding; an existing destination only needs clauses
    // for a newly introduced incoming edge or for newly relevant facts.
    for (size_t leafIndex = _active_frontier_start; leafIndex < _leaf_positions.size(); leafIndex++) {
        Position& destination = *_leaf_positions[leafIndex];
        if (wasCreatedInCurrentExpansion(destination, currentExpansionIteration)) {
            Log::v("- Position (%zu,%zu)\n", destination.getCreationIteration(), destination.getFrontierIndex());
            encodeFreshPosition(destination);
        } else if (leafIndex > _active_frontier_start) {
            Position& source = *_leaf_positions[leafIndex - 1];
            if (wasCreatedInCurrentExpansion(source, currentExpansionIteration)) {
                encodeTransition(source, destination, currentExpansionIteration);
            } else {
                propagateNewRelevantFacts(source, destination, currentExpansionIteration, newlyRelevantFactIds);
            }
        }
    }
    stats.endTiming(TimingStage::ENCODING);

    // Expanded positions are now internal nodes; retained frontier positions no
    // longer need the temporary decoding data used during this encoding pass.
    if (hasCarriedPositions) {
        FlatHashSet<Position*> expandedOldLeaves;
        for (Position* leaf : _leaf_positions) {
            if (!wasCreatedInCurrentExpansion(*leaf, currentExpansionIteration)) continue;
            Position* parent = leaf->getParentPosition();
            if (parent != nullptr && parent != _root_position && !expandedOldLeaves.count(parent)) {
                expandedOldLeaves.insert(parent);
            }
        }
        for (Position* node : expandedOldLeaves) {
            Log::v("Freeing position %zu created in iteration %zu\n", node->getPositionId(), node->getCreationIteration());
            node->clearFullPos();
        }
        for (Position* leaf : _leaf_positions) {
            leaf->clearDecodings();
        }
    }
}

void Encoding::encodeFreshPosition(Position& newPos) {
    Encoding::EncodingEnvironment env = buildFreshPositionEnvironment(newPos);

    _stats.beginPosition();

    encodeOperationVariables(newPos);

    // Ground facts are connected to the incoming state through frame axioms.
    // Q-facts are then assigned either a reusable or a fresh SAT variable.
    if (env.incoming != nullptr) encodeGroundFactTransition(*env.incoming, newPos, env);
    const USigSet newlyCreatedQFacts = encodeQFactVariables(newPos, env);

    // Encode substitution domains, preconditions, and operation selection.
    encodeOperationConstraints(newPos);

    // Link state Q-facts to their possible ground decodings.
    encodeQFactSemantics(newPos, env, newlyCreatedQFacts);

    // Complete the incoming transition with the source action's effects.
    if (newPos.getFrontierIndex() != 0 && newPos.getFrontierIndex() != _active_frontier_start && env.incoming != nullptr) {
        encodeEffects(*env.incoming, newPos);
    }


    // Type constraints and forbidden substitutions for q-constants
    // and (sets of) q-facts
    encodeQConstraints(newPos);

    // Expansion and predecessor specification for each element
    // and prohibition of impossible children
    encodeSubtaskRelationships(newPos, env);

    if (_use_sibylsat_expansion && !_optimal) {
        encodeRecursiveMethodAncestorDistinctness(newPos);
    }

    _stats.endPosition();
}

void Encoding::encodeOperationVariables(Position& newPos) {
    std::vector<int> primitiveOpVars;
    primitiveOpVars.reserve(newPos.getActions().size() + newPos.getReductions().size());
    std::vector<int> nonprimitiveOpVars;
    nonprimitiveOpVars.reserve(newPos.getReductions().size());

    _stats.begin(STAGE_ACTIONCONSTRAINTS);
    for (const auto& aSig : newPos.getActions()) {
        int aVar = _vars.getOrCreateVariable(VarType::OP, newPos, aSig);

        // If the action occurs, the position is primitive
        primitiveOpVars.push_back(aVar);
    }
    _stats.end(STAGE_ACTIONCONSTRAINTS);

    _stats.begin(STAGE_REDUCTIONCONSTRAINTS);
    for (const auto& rSig : newPos.getReductions()) {
        int rVar = _vars.getOrCreateVariable(VarType::OP, newPos, rSig);

        if (isPrimitiveReduction(rSig)) {
            // If a trivial reduction occurs, the position is primitive
            primitiveOpVars.push_back(rVar);
        } else {
            // If another reduction occurs, the position is non-primitive
            nonprimitiveOpVars.push_back(rVar);
        }
    }
    _stats.end(STAGE_REDUCTIONCONSTRAINTS);

    // Only primitive ops here? -> No primitiveness definition necessary
    if (nonprimitiveOpVars.empty()) {
        return;
    }

    int varPrim = _vars.getOrCreatePrimitiveVariable(newPos);

    _stats.begin(STAGE_REDUCTIONCONSTRAINTS);
    if (primitiveOpVars.empty()) {
        // Only non-primitive ops here
        _sat.addClause(-varPrim);
    } else {
        // Mix of primitive and non-primitive ops (default)
        _stats.begin(STAGE_ACTIONCONSTRAINTS);
        for (int primitiveOpVar : primitiveOpVars) _sat.addClause(-primitiveOpVar, varPrim);
        _stats.end(STAGE_ACTIONCONSTRAINTS);
        for (int nonprimitiveOpVar : nonprimitiveOpVars) _sat.addClause(-nonprimitiveOpVar, -varPrim);
    }
    _stats.end(STAGE_REDUCTIONCONSTRAINTS);
}

BitVec Encoding::encodeRelevantFactsAtFrontierStart(Position& position) {
    BitVec newlyRelevantFactIds(_analysis.getNumGroundFacts());

    for (const int predId : _analysis.getRelevantFacts()) {
        const USignature& fact = _analysis.getGroundFact(predId);
        if (position.hasVariable(VarType::FACT, fact)) continue;

        const int factVar = _vars.getOrCreateVariable(VarType::FACT, position, fact);
        _sat.addClause((_analysis.isInitiallyReachable(predId, /*negated=*/false) ? 1 : -1) * factVar);
        newlyRelevantFactIds.set(predId);
    }
    return newlyRelevantFactIds;
}

void Encoding::reuseParentFactVariables(Position& position, const Encoding::EncodingEnvironment& env) {
    if (position.getCreationIteration() == 0 || env.reuseFactsFrom == nullptr) return;

    for (const auto& [fact, factVar] : env.reuseFactsFrom->getVariableTable(VarType::FACT)) {
        if (!_htn.hasQConstants(fact)) position.setVariable(VarType::FACT, fact, factVar);
    }
}

void Encoding::encodeGroundFactTransition(Position& source, Position& destination, const Encoding::EncodingEnvironment& env) {
    if (destination.getFrontierIndex() == 0 || destination.getFrontierIndex() == _active_frontier_start) return;

    _stats.begin(STAGE_FACTVARENCODING);
    encodeFrameAxioms(source, destination, env);
    _stats.end(STAGE_FACTVARENCODING);
}

USigSet Encoding::encodeQFactVariables(Position& newPos, const Encoding::EncodingEnvironment& env) {
    USigSet newlyCreatedQFacts;

    _stats.begin(STAGE_FACTVARENCODING);

    const StateQFacts stateQFacts = collectStateQFacts(newPos, env.incoming);
    const StateQFacts incomingStateQFacts = env.incoming == nullptr
            ? StateQFacts()
            : collectStateQFacts(*env.incoming, getCurrentFrontierLeft(*env.incoming));

    for (const USignature& qfact : stateQFacts.qFacts) {
        if (!stateQFacts.hasAnyDecodings(qfact)
                || newPos.hasVariable(VarType::FACT, qfact)) {
            continue;
        }

        int reusedVar = env.reuseFactsFrom == nullptr
                ? 0
                : env.reuseFactsFrom->getVariableOrZero(VarType::FACT, qfact);
        if (reusedVar == 0) {
            reusedVar = findReusableQFactVariable(
                    qfact, newPos, stateQFacts, env.incoming, incomingStateQFacts);
        }

        if (reusedVar != 0) {
            newPos.setVariable(VarType::FACT, qfact, reusedVar);
        } else {
            _vars.getOrCreateVariable(VarType::FACT, newPos, qfact);
            newlyCreatedQFacts.insert(qfact);
        }
    }

    _stats.end(STAGE_FACTVARENCODING);
    return newlyCreatedQFacts;
}

void Encoding::encodeFrameAxioms(Position& source, Position& destination, const Encoding::EncodingEnvironment& env, const BitVec* selectedFactIds) {
    _stats.begin(STAGE_DIRECTFRAMEAXIOMS);

    const bool nonprimFactSupport = _params.isNonzero("nps") || _use_sibylsat_expansion;
    const bool sourceHasPrimitiveCandidates = hasPrimitiveCandidates(source) || _use_sibylsat_expansion;
    const int sourceVarPrim = _vars.getPrimitiveVariableOrZero(source);

    const bool skipRedundantFrameAxioms = canSkipRedundantFrameAxioms(source, env);

    // If mutex param is used, prevent incompatible facts from being true at the same time
    USigSet positiveFacts;
    positiveFacts.reserve(selectedFactIds == nullptr
            ? source.getVariableTable(VarType::FACT).size()
            : selectedFactIds->count());

    if (selectedFactIds == nullptr) {
        for (const auto& [fact, sourceFactVar] : source.getVariableTable(VarType::FACT)) {
            if (_htn.hasQConstants(fact)) continue;
            encodeFrameAxiomForFact(source, destination, env, fact, sourceFactVar, nonprimFactSupport, sourceHasPrimitiveCandidates, sourceVarPrim, skipRedundantFrameAxioms, positiveFacts);
        }
    } else {
        for (const int factId : *selectedFactIds) {
            const USignature& fact = _analysis.getGroundFact(factId);
            const int sourceFactVar = source.getVariableOrZero(VarType::FACT, fact);
            if (sourceFactVar == 0) {
                Log::e("Newly relevant fact %s has no variable at source position %zu\n", TOSTR(fact), source.getPositionId());
                exit(1);
            }
            encodeFrameAxiomForFact(source, destination, env, fact, sourceFactVar, nonprimFactSupport, sourceHasPrimitiveCandidates, sourceVarPrim, skipRedundantFrameAxioms, positiveFacts);
        }
    }
    _stats.end(STAGE_DIRECTFRAMEAXIOMS);

    if (_mutex_groups != nullptr) {
        encodeMutexPredicates(destination, env, positiveFacts);
    }
}

bool Encoding::canSkipRedundantFrameAxioms(const Position& source, const Encoding::EncodingEnvironment& env) const {
    if (!_params.isNonzero("srfa") || env.reuseFactsFrom == nullptr || env.reusePredecessor == nullptr) return false;
    if (hasNonprimitiveCandidates(source)) return false;
    if (hasNonprimitiveCandidates(*env.reusePredecessor)) return false;
    return true;
}

Encoding::EffectSupports Encoding::findEffectSupports(OutgoingEffects& effects, int factId, bool negated) const {
    EffectSupports result;

    DirectFactSupportMap& directSupports = effects.getSupports(negated);
    auto directIt = directSupports.find(factId);
    if (directIt != directSupports.end()) result.direct = &directIt->second;

    IndirectFactSupportMapId& indirectSupports = effects.getIndirectSupports(negated);
    auto indirectIt = indirectSupports.find(factId);
    if (indirectIt != indirectSupports.end()) result.indirect = &indirectIt->second;

    return result;
}

void Encoding::encodeFrameAxiomForFact(Position& source, Position& destination, const Encoding::EncodingEnvironment& env, const USignature& fact, int sourceFactVar, bool nonprimFactSupport, bool sourceHasPrimitiveCandidates, int sourceVarPrim, bool skipRedundantFrameAxioms, USigSet& positiveFacts) {
    const int factId = _analysis.getGroundFactId(fact, true);
    if (factId < 0) {
        Log::e("factId: %i, fact: %s, var: %i\n", factId, TOSTR(fact), sourceFactVar);
        exit(1);
    }

    OutgoingEffects& effects = source.getOutgoingEffects();
    EffectSupports negativeEffectSupports = findEffectSupports(effects, factId, /*negated=*/true);
    EffectSupports positiveEffectSupports = findEffectSupports(effects, factId, /*negated=*/false);
    const bool factCannotChange = negativeEffectSupports.empty() && positiveEffectSupports.empty();

    int destinationFactVar = destination.getVariableOrZero(VarType::FACT, fact);

    // Decide on the fact variable to use (reuse or encode)
    if (destinationFactVar == 0) {
        if (factCannotChange) {
            destinationFactVar = sourceFactVar;
            destination.setVariable(VarType::FACT, fact, sourceFactVar);
        } else {
            destinationFactVar = _vars.getOrCreateVariable(VarType::FACT, destination, fact);
        }
    }

    // Both states share the same variable, so the fact cannot change.
    if (sourceFactVar == destinationFactVar) return;

    // This destination variable already has equivalent frame clauses from its
    // previously encoded incoming transition.
    if (skipRedundantFrameAxioms && env.reuseFactsFrom->hasVariable(VarType::FACT, fact)) return;

    // An abstract-only position cannot be selected in a primitive plan. Its
    // concrete state transition will be encoded after it is expanded.
    if (!sourceHasPrimitiveCandidates) return;

    struct FactChange {
        int sourceLiteral;
        int destinationLiteral;
        bool makesFactTrue;
        EffectSupports supports;
    };
    const FactChange changes[] = {
        {-sourceFactVar, destinationFactVar, false, negativeEffectSupports},
        {sourceFactVar, -destinationFactVar, true, positiveEffectSupports}
    };

    for (const FactChange& change : changes) {
        std::vector<int> cls = {change.sourceLiteral, change.destinationLiteral};
        if (!change.supports.empty()) {
            std::vector<int> headerLits = cls;
            // Non-primitiveness wildcard
            if (!nonprimFactSupport && sourceVarPrim != 0) cls.push_back(-sourceVarPrim);

            if (_mutex_groups != nullptr && change.makesFactTrue && _mutex_groups->containsFact(fact)) {
                positiveFacts.insert(fact);
            }

            // INDIRECT support
            if (change.supports.indirect != nullptr) {
                for (auto& [op, tree] : *change.supports.indirect) {
                    // Skip if the operation is already a DIRECT support for the fact
                    if (change.supports.direct != nullptr && change.supports.direct->count(op)) continue;

                    // Encode substitutions enabling indirect support for this fact
                    int opVar = source.getVariableOrZero(VarType::OP, op);
                    USignature virtOp(_htn.getRepetitionNameOfAction(op._name_id), op._args);
                    int virtOpVar = source.getVariableOrZero(VarType::OP, virtOp);
                    if (opVar != 0) {
                        cls.push_back(opVar);
                        encodeIndirectFrameAxioms(headerLits, opVar, tree);
                    }
                    if (virtOpVar != 0) {
                        cls.push_back(virtOpVar);
                        encodeIndirectFrameAxioms(headerLits, virtOpVar, tree);
                    }
                }
            }
            // DIRECT support
            if (change.supports.direct != nullptr) for (const USignature& opSig : *change.supports.direct) {
                int opVar = source.getVariableOrZero(VarType::OP, opSig);
                if (opVar != 0) cls.push_back(opVar);
                USignature virt = opSig.renamed(_htn.getRepetitionNameOfAction(opSig._name_id));
                int virtOpVar = source.getVariableOrZero(VarType::OP, virt);
                if (virtOpVar != 0) cls.push_back(virtOpVar);
            }
        }
        _sat.addClause(cls);
    }
}

void Encoding::encodeIndirectFrameAxioms(const std::vector<int>& headerLits, int opVar, const IntPairTree& tree) {
       
    // Unconditional effect?
    if (tree.containsEmpty()) return;

    _stats.begin(STAGE_INDIRECTFRAMEAXIOMS);
            
    // Transform header and tree into a set of clauses
    for (const auto& cls : tree.encode()) {
        for (int lit : headerLits) _sat.appendClause(lit);
        _sat.appendClause(-opVar);
        for (const auto& [src, dest] : cls) {
            _sat.appendClause((src<0 ? -1 : 1) * _vars.getOrCreateSubstitutionVariable(std::abs(src), dest));
        }
        _sat.endClause();
    }
    
    _stats.end(STAGE_INDIRECTFRAMEAXIOMS);
}

void Encoding::encodeOperationConstraints(Position& newPos) {
    std::vector<int> operationVars;
    operationVars.reserve(newPos.getActions().size() + newPos.getReductions().size());

    encodeActionConstraints(newPos, operationVars);
    encodeReductionConstraints(newPos, operationVars);

    encodeOperationSelection(operationVars);
}

void Encoding::encodeActionConstraints(Position& pos, std::vector<int>& operationVars) {
    _stats.begin(STAGE_ACTIONCONSTRAINTS);
    for (const USignature& action : pos.getActions()) {
        const int actionVar = _vars.getVariable(VarType::OP, pos, action);
        operationVars.push_back(actionVar);
        
        if (_htn.isActionRepetition(action._name_id)) continue;

        for (int argument : action._args) encodeSubstitutionVars(action, actionVar, argument);

        for (const Signature& precondition : _htn.getOpTable().getAction(action).getPreconditions()) {
            if (!_vars.hasVariable(VarType::FACT, pos, precondition._usig)) continue;
            const int factVar = _vars.getVariable(VarType::FACT, pos, precondition._usig);
            _sat.addClause(-actionVar, (precondition._negated ? -1 : 1) * factVar);
        }
    }
    _stats.end(STAGE_ACTIONCONSTRAINTS);
}

void Encoding::encodeReductionConstraints(Position& pos, std::vector<int>& operationVars) {
    _stats.begin(STAGE_REDUCTIONCONSTRAINTS);
    for (const USignature& reduction : pos.getReductions()) {
        const int reductionVar = _vars.getVariable(VarType::OP, pos, reduction);
        operationVars.push_back(reductionVar);

        for (int argument : reduction._args) encodeSubstitutionVars(reduction, reductionVar, argument);

        for (const Signature& precondition : _htn.getOpTable().getReduction(reduction).getPreconditions()) {
            if (!_vars.hasVariable(VarType::FACT, pos, precondition._usig)) continue;
            const int factVar = _vars.getVariable(VarType::FACT, pos, precondition._usig);
            _sat.addClause(-reductionVar, (precondition._negated ? -1 : 1) * factVar);
        }
    }
    _stats.end(STAGE_REDUCTIONCONSTRAINTS);
}

void Encoding::encodeOperationSelection(const std::vector<int>& operationVars) {
    if (operationVars.empty()) return;

    // A sole candidate must occur. With multiple candidates, other encoding
    // constraints provide occurrence; this function only makes them exclusive.
    if (operationVars.size() == 1) {
        _stats.begin(STAGE_ATLEASTONEELEMENT);
        _sat.addClause(operationVars.front());
        _stats.end(STAGE_ATLEASTONEELEMENT);
        return;
    }

    if ((int)operationVars.size() >= _params.getIntParam("bamot")) {
        // Binary at-most-one

        _stats.begin(STAGE_ATMOSTONEELEMENT);
        auto bamo = BinaryAtMostOne(operationVars, operationVars.size()+1, _variable_allocator);
        for (const auto& c : bamo.encode()) _sat.addClause(c);
        _stats.end(STAGE_ATMOSTONEELEMENT);

    } else {
        // Naive at-most-one

        _stats.begin(STAGE_ATMOSTONEELEMENT);
        for (size_t i = 0; i < operationVars.size(); i++) {
            for (size_t j = i+1; j < operationVars.size(); j++) {
                _sat.addClause(-operationVars[i], -operationVars[j]);
            }
        }
        _stats.end(STAGE_ATMOSTONEELEMENT);
    }
}

void Encoding::encodeSubstitutionVars(const USignature& opSig, int opVar, int arg) {
    if (!_htn.isQConstant(arg)) return;

    std::optional<std::vector<int>> domain = _htn.takeQConstantDomainForOperation(arg, opSig);
    if (!domain) return;

    std::vector<int> substitutionVars;
    substitutionVars.reserve(domain->size());
    for (int c : *domain) {
        assert(!_htn.isVariable(c));

        // either of the possible substitutions must be chosen
        int varSubst = _vars.getOrCreateSubstitutionVariable(arg, c);
        substitutionVars.push_back(varSubst);
    }
    assert(!substitutionVars.empty());

    // AT LEAST ONE substitution, or the parent op does NOT occur
    _sat.appendClause(-opVar);
    for (int vSub : substitutionVars) _sat.appendClause(vSub);
    _sat.endClause();

    // AT MOST ONE substitution
    if ((int)substitutionVars.size() >= _params.getIntParam("bamot")) {
        // Binary at-most-one
        auto bamo = BinaryAtMostOne(substitutionVars, substitutionVars.size()+1, _variable_allocator);
        for (const auto& c : bamo.encode()) _sat.addClause(c);
    } else {
        // Naive at-most-one
        for (int vSub1 : substitutionVars) {
            for (int vSub2 : substitutionVars) {
                if (vSub1 < vSub2) _sat.addClause(-vSub1, -vSub2);
            }
        }
    }
}

void Encoding::encodeQFactSemantics(Position& pos, const Encoding::EncodingEnvironment& env, const USigSet& newlyCreatedQFacts) {
    const StateQFacts stateQFacts = collectStateQFacts(pos, env.incoming);
    const StateQFacts reusedStateQFacts = env.reuseFactsFrom == nullptr
            ? StateQFacts()
            : collectStateQFacts(*env.reuseFactsFrom, env.reusePredecessor);

    _stats.begin(STAGE_QFACTSEMANTICS);
    encodeQFactSemanticsWithReuseFiltering(pos, env, stateQFacts, reusedStateQFacts, newlyCreatedQFacts);
    _stats.end(STAGE_QFACTSEMANTICS);
}

void Encoding::encodeIncomingEffectQFactSemantics(Position& pos, const Encoding::EncodingEnvironment& env, const USigSet& newlyCreatedQFacts) {
    assert(env.incoming != nullptr);

    StateQFacts effectQFacts;
    effectQFacts.add(env.incoming->getOutgoingEffects());

    _stats.begin(STAGE_QFACTSEMANTICS);
    if (_use_sibylsat_expansion) {
        // A newly expanded predecessor may contain an aar repetition action.
        // Its effect decodings belong to this new transition and must be encoded.
        encodeAllQFactSemantics(pos, effectQFacts);
    } else {
        const StateQFacts reusedStateQFacts = env.reuseFactsFrom == nullptr
                ? StateQFacts()
                : collectStateQFacts(*env.reuseFactsFrom, env.reusePredecessor);
        encodeQFactSemanticsWithReuseFiltering(pos, env, effectQFacts, reusedStateQFacts, newlyCreatedQFacts);
    }
    _stats.end(STAGE_QFACTSEMANTICS);
}

void Encoding::encodeQFactSemanticsWithReuseFiltering(Position& pos, const Encoding::EncodingEnvironment& env, const StateQFacts& stateQFacts, const StateQFacts& reusedStateQFacts, const USigSet& newlyCreatedQFacts) {
    std::vector<int> substitutionVars;
    substitutionVars.reserve(128);
    for (const USignature& qfactSig : stateQFacts.qFacts) {
        assert(_htn.hasQConstants(qfactSig));
        
        const int qfactVar = _vars.getVariable(VarType::FACT, pos, qfactSig);

        for (int sign = -1; sign <= 1; sign += 2) {
            const bool negated = sign < 0;
            if (!stateQFacts.hasDecodings(qfactSig, negated)) continue;
            
            for (const USignature& decFactSig : stateQFacts.getDecodings(qfactSig, negated)) {
                if (!newlyCreatedQFacts.count(qfactSig)
                        && isQFactDecodingAlreadyEncoded(env, reusedStateQFacts, qfactSig, decFactSig, negated, qfactVar)) {
                    continue;
                }
                encodeQFactDecoding(pos, qfactSig, qfactVar, decFactSig, negated, substitutionVars);
            }
        }
    }
}

bool Encoding::isQFactDecodingAlreadyEncoded(const Encoding::EncodingEnvironment& env, const StateQFacts& reusedStateQFacts, const USignature& qfact, const USignature& decoding, bool negated, int qfactVar) const {
    // When the destination reuses a fact variable, only decodings that were not
    // present in the reused state need new semantic clauses.
    if (env.reuseFactsFrom != nullptr
            && env.reuseFactsFrom->getVariableOrZero(VarType::FACT, qfact) == qfactVar
            && reusedStateQFacts.hasDecodings(qfact, negated)) {
        return reusedStateQFacts.getDecodings(qfact, negated).count(decoding);
    }

    // A variable shared with the incoming state already has all of that state's
    // decoding semantics attached to it.
    return env.incoming != nullptr
            && env.incoming->getVariableOrZero(VarType::FACT, qfact) == qfactVar;
}

void Encoding::encodeAllQFactSemantics(Position& pos, const StateQFacts& stateQFacts) {
    std::vector<int> substitutionVars;
    substitutionVars.reserve(128);
    for (const USignature& qfact : stateQFacts.qFacts) {
        assert(_htn.hasQConstants(qfact));
        const int qfactVar = _vars.getVariable(VarType::FACT, pos, qfact);

        for (const bool negated : {true, false}) {
            if (!stateQFacts.hasDecodings(qfact, negated)) continue;
            for (const USignature& decoding : stateQFacts.getDecodings(qfact, negated)) {
                encodeQFactDecoding(pos, qfact, qfactVar, decoding, negated, substitutionVars);
            }
        }
    }
}

void Encoding::encodeQFactDecoding(Position& pos, const USignature& qfact, int qfactVar, const USignature& decoding, bool negated, std::vector<int>& substitutionVars) {
    const int decodingVar = pos.getVariableOrZero(VarType::FACT, decoding);
    if (decodingVar == 0) return;

    for (size_t argumentIndex = 0; argumentIndex < qfact._args.size(); argumentIndex++) {
        if (qfact._args[argumentIndex] != decoding._args[argumentIndex]) {
            substitutionVars.push_back(_vars.getOrCreateSubstitutionVariable(qfact._args[argumentIndex], decoding._args[argumentIndex]));
        }
    }

    for (int substitutionVar : substitutionVars) _sat.appendClause(-substitutionVar);
    const int sign = negated ? -1 : 1;
    _sat.appendClause(-sign * qfactVar, sign * decodingVar);
    _sat.endClause();
    substitutionVars.clear();
}

void Encoding::encodeEffects(Position& source, Position& destination) {
    const bool useTreeConversion = _params.isNonzero("tc");
    _stats.begin(STAGE_ACTIONEFFECTS);
    for (const USignature& action : source.getActions()) {
        if (_htn.isActionRepetition(action._name_id)) continue;
        const int actionVar = _vars.getVariable(VarType::OP, source, action);
        encodeActionEffects(action, actionVar, destination, useTreeConversion);
    }
    _stats.end(STAGE_ACTIONEFFECTS);
}

void Encoding::encodeActionEffects(const USignature& action, int actionVar, Position& destination, bool useTreeConversion) {
    const SigSet& effects = _htn.getOpTable().getAction(action).getEffects();
    for (const Signature& effect : effects) {
        const int factVar = destination.getVariableOrZero(VarType::FACT, effect._usig);
        if (factVar == 0) continue;

        if (!effect._negated) {
            _sat.addClause(-actionVar, factVar);
            continue;
        }

        PositiveEffectUnifiers unifiers = findPositiveEffectUnifiers(effect, effects, destination);
        if (unifiers.unconditional) continue;
        if (unifiers.alternatives.empty()) {
            _sat.addClause(-actionVar, -factVar);
            continue;
        }

        encodeConditionalNegativeEffect(actionVar, factVar, unifiers.alternatives, useTreeConversion);
    }
}

Encoding::PositiveEffectUnifiers Encoding::findPositiveEffectUnifiers(const Signature& negativeEffect, const SigSet& effects, const Position& destination) {
    PositiveEffectUnifiers result;
    for (const Signature& positiveEffect : effects) {
        if (positiveEffect._negated) continue;
        if (positiveEffect._usig._name_id != negativeEffect._usig._name_id) continue;
        if (!_vars.hasVariable(VarType::FACT, destination, positiveEffect._usig)) continue;

        std::optional<EffectUnifier> unifier = findEffectUnifier(negativeEffect, positiveEffect);
        if (!unifier) continue;
        if (unifier->empty()) {
            result.unconditional = true;
            break;
        }
        result.alternatives.insert(std::move(*unifier));
    }
    return result;
}

std::optional<Encoding::EffectUnifier> Encoding::findEffectUnifier(const Signature& first, const Signature& second) {
    EffectUnifier unifier;
    for (size_t argumentIndex = 0; argumentIndex < first._usig._args.size(); argumentIndex++) {
        const int firstArgument = first._usig._args[argumentIndex];
        const int secondArgument = second._usig._args[argumentIndex];
        if (firstArgument == secondArgument) continue;

        const bool firstIsQConstant = _htn.isQConstant(firstArgument);
        const bool secondIsQConstant = _htn.isQConstant(secondArgument);
        if (firstIsQConstant && secondIsQConstant) {
            unifier.insert(encodeQConstEquality(firstArgument, secondArgument));
        } else if (firstIsQConstant && _htn.getDomainOfQConstant(firstArgument).count(secondArgument)) {
            unifier.insert(_vars.getOrCreateSubstitutionVariable(firstArgument, secondArgument));
        } else if (secondIsQConstant && _htn.getDomainOfQConstant(secondArgument).count(firstArgument)) {
            unifier.insert(_vars.getOrCreateSubstitutionVariable(secondArgument, firstArgument));
        } else {
            return std::nullopt;
        }
    }
    return unifier;
}

void Encoding::encodeConditionalNegativeEffect(int actionVar, int factVar, const EffectUnifierDnf& unifiers, bool useTreeConversion) {
    if (useTreeConversion) {
        LiteralTree<int> tree;
        for (const EffectUnifier& unifier : unifiers) tree.insert(std::vector<int>(unifier.begin(), unifier.end()));
        for (const std::vector<int>& clause : tree.encode({actionVar, factVar})) _sat.addClause(clause);
        return;
    }

    std::vector<int> dnf;
    for (const EffectUnifier& unifier : unifiers) {
        dnf.insert(dnf.end(), unifier.begin(), unifier.end());
        dnf.push_back(0);
    }
    for (const auto& clause : Dnf2Cnf::getCnf(dnf)) {
        _sat.appendClause(-actionVar, -factVar);
        for (int literal : clause) _sat.appendClause(literal);
        _sat.endClause();
    }
}

void Encoding::encodeQConstraints(Position& pos) {
    encodeQConstantTypeConstraints(pos);
    encodeSubstitutionConstraints(pos);
}

void Encoding::encodeQConstantTypeConstraints(Position& pos) {
    _stats.begin(STAGE_QTYPECONSTRAINTS);
    const auto& constraintsByOperation = pos.getQConstantsTypeConstraints();
    for (const auto& [operation, constraints] : constraintsByOperation) {
        const int operationVar = pos.getVariableOrZero(VarType::OP, operation);
        if (operationVar == 0) continue;

        for (const TypeConstraint& constraint : constraints) {
            const int qconstant = constraint.qconstant;
            assert(_htn.isQConstant(qconstant));

            if (constraint.sign) {
                // The operation requires one of the allowed substitutions.
                _sat.appendClause(-operationVar);
                for (int constant : constraint.constants) {
                    _sat.appendClause(_vars.getOrCreateSubstitutionVariable(qconstant, constant));
                }
                _sat.endClause();
            } else {
                // The operation excludes every forbidden substitution.
                for (int constant : constraint.constants) {
                    _sat.addClause(-operationVar, -_vars.getOrCreateSubstitutionVariable(qconstant, constant));
                }
            }
        }
    }
    _stats.end(STAGE_QTYPECONSTRAINTS);
}

void Encoding::encodeSubstitutionConstraints(Position& pos) {
    _stats.begin(STAGE_SUBSTITUTIONCONSTRAINTS);
    encodeSubstitutionConstraintsForOperations(pos, pos.getActions());
    encodeSubstitutionConstraintsForOperations(pos, pos.getReductions());
    pos.clearSubstitutions();
    _stats.end(STAGE_SUBSTITUTIONCONSTRAINTS);
}

void Encoding::encodeSubstitutionConstraintsForOperations(Position& pos, const USigSet& operations) {
    const auto& constraintsByOperation = pos.getSubstitutionConstraints();
    for (const USignature& operation : operations) {
        auto constraintIt = constraintsByOperation.find(operation);
        if (constraintIt == constraintsByOperation.end()) continue;
        
        const int operationVar = _vars.getVariable(VarType::OP, pos, operation);
        for (const SubstitutionConstraint& constraint : constraintIt->second) {
            const SubstitutionConstraint::Representation representation = constraint.getRepresentation();
            for (const auto& clause : constraint.getEncoding()) {
                _sat.appendClause(-operationVar);
                for (const auto& [qArg, decArg] : clause) {
                    const bool negated = qArg < 0;
                    _sat.appendClause((representation == SubstitutionConstraint::FORBIDDEN_ASSIGNMENTS ? -1 : (negated ? -1 : 1))
                            * _vars.getOrCreateSubstitutionVariable(std::abs(qArg), decArg));
                }
                _sat.endClause();
            }
        }
    }
}

void Encoding::encodeSubtaskRelationships(Position& pos, const Encoding::EncodingEnvironment& env) {

    if (pos.getActions().size() == 1 && pos.getReductions().empty()
            && pos.hasAction(_htn.getBlankActionSig()) && !_use_sibylsat_expansion) {
        // This position contains the blank action and nothing else.
        // No subtask relationships need to be encoded.
        return;
    }

    if (env.parent == nullptr) return;

    encodeExpansionRelationships(pos, *env.parent);
    if (_params.isNonzero("p")) encodePredecessorRelationships(pos, *env.parent);
}

void Encoding::encodeExpansionRelationships(Position& pos, Position& parentPosition) {
    _stats.begin(STAGE_EXPANSIONS);
    for (const auto& [parentOperation, children] : pos.getExpansions()) {
        const int parentVar = _vars.getVariable(VarType::OP, parentPosition, parentOperation);
        _sat.appendClause(-parentVar);
        for (const USignature& child : children) {
            assert(child != Sig::NONE_SIG);
            _sat.appendClause(_vars.getVariable(VarType::OP, pos, child));
        }
        _sat.endClause();

        encodeExpansionSubstitutions(pos, parentOperation, parentVar);
    }
    _stats.end(STAGE_EXPANSIONS);
}

void Encoding::encodeExpansionSubstitutions(Position& pos, const USignature& parentOperation, int parentVar) {
    const auto& substitutionsByParent = pos.getExpansionSubstitutions();
    auto parentIt = substitutionsByParent.find(parentOperation);
    if (parentIt == substitutionsByParent.end()) return;

    for (const auto& [child, substitution] : parentIt->second) {
        const int childVar = pos.getVariableOrZero(VarType::OP, child);
        if (childVar == 0) continue;

        for (const auto& [sourceArgument, childQConstant] : substitution) {
            assert(_htn.isQConstant(childQConstant));

            // The child's Q-constant may have a wider domain than the parent
            // argument, so selecting both operations links their values.
            const int matchingValue = _htn.isQConstant(sourceArgument)
                    ? encodeQConstEquality(childQConstant, sourceArgument)
                    : _vars.getOrCreateSubstitutionVariable(childQConstant, sourceArgument);
            _sat.addClause(-parentVar, -childVar, matchingValue);
        }
    }
}

void Encoding::encodePredecessorRelationships(Position& pos, Position& parentPosition) {
    _stats.begin(STAGE_PREDECESSORS);
    for (const auto& [child, parentOperations] : pos.getPredecessors()) {
        _sat.appendClause(-_vars.getVariable(VarType::OP, pos, child));
        for (const USignature& parentOperation : parentOperations) {
            _sat.appendClause(_vars.getVariable(VarType::OP, parentPosition, parentOperation));
        }
        _sat.endClause();
    }
    _stats.end(STAGE_PREDECESSORS);
}

int Encoding::encodeQConstEquality(int q1, int q2) {

    if (!_vars.hasQConstantEqualityVariable(q1, q2)) {
        
        _stats.begin(STAGE_QCONSTEQUALITY);
        FlatHashSet<int> good, bad1, bad2;
        for (int c : _htn.getDomainOfQConstant(q1)) {
            if (!_htn.getDomainOfQConstant(q2).count(c)) bad1.insert(c);
            else good.insert(c);
        }
        for (int c : _htn.getDomainOfQConstant(q2)) {
            if (_htn.getDomainOfQConstant(q1).count(c)) continue;
            bad2.insert(c);
        }
        int varEq = _vars.createQConstantEqualityVariable(q1, q2);
        if (good.empty()) {
            // Domains are incompatible -- equality never holds
            _sat.addClause(-varEq);
        } else {
            // If equality, then all "good" substitution vars are equivalent
            for (int c : good) {
                int v1 = _vars.getOrCreateSubstitutionVariable(q1, c);
                int v2 = _vars.getOrCreateSubstitutionVariable(q2, c);
                _sat.addClause(-varEq, v1, -v2);
                _sat.addClause(-varEq, -v1, v2);
            }
            // If any of the GOOD ones, then equality
            for (int c : good) _sat.addClause(-_vars.getOrCreateSubstitutionVariable(q1, c), -_vars.getOrCreateSubstitutionVariable(q2, c), varEq);
            // If any of the BAD ones, then inequality
            for (int c : bad1) _sat.addClause(-_vars.getOrCreateSubstitutionVariable(q1, c), -varEq);
            for (int c : bad2) _sat.addClause(-_vars.getOrCreateSubstitutionVariable(q2, c), -varEq);
        }
        _stats.end(STAGE_QCONSTEQUALITY);
    }
    return _vars.getQConstantEqualityVariable(q1, q2);
}

void Encoding::addAssumptionsPrimPlan(bool permanent, int assumptions_until) {
    _stats.begin(STAGE_ASSUMPTIONS);
    for (size_t pos = 0; pos < _leaf_positions.size(); pos++) {
        if (pos == assumptions_until) break;
        
        int v = _vars.getPrimitiveVariableOrZero(*_leaf_positions[pos]);
        if (v != 0) {
            if (permanent) _sat.addClause(v);
            else _sat.assume(v);
        }
    }
    _stats.end(STAGE_ASSUMPTIONS);
}

void Encoding::encodeMutexPredicates(Position& pos, const Encoding::EncodingEnvironment& env, const USigSet& possibleEffects) {
    assert(_mutex_groups != nullptr);
    _stats.begin(STAGE_MUTEX);
    std::vector<int> mutexFactVars;
    FlatHashSet<int> encodedGroupIds;

    if (env.reuseFactsFrom != nullptr) {
        const FlatHashSet<int>& reusedGroupIds = env.reuseFactsFrom->getGroupMutexEncoded();
        encodedGroupIds.insert(reusedGroupIds.begin(), reusedGroupIds.end());
    }

    // Only groups containing a fact that may become true need consideration.
    for (const USignature& fact : possibleEffects) {
        for (int groupId : _mutex_groups->getGroupIdsForFact(fact)) {
            if (encodedGroupIds.count(groupId)) continue;

            mutexFactVars.clear();
            const USigSet& factsInGroup = _mutex_groups->getFactsInGroup(groupId);
            mutexFactVars.reserve(factsInGroup.size());

            bool groupIsFullyDefined = true;
            for (const USignature& groupFact : factsInGroup) {
                const int factVar = pos.getVariableOrZero(VarType::FACT, groupFact);
                if (factVar == 0) {
                    groupIsFullyDefined = false;
                    continue;
                }
                mutexFactVars.push_back(factVar);
            }

            if (mutexFactVars.size() > 1) encodeMutexGroup(mutexFactVars);
            encodedGroupIds.insert(groupId);
            if (groupIsFullyDefined) pos.addGroupMutexEncoded(groupId);
        }
    }
    _stats.end(STAGE_MUTEX);
}

void Encoding::encodeMutexGroup(const std::vector<int>& factVars) {
    constexpr size_t binaryEncodingClauseThreshold = 250000000;
    const bool useBinaryEncoding = (int)factVars.size() >= _params.getIntParam("bamot")
            && _stats._num_cls > binaryEncodingClauseThreshold;

    if (useBinaryEncoding) {
        BinaryAtMostOne encoding(factVars, factVars.size() + 1, _variable_allocator);
        for (const auto& clause : encoding.encode()) _sat.addClause(clause);
        return;
    }

    for (size_t first = 0; first < factVars.size(); first++) {
        for (size_t second = first + 1; second < factVars.size(); second++) {
            _sat.addClause(-factVars[first], -factVars[second]);
        }
    }
}

void Encoding::encodeTransition(Position& source, Position& destination, size_t expansionIteration) {
    Encoding::EncodingEnvironment env = buildExistingTransitionEnvironment(source, destination, expansionIteration);
    encodeGroundFactTransition(source, destination, env);
    const USigSet newlyCreatedQFacts = encodeQFactVariables(destination, env);

    encodeIncomingEffectQFactSemantics(destination, env, newlyCreatedQFacts);
    encodeEffects(source, destination);
}

std::vector<Encoding::PositionedMethod> Encoding::findMethodAncestorsWithSameName(Position& position, const USignature& method) const {
    std::queue<PositionedMethod> methodsToVisit;
    methodsToVisit.push({&position, method});

    USigSet visitedSignatures;
    visitedSignatures.insert(method);

    std::vector<PositionedMethod> matchingAncestors;
    while (!methodsToVisit.empty()) {
        const PositionedMethod current = methodsToVisit.front();
        methodsToVisit.pop();

        Position* parentPosition = getParentExcludingRoot(*current.position);
        if (parentPosition == nullptr) continue;

        const auto predecessorIt = current.position->getPredecessors().find(current.signature);
        if (predecessorIt == current.position->getPredecessors().end()) continue;

        for (const USignature& predecessor : predecessorIt->second) {
            if (!parentPosition->getReductions().count(predecessor)) continue;

            PositionedMethod ancestor{parentPosition, predecessor};
            if (predecessor._name_id == method._name_id
                    && std::find(matchingAncestors.begin(), matchingAncestors.end(), ancestor) == matchingAncestors.end()) {
                matchingAncestors.push_back(ancestor);
            }

            // Avoid following the same signature repeatedly through recursive
            // ancestry; matching position instances are still collected above.
            if (visitedSignatures.insert(predecessor).second) {
                methodsToVisit.push(ancestor);
            }
        }
    }
    return matchingAncestors;
}

void Encoding::encodeMethodMustDifferFromAncestors(Position& position, const USignature& method, const std::vector<PositionedMethod>& ancestors) {
    const int methodVar = _vars.getVariable(VarType::OP, position, method);

    for (const PositionedMethod& ancestor : ancestors) {
        const int ancestorVar = _vars.getVariable(VarType::OP, *ancestor.position, ancestor.signature);
        std::vector<int> clause{-ancestorVar, -methodVar};
        bool alreadyDifferent = false;

        // If both methods are selected, at least one argument must differ:
        // - different ground arguments already make the methods distinct;
        // - two Q-constants require a negated equality literal;
        // - one Q-constant and one ground argument require a negated substitution literal;
        // - identical arguments require no additional literal.
        for (size_t argIndex = 0; argIndex < method._args.size(); argIndex++) {
            const int methodArg = method._args[argIndex];
            const int ancestorArg = ancestor.signature._args[argIndex];
            if (methodArg == ancestorArg) continue;

            const bool methodArgIsQConstant = _htn.isQConstant(methodArg);
            const bool ancestorArgIsQConstant = _htn.isQConstant(ancestorArg);
            if (!methodArgIsQConstant && !ancestorArgIsQConstant) {
                alreadyDifferent = true;
                break;
            }
            if (methodArgIsQConstant && ancestorArgIsQConstant) {
                clause.push_back(-encodeQConstEquality(methodArg, ancestorArg));
            } else {
                const int qConstant = methodArgIsQConstant ? methodArg : ancestorArg;
                const int groundArgument = methodArgIsQConstant ? ancestorArg : methodArg;
                clause.push_back(-_vars.getOrCreateSubstitutionVariable(qConstant, groundArgument));
            }
        }

        if (alreadyDifferent) continue;
        _sat.addClause(clause);

        // An exact symbolic match already makes the two method variables
        // mutually exclusive, so further ancestor clauses are redundant.
        if (clause.size() == 2) break;
    }
}

void Encoding::encodeRecursiveMethodAncestorDistinctness(Position& position) {
    for (const USignature& method : position.getReductions()) {
        if (!_htn.isRecursiveMethod(method._name_id)) continue;
        if (!_htn.hasQConstants(method)) continue;

        const std::vector<PositionedMethod> ancestors = findMethodAncestorsWithSameName(position, method);
        encodeMethodMustDifferFromAncestors(position, method, ancestors);
    }
}


void Encoding::propagateNewRelevantFacts(Position& source, Position& destination, size_t expansionIteration, const BitVec& newlyRelevantFactIds) {
    if (newlyRelevantFactIds.none()) return;

    Encoding::EncodingEnvironment env = buildRelevantFactPropagationEnvironment(source, destination, expansionIteration);
    encodeFrameAxioms(source, destination, env, &newlyRelevantFactIds);
}
void onClauseLearnt(void* state, int* cls) {
    std::string str = "";
    int i = 0; while (cls[i] != 0) str += std::to_string(cls[i++]) + " ";
    Log::d("LEARNT_CLAUSE %s\n", str.c_str());
}

int Encoding::solve() {
    Log::i("Attempting to solve formula with %i clauses (%i literals) and %i assumptions\n", 
                _stats._num_cls, _stats._num_lits, _stats._num_asmpts);
    
    if (_params.isNonzero("plc"))
        _sat.setLearnCallback(/*maxLength=*/100, this, onClauseLearnt);

    int result = _sat.solve();

    return result;
}

void Encoding::addUnitConstraint(int lit) {
    _stats.begin(STAGE_FORBIDDENOPERATIONS);
    _sat.addClause(lit);
    _stats.end(STAGE_FORBIDDENOPERATIONS);
}

void Encoding::addAssumptionsTasksAccomplished(NodeHashSet<int>& opsAndPredsTrue, bool permanent) {
    for (const int& var : opsAndPredsTrue) {
        if (permanent) _sat.addClause(var);
        else _sat.assume(var);
    }
    if (permanent) {
        // We can clear the set of ops and preds true
        opsAndPredsTrue.clear();
    }
}

void Encoding::clearSoftLits() {
    _sat.clearSoftLits();
}

void Encoding::addSoftLit(int lit, int weight) {
    _sat.addSoftLit(lit, weight);
}

int Encoding::getObjectiveValue() {
    return _sat.getObjectiveValue();
}

void Encoding::writeFormulaFile() {
    if (!_params.isNonzero("wf")) return;
    if (!_params.isNonzero("cs") && !_sat.hasFormulaAssumptions()) addAssumptionsPrimPlan();
    _sat.writeFormulaFile(_variable_allocator.getMaxVariable());
}
