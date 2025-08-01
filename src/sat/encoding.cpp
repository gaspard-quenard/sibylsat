
#include <random>
#include <queue>

#include "sat/encoding.h"
#include "sat/literal_tree.h"
#include "sat/binary_amo.h"
#include "sat/dnf2cnf.h"
#include "util/log.h"
#include "util/timer.h"

void Encoding::encode(size_t layerIdx, size_t pos) {
    _termination_callback();

    _stats.beginPosition();

    _layer_idx = layerIdx;
    _pos = pos;

    // Calculate relevant environment of the position
    Position NULL_POS;
    NULL_POS.setPos(-1, -1);
    Layer& newLayer = *_layers.at(layerIdx);
    Position& newPos = newLayer[pos];
    bool hasLeft = pos > 0;
    Position& left = (hasLeft ? newLayer[pos-1] : NULL_POS);
    bool hasAbove = layerIdx > 0;
    _offset = 0, _old_pos = 0;
    if (hasAbove) {
        const Layer& oldLayer = *_layers.at(layerIdx-1);
        while (_old_pos+1 < oldLayer.size() && oldLayer.getSuccessorPos(_old_pos+1) <= pos) 
            _old_pos++;
        _offset = pos - oldLayer.getSuccessorPos(_old_pos);
    }
    Position& above = (hasAbove ? (*_layers.at(layerIdx-1))[_old_pos] : NULL_POS);
    
    // 1st pass over all operations (actions and reductions): 
    // encode as variables, define primitiveness
    encodeOperationVariables(newPos);

    // Encode true facts at this position and decide for each fact
    // whether to encode it or to reuse the previous variable
    encodeFactVariables(newPos, left, above);

    // 2nd pass over all operations: Init substitution vars where necessary,
    // encode precondition constraints and at-{most,least}-one constraints
    encodeOperationConstraints(newPos);

    // Link qfacts to their possible decodings
    encodeQFactSemantics(newPos);

    // Effects of "old" actions to the left
    if (_pos != 0 && _pos != _new_init_pos) {
        // Encode frame axioms for the left position
        encodeActionEffects(newPos, left);
    }
    

    // Type constraints and forbidden substitutions for q-constants
    // and (sets of) q-facts
    encodeQConstraints(newPos);

    // Expansion and predecessor specification for each element
    // and prohibition of impossible children
    encodeSubtaskRelationships(newPos, above);

    if (_use_sibylsat_expansion && !_optimal) {
        encodePreventionIdenticalSignatureThanParentsForAllMethods(newPos);
    }

    // choice of axiomatic ops
    _stats.begin(STAGE_AXIOMATICOPS);
    const USigSet& axiomaticOps = newPos.getAxiomaticOps();
    if (!axiomaticOps.empty()) {
        for (const USignature& op : axiomaticOps) {
            _sat.appendClause(_vars.getVariable(VarType::OP, newPos, op));
        }
        _sat.endClause();
    }
    _stats.end(STAGE_AXIOMATICOPS);

    _stats.endPosition();
}

void Encoding::encodeOperationVariables(Position& newPos) {

    _primitive_ops.clear();
    _nonprimitive_ops.clear();

    _stats.begin(STAGE_ACTIONCONSTRAINTS);
    for (const auto& aSig : newPos.getActions()) {
        int aVar = _vars.encodeVariable(VarType::OP, newPos, aSig);

        // If the action occurs, the position is primitive
        _primitive_ops.push_back(aVar);
    }
    _stats.end(STAGE_ACTIONCONSTRAINTS);

    _stats.begin(STAGE_REDUCTIONCONSTRAINTS);
    for (const auto& rSig : newPos.getReductions()) {
        int rVar = _vars.encodeVariable(VarType::OP, newPos, rSig);

        bool trivialReduction = _htn.getOpTable().getReduction(rSig).getSubtasks().size() == 0;
        if (trivialReduction) {
            // If a trivial reduction occurs, the position is primitive
            _primitive_ops.push_back(rVar);
        } else {
            // If another reduction occurs, the position is non-primitive
            _nonprimitive_ops.push_back(rVar);
        }
    }
    _stats.end(STAGE_REDUCTIONCONSTRAINTS);

    newPos.setHasPrimitiveOps(!_primitive_ops.empty());
    newPos.setHasNonprimitiveOps(!_nonprimitive_ops.empty());
    
    // Implicit primitiveness?
    if (_implicit_primitiveness) return;

    // Only primitive ops here? -> No primitiveness definition necessary
    if (_nonprimitive_ops.empty()) {
        // Workaround for "x-1" ID assignment of primitivizations
        _vars.skipVariable();
        return;
    }

    int varPrim = _vars.encodeVarPrimitive(newPos.getLayerIndex(), newPos.getPositionIndex());

    _stats.begin(STAGE_REDUCTIONCONSTRAINTS);
    if (_primitive_ops.empty()) {
        // Only non-primitive ops here
        _sat.addClause(-varPrim);
    } else {
        // Mix of primitive and non-primitive ops (default)
        _stats.begin(STAGE_ACTIONCONSTRAINTS);
        for (int aVar : _primitive_ops) _sat.addClause(-aVar, varPrim);
        _stats.end(STAGE_ACTIONCONSTRAINTS);
        for (int rVar : _nonprimitive_ops) _sat.addClause(-rVar, -varPrim);
    }
    _stats.end(STAGE_REDUCTIONCONSTRAINTS);
}

void Encoding::encodeFactVariables(Position& newPos, Position& left, Position& above) {

    _new_fact_vars.clear();

    _stats.begin(STAGE_FACTVARENCODING);

    // Reuse ground fact variables from above position
    if (newPos.getLayerIndex() > 0 && _offset == 0) {
        for (const auto& [factSig, factVar] : above.getVariableTable(VarType::FACT)) {
            if (!_htn.hasQConstants(factSig)) newPos.setVariable(VarType::FACT, factSig, factVar);
        }
    }

    if (_pos == 0 || _pos == _new_init_pos) {
        _new_relevants_facts_to_encode.clear();
        // Encode all relevant definitive facts
        const USigSet* defFacts[] = {&newPos.getTrueFacts(), &newPos.getFalseFacts()};
        bool trueFacts = true;
        for (auto set : defFacts) {for (const auto& fact : *set) {
                if (!newPos.hasVariable(VarType::FACT, fact) && _analysis.isRelevantBitVec(fact, !trueFacts)) {

                    if (_use_sibylsat_expansion) {
                        int var = _vars.encodeVariable(VarType::FACT, newPos, fact);
                        _sat.addClause((trueFacts ? 1 : -1) * var);
                        _new_relevants_facts_to_encode[fact] = var;
                    } else {
                        _new_fact_vars.insert(_vars.encodeVariable(VarType::FACT, newPos, fact));
                    }
                }
            }
            trueFacts = false;
        }
    } else {
        // Encode frame axioms which will assign variables to all ground facts
        // that have some support to change at this position
        encodeFrameAxioms(newPos, left);
    }

    auto reuseQFact = [&](const USignature& qfact, int var, Position& otherPos, bool negated) {
        if (!newPos.hasQFactDecodings(qfact, negated)) return true;
        if (var == 0 || !otherPos.hasQFactDecodings(qfact, negated)
                || otherPos.getQFactDecodings(qfact, negated).size() < newPos.getQFactDecodings(qfact, negated).size())
            return false;
        const auto& otherDecodings = otherPos.getQFactDecodings(qfact, negated);
        for (const auto& decFact : newPos.getQFactDecodings(qfact, negated)) {
            int decFactVar = newPos.getVariableOrZero(VarType::FACT, decFact);
            int otherDecFactVar = otherPos.getVariableOrZero(VarType::FACT, decFact);
            if (decFactVar == 0 || otherDecFactVar == 0 
                    || decFactVar != otherDecFactVar 
                    || !otherDecodings.count(decFact)) {
                return false;
            }
        }
        return true;
    };

    // Encode q-facts that are not encoded yet
    for ([[maybe_unused]] const auto& qfact : newPos.getQFacts()) {
        if (!newPos.hasQFactDecodings(qfact, true) && !newPos.hasQFactDecodings(qfact, false)) continue;
        // assert(!newPos.hasVariable(VarType::FACT, qfact));
        if (newPos.hasVariable(VarType::FACT, qfact)) continue;

        // Reuse variable from above?
        int aboveVar = above.getVariableOrZero(VarType::FACT, qfact);
        if (_offset == 0 && aboveVar != 0) {
            // Reuse qfact variable from above
            newPos.setVariable(VarType::FACT, qfact, aboveVar);

        } else {
            // Reuse variable from left?
            int leftVar = left.getVariableOrZero(VarType::FACT, qfact);           
            if (reuseQFact(qfact, leftVar, left, true) && reuseQFact(qfact, leftVar, left, false)) {
                // Reuse qfact variable from above
                newPos.setVariable(VarType::FACT, qfact, leftVar);

            } else {
                // Encode new variable
                _new_fact_vars.insert(_vars.encodeVariable(VarType::FACT, newPos, qfact));
            }
        }
    }

    _stats.end(STAGE_FACTVARENCODING);

    // Facts that must hold at this position
    _stats.begin(STAGE_TRUEFACTS);
    const USigSet* cHere[] = {&newPos.getTrueFacts(), &newPos.getFalseFacts()}; 
    bool negated = false;
    for (int i = 0; i < 2; i++) {
        for (const USignature& factSig : *cHere[i]) {
            if (_analysis.isRelevantBitVec(factSig, negated)) {
                int var = newPos.getVariableOrZero(VarType::FACT, factSig);
                if (var == 0) {
                    // Variable is not encoded yet.
                    _sat.addClause((i == 0 ? 1 : -1) * _vars.encodeVariable(VarType::FACT, newPos, factSig));
                } else {
                    // Variable is already encoded. If the variable is new, constrain it.
                    if (_new_fact_vars.count(var)) _sat.addClause((i == 0 ? 1 : -1) * var);
                }
                Log::d("(%i,%i) DEFFACT %s\n", _layer_idx, _pos, TOSTR(factSig));
            }
        }
        negated = true;
    }
    _stats.end(STAGE_TRUEFACTS);
}

void Encoding::encodeFrameAxioms(Position& newPos, Position& left, bool onlyForNewRelevantsFacts) {
    static Position NULL_POS;

    using SupportsId = const NodeHashMap<int, USigSet>;

    _stats.begin(STAGE_DIRECTFRAMEAXIOMS);

    bool nonprimFactSupport = _params.isNonzero("nps") || _use_sibylsat_expansion;
    bool hasPrimitiveOps = left.hasPrimitiveOps() || _use_sibylsat_expansion;

    int layerIdx = newPos.getLayerIndex();
    int pos = newPos.getPositionIndex();
    int prevVarPrim = _vars.getVarPrimitiveOrZero(layerIdx, pos-1);

    // Check if frame axioms can be skipped because
    // the above position had a superset of operations
    // Position& above = layerIdx > 0 ? _layers[layerIdx-1]->at(_old_pos) : NULL_POS;
    Position& above = newPos.getOriginalLayerIndex() > 0 ? _layers[newPos.getOriginalLayerIndex() - 1]->at(newPos.getAbovePos()) : NULL_POS;
    // Position& leftOfAbove = layerIdx > 0 && _old_pos > 0 ? _layers[layerIdx-1]->at(_old_pos-1) : NULL_POS;
    Position& leftOfAbove = newPos.getOriginalLayerIndex() > 0 && newPos.getAbovePos() > 0 ? _layers[newPos.getOriginalLayerIndex() - 1]->at(newPos.getAbovePos() - 1) : NULL_POS;
    bool skipRedundantFrameAxioms = _params.isNonzero("srfa") && _offset == 0
        && !left.hasNonprimitiveOps() && !leftOfAbove.hasNonprimitiveOps() 
        && left.getActions().size()+left.getReductions().size() <= leftOfAbove.getActions().size()+leftOfAbove.getReductions().size();

    // Retrieve supports from left position
    SupportsId* supp[2] = {&newPos.getNegFactSupportsId(), &newPos.getPosFactSupportsId()};
    IndirectFactSupportMapId* iSupp[2] = {&newPos.getNegIndirectFactSupportsId(), &newPos.getPosIndirectFactSupportsId()};

    // If mutex param is used, prevent incompatible facts from being true at the same time
    USigSet positiveFacts;
    // positiveFacts.reserve(left.getVariableTable(VarType::FACT).size());
    positiveFacts.reserve(onlyForNewRelevantsFacts ? _new_relevants_facts_to_encode.size() : left.getVariableTable(VarType::FACT).size());

    if (onlyForNewRelevantsFacts) {
        // Update the variable associated with the facts that are already encoded
        for (const auto& fact: _new_relevants_facts_to_encode) {
            int var = left.getVariableOrZero(VarType::FACT, fact.first);
            if (var != 0) {
                _new_relevants_facts_to_encode[fact.first] = var;
            }
        }
    }

    // Find and encode frame axioms for each applicable fact from the left
    size_t skipped = 0;
    for ([[maybe_unused]] const auto& [fact, var] : onlyForNewRelevantsFacts ? _new_relevants_facts_to_encode : left.getVariableTable(VarType::FACT)) {
        if (_htn.hasQConstants(fact)) continue;

        int factId = _htn.getGroundFactId(fact, true);
        if (factId < 0) {
            Log::e("factId: %i, fact: %s, var: %i\n", factId, TOSTR(fact), var);
            exit(1);
        }
        int oldFactVars[2] = {-var, var};
        const USigSet* dir[2] = {nullptr, nullptr};
        IndirectFactSupportMapEntry* indir[2] = {nullptr, nullptr};

        // Retrieve direct and indirect support for this fact
        bool reuse = true;
        for (int i = 0; i < 2; i++) {
            if (!supp[i]->empty()) { // Direct support
                auto it = supp[i]->find(factId);
                if (it != supp[i]->end()) {
                    dir[i] = &(it->second);
                    reuse = false;
                } 
            }
            if (!iSupp[i]->empty()) { // Indirect support
                auto it = iSupp[i]->find(factId);
                if (it != iSupp[i]->end()) {
                    indir[i] = &(it->second);
                    reuse = false;
                } 
            }
        }

        int factVar = newPos.getVariableOrZero(VarType::FACT, fact);

        // Decide on the fact variable to use (reuse or encode)
        if (factVar == 0) {
            if (reuse) {
                // No support for this fact -- variable can be reused from left
                factVar = var;
                newPos.setVariable(VarType::FACT, fact, var);
            } else {
                // There is some support for this fact -- need to encode new var
                int v = _vars.encodeVariable(VarType::FACT, newPos, fact);
                _new_fact_vars.insert(v);
                factVar = v;
            }
        }

        skipped++;
        // Skip frame axiom encoding if nothing can change
        if (var == factVar) continue; 
        // Skip frame axioms if they were already encoded
        if (skipRedundantFrameAxioms && above.hasVariable(VarType::FACT, fact)) continue;
        // No primitive ops at this position: No need for encoding frame axioms
        if (!hasPrimitiveOps) continue;
        skipped--;

        // Encode general frame axioms for this fact
        int i = -1;
        for (int sign = -1; sign <= 1; sign += 2) {
            i++;
            std::vector<int> cls;
            // Fact change:
            if (oldFactVars[i] != 0) cls.push_back(oldFactVars[i]);
            cls.push_back(-sign*factVar);
            if (dir[i] != nullptr || indir[i] != nullptr) {
                std::vector<int> headerLits = cls;
                // Non-primitiveness wildcard
                if (!nonprimFactSupport) {
                    if (_implicit_primitiveness) {
                        for (int var : _nonprimitive_ops) cls.push_back(var);
                    } else if (prevVarPrim != 0) cls.push_back(-prevVarPrim);
                }

                if (_mutex_predicates && (sign == 1) && (_htn._sas_plus != nullptr && _htn._sas_plus->isInMutexGroup(fact))) {
                    positiveFacts.insert(fact);
                }

                // INDIRECT support
                if (indir[i] != nullptr) {                    
                    for (auto& [op, tree] : *indir[i]) {
                        // Skip if the operation is already a DIRECT support for the fact
                        if (dir[i] != nullptr && dir[i]->count(op)) continue;

                        tree.pruneRedundantPaths();

                        // Encode substitutions enabling indirect support for this fact
                        int opVar = left.getVariableOrZero(VarType::OP, op);
                        USignature virtOp(_htn.getRepetitionNameOfAction(op._name_id), op._args);
                        int virtOpVar = left.getVariableOrZero(VarType::OP, virtOp);
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
                if (dir[i] != nullptr) for (const USignature& opSig : *dir[i]) {
                    int opVar = left.getVariableOrZero(VarType::OP, opSig);
                    if (opVar != 0) cls.push_back(opVar);
                    USignature virt = opSig.renamed(_htn.getRepetitionNameOfAction(opSig._name_id));
                    int virtOpVar = left.getVariableOrZero(VarType::OP, virt);
                    if (virtOpVar != 0) cls.push_back(virtOpVar);
                }
            }
            _sat.addClause(cls);
        }
    }
    _stats.end(STAGE_DIRECTFRAMEAXIOMS);

    Log::d("Skipped %i frame axioms\n", skipped);

    if (_mutex_predicates) {
        // _stats.beginTiming(TimingStage::ENCODING_MUTEXES);
        encodeMutexPredicates(newPos, above, positiveFacts);
        // _stats.endTiming(TimingStage::ENCODING_MUTEXES);
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
            _sat.appendClause((src<0 ? -1 : 1) * _vars.varSubstitution(std::abs(src), dest));
        }
        _sat.endClause();
    }
    
    _stats.end(STAGE_INDIRECTFRAMEAXIOMS);
}

void Encoding::encodeOperationConstraints(Position& newPos) {

    size_t layerIdx = newPos.getLayerIndex();
    size_t pos = newPos.getPositionIndex();

    // Store all operations occurring here, for one big clause ORing them
    std::vector<int> elementVars(newPos.getActions().size() + newPos.getReductions().size(), 0);
    int numOccurringOps = 0;

    _stats.begin(STAGE_ACTIONCONSTRAINTS);
    for (const auto& aSig : newPos.getActions()) {

        int aVar = _vars.getVariable(VarType::OP, newPos, aSig);
        elementVars[numOccurringOps++] = aVar;
        
        if (_htn.isActionRepetition(aSig._name_id)) continue;

        for (int arg : aSig._args) encodeSubstitutionVars(aSig, aVar, arg);

        // Preconditions
        for (const Signature& pre : _htn.getOpTable().getAction(aSig).getPreconditions()) {
            if (!_vars.isEncoded(VarType::FACT, layerIdx, pos, pre._usig)) continue;
            _sat.addClause(-aVar, (pre._negated?-1:1)*_vars.getVariable(VarType::FACT, newPos, pre._usig));
        }
    }
    _stats.end(STAGE_ACTIONCONSTRAINTS);
    _stats.begin(STAGE_REDUCTIONCONSTRAINTS);
    for (const auto& rSig : newPos.getReductions()) {

        int rVar = _vars.getVariable(VarType::OP, newPos, rSig);
        for (int arg : rSig._args) encodeSubstitutionVars(rSig, rVar, arg);
        elementVars[numOccurringOps++] = rVar;

        // Preconditions
        for (const Signature& pre : _htn.getOpTable().getReduction(rSig).getPreconditions()) {
            if (!_vars.isEncoded(VarType::FACT, layerIdx, pos, pre._usig)) continue;
            _sat.addClause(-rVar, (pre._negated?-1:1)*_vars.getVariable(VarType::FACT, newPos, pre._usig));
        }
    }
    _stats.end(STAGE_REDUCTIONCONSTRAINTS);

    _q_constants.insert(_new_q_constants.begin(), _new_q_constants.end());
    _new_q_constants.clear();
    
    if (numOccurringOps == 0) return;

    if ((int)elementVars.size() >= _params.getIntParam("bamot")) {
        // Binary at-most-one

        _stats.begin(STAGE_ATMOSTONEELEMENT);
        auto bamo = BinaryAtMostOne(elementVars, elementVars.size()+1);
        for (const auto& c : bamo.encode()) _sat.addClause(c);
        _stats.end(STAGE_ATMOSTONEELEMENT);

    } else {
        // Naive at-most-one

        _stats.begin(STAGE_ATMOSTONEELEMENT);
        for (size_t i = 0; i < elementVars.size(); i++) {
            for (size_t j = i+1; j < elementVars.size(); j++) {
                _sat.addClause(-elementVars[i], -elementVars[j]);
            }
        }
        _stats.end(STAGE_ATMOSTONEELEMENT);
    }
}

void Encoding::encodeSubstitutionVars(const USignature& opSig, int opVar, int arg) {

    if (!_htn.isQConstant(arg)) return;
    if (_q_constants.count(arg)) return;

    // arg is a *new* q-constant: initialize substitution logic
    _new_q_constants.insert(arg);

    std::vector<int> substitutionVars;
    //Log::d("INITSUBVARS @(%i,%i) %s:%s [ ", pos.getLayerIndex(), pos.getPositionIndex(), TOSTR(opSig), TOSTR(arg));
    for (int c : _htn.popOperationDependentDomainOfQConstant(arg, opSig)) {

        assert(!_htn.isVariable(c));

        // either of the possible substitutions must be chosen
        int varSubst = _vars.varSubstitution(arg, c);
        substitutionVars.push_back(varSubst);
        //Log::log_notime(Log::V4_DEBUG, "%s ", TOSTR(sigSubstitute(arg, c)));
    }
    //Log::log_notime(Log::V4_DEBUG, "]\n");
    assert(!substitutionVars.empty());

    // AT LEAST ONE substitution, or the parent op does NOT occur
    _sat.appendClause(-opVar);
    for (int vSub : substitutionVars) _sat.appendClause(vSub);
    _sat.endClause();

    // AT MOST ONE substitution
    if ((int)substitutionVars.size() >= _params.getIntParam("bamot")) {
        // Binary at-most-one
        auto bamo = BinaryAtMostOne(substitutionVars, substitutionVars.size()+1);
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

void Encoding::encodeQFactSemantics(Position& newPos, bool encodeOnlyEffectQFacts) {
    static Position NULL_POS;

    USigSet qfactsEffsFromLeft;
    if (encodeOnlyEffectQFacts) {
        Position& left = _layers[_layer_idx]->at(_pos-1);
        for (const auto& aSig : left.getActions()) {
            if (_htn.isActionRepetition(aSig._name_id)) continue;
            const SigSet& effects = _htn.getOpTable().getAction(aSig).getEffects();
            for (const Signature& eff : effects) {
                if (!_htn.hasQConstants(eff._usig)) continue;
                qfactsEffsFromLeft.insert(eff._usig);
            }
        }
        for (const auto& rSig: left.getReductions()) {
            const SigSet& effects = _htn.getOpTable().getReduction(rSig).getEffects();
            for (const Signature& eff : effects) {
                if (!_htn.hasQConstants(eff._usig)) continue;
                qfactsEffsFromLeft.insert(eff._usig);
            }
        }
    }

    _stats.begin(STAGE_QFACTSEMANTICS);
    std::vector<int> substitutionVars; substitutionVars.reserve(128);
    for (const auto& qfactSig : newPos.getQFacts()) {
        assert(_htn.hasQConstants(qfactSig));

        if (encodeOnlyEffectQFacts && !qfactsEffsFromLeft.count(qfactSig)) continue;
        
        
        int qfactVar = _vars.getVariable(VarType::FACT, newPos, qfactSig);

        for (int sign = -1; sign <= 1; sign += 2) {
            bool negated = sign < 0;
            if (!newPos.hasQFactDecodings(qfactSig, negated)) 
                continue;

            bool filterAbove = false;
            Position& above = _offset == 0 && _layer_idx > 0 ? _layers[_layer_idx-1]->at(_old_pos) : NULL_POS;
            // Carefull here, if we use sibylsat, the above position when we launch this function from 
            // the encodeOnlyEffsAndFrameAxioms function, will be itself. So obviously, it will have the 
            // QFactDecodings for every Q facts of the current position (since it is the same position).
            if (!encodeOnlyEffectQFacts || !_use_sibylsat_expansion) {
                if (!_new_fact_vars.count(qfactVar)) {
                    if (_offset == 0 && _layer_idx > 0 && above.getVariableOrZero(VarType::FACT, qfactSig) == qfactVar
                                    && above.hasQFactDecodings(qfactSig, negated)) {
                        filterAbove = true;

                        /*
                        TODO
                        aar=0 : qfact semantics are added once, then for each further layer
                        they are skipped because they were already encoded.
                        aar=1 : qfact semantics are added once, skipped once, then added again
                        because the qfact (and decodings) do not occur above any more.
                        */

                    }
                    if (!filterAbove && _pos > 0) {
                        Position& left = _layers[_layer_idx]->at(_pos-1);
                        if (left.getVariableOrZero(VarType::FACT, qfactSig) == qfactVar)
                            continue;
                    }
                }
            }
            
            // For each possible fact decoding:
            for (const auto& decFactSig : newPos.getQFactDecodings(qfactSig, negated)) {
                
                int decFactVar = newPos.getVariableOrZero(VarType::FACT, decFactSig);
                if (decFactVar == 0) continue;
                if (filterAbove && above.getQFactDecodings(qfactSig, negated).count(decFactSig)) continue;

                // Assemble list of substitution variables
                for (size_t i = 0; i < qfactSig._args.size(); i++) {
                    if (qfactSig._args[i] != decFactSig._args[i])
                        substitutionVars.push_back(
                            _vars.varSubstitution(qfactSig._args[i], decFactSig._args[i])
                        );
                }
                
                // If the substitution is chosen,
                // the q-fact and the corresponding actual fact are equivalent
                //Log::v("QFACTSEM (%i,%i) %s -> %s\n", _layer_idx, _pos, TOSTR(qfactSig), TOSTR(decFactSig));
                for (const int& varSubst : substitutionVars) {
                    _sat.appendClause(-varSubst);
                }
                _sat.appendClause(-sign*qfactVar, sign*decFactVar);
                _sat.endClause();
                substitutionVars.clear();
            }
        }
    }
    _stats.end(STAGE_QFACTSEMANTICS);
}

void Encoding::encodeActionEffects(Position& newPos, Position& left) {

    bool treeConversion = _params.isNonzero("tc");
    _stats.begin(STAGE_ACTIONEFFECTS);
    for (const auto& aSig : left.getActions()) {
        if (_htn.isActionRepetition(aSig._name_id)) continue;
        int aVar = _vars.getVariable(VarType::OP, left, aSig);

        const SigSet& effects = _htn.getOpTable().getAction(aSig).getEffects();

        for (const Signature& eff : effects) {
            if (!_vars.isEncoded(VarType::FACT, _layer_idx, _pos, eff._usig)) continue;

            std::set<std::set<int>> unifiersDnf;
            bool unifiedUnconditionally = false;
            if (eff._negated) {
                for (const auto& posEff : effects) {
                    if (posEff._negated) continue;
                    if (posEff._usig._name_id != eff._usig._name_id) continue;
                    if (!_vars.isEncoded(VarType::FACT, _layer_idx, _pos, posEff._usig)) continue;

                    bool fits = true;
                    std::set<int> s;
                    for (size_t i = 0; i < eff._usig._args.size(); i++) {
                        const int& effArg = eff._usig._args[i];
                        const int& posEffArg = posEff._usig._args[i];
                        if (effArg != posEffArg) {
                            bool effIsQ = _q_constants.count(effArg);
                            bool posEffIsQ = _q_constants.count(posEffArg);
                            if (effIsQ && posEffIsQ) {
                                s.insert(encodeQConstEquality(effArg, posEffArg));
                            } else if (effIsQ) {
                                if (!_htn.getDomainOfQConstant(effArg).count(posEffArg)) fits = false;
                                else s.insert(_vars.varSubstitution(effArg, posEffArg));
                            } else if (posEffIsQ) {
                                if (!_htn.getDomainOfQConstant(posEffArg).count(effArg)) fits = false;
                                else s.insert(_vars.varSubstitution(posEffArg, effArg));
                            } else fits = false;
                        }
                    }
                    if (fits && s.empty()) {
                        // Empty substitution does the job
                        unifiedUnconditionally = true;
                        break;
                    }
                    if (fits) unifiersDnf.insert(s);
                }
            }
            if (unifiedUnconditionally) continue; // Always unified
            if (unifiersDnf.empty()) {
                // Positive or ununifiable negative effect: enforce it
                _sat.addClause(-aVar, (eff._negated?-1:1)*_vars.getVariable(VarType::FACT, newPos, eff._usig));
                continue;
            }

            // Negative effect which only holds in certain cases
            if (treeConversion) {
                LiteralTree<int> tree;
                for (const auto& set : unifiersDnf) tree.insert(std::vector<int>(set.begin(), set.end()));
                std::vector<int> headerLits;
                headerLits.push_back(aVar);
                headerLits.push_back(_vars.getVariable(VarType::FACT, newPos, eff._usig));
                for (const auto& cls : tree.encode(headerLits)) _sat.addClause(cls);
            } else {
                std::vector<int> dnf;
                for (const auto& set : unifiersDnf) {
                    for (int lit : set) dnf.push_back(lit);
                    dnf.push_back(0);
                }
                auto cnf = Dnf2Cnf::getCnf(dnf);
                for (const auto& clause : cnf) {
                    _sat.appendClause(-aVar, -_vars.getVariable(VarType::FACT, newPos, eff._usig));
                    for (int lit : clause) _sat.appendClause(lit);
                    _sat.endClause();
                }
            }
        }
    }
    _stats.end(STAGE_ACTIONEFFECTS);
}

void Encoding::encodeQConstraints(Position& newPos) {

    // Q-constants type constraints
    _stats.begin(STAGE_QTYPECONSTRAINTS);
    const auto& constraints = newPos.getQConstantsTypeConstraints();
    for (const auto& [opSig, constraints] : constraints) {
        int opVar = newPos.getVariableOrZero(VarType::OP, opSig);
        if (opVar != 0) {
            for (const TypeConstraint& c : constraints) {
                int qconst = c.qconstant;
                bool positiveConstraint = c.sign;
                assert(_q_constants.count(qconst));

                if (positiveConstraint) {
                    // EITHER of the GOOD constants - one big clause
                    _sat.appendClause(-opVar);
                    for (int cnst : c.constants) {
                        _sat.appendClause(_vars.varSubstitution(qconst, cnst));
                    }
                    _sat.endClause();
                } else {
                    // NEITHER of the BAD constants - many 2-clauses
                    for (int cnst : c.constants) {
                        _sat.addClause(-opVar, -_vars.varSubstitution(qconst, cnst));
                    }
                }
            }
        }
    }
    _stats.end(STAGE_QTYPECONSTRAINTS);

    // Forbidden substitutions
    _stats.begin(STAGE_SUBSTITUTIONCONSTRAINTS);

    // For each operation (action or reduction)
    const USigSet* ops[2] = {&newPos.getActions(), &newPos.getReductions()};
    for (const auto& set : ops) for (auto opSig : *set) {

        auto it = newPos.getSubstitutionConstraints().find(opSig);
        if (it == newPos.getSubstitutionConstraints().end()) continue;
        
        for (const auto& c : it->second) {
            auto f = c.getEncoding();
            auto polarity = c.getPolarity();
            for (const auto& cls : f) {
                //std::string out = (polarity == SubstitutionConstraint::ANY_VALID ? "+" : "-") + std::string("SUBSTITUTION ") 
                //        + Names::to_string(opSig) + " ";
                _sat.appendClause(-_vars.getVariable(VarType::OP, newPos, opSig));
                for (const auto& [qArg, decArg] : cls) {
                    bool negated = qArg < 0;
                    //out += (negated ? "-" : "+")
                    //        + Names::to_string(involvedQConsts[idx]) + "/" + Names::to_string(std::abs(lit)) + " ";
                    _sat.appendClause((polarity == SubstitutionConstraint::NO_INVALID ? -1 : (negated ? -1 : 1)) 
                            * _vars.varSubstitution(std::abs(qArg), decArg));
                }
                _sat.endClause();
                //out += "\n";
                //Log::d(out.c_str());
            }
        }
    }
    newPos.clearSubstitutions();
    
    _stats.end(STAGE_SUBSTITUTIONCONSTRAINTS);
}

void Encoding::encodeSubtaskRelationships(Position& newPos, Position& above) {

    if (newPos.getActions().size() == 1 && newPos.getReductions().empty() 
            && newPos.hasAction(_htn.getBlankActionSig()) && !_use_sibylsat_expansion) {
        // This position contains the blank action and nothing else.
        // No subtask relationships need to be encoded.
        return;
    }

    // expansions
    _stats.begin(STAGE_EXPANSIONS);
    for (const auto& [parent, children] : newPos.getExpansions()) {

        int parentVar = _vars.getVariable(VarType::OP, above, parent);
        _sat.appendClause(-parentVar);
        for (const USignature& child : children) {
            assert(child != Sig::NONE_SIG);
            _sat.appendClause(_vars.getVariable(VarType::OP, newPos, child));
        }
        _sat.endClause();

        if (newPos.getExpansionSubstitutions().count(parent)) {
            for (const auto& [child, s] : newPos.getExpansionSubstitutions().at(parent)) {
                int childVar = newPos.getVariableOrZero(VarType::OP, child);
                if (childVar == 0) continue;

                for (const auto& [src, dest] : s) {
                    assert(_htn.isQConstant(dest));

                    // Q-constant dest has a larger domain than (q-)constant src.
                    // Enforce that dest only takes values from the domain of src!
                    //Log::d("DOM %s->%s : Enforce %s only to take values from domain of %s\n", TOSTR(parent), TOSTR(child), TOSTR(dest), TOSTR(src));

                    if (!_htn.isQConstant(src)) {
                        _sat.addClause(-parentVar, -childVar, _vars.varSubstitution(dest, src));
                    } else {
                        _sat.addClause(-parentVar, -childVar, encodeQConstEquality(dest, src));
                    }
                }
            }
        }
    }
    _stats.end(STAGE_EXPANSIONS);

    // predecessors
    if (_params.isNonzero("p")) {
        _stats.begin(STAGE_PREDECESSORS);
        for (const auto& [child, parents] : newPos.getPredecessors()) {

            _sat.appendClause(-_vars.getVariable(VarType::OP, newPos, child));
            for (const USignature& parent : parents) {
                _sat.appendClause(_vars.getVariable(VarType::OP, above, parent));
            }
            _sat.endClause();
        }
        _stats.end(STAGE_PREDECESSORS);
    }
}

int Encoding::encodeQConstEquality(int q1, int q2) {

    if (!_vars.isQConstantEqualityEncoded(q1, q2)) {
        
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
        int varEq = _vars.encodeQConstantEqualityVar(q1, q2);
        if (good.empty()) {
            // Domains are incompatible -- equality never holds
            _sat.addClause(-varEq);
        } else {
            // If equality, then all "good" substitution vars are equivalent
            for (int c : good) {
                int v1 = _vars.varSubstitution(q1, c);
                int v2 = _vars.varSubstitution(q2, c);
                _sat.addClause(-varEq, v1, -v2);
                _sat.addClause(-varEq, -v1, v2);
            }
            // If any of the GOOD ones, then equality
            for (int c : good) _sat.addClause(-_vars.varSubstitution(q1, c), -_vars.varSubstitution(q2, c), varEq);
            // If any of the BAD ones, then inequality
            for (int c : bad1) _sat.addClause(-_vars.varSubstitution(q1, c), -varEq);
            for (int c : bad2) _sat.addClause(-_vars.varSubstitution(q2, c), -varEq);
        }
        _stats.end(STAGE_QCONSTEQUALITY);
    }
    return _vars.getQConstantEqualityVar(q1, q2);
}

void Encoding::addAssumptionsPrimPlan(int layerIdx, bool permanent, int assumptions_until) {
    Layer& l = *_layers.at(layerIdx);
    if (_implicit_primitiveness) {
        _stats.begin(STAGE_ACTIONCONSTRAINTS);
        for (size_t pos = 0; pos < l.size(); pos++) {
            if (pos == assumptions_until) break;
            _sat.appendClause(-_vars.encodeVarPrimitive(layerIdx, pos));
            for (int var : _primitive_ops) _sat.appendClause(var);
            _sat.endClause();
        }
        _stats.end(STAGE_ACTIONCONSTRAINTS);
    }
    _stats.begin(STAGE_ASSUMPTIONS);
    for (size_t pos = 0; pos < l.size(); pos++) {
        if (pos == assumptions_until) break;
        
        int v = _vars.getVarPrimitiveOrZero(layerIdx, pos);
        if (v != 0) {
            if (permanent) _sat.addClause(v);
            else _sat.assume(v);
        }
    }
    _stats.end(STAGE_ASSUMPTIONS);
}

void Encoding::encodeMutexPredicates(Position& pos, Position& above, USigSet& possibleEffects) {
    _stats.begin(STAGE_MUTEX);
    // Encode the SAS+ constrains for this fact
    // Indicate that if this fact is true then all the other facts that are in the same lifted fam ground that this fact must be false
    std::vector<int> mutex;

    FlatHashSet<int> groupsDone;

    if (_offset == 0) {
        // Do not add all the groups already done by the parent if we are the first child (since we will reuse the same predicates)
        for (const int& group_mutex: above.getGroupMutexEncoded()) {
            groupsDone.insert(group_mutex);
        }
    }

    // Would be better to iterate the groups here (todo after)
    for (const USignature& fact : possibleEffects) {

        int factVar = pos.getVariable(VarType::FACT, fact);

        // Get all the group mutex in which this fact is
        for (const int& group_mutex: _htn._sas_plus->getGroupsMutexesOfPred(fact)) {

            if (groupsDone.count(group_mutex)) continue;

            mutex.clear();
            mutex.reserve(_htn._sas_plus->getPredsInGroup(group_mutex).size());
            int num_mutex = 0;

            bool groupIsFullyDefined = true;

            // Iterate over all the predicates in this group
            for (const USignature& factsInGroup: _htn._sas_plus->getPredsInGroup(group_mutex)) {

                // If the fact is not in the positive facts, skip it
                // if (!positiveFacts.count(factsInGroup)) continue;

                // Get the variable of the fact
                int otherFactVar = pos.getVariableOrZero(VarType::FACT, factsInGroup);
                if (otherFactVar == 0) {
                    groupIsFullyDefined = false;
                    continue;
                }

                // Log::i("Encode mutex for %s and %s\n", TOSTR(fact), TOSTR(mutexFact));
                
                mutex[num_mutex] = otherFactVar;
                num_mutex++;
            }

            if (num_mutex <= 1) continue;

            // Encode this mutex group 

            // The solver is a lot slower if we use a binary at most one so we only do it if we have too much clauses already
            if ((int)num_mutex >= _params.getIntParam("bamot") && _stats._num_cls > 250000000) {
                // Binary at-most-one
                auto bamo = BinaryAtMostOne(mutex, num_mutex + 1);
                for (const auto& c : bamo.encode()) _sat.addClause(c);

            } else {
                

                // if (_params.isNonzero("bimander")) {

                //     // Log::i("There are %i mutexes for %s\n", num_mutex, TOSTR(fact));
                //     auto bamo = BimanderAtMostOne(mutex, num_mutex, (size_t) std::sqrt(num_mutex));
                //     for (const auto& c : bamo.encode()) {
                //         _sat.addClause(c);
                //     }
                // } else 
                {
                    // Naive at-most-one
                    for (size_t i = 0; i < num_mutex; i++) {
                        for (size_t j = i+1; j < num_mutex; j++) {
                            _sat.addClause(-mutex[i], -mutex[j]);
                        }
                    }  
                }
            }

            groupsDone.insert(group_mutex);
            if (groupIsFullyDefined) {
                pos.addGroupMutexEncoded(group_mutex);
            }
        }
    }
    _stats.end(STAGE_MUTEX);
}

void Encoding::encodeOnlyEffsAndFrameAxioms(size_t layerIdx, size_t pos) {

    _layer_idx = layerIdx;
    _pos = pos;

    // Calculate relevant environment of the position
    Position NULL_POS;
    NULL_POS.setPos(-1, -1);
    Layer& newLayer = *_layers.at(layerIdx);
    Position& newPos = newLayer[pos];
    bool hasLeft = pos > 0;
    Position& left = (hasLeft ? newLayer[pos-1] : NULL_POS);
    bool hasAbove = layerIdx > 0;
        _offset = 0, _old_pos = 0;
    if (hasAbove) {
        const Layer& oldLayer = *_layers.at(layerIdx-1);
        while (_old_pos+1 < oldLayer.size() && oldLayer.getSuccessorPos(_old_pos+1) <= pos) 
            _old_pos++;
        _offset = pos - oldLayer.getSuccessorPos(_old_pos);
    }
    Position& above = (hasAbove ? (*_layers.at(layerIdx-1))[_old_pos] : NULL_POS);
 
    encodeFactVariables(newPos, left, above);


    // Should add qfact decoding if there is an effect of left that is a qfact (but only for the qfact that are in the effects of all actions in left)
    // Example: ACTION__drive__ID71-truck_0-Q_3-3_location%0_e4354a979566ec9d-city_loc_3__4_4 => not at-truck_0-Q_3-3_location%0_e4354a979566ec9d__4_5
    // Link qfacts to their possible decodings
    
    encodeQFactSemantics(newPos, /*encodeOnlyQFactsEffs=*/true);
    encodeActionEffects(newPos, left);
}

void Encoding::encodePreventionIdenticalSignatureThanParentsForAllMethods(Position& pos) {

    for (const auto& rSig : pos.getReductions()) {
        if (!_htn.isRecursiveMethod(rSig._name_id)) continue;

        // Log::i("Recursive method %s at %d,%d\n", TOSTR(rSig), newPos.getLayerIndex(), newPos.getPositionIndex());

        // If this recursive method does not contains Q-constants, skip it
        if (!_htn.hasQConstants(rSig)) continue;


        // First, find all the possible parents with the same name id

        // Create a queue which will contains all the methods to check
        std::queue<PositionedUSig> methodsToCheck;

        // Add the current method to the queue
        methodsToCheck.push(PositionedUSig(pos.getLayerIndex(), pos.getPositionIndex(), rSig));

        // Get all the parent which are the same method
        PositionUSigSet parents;

        USigSet visited;
        visited.insert(rSig);

        // Iterate the queue until it is empty
        while (!methodsToCheck.empty()) {

            PositionedUSig methodToCheck = methodsToCheck.front();
            methodsToCheck.pop();

            // Get the position idx
            Position& methodPos = _layers.at(methodToCheck.layer)->at(methodToCheck.pos);

            // If the layer is 0, continue
            if (methodToCheck.layer == 0) continue;

            // SHOULD NOT HAPPENENED... BUT I HAVE A BUG HERE...
            // Need to investigate...
            if (!methodPos.getPredecessors().count(methodToCheck.usig)) continue;

            // Iterate over all predecessors
            for (const auto& pred : methodPos.getPredecessors().at(methodToCheck.usig)) {

                // Log::i("Pred: %s\n", TOSTR(pred));

                // Get the last layer and position of the predecessor
                int parentPos = methodPos.getAbovePos();
                int parentLayer = methodPos.getOriginalLayerIndex() - 1;

                if (!_layers.at(parentLayer)->at(parentPos).getReductions().count(pred)) {
                    // Strange bugs, should not happen, but it does sometime (example Hiking problem 1)
                    // Need to invistigate more
                    continue;
                }

                PositionedUSig posPred = PositionedUSig(parentLayer, parentPos, pred);

                // If the predecessor is the same method as the current one, add it to parents
                if (pred._name_id == rSig._name_id) {
                    parents.insert(posPred);
                }

                // Add the predecessor to the queue
                if (!visited.count(posPred.usig)) {
                    methodsToCheck.push(posPred);
                    visited.insert(posPred.usig);
                }
            }
        }

        // Get the variable of the child
        int varNewMethod = _vars.getVariable(VarType::OP, pos, rSig);

        // Ok, now we have to encode the constrains that the new method must be different from all its parents
        for (const auto& parent: parents) {

            // First, check if by default this method is different from its parent 
            // Occurs if both have a ground parameter that are not the same
            bool invarientDifferent = false;
            for (int i = 0; i < rSig._args.size(); i++) {
                if (!_htn.isQConstant(rSig._args[i]) && !_htn.isQConstant(parent.usig._args[i]) && rSig._args[i] != parent.usig._args[i]) {
                    invarientDifferent = true;
                    break;
                }
            }

            if (invarientDifferent) continue;

            bool strictlyEqual = true;
            // Check if all the parameters are identical
            for (int i = 0; i < rSig._args.size(); i++) {
                if (rSig._args[i] != parent.usig._args[i]) {
                    strictlyEqual = false;
                    break;
                }
            }

            if (strictlyEqual) {
                // Add the clause that if the parent is true then this method must be false
                Position& parentPos = _layers.at(parent.layer)->at(parent.pos);
                int varParent = _vars.getVariable(VarType::OP, parentPos, parent.usig);
                _sat.addClause(-varParent, -varNewMethod);
                break;
            }

            // We want to add a clause (parent true AND child true) => OR not(arg1_equal) OR not(arg2_equal) OR ...
            std::vector<int> clause;

            // Add the clause parent and child true => not equal parameters between the two
            Position& parentPos = _layers.at(parent.layer)->at(parent.pos);
            int varParent = _vars.getVariable(VarType::OP, parentPos, parent.usig);
            clause.push_back(-varParent);
            clause.push_back(-varNewMethod);

            // Now, iterate all the paramters of the method
            for (int i = 0; i < rSig._args.size(); i++) {

                // Three cases:
                // Both paramters are Q-constants: needs to create an equalityQConstants
                // Both paramters are not Q-constants: no need to do anything, they are equals by default (or we would have broken on the invariantDifferent)
                // One is a Q-constant and the other is not: needs to get the substitution of the Q-constant and add it to the clause

                if (_htn.isQConstant(rSig._args[i]) && _htn.isQConstant(parent.usig._args[i])) {

                    // If both use the same Q-constant, skip it
                    if (rSig._args[i] == parent.usig._args[i]) continue;

                    // Both paramters are Q-constants: needs to create an equalityQConstants
                    int eq = encodeQConstEquality(rSig._args[i], parent.usig._args[i]);
                    clause.push_back(-eq);
                }
                else if (_htn.isQConstant(rSig._args[i]) || _htn.isQConstant(parent.usig._args[i])) {

                    // Get the substitution vars of the Q-constant to the ground param
                    int varSubt;
                    if (_htn.isQConstant(rSig._args[i])) {
                        varSubt = _vars.varSubstitution(rSig._args[i], parent.usig._args[i]);
                    } else {
                        varSubt = _vars.varSubstitution(parent.usig._args[i], rSig._args[i]);
                    }
                    clause.push_back(-varSubt);
                }
            }

            if (clause.size() == 2) continue;

            // Add the clause
            _sat.addClause(clause);
            
        }
    }
}


void Encoding::encodeNewRelevantsFacts(Position& initPos) {
    int num_relevants_facts = 0;
    _new_relevants_facts_to_encode.clear();
    // Encode all relevant definitive facts
    const USigSet* defFacts[] = {&initPos.getTrueFacts(), &initPos.getFalseFacts()};
    bool trueFacts = true;
    for (const auto& set : defFacts) { 
        for (const auto& fact : *set) {
            if (!initPos.hasVariable(VarType::FACT, fact) && _analysis.isRelevantBitVec(fact, !trueFacts)) {
                int var = _vars.encodeVariable(VarType::FACT, initPos, fact);
                _sat.addClause((trueFacts ? 1 : -1) * var);
                _new_relevants_facts_to_encode[fact] = var;
                num_relevants_facts++;
            }
        }
        trueFacts = false;
    }
    // Log::i("Number of new relevant facts encoded: %d\n", num_relevants_facts);
}


void Encoding::propagateRelevantsFacts(size_t layerIdx, size_t pos) {

    if (_new_relevants_facts_to_encode.empty()) {
        return;
    }

    _layer_idx = layerIdx;
    _pos = pos;

    // Calculate relevant environment of the position
    Position NULL_POS;
    NULL_POS.setPos(-1, -1);
    Layer& newLayer = *_layers.at(layerIdx);
    Position& newPos = newLayer[pos];
    bool hasLeft = pos > 0;
    Position& left = (hasLeft ? newLayer[pos-1] : NULL_POS);
    encodeFrameAxioms(newPos, left, /*onlyForNewRelevantsFacts=*/true);
}



void Encoding::setTerminateCallback(void * state, int (*terminate)(void * state)) {
    _sat.setTerminateCallback(state, terminate);
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

    _sat_call_start_time = Timer::elapsedSeconds();
    int result = _sat.solve();
    _sat_call_start_time = 0;

    _termination_callback();

    return result;
}

void Encoding::addUnitConstraint(int lit) {
    _stats.begin(STAGE_FORBIDDENOPERATIONS);
    _sat.addClause(lit);
    _stats.end(STAGE_FORBIDDENOPERATIONS);
}

float Encoding::getTimeSinceSatCallStart() {
    if (_sat_call_start_time == 0) return 0;
    return Timer::elapsedSeconds() - _sat_call_start_time;
}

void Encoding::printFailedVars(Layer& layer) {
    Log::d("FAILED ");
    for (size_t pos = 0; pos < layer.size(); pos++) {
        int v = _vars.getVarPrimitiveOrZero(layer.index(), pos);
        if (v == 0) continue;
        if (_sat.didAssumptionFail(v)) Log::d("%i ", v);
    }
    Log::d("\n");
}

void Encoding::printSatisfyingAssignment() {
    Log::d("SOLUTION_VALS ");
    for (int v = 1; v <= _vars.getNumVariables(); v++) {
        Log::d("%i ", _sat.holds(v) ? v : -v);
    }
    Log::d("\n");
}

const USignature Encoding::getOpHoldingInLayerPos(int layer, int position) {

    int numOps = 0;

    USignature op = Sig::NONE_SIG;
    //State newState = state;
    for (const auto& [sig, aVar] : _layers[layer]->at(position).getVariableTable(VarType::OP)) {
        if (!_sat.holds(aVar)) continue;

        // Ignore PRIM op
        if (sig._name_id == _htn.nameId("__PRIMITIVE___")) continue;

        op = sig;

        numOps++;

    }

    assert(numOps <= 1);
    return op;
}

void Encoding::printStatementsAtPosition(int layer, int pos) {
    Position& newPos = _layers[layer]->at(pos);
    Position NULL_POS;
    NULL_POS.setPos(-1, -1);
    bool hasLeft = pos > 0;
    Position& left = (hasLeft ? _layers[newPos.getOriginalLayerIndex()]->at(newPos.getOriginalPositionIndex() - 1) : NULL_POS);
    Log::i("STATE AT (%i,%i) (original: %i,%i)\n", layer, pos, newPos.getOriginalLayerIndex(), newPos.getOriginalPositionIndex());
    Layer& l = *_layers[layer];
    Position& p = l[pos];
    for (const auto& [sig, aVar] : p.getVariableTable(VarType::FACT)) {
        if (!_htn.isFullyGround(sig) || _htn.hasQConstants(sig)) continue; // skip non-ground facts)
        if (!_sat.holds(aVar)) continue; // skip false facts
        // Log::i("  FACT %s => %s\n", TOSTR(sig), _sat.holds(aVar) ? "TRUE" : "FALSE");
        Log::i("  FACT %s (%d) => TRUE\n", TOSTR(sig), aVar);
        // Print the value on the left if it is not the same
        if (hasLeft && left.hasVariable(VarType::FACT, sig)) {
            int leftVar = left.getVariableOrZero(VarType::FACT, sig);
            Log::i("    LEFT FACT %s (%d) => %s\n", TOSTR(sig), leftVar, _sat.holds(leftVar) ? "TRUE" : "FALSE");
        }
    }
    // for (const auto& [sig, aVar] : p.getVariableTable(VarType::OP)) {
    //     Log::d("  OP %s => %s\n", TOSTR(sig), _sat.holds(aVar) ? "TRUE" : "FALSE");
    // }
}

const USignature Encoding::getDecodingOpHoldingInLayerPos(int layer, int pos) {

    const USignature origSig = getOpHoldingInLayerPos(layer, pos);
    USignature sig = origSig;
    while (true) {
        bool containsQConstants = false;
        for (int arg : sig._args) if (_htn.isQConstant(arg)) {
            // q constant found
            containsQConstants = true;

            int numSubstitutions = 0;
            for (int argSubst : _htn.getDomainOfQConstant(arg)) {
                const USignature& sigSubst = _vars.sigSubstitute(arg, argSubst);
                if (_vars.isEncodedSubstitution(sigSubst) && _sat.holds(_vars.varSubstitution(arg, argSubst))) {
                    Log::d("SUBSTVAR [%s/%s] TRUE => %s ~~> ", TOSTR(arg), TOSTR(argSubst), TOSTR(sig));
                    numSubstitutions++;
                    Substitution sub;
                    sub[arg] = argSubst;
                    sig.apply(sub);
                    Log::d("%s\n", TOSTR(sig));
                } else {
                    //Log::d("%i FALSE\n", varSubstitution(sigSubst));
                }
            }

            if (numSubstitutions == 0) {
                Log::v("(%i,%i) No substitutions for arg %s of %s\n", layer, pos, TOSTR(arg), TOSTR(origSig));
                return Sig::NONE_SIG;
            }
            assert(numSubstitutions == 1 || Log::e("%i substitutions for arg %s of %s\n", numSubstitutions, TOSTR(arg), TOSTR(origSig)));
        }

        if (!containsQConstants) break; // done
    }

    //if (origSig != sig) Log::d("%s ~~> %s\n", TOSTR(origSig), TOSTR(sig));
    
    return sig;
}

NodeHashSet<int> Encoding::getSnapshotsOpsAndPredsTrue(int untilPos) {

    Layer& layer = *_layers[_layer_idx];
    NodeHashSet<int> snapshotsVarsTrue;

    // First, get for each layer, the limit 
    std::vector<int> limits;
    limits.push_back(untilPos);
    const Position& lastPos = layer[untilPos];

    for (size_t pos = 0; pos < untilPos; pos++) {
        Position& newPos = layer[pos];
        for (const auto& [sig, aVar] : newPos.getVariableTable(VarType::FACT)) {
            if (!_sat.holds(aVar)); // snapshotsVarsTrue.insert(-aVar);
            else snapshotsVarsTrue.insert(aVar);
        }
        for (const auto& [sig, aVar] : newPos.getVariableTable(VarType::OP)) {
            if (!_sat.holds(aVar)); // snapshotsVarsTrue.insert(-aVar);
            else snapshotsVarsTrue.insert(aVar);
        }

        size_t aboveLayer = newPos.getOriginalLayerIndex() - 1;
        size_t abovePos = newPos.getAbovePos();

        while (_layers[aboveLayer]->at(abovePos).getOriginalLayerIndex() != 0) {

            Position& above = _layers[aboveLayer]->at(abovePos);
            
            for (const auto& [sig, aVar] : above.getVariableTable(VarType::FACT)) {
                if (!_sat.holds(aVar)); //snapshotsVarsTrue.insert(-aVar);
                else snapshotsVarsTrue.insert(aVar);
            }
            for (const auto& [sig, aVar] : above.getVariableTable(VarType::OP)) {
                if (!_sat.holds(aVar)); // snapshotsVarsTrue.insert(-aVar);
                else snapshotsVarsTrue.insert(aVar);
            }

            size_t newAboveLayer = above.getOriginalLayerIndex() - 1;
            size_t newAbovePos = above.getAbovePos();
            aboveLayer = newAboveLayer;
            abovePos = newAbovePos;
        }
    }
    return std::move(snapshotsVarsTrue);
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