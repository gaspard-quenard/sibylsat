
#include "position.h"

#include <algorithm>

#include "sat/variable_domain.h"
#include "util/log.h"

void OutgoingEffects::reset(size_t numFacts) {
    _positive_changes = BitVec(numFacts);
    _negative_changes = BitVec(numFacts);
    clearSupports();
    _qfacts.clear();
    clearDecodings();
}

void OutgoingEffects::addFactChange(int factId, bool negated) {
    (negated ? _negative_changes : _positive_changes).set(factId);
}

void OutgoingEffects::addFactChanges(const BitVec& facts, bool negated) {
    (negated ? _negative_changes : _positive_changes).or_with(facts);
}

const BitVec& OutgoingEffects::getFactChanges(bool negated) const {
    return negated ? _negative_changes : _positive_changes;
}

void OutgoingEffects::addSupport(int factId, bool negated, const USignature& operation) {
    std::unique_ptr<DirectFactSupportMap>& supports = negated ? _negative_supports : _positive_supports;
    if (supports == nullptr) {
        supports = std::make_unique<DirectFactSupportMap>();
    }
    (*supports)[factId].insert(operation);
}

void OutgoingEffects::addIndirectSupport(
        int factId,
        bool negated,
        const USignature& operation,
        const std::vector<IntPair>& path) {
    std::unique_ptr<IndirectFactSupportMapId>& supports = negated
            ? _negative_indirect_supports
            : _positive_indirect_supports;
    if (supports == nullptr) {
        supports = std::make_unique<IndirectFactSupportMapId>();
    }
    (*supports)[factId][operation].insert(path);
}

void OutgoingEffects::touchSupport(int factId, bool negated) {
    std::unique_ptr<DirectFactSupportMap>& supports = negated ? _negative_supports : _positive_supports;
    if (supports == nullptr) {
        supports = std::make_unique<DirectFactSupportMap>();
    }
    (*supports)[factId];
}

const DirectFactSupportMap& OutgoingEffects::getSupports(bool negated) const {
    static const DirectFactSupportMap empty;
    const std::unique_ptr<DirectFactSupportMap>& supports = negated ? _negative_supports : _positive_supports;
    return supports == nullptr ? empty : *supports;
}

DirectFactSupportMap& OutgoingEffects::getSupports(bool negated) {
    static DirectFactSupportMap empty;
    std::unique_ptr<DirectFactSupportMap>& supports = negated ? _negative_supports : _positive_supports;
    return supports == nullptr ? empty : *supports;
}

const IndirectFactSupportMapId& OutgoingEffects::getIndirectSupports(bool negated) const {
    static const IndirectFactSupportMapId empty;
    const std::unique_ptr<IndirectFactSupportMapId>& supports = negated
            ? _negative_indirect_supports
            : _positive_indirect_supports;
    return supports == nullptr ? empty : *supports;
}

IndirectFactSupportMapId& OutgoingEffects::getIndirectSupports(bool negated) {
    static IndirectFactSupportMapId empty;
    std::unique_ptr<IndirectFactSupportMapId>& supports = negated
            ? _negative_indirect_supports
            : _positive_indirect_supports;
    return supports == nullptr ? empty : *supports;
}

void OutgoingEffects::addQFact(const USignature& fact) {
    _qfacts.insert(fact);
}

void OutgoingEffects::addQFactDecoding(
        const USignature& fact,
        const USignature& decoding,
        bool negated) {
    auto& decodings = negated ? _negative_qfact_decodings : _positive_qfact_decodings;
    decodings[fact].insert(decoding);
}

bool OutgoingEffects::hasQFactDecodings(const USignature& fact, bool negated) const {
    const auto& decodings = negated ? _negative_qfact_decodings : _positive_qfact_decodings;
    return decodings.count(fact);
}

const USigSet& OutgoingEffects::getQFactDecodings(const USignature& fact, bool negated) const {
    const auto& decodings = negated ? _negative_qfact_decodings : _positive_qfact_decodings;
    assert(decodings.count(fact) || Log::e("No outgoing qfact decodings for %s!\n", TOSTR(fact)));
    return decodings.at(fact);
}

void OutgoingEffects::clearSupports() {
    _positive_supports.reset();
    _negative_supports.reset();
    _positive_indirect_supports.reset();
    _negative_indirect_supports.reset();
}

void OutgoingEffects::clearDecodings() {
    _positive_qfact_decodings.clear();
    _negative_qfact_decodings.clear();
}

void OutgoingEffects::clear() {
    clearSupports();
    _qfacts.clear();
    clearDecodings();
}

// Starts at 1 so that id 0 is reserved for "no/default position" markers.
size_t Position::_next_pos_id = 1;

Position::Position() : _layer_idx(-1), _offset(0) {}
void Position::setPos(size_t layerIdx, size_t pos) {
    _layer_idx = layerIdx;
    // _pos is a stable, globally unique id assigned in the constructor and
    // never modified afterward (used for q-constant naming and logging).
    (void) pos;
}
void Position::setParentPosition(Position* parent) {
    if (_parent_position == parent) return;
    assert(_parent_position == nullptr || _parent_position == parent);
    _parent_position = parent;
    if (parent == nullptr) {
        _offset = 0;
        return;
    }

    auto& siblings = parent->_children_positions;
    auto it = std::find(siblings.begin(), siblings.end(), this);
    if (it == siblings.end()) {
        _offset = siblings.size();
        siblings.push_back(this);
    } else {
        _offset = std::distance(siblings.begin(), it);
    }
}

void Position::addQFact(const USignature& qfact) {
    _qfacts.insert(qfact);
}


void Position::setHasPrimitiveOps(bool has) {
    _has_primitive_ops = has;
}
void Position::setHasNonprimitiveOps(bool has) {
    _has_nonprimitive_ops = has;
}
bool Position::hasPrimitiveOps() {
    return _has_primitive_ops;
}
bool Position::hasNonprimitiveOps() {
    return _has_nonprimitive_ops;
}

void Position::addQConstantTypeConstraint(const USignature& op, const TypeConstraint& c) {
    auto& vec = _q_constants_type_constraints[op];
    vec.push_back(c);
}

void Position::addSubstitutionConstraint(const USignature& op, SubstitutionConstraint&& constr) {
    _substitution_constraints[op].emplace_back(std::move(constr));
}

void Position::addQFactDecoding(const USignature& qFact, const USignature& decFact, bool negated) {
    auto& set = negated ? _neg_qfact_decodings : _pos_qfact_decodings;
    set[qFact].insert(decFact);
    //Log::v("QFACTDEC %s -> %s (%s)\n", TOSTR(qFact), TOSTR(decFact), negated?"false":"true");
}

void Position::removeQFactDecoding(const USignature& qFact, const USignature& decFact, bool negated) {
    auto& set = negated ? _neg_qfact_decodings : _pos_qfact_decodings;
    set[qFact].erase(decFact);
}

bool Position::hasQFactDecodings(const USignature& qFact, bool negated) const {
    auto& set = negated ? _neg_qfact_decodings : _pos_qfact_decodings;
    return set.count(qFact);
}

const USigSet& Position::getQFactDecodings(const USignature& qFact, bool negated) const {
    auto& set = negated ? _neg_qfact_decodings : _pos_qfact_decodings;
    assert(set.count(qFact) || Log::e("No qfact decodings for %s!\n", TOSTR(qFact)));
    return set.at(qFact);
}

void Position::addAction(const USignature& action) {
    _actions.insert(action);
    Log::d("+ACTION@(%i,%i) %s\n", _layer_idx, _pos, TOSTR(action));
}
void Position::addAction(USignature&& action) {
    Log::d("+ACTION@(%i,%i) %s\n", _layer_idx, _pos, TOSTR(action));
    _actions.insert(std::move(action));
}
void Position::addReduction(const USignature& reduction) {
    _reductions.insert(reduction);
    Log::d("+REDUCTION@(%i,%i) %s\n", _layer_idx, _pos, TOSTR(reduction));
}
void Position::addExpansion(const USignature& parent, const USignature& child) {
    auto& set = _expansions[parent];
    set.insert(child);
    auto& pred = _predecessors[child];
    pred.insert(parent);
}
void Position::addExpansionSubstitution(const USignature& parent, const USignature& child, Substitution&& s) {
    _expansion_substitutions[parent][child] = std::move(s);
}
void Position::addExpansionSubstitution(const USignature& parent, const USignature& child, const Substitution& s) {
    _expansion_substitutions[parent][child] = s;
}

void Position::removeActionOccurrence(const USignature& action) {
    _actions.erase(action);
    for (auto& [parent, children] : _expansions) {
        children.erase(action);
    }
    _predecessors.erase(action);
}
void Position::removeReductionOccurrence(const USignature& reduction) {
    _reductions.erase(reduction);
    for (auto& [parent, children] : _expansions) {
        children.erase(reduction);
    }
    _predecessors.erase(reduction);
}
void Position::replaceOperation(const USignature& from, const USignature& to, Substitution&& s) {
    auto predecessors = getPredecessors().at(from);
    removeActionOccurrence(from);
    removeReductionOccurrence(from);
    for (const auto& parent : predecessors) {
        addExpansion(parent, to);
        addExpansionSubstitution(parent, to, s);
    }
}

const NodeHashMap<USignature, int, USignatureHasher>& Position::getVariableTable(VarType type) const {
    return type == OP ? _op_variables : _fact_variables;
}
void Position::setVariableTable(VarType type, const NodeHashMap<USignature, int, USignatureHasher>& table) {
    if (type == OP) {
        _op_variables = table;
    } else {
        _fact_variables = table;
    }
}
void Position::moveVariableTable(VarType type, Position& destination) {
    auto& src = type == OP ? _op_variables : _fact_variables;
    auto& dest = type == OP ? destination._op_variables : destination._fact_variables;
    dest = std::move(src);
    src.clear();
    src.reserve(0);
}

bool Position::hasQFact(const USignature& fact) const {return _qfacts.count(fact);}
bool Position::hasAction(const USignature& action) const {return _actions.count(action);}
bool Position::hasReduction(const USignature& red) const {return _reductions.count(red);}

size_t Position::getLayerIndex() const {return _layer_idx;}
size_t Position::getPositionIndex() const {return _pos;}
size_t Position::getOffset() const {return _offset;}

const USigSet& Position::getQFacts() const {return _qfacts;}

const NodeHashMap<USignature, std::vector<TypeConstraint>, USignatureHasher>& Position::getQConstantsTypeConstraints() const {
    return _q_constants_type_constraints;
}

USigSet& Position::getActions() {return _actions;}
const USigSet& Position::getActions() const {return _actions;}
const USigSet& Position::getReductions() const {return _reductions;}
NodeHashMap<USignature, USigSet, USignatureHasher>& Position::getExpansions() {return _expansions;}
NodeHashMap<USignature, USigSet, USignatureHasher>& Position::getPredecessors() {return _predecessors;}
const NodeHashMap<USignature, USigSubstitutionMap, USignatureHasher>& Position::getExpansionSubstitutions() const {return _expansion_substitutions;}

void Position::clearAtPastPosition() {
    _qfacts.clear();
    _qfacts.reserve(0);
    /*
    _expansions.clear();
    _expansions.reserve(0);
    _predecessors.clear();
    _predecessors.reserve(0);
    */
   _expansion_substitutions.clear();
   _expansion_substitutions.reserve(0);
    _q_constants_type_constraints.clear();
    _q_constants_type_constraints.reserve(0);
    clearSubstitutions();
    _outgoing_effects.clear();
}

void Position::clearAtPastLayer() {
    _pos_qfact_decodings.clear();
    _pos_qfact_decodings.reserve(0);
    _neg_qfact_decodings.clear();
    _neg_qfact_decodings.reserve(0);
    _fact_variables.clear();
    _fact_variables.reserve(0);
    /*
    _actions.clear();
    _actions.reserve(0);
    _reductions.clear();
    _reductions.reserve(0);
    */
}

void Position::clearFullPos() {
    _pos_qfact_decodings.clear();
    _pos_qfact_decodings.reserve(0);
    _neg_qfact_decodings.clear();
    _neg_qfact_decodings.reserve(0);
    _fact_variables.clear();
    _fact_variables.reserve(0); 
    _outgoing_effects.clear();

    _qfacts.clear();
    _qfacts.reserve(0);

   _expansion_substitutions.clear();
   _expansion_substitutions.reserve(0);
    _q_constants_type_constraints.clear();
    _q_constants_type_constraints.reserve(0);
    clearSubstitutions();
}

void Position::clearDecodings() {
    _pos_qfact_decodings.clear();
    _pos_qfact_decodings.reserve(0);
    _neg_qfact_decodings.clear();
    _neg_qfact_decodings.reserve(0);
    // _expansion_substitutions.clear();
    // _expansion_substitutions.reserve(0);
    clearSubstitutions();
}
