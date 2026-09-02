
#ifndef DOMPASCH_LILOTANE_POSITION_H
#define DOMPASCH_LILOTANE_POSITION_H

#include <memory>
#include <vector>

#include "util/hashmap.h"
#include "data/signature.h"
#include "util/names.h"
#include "sat/variable_domain.h"
#include "util/log.h"
#include "sat/literal_tree.h"
#include "data/substitution_constraint.h"

typedef NodeHashMap<USignature, IntPairTree, USignatureHasher> IndirectFactSupportMapEntry;
typedef NodeHashMap<USignature, Substitution, USignatureHasher> USigSubstitutionMap;
typedef NodeHashMap<int, USigSet> DirectFactSupportMap;
typedef NodeHashMap<int, IndirectFactSupportMapEntry> IndirectFactSupportMapId;

enum VarType { FACT, OP };

class OutgoingEffects {
private:
    BitVec _positive_changes;
    BitVec _negative_changes;

    std::unique_ptr<DirectFactSupportMap> _positive_supports;
    std::unique_ptr<DirectFactSupportMap> _negative_supports;
    std::unique_ptr<IndirectFactSupportMapId> _positive_indirect_supports;
    std::unique_ptr<IndirectFactSupportMapId> _negative_indirect_supports;

    USigSet _qfacts;
    NodeHashMap<USignature, USigSet, USignatureHasher> _positive_qfact_decodings;
    NodeHashMap<USignature, USigSet, USignatureHasher> _negative_qfact_decodings;

public:
    void reset(size_t numFacts);
    void addFactChange(int factId, bool negated);
    void addFactChanges(const BitVec& facts, bool negated);
    const BitVec& getFactChanges(bool negated) const;

    void addSupport(int factId, bool negated, const USignature& operation);
    void addIndirectSupport(int factId, bool negated, const USignature& operation, const std::vector<IntPair>& path);
    void touchSupport(int factId, bool negated);
    DirectFactSupportMap& getSupports(bool negated);
    const DirectFactSupportMap& getSupports(bool negated) const;
    IndirectFactSupportMapId& getIndirectSupports(bool negated);
    const IndirectFactSupportMapId& getIndirectSupports(bool negated) const;

    void addQFact(const USignature& fact);
    void addQFactDecoding(const USignature& fact, const USignature& decoding, bool negated);
    const USigSet& getQFacts() const { return _qfacts; }
    bool hasQFactDecodings(const USignature& fact, bool negated) const;
    const USigSet& getQFactDecodings(const USignature& fact, bool negated) const;

    void clearSupports();
    void clearDecodings();
    void clear();
};

struct Position {
private:
    // Stable identifiers assigned once at creation. _layer_idx is the depth at
    // which the position was created; _pos is a globally unique monotonic id
    // (used for q-constant naming and logging only -- never a frontier index).
    size_t _layer_idx = -1;
    size_t _pos = _next_pos_id++;
    size_t _offset = 0;

    Position* _parent_position = nullptr;
    std::vector<Position*> _children_positions;
    Position* _left_position = nullptr;  // Cached previous leaf (set per layer).

    // Per-layer ordering of this leaf within the current frontier.
    // Unlike _pos (a stable unique id), this is re-assigned each layer and
    // used by the encoding to know "which leaf is the Nth leaf of the layer".
    size_t _frontier_index = -1;

    // True if this position was newly created by the last expandLeaves call.
    // Carried leaves (re-used from a previous layer) are false. Lets the
    // encoding decide between full and incremental encoding without a result struct.
    bool _fresh_in_current_layer = false;

    // Running counter for globally unique position ids.
    static size_t _next_pos_id;

    USigSet _actions;
    USigSet _reductions;

    NodeHashMap<USignature, USigSet, USignatureHasher> _expansions;
    NodeHashMap<USignature, USigSet, USignatureHasher> _predecessors;
    NodeHashMap<USignature, USigSubstitutionMap, USignatureHasher> _expansion_substitutions;

    // Used for optimal planning
    NodeHashMap<USignature, int, USignatureHasher> _heuristic_value_per_reduction;

    // All VIRTUAL facts potentially occurring at this position.
    USigSet _qfacts;
    // Maps a q-fact to the set of possibly valid decoded facts.
    NodeHashMap<USignature, USigSet, USignatureHasher> _pos_qfact_decodings;
    NodeHashMap<USignature, USigSet, USignatureHasher> _neg_qfact_decodings;

    OutgoingEffects _outgoing_effects;

    NodeHashMap<USignature, std::vector<TypeConstraint>, USignatureHasher> _q_constants_type_constraints;
    NodeHashMap<USignature, std::vector<SubstitutionConstraint>, USignatureHasher> _substitution_constraints;

    // Prop. variable for each occurring signature.
    NodeHashMap<USignature, int, USignatureHasher> _op_variables;
    NodeHashMap<USignature, int, USignatureHasher> _fact_variables;

    bool _has_primitive_ops = false;
    bool _has_nonprimitive_ops = false;

    // Indicate which mutex groups this position has fully encoded (i.e. already done an at most one for all elements in the group)
    FlatHashSet<int> _group_mutex_encoded;

public:

    Position();
    void setPos(size_t layerIdx);
    void setParentPosition(Position* parent);
    Position* getParentPosition() const { return _parent_position; }
    const std::vector<Position*>& getChildrenPositions() const { return _children_positions; }
    void setLeftPosition(Position* left) { _left_position = left; }
    Position* getLeftPosition() const { return _left_position; }

    void addQFact(const USignature& qfact);

    void setHasPrimitiveOps(bool has);
    void setHasNonprimitiveOps(bool has);
    bool hasPrimitiveOps();
    bool hasNonprimitiveOps();

    void addQConstantTypeConstraint(const USignature& op, const TypeConstraint& c);
    void addSubstitutionConstraint(const USignature& op, SubstitutionConstraint&& constr);

    bool hasQFactDecodings(const USignature& qFact, bool negated) const;
    void addQFactDecoding(const USignature& qFact, const USignature& decFact, bool negated);
    void removeQFactDecoding(const USignature& qFact, const USignature& decFact, bool negated);
    const USigSet& getQFactDecodings(const USignature& qfact, bool negated) const;

    void addAction(const USignature& action);
    void addAction(USignature&& action);
    void addReduction(const USignature& reduction);
    void addExpansion(const USignature& parent, const USignature& child);
    void addExpansionSubstitution(const USignature& parent, const USignature& child, const Substitution& s);
    void addExpansionSubstitution(const USignature& parent, const USignature& child, Substitution&& s);
    
    void removeActionOccurrence(const USignature& action);
    void removeReductionOccurrence(const USignature& reduction);
    void replaceOperation(const USignature& from, const USignature& to, Substitution&& s);

    const NodeHashMap<USignature, int, USignatureHasher>& getVariableTable(VarType type) const;

    bool hasQFact(const USignature& fact) const;
    bool hasAction(const USignature& action) const;
    bool hasReduction(const USignature& red) const;

    const USigSet& getQFacts() const;
    OutgoingEffects& getOutgoingEffects() { return _outgoing_effects; }
    const OutgoingEffects& getOutgoingEffects() const { return _outgoing_effects; }


    const NodeHashMap<USignature, std::vector<TypeConstraint>, USignatureHasher>& getQConstantsTypeConstraints() const;
    NodeHashMap<USignature, std::vector<SubstitutionConstraint>, USignatureHasher>& getSubstitutionConstraints() {
        return _substitution_constraints;
    }

    USigSet& getActions();
    const USigSet& getActions() const;
    const USigSet& getReductions() const;
    NodeHashMap<USignature, USigSet, USignatureHasher>& getExpansions();
    NodeHashMap<USignature, USigSet, USignatureHasher>& getPredecessors();
    const NodeHashMap<USignature, USigSubstitutionMap, USignatureHasher>& getExpansionSubstitutions() const;

    size_t getLayerIndex() const;
    size_t getPositionIndex() const;
    size_t getFrontierIndex() const { return _frontier_index; }
    void setFrontierIndex(size_t idx) { _frontier_index = idx; }
    bool isFreshInCurrentLayer() const { return _fresh_in_current_layer; }
    void setFreshInCurrentLayer(bool fresh) { _fresh_in_current_layer = fresh; }
    size_t getOffset() const;
    void clearSubstitutions() {
        _substitution_constraints.clear();
        _substitution_constraints.reserve(0);
    }
    void clearDecodings();
    void clearFullPos();

    inline int encode(VarType type, const USignature& sig) {
        auto& vars = type == OP ? _op_variables : _fact_variables;
        auto it = vars.find(sig);
        if (it == vars.end()) {
            // introduce a new variable
            assert(!VariableDomain::isLocked() || Log::e("Unknown variable %s queried!\n", VariableDomain::varName(_layer_idx, _pos, sig).c_str()));
            int var = VariableDomain::nextVar();
            vars[sig] = var;
            VariableDomain::printVar(var, _layer_idx, _pos, sig);
            return var;
        } else return it->second;
    }

    inline int setVariable(VarType type, const USignature& sig, int var) {
        auto& vars = type == OP ? _op_variables : _fact_variables;
        // assert(!vars.count(sig));
        if (vars.count(sig)) {
            assert(vars.at(sig) == var);
            return var;
        }
        vars[sig] = var;
        return var;
    }

    inline bool hasVariable(VarType type, const USignature& sig) const {
        return (type == OP ? _op_variables : _fact_variables).count(sig);
    }

    inline int getVariable(VarType type, const USignature& sig) const {
        auto& vars = type == OP ? _op_variables : _fact_variables;
        assert(vars.count(sig) || Log::e("Unknown variable %s queried!\n", VariableDomain::varName(_layer_idx, _pos, sig).c_str()));
        return vars.at(sig);
    }

    inline int getVariableOrZero(VarType type, const USignature& sig) const {
        auto& vars = type == OP ? _op_variables : _fact_variables;
        const auto& it = vars.find(sig);
        if (it == vars.end()) return 0;
        return it->second;
    }

    inline void removeVariable(VarType type, const USignature& sig) {
        auto& vars = type == OP ? _op_variables : _fact_variables;
        vars.erase(sig);
    }


    void setOffset(size_t offset) {_offset = offset;}

    void setHeuristicValue(const USignature& reduction, int value) {
        assert(_reductions.count(reduction) || Log::e("Unknown reduction %s queried!\n", Names::to_string(reduction).c_str()));
        _heuristic_value_per_reduction[reduction] = value;
    }

    int getHeuristicValue(const USignature& reduction) {
        assert(_heuristic_value_per_reduction.count(reduction) || Log::e("Unknown reduction %s queried!\n", Names::to_string(reduction).c_str()));
        return _heuristic_value_per_reduction[reduction];
    }

    void addGroupMutexEncoded(int group_mutex) {_group_mutex_encoded.insert(group_mutex);}
    const FlatHashSet<int>& getGroupMutexEncoded() const {return _group_mutex_encoded;}
};


#endif
