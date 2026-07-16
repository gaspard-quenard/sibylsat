#ifndef DOMPASCH_TREE_REXX_TREE_EXPANDER_H
#define DOMPASCH_TREE_REXX_TREE_EXPANDER_H

#include <memory>
#include <vector>
#include <optional>

#include "util/params.h"
#include "data/position.h"
#include "data/htn_instance.h"
#include "algo/fact_analysis.h"
#include "algo/method_effect_analysis.h"
#include "algo/retroactive_pruning.h"
#include "algo/domination_resolver.h"
#include "data/tdg.h"

class TreeExpander {
private:
    Parameters& _params;
    HtnInstance& _htn;
    Statistics& _stats;
    Position* _root_position = nullptr;
    std::vector<Position*> _leaf_positions;
    FactAnalysis _analysis;
    MethodEffectAnalysis _method_effects;
    RetroactivePruning* _pruning = nullptr;
    DominationResolver _domination_resolver;
    TDG* _tdg = nullptr;
    size_t _depth = 0;
    size_t _expansion_start_index = 0;

    const bool _use_sibylsat_expansion;
    const bool _nonprimitive_support;
    const bool _optimal;

    size_t _num_instantiated_positions = 0;
    size_t _num_instantiated_actions = 0;
    size_t _num_instantiated_reductions = 0;

public:
    enum class LeafEncodingAction { NONE, FULL, NEW_RELEVANTS, EFFECTS_AND_FRAME, PROPAGATE_RELEVANTS };

    struct ExpansionResult {
        bool expandAll = false;
        size_t newInitPos = 0;
        std::vector<LeafEncodingAction> leafEncodingActions;
        std::vector<Position*> expandedNodes;
    };

    TreeExpander(Parameters& params, HtnInstance& htn);

    void attachPruning(RetroactivePruning& pruning) { _pruning = &pruning; }
    void attachTDG(TDG& tdg) { _tdg = &tdg; }

    // Set the index from which the next expandLeaves call should start expanding.
    // Leaves before this index are carried over as-is (already solved by the scheduler).
    void setExpansionBoundary(size_t boundary) { _expansion_start_index = boundary; }

    void createInitialLeaves();
    ExpansionResult expandLeaves(const std::vector<Position*>& leavesToExpand);
    void printStatistics() const;
    Position*& getRootPositionRef() { return _root_position; }
    std::vector<Position*>& getLeafPositions() { return _leaf_positions; }
    const std::vector<Position*>& getLeafPositions() const { return _leaf_positions; }
    FactAnalysis& getAnalysis() { return _analysis; }
    const FactAnalysis& getAnalysis() const { return _analysis; }
    MethodEffectAnalysis& getMethodEffects() { return _method_effects; }
    size_t getNumRetroactivePrunings() const;
    size_t getNumRetroactivelyPrunedOps() const;

private:
    void incrementPosition(const Position& pos);
    bool isPotentiallyApplicable(const HtnOp& op);
    size_t computeExpansionSize(const Position& position) const;
    void expandLeaf(Position& parent, size_t expansionSize, ExpansionResult& result);
    void carryLeaf(Position& leaf, LeafEncodingAction encodingAction, ExpansionResult& result);

    void createNextPosition(Position& newPos, size_t pos, Position* parent, Position* left);
    void createNextPositionFromParent(Position& newPos, Position& parent);
    void computeAndApplyOutgoingEffects(Position& position);
    void applyOutgoingEffects(const Position& position);

    void addPreconditionConstraints(Position& pos);
    void addPreconditionsAndConstraints(Position& pos, const USignature& op, const SigSet& preconditions, bool isActionRepetition);
    std::optional<SubstitutionConstraint> addPrecondition(Position& pos, const USignature& op, const Signature& fact, bool addQFact = true);

    enum EffectMode { INDIRECT, DIRECT, DIRECT_NO_QFACT };
    bool addGroundEffect(OutgoingEffects& effects, const USignature& opSig, int predId, bool negated, EffectMode mode);
    void addGroundEffect(OutgoingEffects& effects, const USignature& opSig, BitVec facts, bool negated, EffectMode mode);
    bool addPseudoGroundEffect(OutgoingEffects& effects, Position& position, const USignature& op, const Signature& fact, EffectMode mode);

    std::optional<Reduction> createValidReduction(Position& pos, const USignature& rSig, const USignature& task);

    void propagateActions(Position& newPos, Position& parent);
    void propagateReductions(Position& newPos, Position& parent);
    std::vector<USignature> instantiateAllActionsOfTask(Position& pos, const USignature& task);
    std::vector<USignature> instantiateAllReductionsOfTask(Position& pos, const USignature& task);
    void addQConstantTypeConstraints(Position& pos, const USignature& op);
};

#endif
