#ifndef DOMPASCH_TREE_REXX_TREE_EXPANDER_H
#define DOMPASCH_TREE_REXX_TREE_EXPANDER_H

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
    size_t _expansion_iteration = 0;
    size_t _active_frontier_start = 0;

    const bool _use_sibylsat_expansion;
    const bool _nonprimitive_support;
    const bool _optimal;

    size_t _num_instantiated_positions = 0;
    size_t _num_instantiated_actions = 0;
    size_t _num_instantiated_reductions = 0;

public:
    TreeExpander(Parameters& params, HtnInstance& htn);

    void attachPruning(RetroactivePruning& pruning) { _pruning = &pruning; }
    void attachTDG(TDG& tdg) { _tdg = &tdg; }

    // Set the index from which the next expandLeaves call should start expanding.
    // Leaves before this index are carried over as-is (already solved by the scheduler).
    void setActiveFrontierStart(size_t index) { _active_frontier_start = index; }
    // The number of leaves carried over from the previous frontier (the separate-tasks prefix).
    size_t getActiveFrontierStart() const { return _active_frontier_start; }

    void createInitialLeaves();
    /**
     * Grow the search tree by expanding the given leaves. The new frontier is
     * stored in _leaf_positions (each leaf gets a fresh frontier index and a
     * cached left neighbour). The fact analysis is updated with the outgoing
     * effects of every leaf in the new frontier.
     */
    void expandLeaves(const FlatHashSet<Position*>& leavesToExpand);
    void printStatistics() const;
    Position*& getRootPositionRef() { return _root_position; }
    std::vector<Position*>& getLeafPositions() { return _leaf_positions; }
    FactAnalysis& getAnalysis() { return _analysis; }
    MethodEffectAnalysis& getMethodEffects() { return _method_effects; }
    size_t getNumRetroactivePrunings() const;
    size_t getNumRetroactivelyPrunedOps() const;

private:
    void incrementPosition(const Position& pos);
    bool isPotentiallyApplicable(const HtnOp& op);
    size_t computeExpansionSize(const Position& position) const;
    void expandLeaf(Position& parent, size_t expansionSize);
    void carryLeaf(Position& leaf);

    void createNextPosition(Position& newPos, Position* expandedParent, Position* left);
    void createNextPositionFromParent(Position& newPos, Position& parent);
    void computeOutgoingEffects(Position& position);
    void pruneImpossibleOperations(Position& position, const USigSet& operationsToRemove);
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
