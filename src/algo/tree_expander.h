#ifndef DOMPASCH_TREE_REXX_TREE_EXPANDER_H
#define DOMPASCH_TREE_REXX_TREE_EXPANDER_H

#include <memory>
#include <utility>
#include <vector>
#include <optional>

#include "util/params.h"
#include "util/statistics.h"
#include "data/position.h"
#include "data/htn_instance.h"
#include "algo/fact_analysis.h"
#include "algo/retroactive_pruning.h"
#include "algo/domination_resolver.h"
#include "algo/operation_domain_analyzer.h"
#include "algo/q_constant_manager.h"
#include "data/tdg.h"

class TreeExpander {
private:
    Parameters& _params;
    HtnInstance& _htn;
    QConstantManager& _q_constants;
    Statistics& _stats;
    // Own every node for the lifetime of the search; all other Position pointers are observers.
    std::vector<std::unique_ptr<Position>> _owned_positions;
    Position* _root_position = nullptr;
    std::vector<Position*> _leaf_positions;
    FactAnalysis& _analysis;
    OperationDomainAnalyzer _operation_domain_analyzer;
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
    TreeExpander(Parameters& params, HtnInstance& htn, QConstantManager& qConstants, FactAnalysis& analysis, Statistics& statistics);

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
    size_t getNumRetroactivePrunings() const;
    size_t getNumRetroactivelyPrunedOps() const;

private:
    template<class... Args>
    Position& createPosition(Args&&... args) {
        _owned_positions.push_back(std::make_unique<Position>(std::forward<Args>(args)...));
        return *_owned_positions.back();
    }

    void recordInstantiatedPosition(const Position& position);
    bool isPotentiallyApplicable(const HtnOp& op);
    size_t computeExpansionSize(const Position& position) const;
    void expandLeaf(Position& parent, size_t expansionSize);
    void carryLeaf(Position& leaf);

    void populateChildFromParent(Position& child, Position& parent);
    void computeOutgoingEffects(Position& position);
    bool addActionOutgoingEffects(OutgoingEffects& effects, Position& position, const USignature& actionSig);
    void addReductionOutgoingEffects(OutgoingEffects& effects, Position& position, const USignature& reductionSig);
    void pruneImpossibleActions(Position& position, const USigSet& actionsToPrune);
    void addOutgoingEffectsToReachability(const Position& position);

    void preparePreconditionEncoding(Position& position);
    void prepareOperationPreconditions(Position& position, const HtnOp& operation, bool isRepeatedAction);
    std::optional<SubstitutionConstraint> analyzePrecondition(Position& position, const USignature& operationSig, const Signature& precondition, bool registerDynamicQFact);
    void analyzeGroundPrecondition(const Signature& precondition);
    SubstitutionConstraint buildEqualityPreconditionConstraint(const Signature& precondition, const std::vector<int>& sorts, const std::vector<int>& qArgumentIndices);
    SubstitutionConstraint buildStaticPreconditionConstraint(const Signature& precondition, const std::vector<int>& sorts, const std::vector<int>& qArgumentIndices);
    SubstitutionConstraint buildFluentPreconditionConstraint(Position& position, const Signature& precondition, const std::vector<std::vector<int>>& eligibleArguments, const std::vector<int>& qArgumentIndices, bool registerDynamicQFact);
    std::vector<int> collectQConstants(const USignature& fact, const std::vector<int>& qArgumentIndices) const;
    void mergeCompatibleConstraints(Position& position, const USignature& operationSig);

    enum class EffectMode { POSSIBLE_METHOD_EFFECT, ACTION_EFFECT, REPEATED_ACTION_EFFECT };
    void addGroundEffect(OutgoingEffects& effects, const USignature& opSig, int factId, bool negated, EffectMode mode);
    void addGroundEffect(OutgoingEffects& effects, const USignature& opSig, BitVec facts, bool negated, EffectMode mode);
    /**
     * Match a possibly lifted effect against indexed ground facts, filter any
     * Q-constant assignments through the operation's constraints, and register
     * the remaining decodings. Returns false when no valid decoding exists.
     */
    bool addInstantiatedEffect(OutgoingEffects& effects, Position& position, const USignature& opSig, const Signature& effect, EffectMode mode);
    bool isEffectDecodingAllowed(const std::vector<IntPair>& assignmentPath, const std::vector<const SubstitutionConstraint*>& sameQConstantConstraints, const std::vector<const SubstitutionConstraint*>& relatedConstraints) const;
    bool hasNegativeEffectOnPredicate(const USignature& actionSig, int predicateId) const;

    std::optional<USignature> instantiateAndRegisterReduction(Reduction reduction, const std::optional<USignature>& expectedTask, size_t originPositionId);

    void propagateParentActions(Position& child, Position& parent);
    void expandParentReductions(Position& child, Position& parent);
    std::optional<USignature> instantiateAndRegisterAction(const USignature& actionSig, size_t originPositionId);
    std::vector<USignature> instantiateActionsOfTask(const USignature& task, size_t originPositionId);
    std::vector<USignature> instantiateReductionsOfTask(const USignature& task, size_t originPositionId);
    void addQConstantTypeConstraints(Position& position, const USignature& operationSig);
};

#endif
