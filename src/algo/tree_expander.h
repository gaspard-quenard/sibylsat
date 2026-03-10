#ifndef DOMPASCH_TREE_REXX_TREE_EXPANDER_H
#define DOMPASCH_TREE_REXX_TREE_EXPANDER_H

#include <memory>
#include <vector>

#include "util/params.h"
#include "data/position.h"
#include "data/htn_instance.h"
#include "algo/instantiator.h"
#include "algo/fact_analysis.h"
#include "algo/retroactive_pruning.h"
#include "algo/domination_resolver.h"
#include "data/tdg.h"

class SeparateTasksScheduler;

class TreeExpander {
private:
    Parameters& _params;
    HtnInstance& _htn;
    Statistics& _stats;
    Position* _root_position = nullptr;
    std::vector<Position*> _leaf_positions;
    FactAnalysis _analysis;
    Instantiator _instantiator;
    RetroactivePruning* _pruning = nullptr;
    DominationResolver _domination_resolver;
    TDG* _tdg = nullptr;
    SeparateTasksScheduler* _separate_tasks_scheduler = nullptr;
    size_t _depth = 0;

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
    void attachSeparateTasksScheduler(SeparateTasksScheduler& scheduler) { _separate_tasks_scheduler = &scheduler; }

    void createInitialLeaves();
    ExpansionResult expandLeaves(const std::vector<Position*>& nodesToDevelop);
    void printStatistics() const;
    Position*& getRootPositionRef() { return _root_position; }
    std::vector<Position*>& getLeafPositions() { return _leaf_positions; }
    const std::vector<Position*>& getLeafPositions() const { return _leaf_positions; }
    FactAnalysis& getAnalysis() { return _analysis; }
    const FactAnalysis& getAnalysis() const { return _analysis; }
    size_t getNumRetroactivePrunings() const;
    size_t getNumRetroactivelyPrunedOps() const;

private:
    void incrementPosition(const Position& pos);
    void refreshLeafMetadata();

    void createNextPosition(Position& newPos, Position* parent, Position* left, int positionsDone, bool addTasksAsClauses);
    void createNextPositionFromAbove(Position& newPos, Position& above);
    void createNextPositionFromLeft(Position& newPos, Position& left);
    void createNextPositionFromLeftSimplified(Position& newPos);

    void addPreconditionConstraints(Position& pos);
    void addPreconditionsAndConstraints(Position& pos, const USignature& op, const SigSet& preconditions, bool isActionRepetition);
    std::optional<SubstitutionConstraint> addPreconditionBitVec(Position& pos, const USignature& op, const Signature& fact, bool addQFact = true);

    enum EffectMode { INDIRECT, DIRECT, DIRECT_NO_QFACT };
    bool addGroundEffect(Position& pos, const USignature& opSig, int predId, bool negated, EffectMode mode);
    void addGroundEffectBitVec(Position& pos, const USignature& opSig, BitVec effects, bool negated, EffectMode mode);
    bool addPseudoGroundEffect(Position& pos, Position& left, const USignature& op, const Signature& fact, EffectMode mode);

    std::optional<Reduction> createValidReduction(Position& pos, const USignature& rSig, const USignature& task);

    void propagateInitialState(Position& newPos, const Position& above);
    void propagateActions(Position& newPos, Position& above);
    void propagateReductions(Position& newPos, Position& above);
    std::vector<USignature> instantiateAllActionsOfTask(Position& pos, const USignature& task);
    std::vector<USignature> instantiateAllReductionsOfTask(Position& pos, const USignature& task);
    void initializeNextEffectsBitVec(Position& pos);
    void initializeFactBitVec(Position& newPos, const int predId);
    void addQConstantTypeConstraints(Position& pos, const USignature& op);
};

#endif
