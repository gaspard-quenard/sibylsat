#ifndef DOMPASCH_TREE_REXX_TREE_EXPANDER_H
#define DOMPASCH_TREE_REXX_TREE_EXPANDER_H

#include <memory>
#include <optional>
#include <vector>

#include "util/params.h"
#include "data/position.h"
#include "data/htn_instance.h"
#include "algo/instantiator.h"
#include "algo/fact_analysis.h"
#include "algo/retroactive_pruning.h"
#include "algo/domination_resolver.h"
#include "sat/encoding.h"
#include "data/tdg.h"
#include "algo/separate_tasks_scheduler.h"

class TreeExpander {
private:
    Parameters& _params;
    HtnInstance& _htn;
    Position*& _root_position;
    std::vector<Position*>& _leaf_positions;

    FactAnalysis& _analysis;
    Instantiator& _instantiator;
    Encoding& _enc;
    Statistics& _stats;
    RetroactivePruning& _pruning;
    DominationResolver& _domination_resolver;
    std::optional<TDG>& _tdg;
    std::unique_ptr<SeparateTasksScheduler>& _separate_tasks_scheduler;
    size_t& _depth;

    const bool _use_sibylsat_expansion;
    const bool _separate_tasks;
    const bool _nonprimitive_support;
    const bool _optimal;

    size_t& _num_instantiated_positions;
    size_t& _num_instantiated_actions;
    size_t& _num_instantiated_reductions;

public:
    TreeExpander(
            Parameters& params,
            HtnInstance& htn,
            Position*& rootPosition,
            std::vector<Position*>& leafPositions,
            FactAnalysis& analysis,
            Instantiator& instantiator,
            Encoding& enc,
            Statistics& stats,
            RetroactivePruning& pruning,
            DominationResolver& dominationResolver,
            std::optional<TDG>& tdg,
            std::unique_ptr<SeparateTasksScheduler>& separateTasksScheduler,
            size_t& depth,
            bool useSibylsatExpansion,
            bool separateTasks,
            bool nonprimitiveSupport,
            bool optimal,
            size_t& numInstantiatedPositions,
            size_t& numInstantiatedActions,
            size_t& numInstantiatedReductions);

    void createInitialLeaves();
    void expandLeaves(std::vector<Position*> nodesToDevelop);

private:
    void incrementPosition(const Position& pos);
    void refreshLeafMetadata();
    void refreshLeafLeftPositions();

    void createNextPosition(Position& newPos, Position* parent, Position* left);
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
