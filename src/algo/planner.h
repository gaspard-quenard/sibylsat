
#ifndef DOMPASCH_TREE_REXX_PLANNER_H
#define DOMPASCH_TREE_REXX_PLANNER_H
 
#include "util/names.h"
#include "util/params.h"
#include "util/hashmap.h"
#include "data/position.h"
#include "data/htn_instance.h"
#include "algo/instantiator.h"
#include "algo/arg_iterator.h"
#include "algo/precondition_inference.h"
#include "algo/minres.h"
#include "algo/fact_analysis.h"
#include "algo/retroactive_pruning.h"
#include "algo/domination_resolver.h"
#include "algo/plan_writer.h"
#include "sat/encoding.h"
#include "data/tdg.h"
#include "algo/separate_tasks_scheduler.h"
#include <optional>

typedef std::pair<std::vector<PlanItem>, std::vector<PlanItem>> Plan;

class Planner {

public:
    typedef std::function<bool(const USignature&, bool)> StateEvaluator;

private:
    Parameters& _params;
    HtnInstance& _htn;

    Position* _root_position = nullptr;
    std::vector<Position*> _leaf_positions;

    FactAnalysis _analysis;
    Instantiator _instantiator;
    Encoding _enc;
    Statistics& _stats;
    MinRES _minres;
    RetroactivePruning _pruning;
    DominationResolver _domination_resolver;
    PlanWriter _plan_writer;
    size_t _depth;

    const int _verbosity;

    const bool _use_sibylsat_expansion;
    FlatHashSet<int> _sibylsat_positions_to_develop;

    // For optimal planning
    const bool _optimal;
    std::optional<TDG> _tdg;
    size_t _last_number_of_soft_lits = 0;
    std::unordered_set<int> _soft_lits;

    // For separate tasks
    const bool _separate_tasks;
    std::unique_ptr<SeparateTasksScheduler> _separate_tasks_scheduler;
    

    float _sat_time_limit = 0;
    float _init_plan_time_limit = 0;
    bool _nonprimitive_support;
    float _optimization_factor;
    float _time_at_first_plan = 0;

    bool _has_plan;
    Plan _plan;

    // statistics
    size_t _num_instantiated_positions = 0;
    size_t _num_instantiated_actions = 0;
    size_t _num_instantiated_reductions = 0;

public:
    Planner(Parameters& params, HtnInstance& htn) : _params(params), _htn(htn), _stats(Statistics::getInstance()),
            _verbosity(params.getIntParam("v")),
            _analysis(_htn, true, _htn.getParams().isNonzero("optimal")), 
            _use_sibylsat_expansion(_params.isNonzero("sibylsat")),
            _optimal(_params.isNonzero("optimal")),
            _separate_tasks(_params.isNonzero("separateTasks") && _htn.getInitReduction().getSubtasks().size() > 1 && _use_sibylsat_expansion && !_optimal),
            _instantiator(params, htn, _analysis), 
            _enc(_params, _htn, _analysis, _root_position, _leaf_positions, [this](){checkTermination();}), 
            _minres(_htn), 
            _pruning(_enc),
            _domination_resolver(_htn),
            _plan_writer(_htn, _params),
            _init_plan_time_limit(_params.getFloatParam("T")), _nonprimitive_support(_params.isNonzero("nps")), 
            _optimization_factor(_params.getFloatParam("of")), _has_plan(false) {

        // Mine additional preconditions for reductions from their subtasks
        PreconditionInference::infer(_htn, _analysis, PreconditionInference::MinePrecMode(_params.getIntParam("mp")));

        if (_htn.getParams().isNonzero("mutex") && _analysis.checkGroundingFacts()) {
            _htn._sas_plus->cleanMutexGroupsWithPandaPiGrounderPreprocessingFacts(_analysis.getGroundPosFacts());
        }

        if (_optimal) {
            // Construct the TDG and infer the admissible values for each tasks and methods
            _tdg.emplace(_htn);
        }

        if (_separate_tasks) {
            // Initialize the separate tasks scheduler
            _separate_tasks_scheduler = std::make_unique<SeparateTasksScheduler>(/*htn=*/ htn);
        }
    }
    int findPlan();
    void improvePlan(int& iteration);

    friend int terminateSatCall(void* state);
    void checkTermination();
    bool cancelOptimization();

    const bool mustRestartPlanner() const { 
        return (_separate_tasks && _separate_tasks_scheduler->mustRestartPlanner());
    }

private:

    void createInitialLeaves();
    void expandAllLeaves();
    void expandSelectedLeaves(const FlatHashSet<int>& positionsToDevelop);
    void refreshLeafMetadata();
    void refreshLeafLeftPositions();
    
    void createNextPosition(Position& newPos, Position* parent, Position* left);
    void createNextPositionFromAbove(Position& newPos, Position& above);
    void createNextPositionFromLeft(Position& newPos, Position& left);
    void createNextPositionFromLeftSimplified(Position& newPos);

    void incrementPosition(const Position& pos);

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

    void setSoftLitsForCurrentLeaves();

    int getTerminateSatCall();
    void clearDonePositions(int offset);
    void printStatistics();

};

#endif
