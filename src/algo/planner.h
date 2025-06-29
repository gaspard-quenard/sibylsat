
#ifndef DOMPASCH_TREE_REXX_PLANNER_H
#define DOMPASCH_TREE_REXX_PLANNER_H
 
#include "util/names.h"
#include "util/params.h"
#include "util/hashmap.h"
#include "data/layer.h"
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

    FactAnalysis _analysis;
    Instantiator _instantiator;
    Encoding _enc;
    Statistics& _stats;
    MinRES _minres;
    RetroactivePruning _pruning;
    DominationResolver _domination_resolver;
    PlanWriter _plan_writer;



    std::vector<Layer*> _layers;

    size_t _layer_idx;
    size_t _pos;
    size_t _old_pos;

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
            _enc(_params, _htn, _analysis, _layers, [this](){checkTermination();}), 
            _minres(_htn), 
            _pruning(_layers, _enc),
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

    void createFirstLayer();
    void createNextLayer();
    void createNextLayerUsingSibylSat(const FlatHashSet<int>& positionsToDevelop);
    
    void createNextPosition();
    void createNextPositionFromAbove();
    void createNextPositionFromLeft(Position& left);
    void createNextPositionFromLeftSimplified(Position& left);

    void incrementPosition();

    void addPreconditionConstraints();
    void addPreconditionsAndConstraints(const USignature& op, const SigSet& preconditions, bool isActionRepetition);
    std::optional<SubstitutionConstraint> addPreconditionBitVec(const USignature& op, const Signature& fact, bool addQFact = true);
    
    enum EffectMode { INDIRECT, DIRECT, DIRECT_NO_QFACT };
    bool addEffect(const USignature& op, const Signature& fact, EffectMode mode);

    bool addGroundEffect(const USignature& opSig, const int predId, bool negated, EffectMode mode);
    void addGroundEffectBitVec(const USignature& opSig, BitVec effects, bool negated, EffectMode mode);
    bool addPseudoGroundEffect(const USignature& op, const Signature& fact, EffectMode mode);

    std::optional<Reduction> createValidReduction(const USignature& rSig, const USignature& task);

    void propagateInitialState();
    void propagateActions(size_t offset);
    void propagateReductions(size_t offset);
    std::vector<USignature> instantiateAllActionsOfTask(const USignature& task);
    std::vector<USignature> instantiateAllReductionsOfTask(const USignature& task);
    void initializeNextEffectsBitVec();
    void initializeFactBitVec(Position& newPos, const int predId);
    void addQConstantTypeConstraints(const USignature& op);

    void setSoftLitsForOpsLastLayer();

    int getTerminateSatCall();
    void clearDonePositions(int offset);
    void printStatistics();

};

#endif