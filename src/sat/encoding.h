
#ifndef DOMPASCH_TREE_REXX_ENCODING_H
#define DOMPASCH_TREE_REXX_ENCODING_H

#include "util/params.h"
#include "data/layer.h"
#include "data/signature.h"
#include "data/htn_instance.h"
#include "data/action.h"
#include "sat/literal_tree.h"
#include "sat/sat_interface.h"
#include "algo/fact_analysis.h"
#include "sat/variable_provider.h"
#include "sat/decoder.h"

typedef NodeHashMap<int, SigSet> State;

class Encoding {

private:
    Parameters& _params;
    HtnInstance& _htn;
    FactAnalysis& _analysis;
    std::vector<Layer*>& _layers;
    Statistics& _stats;
    SatInterface _sat;
    VariableProvider _vars;
    Decoder _decoder;

    size_t _new_init_pos = 0;

    std::function<void()> _termination_callback;
    
    size_t _layer_idx;
    size_t _pos;
    size_t _old_pos;
    size_t _offset;

    NodeHashSet<Substitution, Substitution::Hasher> _forbidden_substitutions;
    FlatHashSet<int> _new_fact_vars;

    FlatHashSet<int> _q_constants;
    FlatHashSet<int> _new_q_constants;

    std::vector<int> _primitive_ops;
    std::vector<int> _nonprimitive_ops;

    const bool _use_q_constant_mutexes;
    const bool _implicit_primitiveness;

    float _sat_call_start_time;

    const bool _use_sibylsat_expansion;

    const bool _optimal;

    const bool _mutex_predicates;

    // USigSet new_relevants_facts_to_encode;
    NodeHashMap<USignature, int, USignatureHasher> _new_relevants_facts_to_encode;

public:
    Encoding(Parameters& params, HtnInstance& htn, FactAnalysis& analysis, std::vector<Layer*>& layers, std::function<void()> terminationCallback) : 
            _params(params), _htn(htn), _analysis(analysis), _layers(layers), _stats(Statistics::getInstance()),
            _sat(params), _vars(_params, _htn, _layers),
            _decoder(_htn, _layers, _sat, _vars),
            _termination_callback(terminationCallback),
            _use_q_constant_mutexes(_params.getIntParam("qcm") > 0), 
            _implicit_primitiveness(params.isNonzero("ip")),
            _use_sibylsat_expansion(params.isNonzero("sibylsat")),
            _optimal(params.isNonzero("optimal")),
            _mutex_predicates(_params.isNonzero("mutex")) {}

    void encode(size_t layerIdx, size_t pos);
    void addAssumptionsPrimPlan(int layerIdx, bool permanent = false, int assumptions_until = -1);
    void addUnitConstraint(int lit);
    
    void setTerminateCallback(void * state, int (*terminate)(void * state));
    int solve();
    float getTimeSinceSatCallStart();    

    void printFailedVars(Layer& layer);
    void printSatisfyingAssignment();

    Plan extractPlan() {
        return _decoder.extractPlan();
    }
    std::vector<PlanItem> extractVirtualPlan() {
        return _decoder.extractClassicalPlan(Decoder::ALL);
    }
    SatInterface& getSatInterface() {return _sat;}

    /**
     * When using sibylsat expansion method. If the left position has been developped, we need to add the frame axioms, effects on this position and QfactSemantics (how those lifted effects can be decoded to a ground predicate)
     */
    void encodeOnlyEffsAndFrameAxioms(size_t layerIdx, size_t pos);
    void encodeNewRelevantsFacts(Position& initPos);
    void encodeFrameAxiomsForNewRelevantsFacts(Position& newPos, Position& left);
    void propagateRelevantsFacts(size_t layerIdx, size_t pos);

    const USignature getOpHoldingInLayerPos(int layer, int position);
    const USignature getDecodingOpHoldingInLayerPos(int layer, int position);
    void printStatementsAtPosition(int layer, int position);

    void print_formula(std::string filename) {
        _sat.print_formula(filename);
    }

    // For optimal planning using maxsat
    void clearSoftLits();
    void addSoftLit(int lit, int weight);
    int getObjectiveValue();

    NodeHashSet<int> getSnapshotsOpsAndPredsTrue(int untilPos);
    void addAssumptionsTasksAccomplished(NodeHashSet<int>& opsAndPredsTrue, bool permanent);

    ~Encoding() {
        // Append assumptions to written formula, close stream
        if (!_params.isNonzero("cs") && !_sat.hasLastAssumptions()) {
            addAssumptionsPrimPlan(_layers.size()-1);
        }
    }

    void setNewInitPos(size_t newInitPos) {
        _new_init_pos = newInitPos;
    }

private:
    void encodeOperationVariables(Position& pos);
    void encodeFactVariables(Position& pos, Position& left, Position& above);
    void encodeFrameAxioms(Position& pos, Position& left, bool onlyForNewRelevantsFacts = false);
    void encodeIndirectFrameAxioms(const std::vector<int>& headerLits, int opVar, const IntPairTree& tree);
    void encodeOperationConstraints(Position& pos);
    void encodeSubstitutionVars(const USignature& opSig, int opVar, int qconst);
    void encodeQFactSemantics(Position& pos, bool encodeOnlyEffectQFacts = false);
    void encodeActionEffects(Position& pos, Position& left);
    void encodeQConstraints(Position& pos);
    void encodeSubtaskRelationships(Position& pos, Position& above);
    void encodeMutexPredicates(Position& pos, Position& above, USigSet& possibleEffects);
    int encodeQConstEquality(int q1, int q2);


    /**
     * When using the sibylsat expansion method, prevent a method to have the same signature than one of its parents or transitive parents (meaning same name and same parameters) to be able to have a finite search space
     */
    void encodePreventionIdenticalSignatureThanParentsForAllMethods(Position& pos);

    // void encodeFrameAxiomsForNewRelevantsFacts(Position& newPos, Position& left);
};

#endif