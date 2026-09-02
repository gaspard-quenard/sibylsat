#ifndef DOMPASCH_TREE_REXX_ENCODING_H
#define DOMPASCH_TREE_REXX_ENCODING_H

#include "util/params.h"
#include "data/position.h"
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
    Position*& _root_position;
    std::vector<Position*>& _leaf_positions;
    Statistics& _stats;
    SatInterface _sat;
    VariableProvider _vars;
    Decoder _decoder;

    size_t _new_init_pos = 0;

    NodeHashSet<Substitution, Substitution::Hasher> _forbidden_substitutions;
    FlatHashSet<int> _new_fact_vars;

    FlatHashSet<int> _q_constants;
    FlatHashSet<int> _new_q_constants;

    std::vector<int> _primitive_ops;
    std::vector<int> _nonprimitive_ops;

    const bool _use_q_constant_mutexes;
    const bool _implicit_primitiveness;

    const bool _use_sibylsat_expansion;

    const bool _optimal;

    const bool _mutex_predicates;

    // USigSet new_relevants_facts_to_encode;
    NodeHashMap<USignature, int, USignatureHasher> _new_relevants_facts_to_encode;

public:
    Encoding(Parameters& params, HtnInstance& htn, FactAnalysis& analysis, Position*& rootPosition, std::vector<Position*>& leafPositions) : 
            _params(params), _htn(htn), _analysis(analysis), _root_position(rootPosition), _leaf_positions(leafPositions), _stats(Statistics::getInstance()),
            _sat(params), _vars(_params, _htn),
            _decoder(_htn, _root_position, _leaf_positions, _sat, _vars),
            _use_q_constant_mutexes(_params.getIntParam("qcm") > 0), 
            _implicit_primitiveness(params.isNonzero("ip")),
            _use_sibylsat_expansion(params.isNonzero("sibylsat")),
            _optimal(params.isNonzero("optimal")),
            _mutex_predicates(_params.isNonzero("mutex")) {}

    void encode(Position& pos);
    /**
     * Encode the whole current frontier. Freshly expanded leaves are fully
     * encoded; carried leaves (from a previous layer) get their effects and
     * frame axioms encoded incrementally. Leaves in the separate-tasks prefix
     * (frontier index < _new_init_pos) are skipped as they were already encoded.
     */
    void encodeAllLeaves();
    void addAssumptionsPrimPlan(bool permanent = false, int assumptions_until = -1);
    void addUnitConstraint(int lit);
    
    int solve();

    void printFailedVars();
    void printSatisfyingAssignment();

    Plan extractPlan() {
        return _decoder.extractPlan();
    }
    std::vector<PlanItem> extractAbstractPlan() {
        return _decoder.extractClassicalPlan(Decoder::ALL);
    }
    SatInterface& getSatInterface() {return _sat;}

    /**
     * When using sibylsat expansion method. If the left position has been developped, we need to add the frame axioms, effects on this position and QfactSemantics (how those lifted effects can be decoded to a ground predicate)
     */
    void encodeOnlyEffsAndFrameAxioms(Position& pos);
    void encodeNewRelevantsFacts(Position& initPos);
    void encodeFrameAxiomsForNewRelevantsFacts(Position& newPos, Position& left);
    void propagateRelevantsFacts(Position& pos);

    const USignature getOpHoldingAt(const Position& pos);
    const USignature getDecodingOpHoldingAt(const Position& pos);
    void printStatementsAtPosition(const Position& pos);

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
            addAssumptionsPrimPlan();
        }
    }

    void setNewInitPos(size_t newInitPos) {
        _new_init_pos = newInitPos;
    }

private:
    struct EncodingEnvironment {
        Position* left = nullptr;
        Position* above = nullptr;
        Position* leftOfAbove = nullptr;
        Position* reusedFacts = nullptr;
    };
    struct QFactView {
        USigSet facts;
        NodeHashMap<USignature, USigSet, USignatureHasher> positiveDecodings;
        NodeHashMap<USignature, USigSet, USignatureHasher> negativeDecodings;

        void add(const Position& position);
        void add(const OutgoingEffects& effects);
        bool hasAnyDecodings(const USignature& fact) const;
        bool hasDecodings(const USignature& fact, bool negated) const;
        const USigSet& getDecodings(const USignature& fact, bool negated) const;
    };
    // How a leaf is positioned relative to the previous layer, which determines
    // which facts/effects can be reused vs. must be re-encoded.
    enum class EncodingContext {
        FreshLeaf,              // A newly expanded leaf (new Position object).
        CarriedLeaf,            // A leaf carried over from the previous layer.
        CarriedLeafReuseSelf    // A carried leaf that reuses its own fact variables.
    };

    Position* getLeftPosition(const Position& pos) const;
    Position* getAbovePosition(const Position& pos) const;
    EncodingEnvironment buildEnvironment(Position& pos, EncodingContext context) const;
    QFactView buildQFactView(const Position& position, const Position* left) const;
    int findReusableQFactVariable(
            const USignature& qfact,
            const Position& position,
            const QFactView& qfacts,
            const Position* source,
            const QFactView& sourceQFacts) const;
    void encodeOperationVariables(Position& pos);
    void encodeInitialRelevantFacts(Position& pos, bool rememberForPropagation);
    void encodeFactVariables(Position& pos, const EncodingEnvironment& env);
    void encodeFrameAxioms(Position& pos, Position& left, const EncodingEnvironment& env, bool onlyForNewRelevantsFacts = false);
    bool encodeFrameAxiomForFact(
            Position& newPos, Position& left, const EncodingEnvironment& env,
            const USignature& fact, int oldFactVar,
            bool nonprimFactSupport, bool hasPrimitiveOps, int prevVarPrim,
            bool skipRedundantFrameAxioms, USigSet& positiveFacts);
    void encodeIndirectFrameAxioms(const std::vector<int>& headerLits, int opVar, const IntPairTree& tree);
    void encodeOperationConstraints(Position& pos);
    void encodeSubstitutionVars(const USignature& opSig, int opVar, int qconst);
    void encodeQFactSemantics(Position& pos, const EncodingEnvironment& env, bool encodeOnlyEffectQFacts = false);
    void encodeActionEffects(Position& pos, Position& left);
    void encodeQConstraints(Position& pos);
    void encodeSubtaskRelationships(Position& pos, const EncodingEnvironment& env);
    void encodeMutexPredicates(Position& pos, const EncodingEnvironment& env, USigSet& possibleEffects);
    int encodeQConstEquality(int q1, int q2);


    /**
     * When using the sibylsat expansion method, prevent a method to have the same signature than one of its parents or transitive parents (meaning same name and same parameters) to be able to have a finite search space
     */
    void encodePreventionIdenticalSignatureThanParentsForAllMethods(Position& pos);

};

#endif
