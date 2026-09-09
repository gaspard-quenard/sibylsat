#ifndef DOMPASCH_TREE_REXX_ENCODING_H
#define DOMPASCH_TREE_REXX_ENCODING_H

#include <set>

#include "util/params.h"
#include "util/statistics.h"
#include "data/position.h"
#include "data/signature.h"
#include "data/htn_instance.h"
#include "data/mutex_groups.h"
#include "data/action.h"
#include "sat/literal_tree.h"
#include "sat/sat_interface.h"
#include "algo/fact_analysis.h"
#include "algo/q_constant_manager.h"
#include "sat/variable_provider.h"
#include "sat/decoder.h"

class Encoding {

private:
    Parameters& _params;
    HtnInstance& _htn;
    QConstantManager& _q_constants;
    FactAnalysis& _analysis;
    const MutexGroups* _mutex_groups;
    Position*& _root_position;
    std::vector<Position*>& _leaf_positions;
    Statistics& _stats;
    VariableAllocator _variable_allocator;
    SatInterface _sat;
    VariableProvider _vars;
    Decoder _decoder;

    size_t _active_frontier_start = 0;

    const bool _use_sibylsat_expansion;

    const bool _optimal;

public:
    Encoding(Parameters& params, HtnInstance& htn, QConstantManager& qConstants, FactAnalysis& analysis, const MutexGroups* mutexGroups, Position*& rootPosition, std::vector<Position*>& leafPositions, Statistics& statistics) :
            _params(params), _htn(htn), _q_constants(qConstants), _analysis(analysis), _mutex_groups(mutexGroups), _root_position(rootPosition), _leaf_positions(leafPositions), _stats(statistics),
            _variable_allocator(params), _sat(params, statistics), _vars(_htn, _q_constants, _variable_allocator),
            _decoder(_htn, _q_constants, _root_position, _leaf_positions, _sat, _vars),
            _use_sibylsat_expansion(params.isNonzero("sibylsat")),
            _optimal(params.isNonzero("optimal")) {}

    /**
     * Encode the current frontier, including initial-state facts and any
     * positions or transitions introduced by the latest tree expansion. An
     * already encoded separate-tasks prefix is skipped.
     */
    void encodeAllLeaves();
    void addAssumptionsPrimPlan(bool permanent = false, int assumptions_until = -1);
    void addUnitConstraint(int lit);
    
    int solve();

    Decoder& getDecoder() { return _decoder; }
    SatInterface& getSatInterface() {return _sat;}
    VariableAllocator& getVariableAllocator() { return _variable_allocator; }

    // For optimal planning using maxsat
    void clearSoftLits();
    void addSoftLit(int lit, int weight);
    int getObjectiveValue();
    void writeFormulaFile();

    void addAssumptionsTasksAccomplished(NodeHashSet<int>& opsAndPredsTrue, bool permanent);

    void setActiveFrontierStart(size_t index) {
        _active_frontier_start = index;
    }

private:
    struct EncodingEnvironment {
        Position* incoming = nullptr;         // Source of the incoming state transition.
        Position* parent = nullptr;           // Source of decomposition constraints.
        Position* reuseFactsFrom = nullptr;   // Position whose existing fact variables may be shared.
        Position* reusePredecessor = nullptr; // Incoming source used when reuseFactsFrom was encoded.
    };
    struct StateQFacts {
        USigSet qFacts;
        NodeHashMap<USignature, USigSet, USignatureHasher> positiveDecodings;
        NodeHashMap<USignature, USigSet, USignatureHasher> negativeDecodings;

        void add(const Position& position);
        void add(const OutgoingEffects& effects);
        bool hasAnyDecodings(const USignature& fact) const;
        bool hasDecodings(const USignature& fact, bool negated) const;
        const USigSet& getDecodings(const USignature& fact, bool negated) const;
    };
    struct PositionedMethod {
        Position* position;
        USignature signature;

        bool operator==(const PositionedMethod& other) const {
            return position == other.position && signature == other.signature;
        }
    };
    struct EffectSupports {
        const USigSet* direct = nullptr;
        IndirectFactSupportMapEntry* indirect = nullptr;

        bool empty() const { return direct == nullptr && indirect == nullptr; }
    };
    using EffectUnifier = std::set<int>;
    using EffectUnifierDnf = std::set<EffectUnifier>;
    struct PositiveEffectUnifiers {
        bool unconditional = false;
        EffectUnifierDnf alternatives;
    };
    Position* getCurrentFrontierLeft(const Position& pos) const;
    Position* getPreviousFrontierLeft(const Position& pos, size_t expansionIteration) const;
    Position* getParentExcludingRoot(const Position& pos) const;
    bool wasCreatedInCurrentExpansion(const Position& pos, size_t expansionIteration) const;
    bool isPrimitiveReduction(const USignature& reduction) const;
    bool hasPrimitiveCandidates(const Position& pos) const;
    bool hasNonprimitiveCandidates(const Position& pos) const;
    EncodingEnvironment buildFreshPositionEnvironment(Position& pos) const;
    EncodingEnvironment buildExistingTransitionEnvironment(Position& source, Position& destination, size_t expansionIteration) const;
    EncodingEnvironment buildRelevantFactPropagationEnvironment(Position& source, Position& destination, size_t expansionIteration) const;
    StateQFacts collectStateQFacts(const Position& position, const Position* incoming) const;
    void reuseParentFactVariables(Position& position, const EncodingEnvironment& env);
    int findReusableQFactVariable(
            const USignature& qfact,
            const Position& position,
            const StateQFacts& stateQFacts,
            const Position* source,
            const StateQFacts& sourceStateQFacts) const;
    void encodeFreshPosition(Position& pos);
    void encodeOperationVariables(Position& pos);
    /** Encode newly relevant facts in the state at the active-frontier start. */
    BitVec encodeRelevantFactsAtFrontierStart(Position& position);
    void encodeGroundFactTransition(Position& source, Position& destination, const EncodingEnvironment& env);
    USigSet encodeQFactVariables(Position& pos, const EncodingEnvironment& env);
    /** Encode all frame axioms, or only selected facts when selectedFactIds is provided. */
    void encodeFrameAxioms(Position& source, Position& destination, const EncodingEnvironment& env, const BitVec* selectedFactIds = nullptr);

    bool canSkipRedundantFrameAxioms(const Position& source, const EncodingEnvironment& env) const;
    EffectSupports findEffectSupports(OutgoingEffects& effects, int factId, bool negated) const;
    void encodeFrameAxiomForFact(Position& source, Position& destination, const EncodingEnvironment& env, const USignature& fact, int sourceFactVar, bool nonprimFactSupport, bool sourceHasPrimitiveCandidates, int sourceVarPrim, bool skipRedundantFrameAxioms, USigSet& positiveFacts);
    void encodeIndirectFrameAxioms(const std::vector<int>& headerLits, int opVar, const IntPairTree& tree);
    void encodeOperationConstraints(Position& pos);
    void encodeActionConstraints(Position& pos, std::vector<int>& operationVars);
    void encodeReductionConstraints(Position& pos, std::vector<int>& operationVars);
    void encodeOperationSelection(const std::vector<int>& operationVars);
    void encodeSubstitutionVars(const USignature& opSig, int opVar, int qconst);
    void encodeQFactSemantics(Position& pos, const EncodingEnvironment& env, const USigSet& newlyCreatedQFacts);
    void encodeIncomingEffectQFactSemantics(Position& pos, const EncodingEnvironment& env, const USigSet& newlyCreatedQFacts);
    void encodeQFactSemanticsWithReuseFiltering(Position& pos, const EncodingEnvironment& env, const StateQFacts& stateQFacts, const StateQFacts& reusedStateQFacts, const USigSet& newlyCreatedQFacts);
    bool isQFactDecodingAlreadyEncoded(const EncodingEnvironment& env, const StateQFacts& reusedStateQFacts, const USignature& qfact, const USignature& decoding, bool negated, int qfactVar) const;
    void encodeAllQFactSemantics(Position& pos, const StateQFacts& stateQFacts);
    void encodeQFactDecoding(Position& pos, const USignature& qfact, int qfactVar, const USignature& decoding, bool negated, std::vector<int>& substitutionVars);
    void encodeEffects(Position& source, Position& destination);
    void encodeActionEffects(const USignature& action, int actionVar, Position& destination, bool useTreeConversion);
    PositiveEffectUnifiers findPositiveEffectUnifiers(const Signature& negativeEffect, const SigSet& effects, const Position& destination);
    std::optional<EffectUnifier> findEffectUnifier(const Signature& first, const Signature& second);
    void encodeConditionalNegativeEffect(int actionVar, int factVar, const EffectUnifierDnf& unifiers, bool useTreeConversion);
    void encodeQConstraints(Position& pos);
    void encodeQConstantTypeConstraints(Position& pos);
    void encodeSubstitutionConstraints(Position& pos);
    void encodeSubstitutionConstraintsForOperations(Position& pos, const USigSet& operations);
    void encodeSubtaskRelationships(Position& pos, const EncodingEnvironment& env);
    void encodeExpansionRelationships(Position& pos, Position& parent);
    void encodeExpansionSubstitutions(Position& pos, const USignature& parentOperation, int parentVar);
    void encodePredecessorRelationships(Position& pos, Position& parent);
    void encodeMutexPredicates(Position& pos, const EncodingEnvironment& env, const USigSet& possibleEffects);
    void encodeMutexGroup(const std::vector<int>& factVars);
    int encodeQConstEquality(int q1, int q2);
    void encodeTransition(Position& source, Position& destination, size_t expansionIteration);
    void propagateNewRelevantFacts(Position& source, Position& destination, size_t expansionIteration, const BitVec& newlyRelevantFactIds);

    std::vector<PositionedMethod> findMethodAncestorsWithSameName(Position& position, const USignature& method) const;
    void encodeMethodMustDifferFromAncestors(Position& position, const USignature& method, const std::vector<PositionedMethod>& ancestors);

    /**
     * Prevent a recursive method from having the same signature as one of its
     * ancestors (the same method name with the same decoded arguments), ensuring
     * that recursive expansion has a finite search space.
     */
    void encodeRecursiveMethodAncestorDistinctness(Position& position);

};

#endif
