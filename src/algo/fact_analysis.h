
#ifndef DOMPASCH_LILOTANE_ANALYSIS_H
#define DOMPASCH_LILOTANE_ANALYSIS_H

#include "data/htn_instance.h"
#include "algo/network_traversal.h"
#include "algo/arg_iterator.h"

typedef std::function<bool(const USignature&, bool)> StateEvaluator;

class FactAnalysis {

private:

    HtnInstance& _htn;
    NetworkTraversal _traversal;

    USigSet _init_state;
    USigSet _pos_layer_facts;
    USigSet _neg_layer_facts;

    USigSet _initialized_facts;
    USigSet _relevant_facts;

    const bool _preprocess_facts;
    USigSet _ground_pos_facts;
    USigSet _ground_neg_facts;
    // For each lift fact, store the set of ground facts that it can be grounded to
    NodeHashMap<int, std::vector<FlatHashSet<int>>> _allowed_domain_per_pos_lift_facts;
    NodeHashMap<int, std::vector<FlatHashSet<int>>> _allowed_domain_per_neg_lift_facts;
    long long int _time_grounding_facts = 0;

    // Maps an (action|reduction) name 
    // to the set of (partially lifted) fact signatures
    // that might be added to the state due to this operator. 
    NodeHashMap<int, SigSet> _fact_changes; 
    NodeHashMap<int, SigSet> _lifted_fact_changes;
    NodeHashMap<USignature, SigSet, USignatureHasher> _fact_changes_cache;

    NodeHashMap<int, FactFrame> _fact_frames;

public:
    
    FactAnalysis(HtnInstance& htn, bool preprocess_facts) : _htn(htn), _traversal(htn),  _preprocess_facts(preprocess_facts), _init_state(_htn.getInitState()) {
        resetReachability();

        if (_preprocess_facts) {
            getGroundFacts();
        }
    }
    
    bool checkGroundingFacts() {
        return _preprocess_facts;
    }

    long long int getGroundingTime() {
        return _time_grounding_facts;
    }

    bool isInGroundFacts(const USignature& fact, bool negated) {
        if (negated) {
            return _htn.isEqualityPredicate(fact._name_id) || _ground_neg_facts.count(fact);
        } else {
            return _htn.isEqualityPredicate(fact._name_id) || _ground_pos_facts.count(fact);
        }
    }

    const USigSet& getGroundPosFacts() const {
        return _ground_pos_facts;
    }

    bool isInGroundFacts(const Signature& fact) {
        return isInGroundFacts(fact._usig, fact._negated);
    }

    void resetReachability() {
        _pos_layer_facts = _init_state;
        _neg_layer_facts.clear();
        _initialized_facts.clear();
    }

    void addReachableFact(const Signature& fact) {
        addReachableFact(fact._usig, fact._negated);
    }

    void addReachableFact(const USignature& fact, bool negated) {
        (negated ? _neg_layer_facts : _pos_layer_facts).insert(fact);
    }

    bool isReachable(const Signature& fact) {
        return isReachable(fact._usig, fact._negated);
    }
    
    bool isReachable(const USignature& fact, bool negated) {
        if (_preprocess_facts && !isInGroundFacts(fact, negated)) {
            return false;
        }
        if (negated) {
            return _neg_layer_facts.count(fact) || !_init_state.count(fact);
        }
        return _pos_layer_facts.count(fact);
    }

    void printReachableFacts() {
        Log::i("Reachable facts:\n");
        for (const auto& fact : _pos_layer_facts) {
            Log::i("  +%s\n", TOSTR(fact));
        }
        for (const auto& fact : _neg_layer_facts) {
            Log::i("  -%s\n", TOSTR(fact));
        }
    }

    bool isInvariant(const Signature& fact) {
        return isInvariant(fact._usig, fact._negated);
    }

    bool isInvariant(const USignature& fact, bool negated) {
        return !isReachable(fact, !negated);
    }

    void addRelevantFact(const USignature& fact) {
        _relevant_facts.insert(fact);
    }

    bool isRelevant(const USignature& fact) {
        return _relevant_facts.count(fact);
    }

    const USigSet& getRelevantFacts() {
        return _relevant_facts;
    }

    void addInitializedFact(const USignature& fact) {
        _initialized_facts.insert(fact);
        if (isReachable(fact, /*negated=*/true)) {
            _neg_layer_facts.insert(fact);
        }
    }

    bool isInitialized(const USignature& fact) {
        return _initialized_facts.count(fact);
    }

    enum FactInstantiationMode {FULL, LIFTED};
    enum OperationType {ACTION, REDUCTION, UNKNOWN};
    const SigSet& getPossibleFactChanges(const USignature& sig, FactInstantiationMode mode = FULL, OperationType opType = UNKNOWN);

    void eraseCachedPossibleFactChanges(const USignature& sig);

    SigSet inferPreconditions(const USignature& op) {
        static USigSet EMPTY_USIG_SET;
        auto factFrame = getFactFrame(op, EMPTY_USIG_SET);
        EMPTY_USIG_SET.clear();
        return factFrame.preconditions;
    }

    std::vector<FlatHashSet<int>> getReducedArgumentDomains(const HtnOp& op);

    inline bool isPseudoOrGroundFactReachable(const USignature& sig, bool negated) {
        if (!_htn.isFullyGround(sig)) return true;
        
        // Q-Fact:
        if (_htn.hasQConstants(sig)) {
            for (const auto& decSig : _htn.decodeObjects(sig, _htn.getEligibleArgs(sig))) {
                if (isReachable(decSig, negated)) return true;
            }
            return false;
        }

        return isReachable(sig, negated);
    }

    inline bool isPseudoOrGroundFactReachable(const Signature& sig) {
        return isPseudoOrGroundFactReachable(sig._usig, sig._negated);
    }

    inline bool hasValidPreconditions(const SigSet& preconds) {
        for (const Signature& pre : preconds) if (!isPseudoOrGroundFactReachable(pre)) {
            return false;
        } 
        return true;
    }

private:
    FactFrame getFactFrame(const USignature& sig, USigSet& currentOps);
    void getGroundFacts();
    void extractGroundFactsFromPandaPiGrounderFile(const std::string& filename);

    /**
     * For a lift fact, return for each argument the set of object that it can be grounded to using the set of all possible ground facts that are reachable.
     * Can only be called when using the option preprocessFacts.
     */
    const std::vector<FlatHashSet<int>>& getMaxAllowedDomainForLiftFactParams(const Signature& sig);

};

#endif
