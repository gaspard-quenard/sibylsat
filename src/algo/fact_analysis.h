
#ifndef DOMPASCH_LILOTANE_ANALYSIS_H
#define DOMPASCH_LILOTANE_ANALYSIS_H

#include "data/htn_instance.h"
#include "algo/network_traversal.h"
#include "algo/arg_iterator.h"
#include "util/statistics.h"
#include "util/bitvec.h"

typedef std::function<bool(const USignature&, bool)> StateEvaluator;

class FactAnalysis {

private:

    HtnInstance& _htn;
    Statistics& _stats;
    NetworkTraversal _traversal;

    USigSet _init_state;

    BitVec _init_state_pos_bitvec;
    BitVec _init_state_neg_bitvec;
    BitVec _pos_layer_facts_bitvec;
    BitVec _neg_layer_facts_bitvec;
    BitVec _initialized_facts_bitvec;
    BitVec _relevant_facts_bitvec;
    int _cutoff_neg_facts;
    BitVec _empty;
    NodeHashMap<USignature, SigSet, USignatureHasher> _pseudo_fact_changes_cache;


    const bool _preprocess_facts;
    const bool _optimal;
    USigSet _ground_pos_facts;
    USigSet _ground_neg_facts;
    // For each lift fact, store the set of ground facts that it can be grounded to
    NodeHashMap<int, std::vector<FlatHashSet<int>>> _allowed_domain_per_pos_lift_facts;
    NodeHashMap<int, std::vector<FlatHashSet<int>>> _allowed_domain_per_neg_lift_facts;

    // Maps an (action|reduction) name 
    // to the set of (partially lifted) fact signatures
    // that might be added to the state due to this operator. 
    NodeHashMap<int, SigSet> _fact_changes; 
    NodeHashMap<int, SigSet> _lifted_fact_changes;
    NodeHashMap<USignature, SigSet, USignatureHasher> _fact_changes_cache;

    // TEST
    NodeHashMap<int, BitVec> _fact_changes_ground_pos_bitvec;
    NodeHashMap<int, BitVec> _fact_changes_ground_neg_bitvec;
    NodeHashMap<int, SigSet> _fact_change_pseudo_facts;
    // END TEST

    NodeHashMap<int, FactFrame> _fact_frames;

public:
    
    FactAnalysis(HtnInstance& htn, bool preprocess_facts, bool optimal) : _htn(htn), _traversal(htn),  _preprocess_facts(preprocess_facts), _optimal(optimal), _init_state(_htn.getInitState()), _stats(Statistics::getInstance()) {
        
        // If we preprocess facts, we need to ground them
        if (_preprocess_facts || _optimal) {
            Statistics::getInstance().beginTiming(TimingStage::INIT_GROUNDING);
            getGroundFacts(_optimal);
            std::vector<USignature> posFacts, negFacts;
            for (const USignature& fact : _ground_pos_facts) {
                posFacts.push_back(fact);
                // negFacts.push_back(fact);
            }

            // Get all the _ground_neg_facts that is not in the _ground_pos_facts
            std::vector<USignature> exclusiveNegFacts;
            for (const USignature& fact : _ground_neg_facts) {
                if (!_ground_pos_facts.count(fact)) {
                    exclusiveNegFacts.push_back(fact);
                }
            }
            Log::i("Found %zu exclusive negative facts.\n", exclusiveNegFacts.size());
            // for (const USignature& negFact : exclusiveNegFacts) {
            //     posFacts.push_back(negFact);
            // }
            _cutoff_neg_facts = posFacts.size(); // All predicate with idx >= _cutoff_neg_facts are only negative facts

            _htn.setGroundPosAndNegFacts(posFacts, exclusiveNegFacts);
            _pos_layer_facts_bitvec = BitVec(_htn.getNumPositiveGroundFacts());
            _neg_layer_facts_bitvec = BitVec(_htn.getNumPositiveGroundFacts());
            _init_state_pos_bitvec = BitVec(_htn.getNumPositiveGroundFacts());
            _init_state_neg_bitvec = BitVec(_htn.getNumPositiveGroundFacts());
            _relevant_facts_bitvec = BitVec(_htn.getNumPositiveGroundFacts());
            _empty = BitVec(_htn.getNumPositiveGroundFacts(), false);
            for (int i = 0; i < _htn.getNumPositiveGroundFacts(); ++i) {
                const USignature& iSig = _htn.getGroundPositiveFact(i);
                // Log::i("Init Fact %d: %s\n", i, TOSTR(iSig));
                if (_init_state.count(iSig)) {
                    _init_state_pos_bitvec.set(i);
                } else {
                    _init_state_neg_bitvec.set(i);
                }
            }
            Statistics::getInstance().endTiming(TimingStage::INIT_GROUNDING);
            Log::i("Grounding time: %f\n", Statistics::getInstance().getTiming(TimingStage::INIT_GROUNDING));
        }

        resetReachability();
    }
    
    bool checkGroundingFacts() {
        return _preprocess_facts;
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
        // Reset the bit vectors
        _pos_layer_facts_bitvec = _init_state_pos_bitvec;
        _neg_layer_facts_bitvec = _init_state_neg_bitvec;
        _initialized_facts_bitvec = BitVec(_htn.getNumPositiveGroundFacts());
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




    // API BITVEC
    bool isReachableBitVec(const int predId, bool negated) {
        if (negated) {
            return _neg_layer_facts_bitvec.test(predId);
        } else {
            return predId < _cutoff_neg_facts && _pos_layer_facts_bitvec.test(predId);
        }
    }

    const BitVec& getReachableFactsBitVec(bool negated) {
        return negated ? _neg_layer_facts_bitvec : _pos_layer_facts_bitvec;
    }

    void addReachableFactBitVec(const int predId, bool negated) {
        if (negated) {
            _neg_layer_facts_bitvec.set(predId);
        } else if (predId < _cutoff_neg_facts) {
            _pos_layer_facts_bitvec.set(predId);
        }
    }

    void setReachableFactsBitVec(const BitVec& pos_facts, const BitVec& neg_facts) {
        _pos_layer_facts_bitvec = pos_facts;
        _neg_layer_facts_bitvec = neg_facts;
    }

    void addMultipleReachableFactsBitVec(const BitVec& facts, bool negated) {
        if (negated) {
            _neg_layer_facts_bitvec.or_with(facts);
        } else {
            _pos_layer_facts_bitvec.or_with(facts);
        }
    }

    bool isInvariantBitVec(const int predId, bool negated) {
        return !isReachableBitVec(predId, !negated);
    }

    void removeInvariantGroundFactsBitVec(BitVec& facts, bool negated) {
        if (negated) {
            facts.and_with(_pos_layer_facts_bitvec);
        } else {
            facts.and_with(_neg_layer_facts_bitvec);
        }
    }

    void addInitializedFactBitVec(const int predId) {
        _initialized_facts_bitvec.set(predId);
        if (isReachableBitVec(predId, /*negated=*/true)) {
            _neg_layer_facts_bitvec.set(predId);
        }
    }

    bool isInitializedBitVec(const int predId) {
        return _initialized_facts_bitvec.test(predId);
    }

    inline bool hasValidPreconditionsBitVec(const SigSet& preconds) {
        for (const Signature& pre : preconds) if (!isPseudoOrGroundFactReachableBitVec(pre._usig, pre._negated)) {
            // Log::i("Precondition %s is not reachable\n", TOSTR(pre));
            // printReachableFactsBitVec();
            // printReachableFacts();
            return false;
        } 
        return true;
    }

    inline bool isPseudoOrGroundFactReachableBitVec(const USignature& sig, bool negated) {
        if (!_htn.isFullyGround(sig)) return true;

        if (_htn.isEqualityPredicate(sig._name_id)) {
            // Log::i("Fact %s is an equality predicate\n", TOSTR(sig));
            // I have to do things differently there, since I don't want to ground all possible equality predicates
            // Because if there are many objects, this would create a lot of equality predicates
            // So if this is positive, only check if both parameters can have the same value to have at least one instantiation
            // If this is negative, check that both par                    ameters are different

            // Do it the old way for now
            // Q-Fact:
            bool any = false;
            if (_htn.hasQConstants(sig)) {
                for (const auto& decSig : _htn.decodeObjects(sig, _htn.getEligibleArgs(sig))) {
                    any = negated ? decSig._args[0] != decSig._args[1] : decSig._args[0] == decSig._args[1];
                    if (any) break;
                }
                return any;
            }
            else {
                return negated ? sig._args[0] != sig._args[1] : sig._args[0] == sig._args[1];
            }
        }
        
        if (!_htn.hasQConstants(sig)) {
            int predId = _htn.getGroundFactId(sig, negated);
            return predId >= 0 && isReachableBitVec(predId, negated);
        }
        // Q-Fact:
        BitVec result = ArgIterator2::getFullInstantiation2(sig, negated, _htn, _htn.getSorts(sig._name_id));
        // for (size_t predId : result) {
            // Log::i("Sig %s can be grounded to %s\n", TOSTR(sig), TOSTR(_htn.getGroundPositiveFact(predId)));
        // }
        // If any of the instantiations is reachable, return true
        const BitVec& facts = negated ? _neg_layer_facts_bitvec : _pos_layer_facts_bitvec;
        result.and_with(facts);
        return result.any();
        // }

        // return isReachable(sig, negated);
    }

    void addRelevantFactBitVec(const int predId) {
        _relevant_facts_bitvec.set(predId);
    }

    void addMultipleRelevantFactsBitVec(const BitVec& facts) {
        _relevant_facts_bitvec.or_with(facts);
    }

    // bool isRelevantBitVec(const int predId) {
    //     return _relevant_facts_bitvec.test(predId);
    // }

    bool isRelevantBitVec(const USignature& fact, bool negated) {
        int predId = _htn.getGroundFactId(fact, negated);
        return predId >= 0 && _relevant_facts_bitvec.test(predId);
    }

    void printRelevantFactsBitVec() {
        Log::i("Relevant facts (bitvec):\n");
        for (int predId: _relevant_facts_bitvec) {
            Log::i("  %s\n", TOSTR(_htn.getGroundPositiveFact(predId)));
        }
    }

    bool isRelevantBitVec(const int predId) {
        return _relevant_facts_bitvec.test(predId);
    }

    const BitVec& getRelevantFactsBitVec() {
        return _relevant_facts_bitvec;
    }

    const BitVec& getPossibleGroundFactChanges(const USignature& sig, bool negated, FactInstantiationMode mode = FULL, OperationType opType = UNKNOWN);
    const SigSet& getPossiblePseudoGroundFactChanges(const USignature& sig, FactInstantiationMode mode = FULL, OperationType opType = UNKNOWN);

    void printReachableFactsBitVec() {
        Log::i("Reachable facts bitvec:\n");
        for (int predId: _pos_layer_facts_bitvec) {
            Log::i("  +%s\n", TOSTR(_htn.getGroundPositiveFact(predId)));
        }
        for (int predId: _neg_layer_facts_bitvec) {
            Log::i("  -%s\n", TOSTR(_htn.getGroundPositiveFact(predId)));
        }
    }

private:
    FactFrame getFactFrame(const USignature& sig, USigSet& currentOps);
    /**
     * Ground the problems using pandaPiGrounder. By default, make the pandaPiGrounder output only the ground facts that are reachable.
     * If getAlsoGroundOps is true, make the pandaPiGrounder also output the ground operators (methods and tasks) that are reachable.
     */
    void getGroundFacts(bool getAlsoGroundOps);
    void extractGroundFactsFromPandaPiGrounderFile(const std::string& filename);

    /**
     * For a lift fact, return for each argument the set of object that it can be grounded to using the set of all possible ground facts that are reachable.
     * Can only be called when using the option preprocessFacts.
     */
    const std::vector<FlatHashSet<int>>& getMaxAllowedDomainForLiftFactParams(const Signature& sig);

    void removeDuplicatesInLiftedFactChanges(int nameId);
    bool isLiftedFactSuperset(const USignature& liftedFact, const USignature& possibleSuperset);

};

#endif
