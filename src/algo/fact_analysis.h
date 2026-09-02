
#ifndef DOMPASCH_LILOTANE_ANALYSIS_H
#define DOMPASCH_LILOTANE_ANALYSIS_H

#include <optional>

#include "data/htn_instance.h"
#include "util/bitvec.h"

class FactAnalysis {

private:

    HtnInstance& _htn;

    USigSet _init_state;

    BitVec _init_state_pos;
    BitVec _init_state_neg;
    BitVec _reachable_pos_facts;
    BitVec _reachable_neg_facts;
    BitVec _relevant_facts;
    int _cutoff_neg_facts;

    USigSet _ground_pos_facts;
    USigSet _ground_neg_facts;
    // For each lift fact, store the set of ground facts that it can be grounded to
    NodeHashMap<int, std::vector<FlatHashSet<int>>> _allowed_domain_per_pos_lift_facts;
    NodeHashMap<int, std::vector<FlatHashSet<int>>> _allowed_domain_per_neg_lift_facts;

public:

    explicit FactAnalysis(HtnInstance& htn);

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

    const std::vector<FlatHashSet<int>>& getGroundFactArgumentDomains(const Signature& fact);

    void resetReachability() {
        // Reset the bit vectors
        _reachable_pos_facts = _init_state_pos;
        _reachable_neg_facts = _init_state_neg;
    }

    // Update the "initial state" used by resetReachability(). Call this when the effective
    // starting state of the search shifts (e.g. after a batch of tasks is accomplished).
    void updateInitialState(const BitVec& pos, const BitVec& neg) {
        _init_state_pos = pos;
        _init_state_neg = neg;
    }

    std::optional<std::vector<FlatHashSet<int>>> computeReachableArgumentDomains(const HtnOp& operation);




    // Reachability API
    bool isReachable(const int predId, bool negated) {
        if (negated) {
            return _reachable_neg_facts.test(predId);
        } else {
            return predId < _cutoff_neg_facts && _reachable_pos_facts.test(predId);
        }
    }

    const BitVec& getReachableFacts(bool negated) {
        return negated ? _reachable_neg_facts : _reachable_pos_facts;
    }

    const BitVec& getInitialFacts(bool negated) const {
        return negated ? _init_state_neg : _init_state_pos;
    }

    bool isInitiallyReachable(const int predId, bool negated) const {
        const USignature& fact = _htn.getGroundPositiveFact(predId);
        if (_htn.isEqualityPredicate(fact._name_id)) {
            return negated ? fact._args[0] != fact._args[1] : fact._args[0] == fact._args[1];
        }
        if (negated) {
            return _init_state_neg.test(predId);
        }
        return predId < _cutoff_neg_facts && _init_state_pos.test(predId);
    }

    void addReachableFact(const int predId, bool negated) {
        if (negated) {
            _reachable_neg_facts.set(predId);
        } else if (predId < _cutoff_neg_facts) {
            _reachable_pos_facts.set(predId);
        }
    }

    void addMultipleReachableFacts(const BitVec& facts, bool negated) {
        if (negated) {
            _reachable_neg_facts.or_with(facts);
        } else {
            _reachable_pos_facts.or_with(facts);
        }
    }

    bool isInvariant(const int predId, bool negated) {
        return !isReachable(predId, !negated);
    }

    void removeInvariantGroundFacts(BitVec& facts, bool negated) {
        if (negated) {
            facts.and_with(_reachable_pos_facts);
        } else {
            facts.and_with(_reachable_neg_facts);
        }
    }

    inline bool hasValidPreconditions(const SigSet& preconds) {
        for (const Signature& pre : preconds) if (!isPseudoOrGroundFactReachable(pre._usig, pre._negated)) {
            // Log::i("Precondition %s is not reachable\n", TOSTR(pre));
            // printReachableFacts();
            // printReachableFacts();
            return false;
        } 
        return true;
    }

    inline bool isPseudoOrGroundFactReachable(const USignature& sig, bool negated) {
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
            return predId >= 0 && isReachable(predId, negated);
        }
        // Q-Fact:
        BitVec result = _htn.getMatchingGroundFactIds(sig, negated, _htn.getSorts(sig._name_id));
        // for (size_t predId : result) {
            // Log::i("Sig %s can be grounded to %s\n", TOSTR(sig), TOSTR(_htn.getGroundPositiveFact(predId)));
        // }
        // If any of the instantiations is reachable, return true
        const BitVec& facts = negated ? _reachable_neg_facts : _reachable_pos_facts;
        result.and_with(facts);
        return result.any();
        // }

        // return isReachable(sig, negated);
    }

    void addRelevantFact(const int predId) {
        _relevant_facts.set(predId);
    }

    void addMultipleRelevantFacts(const BitVec& facts) {
        _relevant_facts.or_with(facts);
    }

    // bool isRelevant(const int predId) {
    //     return _relevant_facts.test(predId);
    // }

    bool isRelevant(const USignature& fact, bool negated) {
        int predId = _htn.getGroundFactId(fact, negated);
        return predId >= 0 && _relevant_facts.test(predId);
    }

    void printRelevantFacts() {
        Log::i("Relevant facts:\n");
        for (int predId: _relevant_facts) {
            Log::i("  %s\n", TOSTR(_htn.getGroundPositiveFact(predId)));
        }
    }

    bool isRelevant(const int predId) {
        return _relevant_facts.test(predId);
    }

    const BitVec& getRelevantFacts() {
        return _relevant_facts;
    }

    void printReachableFacts() {
        Log::i("Reachable facts:\n");
        for (int predId: _reachable_pos_facts) {
            Log::i("  +%s\n", TOSTR(_htn.getGroundPositiveFact(predId)));
        }
        for (int predId: _reachable_neg_facts) {
            Log::i("  -%s\n", TOSTR(_htn.getGroundPositiveFact(predId)));
        }
    }

private:
    /**
     * Ground the problems using pandaPiGrounder. By default, make the pandaPiGrounder output only the ground facts that are reachable.
     * If getAlsoGroundOps is true, make the pandaPiGrounder also output the ground operators (methods and tasks) that are reachable.
     */
    void getGroundFacts(bool getAlsoGroundOps);
    void extractGroundFactsFromPandaPiGrounderFile(const std::string& filename);

};

#endif
