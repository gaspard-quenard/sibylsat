#include "algo/fact_analysis.h"

#include "util/log.h"

FactAnalysis::FactAnalysis(HtnInstance& htn, QConstantManager& qConstants, GroundFacts groundFacts)
        : _htn(htn),
          _q_constants(qConstants),
          _init_state(_htn.getInitState()),
          _ground_pos_facts(groundFacts.takePositive()),
          _ground_neg_facts(groundFacts.takeNegative()) {
    std::vector<USignature> positiveFacts(_ground_pos_facts.begin(), _ground_pos_facts.end());
    std::vector<USignature> exclusiveNegativeFacts;
    for (const USignature& fact : _ground_neg_facts) {
        if (!_ground_pos_facts.count(fact)) exclusiveNegativeFacts.push_back(fact);
    }

    Log::i("Found %zu exclusive negative facts.\n", exclusiveNegativeFacts.size());
    _cutoff_neg_facts = positiveFacts.size();
    for (int equalityPredicateId : _htn.getEqualityPredicateIds()) {
        const std::vector<int>& sorts = _htn.getSorts(equalityPredicateId);
        assert(sorts.size() == 2 && sorts[0] == sorts[1]);
        for (int constant : _htn.getConstantsOfSort(sorts[0])) {
            positiveFacts.emplace_back(equalityPredicateId, std::vector<int>{constant, constant});
        }
    }
    _ground_facts.reset(std::move(positiveFacts), exclusiveNegativeFacts);

    const int numGroundFacts = getNumGroundFacts();
    _reachable_pos_facts = BitVec(numGroundFacts);
    _reachable_neg_facts = BitVec(numGroundFacts);
    _init_state_pos = BitVec(numGroundFacts);
    _init_state_neg = BitVec(numGroundFacts);
    _relevant_facts = BitVec(numGroundFacts);
    for (int factId = 0; factId < numGroundFacts; factId++) {
        if (_init_state.count(getGroundFact(factId))) _init_state_pos.set(factId);
        else _init_state_neg.set(factId);
    }
    _original_init_state_pos = _init_state_pos;
    _original_init_state_neg = _init_state_neg;
    resetReachability();
}

BitVec FactAnalysis::findMatchingGroundFactIds(const USignature& signature, bool negated, const std::vector<int>& requestedSorts) {
    const std::vector<int>& argumentSorts = requestedSorts.empty() ? _htn.getSorts(signature._name_id) : requestedSorts;
    std::vector<int> restrictiveSorts(signature._args.size(), -1);
    std::vector<int> fixedConstants(signature._args.size(), -1);
    for (size_t argumentIndex = 0; argumentIndex < signature._args.size(); ++argumentIndex) {
        const int argument = signature._args[argumentIndex];
        if (_q_constants.contains(argument)) restrictiveSorts[argumentIndex] = _q_constants.getDomainSortId(argument);
        else if (!_htn.isVariable(argument)) fixedConstants[argumentIndex] = argument;
    }
    return _ground_facts.findMatchingFactIds(signature._name_id, negated, argumentSorts, restrictiveSorts,
            fixedConstants, _htn.getConstantsBySort());
}
