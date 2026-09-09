#include "data/ground_fact_index.h"

#include <functional>

size_t GroundFactIndex::ArgumentFilterKeyHasher::operator()(const ArgumentFilterKey& key) const {
    const size_t first = std::hash<int>{}(key.value);
    const size_t second = std::hash<size_t>{}(key.argumentIndex);
    return first ^ (second + 0x9e3779b9 + (first << 6) + (first >> 2));
}

void GroundFactIndex::reset(std::vector<USignature> positiveFacts, const std::vector<USignature>& negativeFacts) {
    _firstNegativeFactId = positiveFacts.size();
    _facts = std::move(positiveFacts);
    _facts.insert(_facts.end(), negativeFacts.begin(), negativeFacts.end());

    _positiveFactIds = BitVec(_facts.size());
    for (size_t factId = 0; factId < _firstNegativeFactId; ++factId) _positiveFactIds.set(factId);

    _factIds.clear();
    for (size_t factId = 0; factId < _facts.size(); ++factId) _factIds[_facts[factId]] = factId;
    _filtersByPredicate.clear();
    _filtersBySort.clear();
    _filtersByConstant.clear();
}

int GroundFactIndex::findFactId(const USignature& fact, bool negated) const {
    const auto match = _factIds.find(fact);
    if (match == _factIds.end()) return -1;
    const int factId = match->second;
    if (!negated && static_cast<size_t>(factId) >= _firstNegativeFactId) return -1;
    return factId;
}

const BitVec& GroundFactIndex::getPredicateFilter(int predicateId) {
    const auto existing = _filtersByPredicate.find(predicateId);
    if (existing != _filtersByPredicate.end()) return existing->second;

    BitVec filter(_facts.size());
    for (size_t factId = 0; factId < _facts.size(); ++factId) {
        if (_facts[factId]._name_id == predicateId) filter.set(factId);
    }
    return _filtersByPredicate.emplace(predicateId, std::move(filter)).first->second;
}

const BitVec& GroundFactIndex::getSortFilter(int sortId, size_t argumentIndex, const NodeHashMap<int, FlatHashSet<int>>& constantsBySort) {
    const ArgumentFilterKey key{sortId, argumentIndex};
    const auto existing = _filtersBySort.find(key);
    if (existing != _filtersBySort.end()) return existing->second;

    BitVec filter(_facts.size());
    const FlatHashSet<int>& constants = constantsBySort.at(sortId);
    for (size_t factId = 0; factId < _facts.size(); ++factId) {
        const USignature& fact = _facts[factId];
        if (fact._args.size() > argumentIndex && constants.count(fact._args[argumentIndex])) filter.set(factId);
    }
    return _filtersBySort.emplace(key, std::move(filter)).first->second;
}

const BitVec& GroundFactIndex::getConstantFilter(int constantId, size_t argumentIndex) {
    const ArgumentFilterKey key{constantId, argumentIndex};
    const auto existing = _filtersByConstant.find(key);
    if (existing != _filtersByConstant.end()) return existing->second;

    BitVec filter(_facts.size());
    for (size_t factId = 0; factId < _facts.size(); ++factId) {
        const USignature& fact = _facts[factId];
        if (fact._args.size() > argumentIndex && fact._args[argumentIndex] == constantId) filter.set(factId);
    }
    return _filtersByConstant.emplace(key, std::move(filter)).first->second;
}

BitVec GroundFactIndex::findMatchingFactIds(int predicateId, bool negated, const std::vector<int>& argumentSorts,
        const std::vector<int>& restrictiveSorts, const std::vector<int>& fixedConstants,
        const NodeHashMap<int, FlatHashSet<int>>& constantsBySort) {
    BitVec matching = negated ? BitVec(_facts.size(), true) : _positiveFactIds;
    matching.and_with(getPredicateFilter(predicateId));

    for (size_t argumentIndex = 0; argumentIndex < argumentSorts.size(); ++argumentIndex) {
        if (fixedConstants.size() > argumentIndex && fixedConstants[argumentIndex] != -1) {
            matching.and_with(getConstantFilter(fixedConstants[argumentIndex], argumentIndex));
            continue;
        }
        matching.and_with(getSortFilter(argumentSorts[argumentIndex], argumentIndex, constantsBySort));
        if (restrictiveSorts.size() > argumentIndex && restrictiveSorts[argumentIndex] != -1) {
            matching.and_with(getSortFilter(restrictiveSorts[argumentIndex], argumentIndex, constantsBySort));
        }
    }
    return matching;
}
