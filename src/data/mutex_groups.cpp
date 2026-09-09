#include "data/mutex_groups.h"

#include <algorithm>
#include <cassert>

MutexGroups::MutexGroups(std::vector<std::vector<int>> factIdsByGroup, size_t numGroundFacts)
        : _group_ids_by_fact(numGroundFacts) {
    _fact_ids_by_group.reserve(factIdsByGroup.size());
    for (std::vector<int>& factIds : factIdsByGroup) {
        std::sort(factIds.begin(), factIds.end());
        factIds.erase(std::unique(factIds.begin(), factIds.end()), factIds.end());
        if (factIds.size() < 2) continue;

        const int groupId = _fact_ids_by_group.size();
        for (int factId : factIds) {
            assert(factId >= 0 && static_cast<size_t>(factId) < numGroundFacts);
            _group_ids_by_fact[factId].push_back(groupId);
        }
        _fact_ids_by_group.push_back(std::move(factIds));
    }
}

const std::vector<int>& MutexGroups::getGroupIdsForFact(int factId) const {
    assert(factId >= 0 && static_cast<size_t>(factId) < _group_ids_by_fact.size());
    return _group_ids_by_fact[factId];
}

const std::vector<int>& MutexGroups::getFactIdsInGroup(int groupId) const {
    return _fact_ids_by_group.at(groupId);
}

bool MutexGroups::containsFact(int factId) const {
    return factId >= 0 && static_cast<size_t>(factId) < _group_ids_by_fact.size() && !_group_ids_by_fact[factId].empty();
}
