#include "data/q_constant_registry.h"

#include <algorithm>
#include <cassert>

void QConstantRegistry::add(int id, size_t originPositionId, int primarySort, FlatHashSet<int> guaranteedSorts) {
    assert(!_originPositionIds.count(id));
    _originPositionIds[id] = originPositionId;
    _primarySorts[id] = primarySort;
    _guaranteedSorts[id] = std::move(guaranteedSorts);
    _smallestId = std::min(_smallestId, id);
}

void QConstantRegistry::setOperationDomain(int id, const USignature& operation, std::vector<int> domain) {
    assert(contains(id));
    _operationDomains[id][operation] = std::move(domain);
}

std::optional<std::vector<int>> QConstantRegistry::takeOperationDomain(int id, const USignature& operation) {
    const auto domainsForConstant = _operationDomains.find(id);
    if (domainsForConstant == _operationDomains.end()) return std::nullopt;
    const auto domain = domainsForConstant->second.find(operation);
    if (domain == domainsForConstant->second.end()) return std::nullopt;

    std::vector<int> result = std::move(domain->second);
    domainsForConstant->second.erase(domain);
    if (domainsForConstant->second.empty()) _operationDomains.erase(domainsForConstant);
    return result;
}
