#ifndef SIBYLSAT_Q_CONSTANT_REGISTRY_H
#define SIBYLSAT_Q_CONSTANT_REGISTRY_H

#include <cstddef>
#include <limits>
#include <optional>
#include <vector>

#include "data/signature.h"
#include "util/hashmap.h"

/** Owns pseudo-constant metadata independently of HTN model construction. */
class QConstantRegistry {
private:
    FlatHashMap<int, size_t> _originPositionIds;
    FlatHashMap<int, int> _primarySorts;
    NodeHashMap<int, FlatHashSet<int>> _guaranteedSorts;
    NodeHashMap<int, NodeHashMap<USignature, std::vector<int>, USignatureHasher>> _operationDomains;
    int _smallestId = std::numeric_limits<int>::max();

public:
    /** Allocate the next reserved pseudo-constant ID. */
    int nextId() const { return std::numeric_limits<int>::max() - _originPositionIds.size(); }

    /** Record a newly allocated pseudo-constant and its type information. */
    void add(int id, size_t originPositionId, int primarySort, FlatHashSet<int> guaranteedSorts);

    bool contains(int id) const { return !_originPositionIds.empty() && id >= _smallestId; }
    size_t size() const { return _originPositionIds.size(); }
    size_t getOriginPositionId(int id) const { return _originPositionIds.at(id); }
    int getPrimarySort(int id) const { return _primarySorts.at(id); }
    const FlatHashSet<int>& getGuaranteedSorts(int id) const { return _guaranteedSorts.at(id); }

    /** Remember the domain valid for one instantiated operation. */
    void setOperationDomain(int id, const USignature& operation, std::vector<int> domain);

    /** Remove and return an operation-specific domain once the encoder consumes it. */
    std::optional<std::vector<int>> takeOperationDomain(int id, const USignature& operation);
};

#endif
