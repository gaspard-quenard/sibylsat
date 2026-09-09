#ifndef SIBYLSAT_GROUND_FACT_INDEX_H
#define SIBYLSAT_GROUND_FACT_INDEX_H

#include <cstddef>
#include <unordered_map>
#include <vector>

#include "data/signature.h"
#include "util/bitvec.h"
#include "util/hashmap.h"

/** Indexed collection of reachable positive facts and explicitly represented negative facts. */
class GroundFactIndex {
private:
    struct ArgumentFilterKey {
        int value;
        size_t argumentIndex;

        bool operator==(const ArgumentFilterKey& other) const {
            return value == other.value && argumentIndex == other.argumentIndex;
        }
    };

    struct ArgumentFilterKeyHasher {
        size_t operator()(const ArgumentFilterKey& key) const;
    };

    std::vector<USignature> _facts;
    size_t _firstNegativeFactId = 0;
    BitVec _positiveFactIds;
    NodeHashMap<const USignature, int, USignatureHasher> _factIds;
    std::unordered_map<int, BitVec> _filtersByPredicate;
    std::unordered_map<ArgumentFilterKey, BitVec, ArgumentFilterKeyHasher> _filtersBySort;
    std::unordered_map<ArgumentFilterKey, BitVec, ArgumentFilterKeyHasher> _filtersByConstant;

    const BitVec& getPredicateFilter(int predicateId);
    const BitVec& getSortFilter(int sortId, size_t argumentIndex, const NodeHashMap<int, FlatHashSet<int>>& constantsBySort);
    const BitVec& getConstantFilter(int constantId, size_t argumentIndex);

public:
    /** Replace the indexed facts and invalidate all derived lookup filters. */
    void reset(std::vector<USignature> positiveFacts, const std::vector<USignature>& negativeFacts);

    /** Return the ID of a fact with the requested polarity, or -1 when absent. */
    int findFactId(const USignature& fact, bool negated) const;

    /** Return IDs matching the predicate, polarity, argument sorts, and fixed arguments. */
    BitVec findMatchingFactIds(int predicateId, bool negated, const std::vector<int>& argumentSorts,
            const std::vector<int>& restrictiveSorts, const std::vector<int>& fixedConstants,
            const NodeHashMap<int, FlatHashSet<int>>& constantsBySort);

    size_t size() const { return _facts.size(); }
    const USignature& getFact(size_t factId) const { return _facts.at(factId); }
};

#endif
