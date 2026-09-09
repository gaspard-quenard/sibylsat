#ifndef SIBYLSAT_Q_CONSTANT_MANAGER_H
#define SIBYLSAT_Q_CONSTANT_MANAGER_H

#include <limits>
#include <optional>
#include <string>
#include <vector>

#include "algo/arg_iterator.h"
#include "algo/sample_arg_iterator.h"
#include "data/action.h"
#include "data/reduction.h"
#include "data/signature.h"
#include "util/hashmap.h"

class HtnInstance;
class HtnOp;

/**
 * Owns the pseudo-constants introduced while operations are instantiated.
 *
 * The HTN instance supplies immutable operation and sort information. This
 * manager owns all search-time Q-constant metadata, including domains,
 * origins, type information, and operation-specific domains consumed by the
 * SAT encoding.
 */
class QConstantManager {
private:
    HtnInstance& _htn;
    const bool _share_q_constants;

    FlatHashMap<int, size_t> _origin_position_ids;
    FlatHashMap<int, int> _domain_sort_ids;
    NodeHashMap<int, FlatHashSet<int>> _domains;
    NodeHashMap<int, FlatHashSet<int>> _guaranteed_sorts;
    NodeHashMap<int, NodeHashMap<USignature, std::vector<int>, USignatureHasher>> _operation_domains;
    int _smallest_id = std::numeric_limits<int>::max();

    int nextId() const;
    int create(const std::string& name, const FlatHashSet<int>& domain, size_t originPositionId);
    std::optional<std::vector<int>> instantiateArguments(const HtnOp& operation, const std::vector<FlatHashSet<int>>& argumentDomains, size_t originPositionId);

public:
    QConstantManager(HtnInstance& htn, bool shareQConstants) : _htn(htn), _share_q_constants(shareQConstants) {}

    bool contains(int id) const { return !_origin_position_ids.empty() && id >= _smallest_id; }
    bool containsAny(const USignature& signature) const;
    size_t size() const { return _origin_position_ids.size(); }

    size_t getOriginPositionId(int qConstant) const { return _origin_position_ids.at(qConstant); }
    /** Return the synthetic exact-domain sort used by indexed fact matching. */
    int getDomainSortId(int qConstant) const { return _domain_sort_ids.at(qConstant); }
    const FlatHashSet<int>& getGuaranteedSorts(int qConstant) const { return _guaranteed_sorts.at(qConstant); }
    const FlatHashSet<int>& getDomain(int qConstant) const { return _domains.at(qConstant); }

    /** Remove and return the exact domain recorded for one instantiated operation. */
    std::optional<std::vector<int>> takeOperationDomain(int qConstant, const USignature& operation);

    /** Instantiate free action arguments with constants or newly created Q-constants. */
    std::optional<Action> instantiate(const Action& action, const std::vector<FlatHashSet<int>>& argumentDomains, size_t originPositionId);
    /** Instantiate free reduction arguments with constants or newly created Q-constants. */
    std::optional<Reduction> instantiate(const Reduction& reduction, const std::vector<FlatHashSet<int>>& argumentDomains, size_t originPositionId);

    /** Return whether every fixed or pseudo-constant argument is compatible with its declared sort. */
    bool hasConsistentlyTypedArguments(const USignature& signature) const;
    /** Build SAT type restrictions for Q-constants used outside all of their guaranteed sorts. */
    std::vector<TypeConstraint> getTypeConstraints(const USignature& signature) const;

    /** Return candidate ground objects for each non-ground argument. */
    std::vector<std::vector<int>> getCandidateArgumentDomains(const USignature& signature, const std::vector<int>& restrictiveSorts = {}) const;
    ArgIterator enumerateCandidateDecodings(const USignature& signature, const std::vector<int>& restrictiveSorts = {}) const;
    ArgIterator enumerateCandidateDecodings(const USignature& signature, std::vector<std::vector<int>> candidateDomains) const;
    SampleArgIterator sampleCandidateDecodings(const USignature& signature, const std::vector<int>& restrictiveSorts, size_t numSamples) const;
    SampleArgIterator sampleCandidateDecodings(const USignature& signature, std::vector<std::vector<int>> candidateDomains, size_t numSamples) const;
};

#endif
