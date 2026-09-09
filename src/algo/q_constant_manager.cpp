#include "algo/q_constant_manager.h"

#include <algorithm>
#include <cassert>
#include <iomanip>
#include <sstream>

#include "algo/arg_iterator.h"
#include "algo/sample_arg_iterator.h"
#include "data/htn_instance.h"
#include "data/htn_op.h"
#include "util/log.h"
#include "util/names.h"

int QConstantManager::nextId() const {
    return std::numeric_limits<int>::max() - _origin_position_ids.size();
}

bool QConstantManager::containsAny(const USignature& signature) const {
    return std::any_of(signature._args.begin(), signature._args.end(), [&](int argument) { return contains(argument); });
}

std::optional<std::vector<int>> QConstantManager::takeOperationDomain(int qConstant, const USignature& operation) {
    const auto domainsForConstant = _operation_domains.find(qConstant);
    if (domainsForConstant == _operation_domains.end()) return std::nullopt;
    const auto domain = domainsForConstant->second.find(operation);
    if (domain == domainsForConstant->second.end()) return std::nullopt;

    std::vector<int> result = std::move(domain->second);
    domainsForConstant->second.erase(domain);
    if (domainsForConstant->second.empty()) _operation_domains.erase(domainsForConstant);
    return result;
}

std::optional<Action> QConstantManager::instantiate(const Action& action, const std::vector<FlatHashSet<int>>& argumentDomains, size_t originPositionId) {
    std::optional<std::vector<int>> arguments = instantiateArguments(action, argumentDomains, originPositionId);
    if (!arguments) return std::nullopt;
    return _htn.toAction(action.getNameId(), arguments.value());
}

std::optional<Reduction> QConstantManager::instantiate(const Reduction& reduction, const std::vector<FlatHashSet<int>>& argumentDomains, size_t originPositionId) {
    std::optional<std::vector<int>> arguments = instantiateArguments(reduction, argumentDomains, originPositionId);
    if (!arguments) return std::nullopt;
    return reduction.substituteRed(Substitution(reduction.getArguments(), arguments.value()));
}

std::optional<std::vector<int>> QConstantManager::instantiateArguments(const HtnOp& operation, const std::vector<FlatHashSet<int>>& argumentDomains, size_t originPositionId) {
    if (operation.getArguments().empty()) return std::vector<int>();
    if (argumentDomains.size() != operation.getArguments().size()) return std::nullopt;

    std::vector<int> arguments = operation.getArguments();
    std::vector<size_t> variableArgumentIndices;
    for (size_t argumentIndex = 0; argumentIndex < arguments.size(); argumentIndex++) {
        if (_htn.isVariable(arguments[argumentIndex])) variableArgumentIndices.push_back(argumentIndex);
    }

    for (size_t argumentIndex : variableArgumentIndices) {
        if (!argumentDomains[argumentIndex].empty()) continue;
        Log::d("Empty domain for arg %s of %s\n", TOSTR(arguments[argumentIndex]), TOSTR(operation.getSignature()));
        return std::nullopt;
    }

    FlatHashMap<int, int> introducedQConstantsPerSort;
    NodeHashMap<int, std::vector<int>> operationDomains;
    for (size_t argumentIndex : variableArgumentIndices) {
        const FlatHashSet<int>& domain = argumentDomains[argumentIndex];
        if (domain.size() == 1) {
            arguments[argumentIndex] = *domain.begin();
            continue;
        }

        const int primarySort = _htn.getSorts(operation.getNameId())[argumentIndex];
        const int sortCounter = introducedQConstantsPerSort[primarySort]++;
        std::vector<int> domainVector(domain.begin(), domain.end());
        std::stringstream domainHash;
        domainHash << std::hex << USignatureHasher()(USignature(primarySort, domainVector));
        const std::string name = "Q_" + std::to_string(originPositionId)
                + "_" + _htn.toString(primarySort)
                + ":" + std::to_string(sortCounter)
                + "_" + domainHash.str()
                + (_share_q_constants ? std::string() : "_#" + std::to_string(size()));

        arguments[argumentIndex] = create(name, domain, originPositionId);
        operationDomains[arguments[argumentIndex]] = std::move(domainVector);
    }

    const USignature instantiatedSignature(operation.getNameId(), arguments);
    for (auto& [qConstant, domain] : operationDomains) {
        _operation_domains[qConstant][instantiatedSignature] = std::move(domain);
    }
    return arguments;
}

int QConstantManager::create(const std::string& name, const FlatHashSet<int>& domain, size_t originPositionId) {
    assert(originPositionId > 0);
    const auto existing = _htn._name_table.find(name);
    if (existing != _htn._name_table.end()) {
        const int id = existing->second;
        assert(getOriginPositionId(id) == originPositionId);
        assert(getDomain(id) == domain);
        return id;
    }

    const int id = nextId();
    _htn._name_table[name] = id;
    _htn._name_back_table[id] = name;

    const int exactDomainSort = _htn.nameId("qsort_" + name);
    _htn._constants_by_sort[exactDomainSort].insert(domain.begin(), domain.end());

    FlatHashSet<int> guaranteedSorts(_htn._declared_sort_ids.begin(), _htn._declared_sort_ids.end());
    for (int constant : domain) {
        std::vector<int> invalidSorts;
        for (int sort : guaranteedSorts) {
            if (!_htn._constants_by_sort[sort].count(constant)) invalidSorts.push_back(sort);
        }
        for (int sort : invalidSorts) guaranteedSorts.erase(sort);
    }

    _origin_position_ids[id] = originPositionId;
    _domain_sort_ids[id] = exactDomainSort;
    _domains[id] = domain;
    _guaranteed_sorts[id] = std::move(guaranteedSorts);
    _smallest_id = std::min(_smallest_id, id);
    return id;
}

bool QConstantManager::hasConsistentlyTypedArguments(const USignature& signature) const {
    const std::vector<int>& sorts = _htn.getSorts(signature._name_id);
    for (size_t argumentIndex = 0; argumentIndex < signature._args.size(); ++argumentIndex) {
        const int argument = signature._args[argumentIndex];
        if (_htn.isVariable(argument)) continue;
        const FlatHashSet<int>& validConstants = _htn.getConstantsOfSort(sorts[argumentIndex]);
        if (!contains(argument) && !validConstants.count(argument)) return false;
        if (contains(argument) && std::none_of(getDomain(argument).begin(), getDomain(argument).end(),
                [&](int constant) { return validConstants.count(constant); })) return false;
    }
    return true;
}

std::vector<TypeConstraint> QConstantManager::getTypeConstraints(const USignature& signature) const {
    std::vector<TypeConstraint> constraints;
    const std::vector<int>& sorts = _htn.getSorts(signature._name_id);
    for (size_t argumentIndex = 0; argumentIndex < signature._args.size(); ++argumentIndex) {
        const int argument = signature._args[argumentIndex];
        const int requiredSort = sorts[argumentIndex];
        if (!contains(argument)) {
            assert(_htn.getConstantsOfSort(requiredSort).count(argument));
            continue;
        }
        if (getGuaranteedSorts(argument).count(requiredSort)) continue;

        std::vector<int> valid;
        std::vector<int> invalid;
        const FlatHashSet<int>& validConstants = _htn.getConstantsOfSort(requiredSort);
        for (int constant : getDomain(argument)) {
            (validConstants.count(constant) ? valid : invalid).push_back(constant);
        }
        if (valid.size() >= invalid.size()) constraints.emplace_back(argument, true, std::move(valid));
        else constraints.emplace_back(argument, false, std::move(invalid));
    }
    return constraints;
}

std::vector<std::vector<int>> QConstantManager::getCandidateArgumentDomains(const USignature& signature, const std::vector<int>& restrictiveSorts) const {
    if (!containsAny(signature) && _htn.isFullyGround(signature)) return {};

    std::vector<std::vector<int>> eligibleArguments(signature._args.size());
    for (size_t argumentIndex = 0; argumentIndex < signature._args.size(); argumentIndex++) {
        const int argument = signature._args[argumentIndex];
        if (_htn.isVariable(argument) || contains(argument)) {
            const FlatHashSet<int>& domain = contains(argument)
                    ? getDomain(argument)
                    : _htn.getConstantsOfSort(_htn.getSorts(signature._name_id)[argumentIndex]);
            if (restrictiveSorts.empty()) {
                eligibleArguments[argumentIndex].insert(eligibleArguments[argumentIndex].end(), domain.begin(), domain.end());
            } else {
                const FlatHashSet<int>& restrictiveDomain = _htn.getConstantsOfSort(restrictiveSorts[argumentIndex]);
                for (int constant : domain) {
                    if (restrictiveDomain.count(constant)) eligibleArguments[argumentIndex].push_back(constant);
                }
            }
        } else {
            eligibleArguments[argumentIndex].push_back(argument);
        }
        if (eligibleArguments[argumentIndex].empty()) return {};
    }
    return eligibleArguments;
}

ArgIterator QConstantManager::enumerateCandidateDecodings(const USignature& signature, const std::vector<int>& restrictiveSorts) const {
    return enumerateCandidateDecodings(signature, getCandidateArgumentDomains(signature, restrictiveSorts));
}

ArgIterator QConstantManager::enumerateCandidateDecodings(const USignature& signature, std::vector<std::vector<int>> candidateDomains) const {
    return ArgIterator(signature._name_id, std::move(candidateDomains));
}

SampleArgIterator QConstantManager::sampleCandidateDecodings(const USignature& signature, const std::vector<int>& restrictiveSorts, size_t numSamples) const {
    return sampleCandidateDecodings(signature, getCandidateArgumentDomains(signature, restrictiveSorts), numSamples);
}

SampleArgIterator QConstantManager::sampleCandidateDecodings(const USignature& signature, std::vector<std::vector<int>> candidateDomains, size_t numSamples) const {
    return SampleArgIterator(signature._name_id, std::move(candidateDomains), numSamples);
}
