#include "algo/operation_domain_analyzer.h"

#include "algo/fact_analysis.h"
#include "algo/q_constant_manager.h"
#include "data/htn_instance.h"
#include "data/htn_op.h"

std::vector<int> OperationDomainAnalyzer::mapToOperationArguments(const USignature& precondition, const std::vector<int>& operationArguments, std::vector<bool>& occursInPreconditions) const {
    std::vector<int> result(precondition._args.size(), -1);
    for (size_t preconditionIndex = 0; preconditionIndex < precondition._args.size(); preconditionIndex++) {
        for (size_t operationIndex = 0; operationIndex < operationArguments.size(); operationIndex++) {
            if (precondition._args[preconditionIndex] != operationArguments[operationIndex]) continue;
            result[preconditionIndex] = operationIndex;
            occursInPreconditions[operationIndex] = true;
            break;
        }
    }
    return result;
}

std::vector<int> OperationDomainAnalyzer::getPreconditionSorts(const USignature& precondition, const std::vector<int>& operationArgumentIndices, const std::vector<int>& operationSorts) const {
    std::vector<int> result = _htn.getSorts(precondition._name_id);
    for (size_t preconditionIndex = 0; preconditionIndex < result.size(); preconditionIndex++) {
        const int operationIndex = operationArgumentIndices[preconditionIndex];
        if (operationIndex >= 0) result[preconditionIndex] = operationSorts[operationIndex];
    }
    return result;
}

OperationDomainAnalyzer::PreconditionConstraint OperationDomainAnalyzer::createConstraint(const std::vector<int>& operationArgumentIndices, std::vector<int>& preconditionToTupleIndex) const {
    PreconditionConstraint constraint;
    preconditionToTupleIndex.assign(operationArgumentIndices.size(), -1);
    FlatHashMap<int, int> tupleIndexByOperationArgument;

    for (size_t preconditionIndex = 0; preconditionIndex < operationArgumentIndices.size(); preconditionIndex++) {
        const int operationIndex = operationArgumentIndices[preconditionIndex];
        if (operationIndex < 0) continue;

        const auto existing = tupleIndexByOperationArgument.find(operationIndex);
        if (existing != tupleIndexByOperationArgument.end()) {
            preconditionToTupleIndex[preconditionIndex] = existing->second;
            continue;
        }

        const int tupleIndex = constraint.operationArgumentIndices.size();
        tupleIndexByOperationArgument[operationIndex] = tupleIndex;
        constraint.operationArgumentIndices.push_back(operationIndex);
        preconditionToTupleIndex[preconditionIndex] = tupleIndex;
    }
    return constraint;
}

void OperationDomainAnalyzer::addTuple(PreconditionConstraint& constraint, const std::vector<int>& preconditionToTupleIndex, const USignature& decoding) const {
    if (constraint.operationArgumentIndices.empty()) return;

    std::vector<int> tuple(constraint.operationArgumentIndices.size(), -1);
    for (size_t preconditionIndex = 0; preconditionIndex < preconditionToTupleIndex.size(); preconditionIndex++) {
        const int tupleIndex = preconditionToTupleIndex[preconditionIndex];
        if (tupleIndex < 0) continue;
        const int value = decoding._args[preconditionIndex];
        if (tuple[tupleIndex] >= 0 && tuple[tupleIndex] != value) return;
        tuple[tupleIndex] = value;
    }
    constraint.tuples.push_back(std::move(tuple));
}

bool OperationDomainAnalyzer::collectReachableTuples(const Signature& precondition, const std::vector<int>& preconditionSorts, const std::vector<int>& preconditionToTupleIndex, PreconditionConstraint& constraint) const {
    const USignature& signature = precondition._usig;
    bool hasCandidate = false;
    bool hasReachableCandidate = false;

    auto recordIfReachable = [&](const USignature& decoding, bool reachable) {
        hasCandidate = true;
        if (!reachable) return;
        hasReachableCandidate = true;
        addTuple(constraint, preconditionToTupleIndex, decoding);
    };

    if (_htn.isEqualityPredicate(signature._name_id)) {
        if (!_q_constants.containsAny(signature) && _htn.isFullyGround(signature)) {
            const bool holds = precondition._negated ? signature._args[0] != signature._args[1] : signature._args[0] == signature._args[1];
            if (holds) recordIfReachable(signature, true);
        } else {
            for (const USignature& decoding : _q_constants.enumerateCandidateDecodings(signature, preconditionSorts)) {
                const bool holds = precondition._negated ? decoding._args[0] != decoding._args[1] : decoding._args[0] == decoding._args[1];
                recordIfReachable(decoding, holds);
            }
        }
    } else if (!_q_constants.containsAny(signature) && _htn.isFullyGround(signature)) {
        const int factId = _facts.getGroundFactId(signature, precondition._negated);
        // Fully ground preconditions contain no operation arguments; applicability
        // is validated separately before this domain analysis runs.
        if (factId >= 0 && _facts.isReachable(factId, precondition._negated)) recordIfReachable(signature, true);
    } else {
        const BitVec matchingFacts = _facts.findMatchingGroundFactIds(signature, precondition._negated, preconditionSorts);
        for (size_t factId : matchingFacts) {
            recordIfReachable(_facts.getGroundFact(factId), _facts.isReachable(factId, precondition._negated));
        }
    }

    return !hasCandidate || hasReachableCandidate;
}

bool OperationDomainAnalyzer::propagateConstraints(const std::vector<PreconditionConstraint>& constraints, std::vector<FlatHashSet<int>>& domains) const {
    for (const PreconditionConstraint& constraint : constraints) {
        if (constraint.tuples.empty()) return false;
        for (size_t tupleIndex = 0; tupleIndex < constraint.operationArgumentIndices.size(); tupleIndex++) {
            FlatHashSet<int>& domain = domains[constraint.operationArgumentIndices[tupleIndex]];
            for (const std::vector<int>& tuple : constraint.tuples) domain.insert(tuple[tupleIndex]);
        }
    }

    bool changed = true;
    while (changed) {
        changed = false;
        for (const PreconditionConstraint& constraint : constraints) {
            for (size_t tupleIndex = 0; tupleIndex < constraint.operationArgumentIndices.size(); tupleIndex++) {
                const int operationIndex = constraint.operationArgumentIndices[tupleIndex];
                FlatHashSet<int> supportedValues;
                supportedValues.reserve(domains[operationIndex].size());

                for (const std::vector<int>& tuple : constraint.tuples) {
                    bool supported = true;
                    for (size_t otherTupleIndex = 0; otherTupleIndex < constraint.operationArgumentIndices.size(); otherTupleIndex++) {
                        if (otherTupleIndex == tupleIndex) continue;
                        const int otherOperationIndex = constraint.operationArgumentIndices[otherTupleIndex];
                        if (!domains[otherOperationIndex].count(tuple[otherTupleIndex])) {
                            supported = false;
                            break;
                        }
                    }
                    if (supported) supportedValues.insert(tuple[tupleIndex]);
                }

                if (supportedValues.size() >= domains[operationIndex].size()) continue;
                domains[operationIndex] = std::move(supportedValues);
                if (domains[operationIndex].empty()) return false;
                changed = true;
            }
        }
    }
    return true;
}

std::optional<std::vector<FlatHashSet<int>>> OperationDomainAnalyzer::compute(const HtnOp& operation) const {
    const std::vector<int>& operationArguments = operation.getArguments();
    const std::vector<int>& operationSorts = _htn.getSorts(operation.getNameId());
    std::vector<FlatHashSet<int>> domains(operationArguments.size());
    std::vector<bool> occursInPreconditions(operationArguments.size(), false);
    std::vector<PreconditionConstraint> constraints;

    // Extra preconditions validate complete candidates later but intentionally do not narrow these domains.
    for (const Signature& precondition : operation.getPreconditions()) {
        const std::vector<int> operationArgumentIndices = mapToOperationArguments(precondition._usig, operationArguments, occursInPreconditions);
        const std::vector<int> preconditionSorts = getPreconditionSorts(precondition._usig, operationArgumentIndices, operationSorts);
        std::vector<int> preconditionToTupleIndex;
        PreconditionConstraint constraint = createConstraint(operationArgumentIndices, preconditionToTupleIndex);

        if (!collectReachableTuples(precondition, preconditionSorts, preconditionToTupleIndex, constraint)) return std::nullopt;
        if (!constraint.operationArgumentIndices.empty()) constraints.push_back(std::move(constraint));
    }

    if (!propagateConstraints(constraints, domains)) return std::nullopt;
    for (size_t argumentIndex = 0; argumentIndex < operationArguments.size(); argumentIndex++) {
        if (!occursInPreconditions[argumentIndex]) domains[argumentIndex] = _htn.getConstantsOfSort(operationSorts[argumentIndex]);
    }
    return domains;
}
