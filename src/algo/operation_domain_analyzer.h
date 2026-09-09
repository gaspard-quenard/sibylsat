#ifndef SIBYLSAT_OPERATION_DOMAIN_ANALYZER_H
#define SIBYLSAT_OPERATION_DOMAIN_ANALYZER_H

#include <optional>
#include <vector>

#include "data/signature.h"
#include "util/hashmap.h"

class FactAnalysis;
class HtnInstance;
class HtnOp;
class QConstantManager;

/** Computes currently reachable domains for the arguments of one operation. */
class OperationDomainAnalyzer
{
private:
    struct PreconditionConstraint
    {
        std::vector<int> operationArgumentIndices;
        std::vector<std::vector<int>> tuples;
    };

    HtnInstance &_htn;
    QConstantManager &_q_constants;
    FactAnalysis &_facts;

    std::vector<int> mapToOperationArguments(const USignature &precondition, const std::vector<int> &operationArguments, std::vector<bool> &occursInPreconditions) const;
    std::vector<int> getPreconditionSorts(const USignature &precondition, const std::vector<int> &operationArgumentIndices, const std::vector<int> &operationSorts) const;
    PreconditionConstraint createConstraint(const std::vector<int> &operationArgumentIndices, std::vector<int> &preconditionToTupleIndex) const;
    void addTuple(PreconditionConstraint &constraint, const std::vector<int> &preconditionToTupleIndex, const USignature &decoding) const;
    bool collectReachableTuples(const Signature &precondition, const std::vector<int> &preconditionSorts, const std::vector<int> &preconditionToTupleIndex, PreconditionConstraint &constraint) const;
    bool propagateConstraints(const std::vector<PreconditionConstraint> &constraints, std::vector<FlatHashSet<int>> &domains) const;

public:
    OperationDomainAnalyzer(HtnInstance &htn, QConstantManager &qConstants, FactAnalysis &facts) : _htn(htn), _q_constants(qConstants), _facts(facts) {}

    /**
     * Return, for each operation parameter, the constants it can currently take
     * while satisfying the reachable preconditions.
     *
     * Returns no value if no valid parameter assignment exists.
     */
    std::optional<std::vector<FlatHashSet<int>>> compute(const HtnOp &operation) const;
};

#endif
