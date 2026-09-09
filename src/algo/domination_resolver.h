
#ifndef DOMPASCH_LILOTANE_DOMINATION_RESOLVER_H
#define DOMPASCH_LILOTANE_DOMINATION_RESOLVER_H

#include "algo/q_constant_manager.h"
#include "data/position.h"

class DominationResolver {

private:
    QConstantManager& _q_constants;

    size_t _num_dominated_ops = 0;

public:
    explicit DominationResolver(QConstantManager& qConstants) : _q_constants(qConstants) {}

    enum DominationStatus {DOMINATING, DOMINATED, DIFFERENT, EQUIVALENT};
    struct DominationResult {
        DominationStatus status;
        Substitution qconstSubstitutions;
    };

    DominationResult getDominationStatus(const USignature& op, const USignature& other);
    void eliminateDominatedOperations(Position& newPos);

    size_t getNumDominatedOps() const {
        return _num_dominated_ops;
    }
};

#endif
