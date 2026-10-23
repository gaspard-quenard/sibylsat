
#ifndef DOMPASCH_LILOTANE_DOMINATION_RESOLVER_H
#define DOMPASCH_LILOTANE_DOMINATION_RESOLVER_H

#include "algo/q_constant_manager.h"
#include "data/position.h"

class DominationResolver {

private:
    QConstantManager& _q_constants;

    size_t _num_dominated_ops = 0;
    size_t _num_unsafe_dominations = 0;

    // Values given to a Q-constant of dominating operations by the replacements so far, with the parent
    // operation (and its position) each replacement was made under.
    struct TargetValue {
        size_t parentPositionId;
        USignature parent;
        int value;
    };
    NodeHashMap<int, std::vector<TargetValue>> _target_values;

public:
    explicit DominationResolver(QConstantManager& qConstants) : _q_constants(qConstants) {}

    enum DominationStatus {DOMINATING, DOMINATED, DIFFERENT, EQUIVALENT};
    struct DominationResult {
        DominationStatus status;
        // Maps Q-constants of the dominating operation to the arguments of the dominated operation:
        // substituted into the dominating operation, it gives the dominated operation.
        Substitution qconstSubstitutions;
    };

    DominationResult getDominationStatus(const USignature& op, const USignature& other);
    void eliminateDominatedOperations(Position& newPos);

    size_t getNumDominatedOps() const {
        return _num_dominated_ops;
    }
    size_t getNumUnsafeDominations() const {
        return _num_unsafe_dominations;
    }

private:
    bool isSafeReplacement(const USignature& dominated, const USignature& dominating, const Substitution& s, const Position& newPos);
    bool isCarriedByAncestors(int qConstant, const USigSet& ops, const Position& position) const;
};

#endif
