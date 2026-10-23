
#include "algo/domination_resolver.h"

#include <algorithm>

DominationResolver::DominationResult DominationResolver::getDominationStatus(const USignature& op, const USignature& other) {
    DominationResult res;
    res.status = DIFFERENT;

    if (op._name_id != other._name_id) return res;
    assert(op._args.size() == other._args.size());
    
    DominationStatus status = EQUIVALENT;
    FlatHashSet<int> dummyDomain;

    for (size_t argIdx = 0; argIdx < op._args.size(); argIdx++) {
        int arg = op._args[argIdx];
        int otherArg = other._args[argIdx];

        if (arg == otherArg) continue; 
        
        bool isQ = _q_constants.contains(arg);
        bool isOtherQ = _q_constants.contains(otherArg);
        if (!isQ && !isOtherQ) return res; // Different ground constants

        if (isQ && isOtherQ && _q_constants.getOriginPositionId(arg) != _q_constants.getOriginPositionId(otherArg)) {
            return res;
        }
        
        // Compare domains of pseudo-constants
        
        const auto& domain = isQ ? _q_constants.getDomain(arg) : dummyDomain;
        if (!isQ) dummyDomain.insert(arg);
        const auto& otherDomain = isOtherQ ? _q_constants.getDomain(otherArg) : dummyDomain;
        if (!isOtherQ) dummyDomain.insert(otherArg);
        assert(dummyDomain.size() <= 1);

        if (domain.size() > otherDomain.size()) {
            // This op may dominate the other op

            // Contradicts previous argument indices -> ops are different
            if (status == DOMINATED) return res;
            // Check if this domain actually contains the other domain
            for (int c : otherDomain) if (!domain.count(c)) return res;
            // Yes: Dominating w.r.t. this position
            status = DOMINATING;

        } else if (domain.size() < otherDomain.size()) {
            // This op may be dominated by the other op

            // Contradicts previous argument indices -> ops are different
            if (status == DOMINATING) return res;
            // Check if the other domain actually contains this domain
            for (int c : domain) if (!otherDomain.count(c)) return res;
            // Yes: Dominated w.r.t. this position
            status = DOMINATED;

        } else if (domain != otherDomain) {
            // Different domains
            return res;
        }
        // Domains are equal

        if (!isQ || !isOtherQ) dummyDomain.clear();
    }

    if (status == EQUIVALENT) {
        // The operations are equal. Both dominate another.
        // Tie break using lexicographic ordering of arguments
        for (size_t argIdx = 0; argIdx < op._args.size(); argIdx++) {
            if (op._args[argIdx] != other._args[argIdx]) {
                status = op._args[argIdx] < other._args[argIdx] ? DOMINATED : DOMINATING;
                break;
            }    
        }
    }

    // Each Q-constant of the dominating op takes the argument of the dominated op at the same index. A Q-constant
    // occurring at several indices can only take one value: otherwise the dominating op cannot represent the other.
    const USignature& dominating = status == DOMINATED ? other : op;
    const USignature& dominated = status == DOMINATED ? op : other;
    for (size_t argIdx = 0; argIdx < op._args.size(); argIdx++) {
        const int target = dominating._args[argIdx];
        const int value = dominated._args[argIdx];
        if (target == value || !_q_constants.contains(target)) continue;
        for (const auto& [assignedTarget, assignedValue] : res.qconstSubstitutions) {
            if (assignedTarget == target && assignedValue != value) {
                res.qconstSubstitutions.clear();
                return res;
            }
        }
        res.qconstSubstitutions[target] = value;
    }
    res.status = status;
    return res;
}

bool DominationResolver::isSafeReplacement(const USignature& dominated, const USignature& dominating, const Substitution& s, const Position& newPos) {
    // Under each parent P of the dominated op, the replacement adds the clauses P & dominating -> (target = value).
    // They lose no plan if no operation selected together with P restricts a target:
    // - the target is an argument neither of the dominated op nor of P or a possible ancestor of P. If P is
    //   selected, its selected ancestor at the position where the target was created does not carry the target,
    //   so the operations carrying it are not selected, except those placed by replacements;
    // - replacements that can be selected together give the target the same value. Replacements under different
    //   parents at the same position are never selected together; for an older target, any others may be.
    if (s.empty()) return true;

    const Position* parentPosition = newPos.getParentPosition();
    if (parentPosition == nullptr) return false;
    const USigSet& parents = newPos.getPredecessors().at(dominated);
    const auto& expansions = newPos.getExpansions();

    for (const auto& parent : parents) {
        // As a child of its own, the dominating op must keep its Q-constants free under this parent
        auto expansionIt = expansions.find(parent);
        if (expansionIt != expansions.end() && expansionIt->second.count(dominating)) return false;
    }
    for (const auto& [target, value] : s) {
        if (std::find(dominated._args.begin(), dominated._args.end(), target) != dominated._args.end()) return false;
        if (isCarriedByAncestors(target, parents, *parentPosition)) return false;
        auto valuesIt = _target_values.find(target);
        if (valuesIt == _target_values.end()) continue;
        // A target created at this position or at the parent position is only targeted by replacements at its
        // creation position (whose dominating op is at it) or at a child position of it (whose parent is at it).
        // Two of them with different parent positions are never selected together: that dominating op carries the
        // target, that parent does not, and they are at the same position.
        const size_t origin = _q_constants.getOriginPositionId(target);
        const bool local = origin == newPos.getPositionId() || origin == parentPosition->getPositionId();
        for (const auto& assigned : valuesIt->second) {
            if (assigned.value == value) continue;
            if (assigned.parentPositionId == parentPosition->getPositionId()) {
                if (parents.count(assigned.parent)) return false;
            } else if (!local) return false;
        }
    }

    for (const auto& [target, value] : s) {
        auto& values = _target_values[target];
        for (const auto& parent : parents) values.push_back({parentPosition->getPositionId(), parent, value});
    }
    return true;
}

bool DominationResolver::isCarriedByAncestors(int qConstant, const USigSet& ops, const Position& position) const {
    // Whether the Q-constant is an argument of one of these operations at this position or of one of their
    // possible ancestors. It only occurs at the position where it was created and below (higher position ids).
    const size_t origin = _q_constants.getOriginPositionId(qConstant);
    USigSet level = ops;
    const Position* pos = &position;
    while (pos != nullptr && pos->getPositionId() >= origin) {
        for (const auto& op : level) {
            if (std::find(op._args.begin(), op._args.end(), qConstant) != op._args.end()) return true;
        }
        if (pos->getPositionId() == origin) return false;
        const Position* above = pos->getParentPosition();
        if (above == nullptr) return false;
        USigSet predecessors;
        for (const auto& op : level) {
            auto it = pos->getPredecessors().find(op);
            if (it == pos->getPredecessors().end()) return true; // unknown ancestry
            predecessors.insert(it->second.begin(), it->second.end());
        }
        level = std::move(predecessors);
        pos = above;
    }
    return false;
}

void DominationResolver::eliminateDominatedOperations(Position& newPos) {

    // Map of an op name id to (map of a dominating op to the ops it dominates, directly or transitively)
    NodeHashMap<int, NodeHashMap<USignature, USigSet, USignatureHasher>> dominatingActionsByName;
    NodeHashMap<int, NodeHashMap<USignature, USigSet, USignatureHasher>> dominatingReductionsByName;

    // For each operation
    const USigSet* ops[2] = {&newPos.getActions(), &newPos.getReductions()};
    NodeHashMap<int, NodeHashMap<USignature, USigSet, USignatureHasher>>* dMaps[2] = {
        &dominatingActionsByName, &dominatingReductionsByName
    };
    for (size_t i = 0; i < 2; i++) {

        for (const auto& op : *ops[i]) {
            auto& dominatingOps = (*dMaps[i])[op._name_id];

            // Compare operation with each currently dominating op of the same name
            std::vector<USignature> dominated;

            if (dominatingOps.empty()) {
                dominatingOps[op];
                continue;
            }

            for (auto& [other, dominatedByOther] : dominatingOps) {
                const DominationStatus status = getDominationStatus(op, other).status;
                if (status == DOMINATED) {
                    // This op is being dominated; mark for deletion
                    dominatedByOther.insert(op);
                    dominated.clear();
                    break;
                }
                if (status == DOMINATING) {
                    // This op dominates the other op
                    dominated.push_back(other);
                }
            }
            // This op takes over the dominated ops and the ops they dominate
            assert(!dominatingOps.count(op));
            for (const auto& other : dominated) {
                auto& dominatedByOp = dominatingOps[op];
                dominatedByOp.insert(other);
                auto otherIt = dominatingOps.find(other);
                if (otherIt != dominatingOps.end()) {
                    for (const auto& transitivelyDominated : otherIt->second) dominatedByOp.insert(transitivelyDominated);
                    dominatingOps.erase(otherIt);
                }
            }
        }

        // Replace the dominated ops where this loses no plan, each compared directly with its dominating op
        for (auto& [nameId, dMap] : *dMaps[i]) for (auto& [op, dominated] : dMap) {
            for (const auto& other : dominated) {
                DominationResult result = getDominationStatus(other, op);
                if (result.status != DOMINATED || !isSafeReplacement(other, op, result.qconstSubstitutions, newPos)) {
                    _num_unsafe_dominations++;
                    continue;
                }
                Log::v("%s dominates %s (%s)\n", TOSTR(op), TOSTR(other), TOSTR(result.qconstSubstitutions));
                newPos.replaceOperation(other, op, std::move(result.qconstSubstitutions));
                _num_dominated_ops++;
            }
        }
    }
}
