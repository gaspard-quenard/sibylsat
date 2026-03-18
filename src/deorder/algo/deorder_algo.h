#ifndef DEORDER_ALGO_H
#define DEORDER_ALGO_H

#include <utility>
#include <vector>
#include <unordered_set>

#include "sat/sat_interface.h"
#include "data/htn_instance.h"
#include "libpanda.hpp"

enum class DeorderMode {
    DEORDERING,
    REORDERING
};

/**
 * @brief A minimal structure representing a single partial-order constraint: A before B.
 *        Could also just be std::pair<int,int>.
 */
struct OrderConstraint {
    int before;
    int after;
};

struct OrderConstraintHasher {
    size_t operator()(OrderConstraint const& oc) const noexcept {
        auto h1 = robin_hood::hash<int>()(oc.before);
        auto h2 = robin_hood::hash<int>()(oc.after);
        h1 ^= h2 + 0x9e3779b97f4a7c15ULL + (h1 << 6) + (h1 >> 2);
        return h1;
    }
};

struct OrderConstraintEqual {
    bool operator()(OrderConstraint const& lhs, OrderConstraint const& rhs) const noexcept {
        return lhs.before == rhs.before && lhs.after == rhs.after;
    }
};


/**
 * @brief Generic interface for plan (re)ordering solvers.
 *        Implementations only need the data required to perform reordering/deordering.
 */
class DeorderAlgo {

protected:
    const DeorderMode _mode;

    HtnInstance& _htn;

    // Indicate for each predicate the ids of the primtive tasks that consume it
    NodeHashMap<Signature, NodeHashSet<int>, SignatureHasher>& _consumers;
    // Indicate for each predicate the ids of the primitive tasks that add it
    NodeHashMap<Signature, NodeHashSet<int>, SignatureHasher>& _adders;
    // Indicate for each predicate the ids of the primitive tasks that delete it
    NodeHashMap<Signature, NodeHashSet<int>, SignatureHasher>& _deleters;

    const std::vector<int>& _prim_plan_ids;

    // Id and primitive tasks of the plan
    NodeHashMap<int, USignature>& _plan_map;

    const int& _id_init_action;
    const int& _id_goal_action;

    // Set to store the mandatory constraints (induced by the hierarchy) between two primitive tasks ids. 
    const NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual>& _mandatory_ordering_constrains;

    NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual> _solution_ordering;

    bool canBeBefore(int idPrim1, int idPrim2) {
    if (idPrim1 == _id_init_action) return true;
    if (idPrim1 == _id_goal_action) return false;

    if (idPrim2 == _id_goal_action) return true;
    if (idPrim2 == _id_init_action) return false;
    
    // Do we have a mandatory ordering constrain between idPrim2 and idPrim1 ?
    if (_mandatory_ordering_constrains.count({idPrim2, idPrim1})) return false;
    if (_mode == DeorderMode::DEORDERING) {
        // Assert that idPrim1 is before idPrim2 in the original plan
        return std::find(_prim_plan_ids.begin(), _prim_plan_ids.end(), idPrim1) < std::find(_prim_plan_ids.begin(), _prim_plan_ids.end(), idPrim2);
    }
    return true;
}


public:

    DeorderAlgo(
        HtnInstance& htn,
        DeorderMode mode,
        std::vector<int>& prim_plan_ids,
        NodeHashMap<Signature, NodeHashSet<int>, SignatureHasher>& adders,
        NodeHashMap<Signature, NodeHashSet<int>, SignatureHasher>& deleters,
        NodeHashMap<Signature, NodeHashSet<int>, SignatureHasher>& consumers,
        NodeHashMap<int, USignature>& plan_map,
        const NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual>& mandatory,
        const int& id_init_action,
        const int& id_goal_action
    ) : _htn(htn), _mode(mode), _prim_plan_ids(prim_plan_ids), _adders(adders), _deleters(deleters), _consumers(consumers), _plan_map(plan_map), _mandatory_ordering_constrains(mandatory), _id_init_action(id_init_action), _id_goal_action(id_goal_action) {}


    virtual ~DeorderAlgo() = default;

    /**
     * @brief Run the solver to produce a final (re)ordered plan.
     * @return True if a valid solution was found, false otherwise.
     */
    virtual bool solve() = 0;


    bool verifySolution(int numSamples=10);
    NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual> getSolutionOrdering(bool remove_method_prec_actions=false);
};

#endif // DEORDER_ALGO_H