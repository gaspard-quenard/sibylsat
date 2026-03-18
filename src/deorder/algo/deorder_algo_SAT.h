#ifndef DEORDER_ALGO_SAT_H
#define DEORDER_ALGO_SAT_H

#include "deorder_algo.h"
#include "sat/sat_interface.h" 

/**
 * @class DeorderAlgoSat
 * @brief A MaxSAT-based solver for optimal plan deordering or reorderin based on the paper: Optimization of Partial-Order Plans via MaxSAT
 */
class DeorderAlgoSat : public DeorderAlgo {
public:
    DeorderAlgoSat(
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
    ) : DeorderAlgo(htn, mode, prim_plan_ids, adders, deleters, consumers, plan_map, mandatory, id_init_action, id_goal_action), _sat(_htn.getParams()) {}

    ~DeorderAlgoSat() override = default;

    bool solve() override;
    // NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual> getSolutionOrdering() const override;

private:
   
    SatInterface _sat;
    NodeHashMap<OrderConstraint, int, OrderConstraintHasher, OrderConstraintEqual> _constraints_order_vars; 


    int getOrderingConstrainVar(int id_action_before, int id_action_after);

    void encodeActionCannotBeBeforeInitAndAfterGoal();
    void encodeTransitiveClosureDeordering();
    void encodeTransitiveClosureReordering();
    void encodeSymmetry();
    void encodeOrderingConstrainsEnforcedByHierarchy();
    void encodePreconditionsMustBeSatisfiedByAchievers();
};

#endif // DEORDER_ALGO_SAT_H