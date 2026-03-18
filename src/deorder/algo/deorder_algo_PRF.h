#ifndef DEORDER_ALGO_PRF_H
#define DEORDER_ALGO_PRF_H

#include "deorder_algo.h"

/**
 * @class DeorderSolverPRF
 * @brief The PRF deordering algorithm from Christer Backstrom paper: Computational Aspects of Reordering Plans.
 */
class DeorderAlgoPRF : public DeorderAlgo {
public:
    DeorderAlgoPRF(
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
    ) : DeorderAlgo(htn, mode, prim_plan_ids, adders, deleters, consumers, plan_map, mandatory, id_init_action, id_goal_action) {
        if (mode == DeorderMode::REORDERING) {
            Log::e("PRF algorithm is only for deordering\n");
            exit(1);
        }
    }

    ~DeorderAlgoPRF() override = default;

    bool solve() override;

private:

bool verifyConcurencyCriterions(const int id_prim_task_before, const int _id_prim_task_after);
   
};

#endif // DEORDER_ALGO_PRF_H