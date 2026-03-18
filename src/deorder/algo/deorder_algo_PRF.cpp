
#include "deorder_algo_PRF.h"



bool DeorderAlgoPRF::solve() {


    for (int i = 0; i < _prim_plan_ids.size(); i++) {
        std::unordered_set<int> already_visited;

        Log::d("Checking ordering constraints for %s(%d)\n", TOSTR(_plan_map[_prim_plan_ids[i]]), _prim_plan_ids[i]);
        for (int j = i + 1; j < _prim_plan_ids.size(); j++) {
            
            if (already_visited.count(_prim_plan_ids[i])) {
                Log::d("Already visited %s(%d)\n", TOSTR(_plan_map[_prim_plan_ids[i]]), _prim_plan_ids[i]);
                continue;
            }

            Log::d("With %s(%d)\n", TOSTR(_plan_map[_prim_plan_ids[j]]), _prim_plan_ids[j]);


            // Do the hierarchy constraints enforce that i is before j ?
            if (_mandatory_ordering_constrains.count({_prim_plan_ids[i], _prim_plan_ids[j]})) {
                Log::d("Hierarchical ordering constraint between %s(%d) and %s(%d)\n", TOSTR(_plan_map[_prim_plan_ids[i]]), _prim_plan_ids[i], TOSTR(_plan_map[_prim_plan_ids[j]]), _prim_plan_ids[j]);
                _solution_ordering.insert({_prim_plan_ids[i], _prim_plan_ids[j]});
                // For all the mandatory constrains of j to k, add the ordering between i and k
                for (const auto& order : _mandatory_ordering_constrains) {
                    if (order.before == _prim_plan_ids[j]) {
                        Log::d("Adding transitive ordering constraint between %s(%d) and %s(%d)\n", TOSTR(_plan_map[_prim_plan_ids[i]]), _prim_plan_ids[i], TOSTR(_plan_map[order.after]), order.after);
                        _solution_ordering.insert({_prim_plan_ids[i], order.after});
                        already_visited.insert(order.after);
                    }
                }
                continue;
            }
            // Do the simple concurrency criterions enforce that i is before j ?
            if (!verifyConcurencyCriterions(_prim_plan_ids[i], _prim_plan_ids[j])) {
                Log::d("Concurrency criterions between %s(%d) and %s(%d)\n", TOSTR(_plan_map[_prim_plan_ids[i]]), _prim_plan_ids[i], TOSTR(_plan_map[_prim_plan_ids[j]]), _prim_plan_ids[j]);
                _solution_ordering.insert({_prim_plan_ids[i], _prim_plan_ids[j]});
                // For all the mandatory constrains of j to k, add the ordering between i and k
                for (const auto& order : _mandatory_ordering_constrains) {
                    if (order.before == _prim_plan_ids[j]) {
                        Log::d("Adding transitive ordering constraint between %s(%d) and %s(%d)\n", TOSTR(_plan_map[_prim_plan_ids[i]]), _prim_plan_ids[i], TOSTR(_plan_map[order.after]), order.after);
                        _solution_ordering.insert({_prim_plan_ids[i], order.after});
                        already_visited.insert(order.after);
                    }
                }
                continue;
            }
            // No ordering constrains between i and j
            Log::d("Drop ordering constraint between %s(%d) and %s(%d)\n", TOSTR(_plan_map[_prim_plan_ids[i]]), _prim_plan_ids[i], TOSTR(_plan_map[_prim_plan_ids[j]]), _prim_plan_ids[j]);
        } 
    }

    // removeMethodPreconditionsInOrdering();

    int initial_number_of_ordering_constrains = _plan_map.size() * (_plan_map.size() - 1) / 2;
    Log::i("Initial number of ordering constrains: %d\n", initial_number_of_ordering_constrains);

    // Print the number of ordering constrains after the PRF algorithm
    Log::i("Final Number of ordering constrains : %d\n", _solution_ordering.size());

    return true;
}

/**
 * @brief Verifies simple concurrency conditions between two primitive tasks, a and b.
 *
 * The tasks are considered non-concurrent if all of the following conditions hold for any pair of tasks a and b and predicate pred:
 * 1. prod(a, pred) AND cons(b, pred) is false.
 * 2. prod(a, pred) AND threat(b, pred) is false.
 * 3. cons(a, pred) AND threat(b, pred) is false.
 */
bool DeorderAlgoPRF::verifyConcurencyCriterions(const int id_prim_task_before, const int _id_prim_task_after) {

    Action action_before = _htn.toAction(_plan_map[id_prim_task_before]._name_id, _plan_map[id_prim_task_before]._args);
    Action action_after = _htn.toAction(_plan_map[_id_prim_task_after]._name_id, _plan_map[_id_prim_task_after]._args);

    NodeHashSet<Signature, SignatureHasher> prod_action_before;
    NodeHashSet<Signature, SignatureHasher> cons_action_before;

    NodeHashSet<Signature, SignatureHasher> cons_action_after;
    NodeHashSet<Signature, SignatureHasher> threat_action_after;
    
    for (const Signature& eff : action_before.getEffects()) prod_action_before.insert(eff);
    for (const Signature& prec : action_before.getPreconditions()) cons_action_before.insert(prec);

    for (const Signature& eff : action_after.getPreconditions()) cons_action_after.insert(eff);
    for (const Signature& eff : action_after.getEffects()) threat_action_after.insert(eff.opposite());

    // Check condition 1
    for (const Signature& pred : prod_action_before) {
        if (cons_action_after.count(pred) > 0) {
            return false;
        }
    }

    // Check condition 2
    for (const Signature& pred : prod_action_before) {
        if (threat_action_after.count(pred) > 0) {
            return false;
        }
    }

    // Check condition 3
    for (const Signature& pred : cons_action_before) {
        if (threat_action_after.count(pred) > 0) {
            return false;
        }
    }

    return true;
}