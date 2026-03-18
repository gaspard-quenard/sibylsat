#include <cstdlib> 
#include <ctime> 

#include "deorder_algo.h"


/**
 * @brief Verifies the correctness of the deordered plan.
 *
 * This function first checks that every mandatory ordering constraint is present in
 * the solution ordering. It then builds a partial order graph and generates a number of
 * random total orders (topological sorts) consistent with the partial order. For each
 * total order, it simulates sequential plan execution by verifying that each action's
 * preconditions are met before applying its effects.
 *
 * @param numSamples The number of total order samples to generate and test.
 * @return true if all sampled total orders pass the verification; false otherwise.
 */
bool DeorderAlgo::verifySolution(int numSamples /*=10*/) {
    // Seed the random generator (do this once)
    std::srand(static_cast<unsigned>(std::time(nullptr)));

    // First verification, check if the mandatory ordering constrains are directly satisfied
    Log::i("Checking mandatory ordering constraints...\n");
    bool allMandatoryConstraintsSatisfied = true;
    for (const OrderConstraint& m : _mandatory_ordering_constrains) {
        if (_solution_ordering.find(m) == _solution_ordering.end()) {
            Log::e("Mandatory ordering constraint violated: Action %s(%d) should precede Action %s(%d).\n", 
                   TOSTR(_plan_map[m.before]), m.before, TOSTR(_plan_map[m.after]), m.after);
            allMandatoryConstraintsSatisfied = false;
        }
    }
    if (!allMandatoryConstraintsSatisfied) {
        Log::e("Verification failed: Mandatory ordering constraints are not satisfied.\n");
        return false;
    }

    Log::i("Mandatory ordering constraints are satisfied.\n");
    Log::i("Starting verification with %d sample total orders...\n", numSamples);

    // ========================================
    // STEP 1. Build the Partial Order Graph
    // ========================================
    // The final (deordered) plan is given by _solution_ordering (a set of ordering constraints)
    // and the set of all primitive action IDs is assumed to be in _prim_plan_ids.
    const std::vector<int>& allActions = _prim_plan_ids;

    // Build two maps:
    //  - 'graph': for each action, list its direct successors.
    //  - 'inDegree': for each action, count the number of incoming ordering constraints.
    std::unordered_map<int, std::vector<int>> graph;
    std::unordered_map<int, int> inDegree;
    for (int id : allActions) {
        graph[id] = std::vector<int>();
        inDegree[id] = 0;
    }
    // Add an edge for every ordering constraint in _solution_ordering.
    for (const OrderConstraint& oc : _solution_ordering) {
        graph[oc.before].push_back(oc.after);
        inDegree[oc.after]++;
    }

    // ========================================
    // STEP 2. Helper Lambdas
    // ========================================

    // (a) Generate a random topological ordering that is consistent with the partial order.
    auto generateRandomTopologicalOrder = [&]() -> std::vector<int> {
        std::vector<int> order;

        // Make a local copy of inDegree so that we can modify it.
        std::unordered_map<int, int> localInDegree = inDegree;
        // Start with all actions that have no incoming constraints.
        std::vector<int> zeroInDegree;
        for (const auto& p : localInDegree) {
            if (p.second == 0) {
                zeroInDegree.push_back(p.first);
            }
        }

        // Continue while there are actions available with zero in-degree.
        while (!zeroInDegree.empty()) {
            // Pick one at random.
            int idx = std::rand() % zeroInDegree.size();
            int current = zeroInDegree[idx];
            // Remove the selected action.
            zeroInDegree.erase(zeroInDegree.begin() + idx);
            order.push_back(current);
            // For each successor of the current action, decrease its in-degree.
            for (int succ : graph[current]) {
                localInDegree[succ]--;
                if (localInDegree[succ] == 0) {
                    zeroInDegree.push_back(succ);
                }
            }
        }

        // Add the goal action to the order last.
        order.push_back(_id_goal_action);

        // If the ordering does not include every action + init and goal actions, then a cycle exists.
        if (order.size() != allActions.size() + 1) {
            return std::vector<int>(); // return an empty ordering to signal an error.
        }

        return order;
    };

    // (c) Simulate the sequential execution of the plan.
    // For each action (retrieved via _plan_map), we check that its preconditions are satisfied in the current state,
    // then we update the state by applying the effects (first deleting, then adding facts).
    auto simulatePlanExecution = [&](const std::vector<int>& totalOrder) -> bool {
        std::unordered_set<USignature, USignatureHasher> state;

        // Add init state
        for (const USignature& init : _htn.getInitState()) {
            state.insert(init);
        }

        for (int actionId : totalOrder) {
            // Retrieve the Action object.
            int id = _plan_map[actionId]._name_id;
            std::vector<int> args = _plan_map[actionId]._args;
            Action action = _htn.toAction(id, args);
            const auto& preconditions = action.getPreconditions();
            for (const auto& pre : preconditions) {
                // If positive, should be in the state. If negative, the opposite should not be in the state.
                USignature absPre = pre.getUnsigned();
                bool positive = !pre._negated;
                if ((positive && state.find(absPre) == state.end())
                || (!positive && state.find(absPre) != state.end())) {
                    Log::e("Precondition %c%s not satisfied for action %s(%d)\n", positive ? '+' : '-', TOSTR(absPre), TOSTR(_plan_map[actionId].toSignature()), actionId);
                    // Print the state
                    Log::e("Current state: \n");
                    for (const USignature& fact : state) {
                        Log::e("  %s\n", TOSTR(fact));
                    }
                    return false;
                }
            }
            // Apply the action's effects.
            const auto& effects = action.getEffects();
            // First, remove all facts that are deleted by the action.
            for (const auto& delFact : effects) {
                if (delFact._negated) state.erase(delFact.getUnsigned());
            }

            // Next, add all facts that are added by the action.
            for (const auto& addFact : effects) {
                if (!addFact._negated) state.insert(addFact.getUnsigned());
            }
        }
        return true;
    };

    // ========================================
    // STEP 3. Perform the Verification by Sampling
    // ========================================
    bool allSamplesValid = true;
    for (int sample = 0; sample < numSamples; ++sample) {
        if (sample % 10 == 0) Log::i("Testing sample %d/%d...\n", sample + 1, numSamples);
        
        std::vector<int> totalOrder = generateRandomTopologicalOrder();
        if (totalOrder.empty()) {
            Log::e("Error: A cycle was detected in the ordering constraints (sample %d).\n", sample);
            allSamplesValid = false;
            break;
        }
        if (!simulatePlanExecution(totalOrder)) {
            Log::e("Sample %d failed the plan execution simulation.\n", sample);
            allSamplesValid = false;
        }
    }

    if (allSamplesValid) {
        Log::i("Verification successful: All %d sampled total orders satisfy the mandatory constraints and simulation criteria.\n", numSamples);
    } else {
        Log::e("Verification failed: Some sampled total orders did not meet all checks.\n");
    }

    return allSamplesValid;
}




/**
 * @brief Get the final set of ordering constraints after the solver is done. Optionally remove all specific methods preconditions.
 */
NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual> DeorderAlgo::getSolutionOrdering(bool remove_method_prec_actions) {
    if (!remove_method_prec_actions) return _solution_ordering;
    
    NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual> result;
    for (const OrderConstraint& oc : _solution_ordering) {
        // If the name contains <method_prec>, skip it
        if (Names::to_string(_plan_map[oc.before]._name_id).find(method_precondition_action_name) != std::string::npos) continue;
        if (Names::to_string(_plan_map[oc.after]._name_id).find(method_precondition_action_name) != std::string::npos) continue;
        result.insert(oc);
    }
    return result;
}