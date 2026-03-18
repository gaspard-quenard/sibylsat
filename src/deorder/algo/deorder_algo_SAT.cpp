#include "deorder_algo_SAT.h"



bool DeorderAlgoSat::solve() {
    // For each action, this action is after the __init__ action and before the goal_action (N clauses)
    Log::i("Encoding action cannot be before __init__ and after goal...\n");
    encodeActionCannotBeBeforeInitAndAfterGoal();
    Log::i("Done !\n");
    // Encode the transitive closure of all ordering constrains (N^3 clauses)
    Log::i("Encoding transitive closure...\n");
    if (_mode == DeorderMode::DEORDERING) encodeTransitiveClosureDeordering();
    else encodeTransitiveClosureReordering();
    // If we have ai before aj, we cannot have aj before ai
    Log::i("Encoding break acyclic closure...\n");
    encodeSymmetry();
    // Encode the constrains ordering enforced by the hierarchy 
    Log::i("Encoding mandatory ordering constrains...\n");
    encodeOrderingConstrainsEnforcedByHierarchy();
    Log::i("Done !\n");
    Log::i("Encode achievers and threats...\n");
    encodePreconditionsMustBeSatisfiedByAchievers();
    Log::i("Done !\n");
    if (_mode == DeorderMode::DEORDERING) {
        Log::i("Only derodering, prevent reordering...\n");
        for (int i = 0; i < _prim_plan_ids.size(); i++) {
            for (int j = i + 1; j < _prim_plan_ids.size(); j++) {
                // j cannot be before i
                _sat.addClause(-getOrderingConstrainVar(_prim_plan_ids[j], _prim_plan_ids[i]));
            }
        }
    } 

    // Finally, add a weight of 1 for each ordering constrains which do not contains the init and goal actions
    Log::i("Adding soft clauses for ordering constrains...\n");
    int num_soft_clauses = 0;
    for (const auto& [constraint, var] : _constraints_order_vars) {
        // If goal id or init id is in the ordering constrain, then it is not a real ordering constrain
        if (constraint.before == _id_goal_action || constraint.after == _id_goal_action || constraint.before == _id_init_action || constraint.after == _id_init_action) continue;
        // Is there a mandatory ordering constrain between these two actions ?
        if (_mandatory_ordering_constrains.count(constraint)) continue;
        // Is there a mandatory ordering constrain between the opposite actions ?
        // if (_mandatory_ordering_constrains.count(std::make_pair(pair.second, pair.first))) continue;
        if (_mandatory_ordering_constrains.count({constraint.after, constraint.before})) continue;
        num_soft_clauses++;
        _sat.addSoftLit(var, 1);
    }
    Log::i("Done ! Number of soft literals: %d\n", num_soft_clauses);




    // Launch the solver
    Log::i("Solving with %d soft clauses...\n", num_soft_clauses);
    int result = _sat.solve();
    bool solved = result == 10;
    Log::i("Result: %s\n", solved ? "SAT" : "UNSAT");
    Log::i("Done !\n");

    if (!solved) {
        Log::e("Failed to find deordering !\n");
        return false;
    }

    // Print the value of all the ordering constrains which are positive
    // int num_initial_ordering_constrains = (_prim_plan.size() + 2) * (_prim_plan.size() + 1) / 2;
    // int num_initial_ordering_constrains = _original_plan_length * (_original_plan_length - 1) / 2;
    int num_ordering_constrains = 0;
    // int init_size_critical_path = _original_plan_length;
    int size_critical_path = 0;
    // std::vector<std::pair<int, int>> final_ordering;

    for (const auto& [constraint, var] : _constraints_order_vars) {
        // If goal id or init id is in the ordering constrain, then it is not a real ordering constrain
        // if (pair.first == _id_goal_action || pair.second == _id_goal_action || pair.first == _id_init_action || pair.second == _id_init_action) continue;
        if (_sat.holds(var)) {
            USignature before = _plan_map[constraint.before];
            USignature after = _plan_map[constraint.after];
            // If the name contains <method_prec>, skip it
            // if (Names::to_string(before._name_id).find(method_precondition_action_name) != std::string::npos) continue;
            // if (Names::to_string(after._name_id).find(method_precondition_action_name) != std::string::npos) continue;
            if (constraint.after == _id_goal_action && constraint.before != _id_init_action) {
                size_critical_path++;
            }
            if (constraint.before == _id_init_action || constraint.after == _id_goal_action) continue;
            assert(constraint.before != _id_goal_action || Log::e("Goal action should not be before any action\n"));
            assert(constraint.after != _id_init_action || Log::e("Init action should not be after any action\n"));
            num_ordering_constrains++;
            Log::d("%i -> %s(%d) before %s(%d)\n", var, TOSTR(_plan_map[constraint.before]), constraint.before, TOSTR(_plan_map[constraint.after]), constraint.after);
            // final_ordering.push_back({constraint.before, constraint.after});
            _solution_ordering.insert({constraint.before, constraint.after});
        }
    }

    int initial_number_of_ordering_constrains = _plan_map.size() * (_plan_map.size() - 1) / 2;
    Log::i("Initial number of ordering constrains: %d\n", initial_number_of_ordering_constrains);
    
    Log::i("Final Number of ordering constrains : %d\n", _solution_ordering.size());
    return true;
}

int DeorderAlgoSat::getOrderingConstrainVar(int id_action_before, int id_action_after) {

    // assert(id_action_before != _id_goal_action || Log::e("Goal action cannot be before another action\n"));
    if (id_action_before == _id_goal_action) {
        Log::e("goal action cannot be after another action\n");
    }
    // assert(id_action_after != _id_init_action || Log::e("Init action cannot be after another action\n"));
    if (id_action_after == _id_init_action) {
        Log::e("init action cannot be before another action\n");
    }


    OrderConstraint constr = {id_action_before, id_action_after};

    if (!_constraints_order_vars.count(constr)) {
        _constraints_order_vars[constr] = VariableDomain::nextVar();
        if (_htn.getParams().isNonzero("pvn")) {
            // Log::d("VARMAP %i %s(%d)_BEFORE_%s(%d)\n", _constraints_order_vars[constr], TOSTR(_plan_map[id_action_before]), id_action_before, TOSTR(_plan_map[id_action_after]), id_action_after);
        }
    }

    return _constraints_order_vars[constr];
}


void DeorderAlgoSat::encodeActionCannotBeBeforeInitAndAfterGoal() {
    // For each action, this action is after the __init__ action and before the goal_action
    for (auto const& kv : _plan_map) {
        int id = kv.first;
        // Get the ordering constrain variable between the init action and the current action
        int var_init_action_before_id = getOrderingConstrainVar(_id_init_action, id);
        _sat.addClause(var_init_action_before_id);
        // Get the ordering constrain variable between the current action and the goal action
        int var_id_before_goal_action = getOrderingConstrainVar(id, _id_goal_action);
        _sat.addClause(var_id_before_goal_action);
    }

    // Finally, add the ordering constrain between the __init__ action and the goal action
    int var_init_action_before_goal_action = getOrderingConstrainVar(_id_init_action, _id_goal_action);
    _sat.addClause(var_init_action_before_goal_action);
}

void DeorderAlgoSat::encodeTransitiveClosureDeordering() {
    // For each triple of different IDs, but respectecting the original ordering of the plan
    for (int i = 0; i < _prim_plan_ids.size(); i++) {
        for (int j = i + 1; j < _prim_plan_ids.size(); j++) {
            for (int k = j + 1; k < _prim_plan_ids.size(); k++) {
                // Get the ordering constraint variables
                int var_i_before_j = getOrderingConstrainVar(_prim_plan_ids[i], _prim_plan_ids[j]);
                int var_j_before_k = getOrderingConstrainVar(_prim_plan_ids[j], _prim_plan_ids[k]);
                int var_i_before_k = getOrderingConstrainVar(_prim_plan_ids[i], _prim_plan_ids[k]);
                
                // Add transitivity clause:
                // If (i before j) AND (j before k) THEN (i before k)
                _sat.addClause(-var_i_before_j, -var_j_before_k, var_i_before_k);
            }
        }
    }
}

// Encode transitive closure for all ordering constraints
void DeorderAlgoSat::encodeTransitiveClosureReordering() {
    // For each triple of different IDs
    for (int id1 : _prim_plan_ids) {
        for (int id2 : _prim_plan_ids) {
            if (id2 == id1) continue;  // Skip same IDs
            
            for (int id3 : _prim_plan_ids) {
                // Skip if id3 is same as either id1 or id2
                if (id3 == id1 || id3 == id2) continue;
                
                // Get the ordering constraint variables
                int var_id1_before_id2 = getOrderingConstrainVar(id1, id2);
                int var_id2_before_id3 = getOrderingConstrainVar(id2, id3);
                int var_id1_before_id3 = getOrderingConstrainVar(id1, id3);
                
                // Add transitivity clause:
                // If (id1 before id2) AND (id2 before id3) THEN (id1 before id3)
                _sat.addClause(-var_id1_before_id2, -var_id2_before_id3, var_id1_before_id3);
            }
        }
    }
}

void DeorderAlgoSat::encodeSymmetry() {
    // If action i is before action j, then action j cannot be before action i
    for (int i = 0; i < _prim_plan_ids.size(); i++) {
        for (int j = i + 1; j < _prim_plan_ids.size(); j++) {
            // If i is mandatory before j, then no need to add the symmetry clause
            if (_mandatory_ordering_constrains.count({_prim_plan_ids[i], _prim_plan_ids[j]})) continue;
            

            int var_i_before_j = getOrderingConstrainVar(_prim_plan_ids[i], _prim_plan_ids[j]);
            int var_j_before_i = getOrderingConstrainVar(_prim_plan_ids[j], _prim_plan_ids[i]);
            _sat.addClause(-var_i_before_j, -var_j_before_i);
        }
    }
}

void DeorderAlgoSat::encodeOrderingConstrainsEnforcedByHierarchy() {
    for (const auto& [id1, id2] : _mandatory_ordering_constrains) {
        int var_id1_before_id2 = getOrderingConstrainVar(id1, id2);
        _sat.addClause(var_id1_before_id2);
    }
}


void DeorderAlgoSat::encodePreconditionsMustBeSatisfiedByAchievers() {
    // For each action, get the preconditions and ensure that the achievers of these preconditions are before the action
    // and that there is no threat between the achievers and the action

    // Get a copy of _prim_plan where we add the __goal__ action
    std::vector<int> prim_plan_with_goal = _prim_plan_ids;
    prim_plan_with_goal.push_back(_id_goal_action);

    for (int id : prim_plan_with_goal) {
        Action action = _htn.toAction(_plan_map[id]._name_id, _plan_map[id]._args);
        for (const Signature& precond : action.getPreconditions()) {
            // If this is a constrain preconditions, we know it is already satisfied
            if (_htn.isEqualityPredicate(precond._usig._name_id)) continue;
            // Get the adders of the precondition
            const NodeHashSet<int>& adderIds = _adders[precond];
            std::vector<int> vars_achievers;
            for (int adderId : adderIds) {
                if (adderId == id) continue;  // Skip if the adder is the same as the current action
                // If the adder is mandatory after the current action, then no need to add the clause
                if (!canBeBefore(adderId, id)) {
                    Log::d("Adder %s(%d) cannot be before %s(%d)\n", TOSTR(_plan_map[adderId]), adderId, TOSTR(_plan_map[id]), id);
                    continue;
                }

                // Create a new variable which correspond to the fact that the addedId is the achiever of the precondition for the current action
                int var_addedId_is_achiever_of_precond_for_id = VariableDomain::nextVar();
                if (_htn.getParams().isNonzero("pvn")) {
                    Log::d("VARMAP %i %s(%d)_IS_ACHIEVER_OF_%s(%d)_FOR_PRECOND_%s\n", var_addedId_is_achiever_of_precond_for_id, TOSTR(_plan_map[adderId]), adderId, TOSTR(action.getSignature()), id, TOSTR(precond));
                }
                // Create the logic for this variable
                // 1: If the addedId is the achiever of the precondition for the current action, then the addedId is before the current action
                // 2: If the adderId is the achiever of the precondition for the current action, then there must be no threat between the adderId and the current action

                // 1
                if (adderId != _id_init_action) {
                    // Because the __init__ action is always before all the other actions
                    _sat.addClause(-var_addedId_is_achiever_of_precond_for_id, getOrderingConstrainVar(adderId, id));
                }
                

                // 2
                // Create a special variable for the threat between the adderId and the current action for the precondition
                int var_no_threat_between_adderId_and_id_for_precond = VariableDomain::nextVar();
                if (_htn.getParams().isNonzero("pvn")) {
                    Log::d("VARMAP %i NO_THREAT_BETWEEN_%s(%d)_AND_%s(%d)_FOR_%s\n", var_no_threat_between_adderId_and_id_for_precond, TOSTR(_plan_map[adderId]), adderId, TOSTR(action.getSignature()), id, TOSTR(precond));
                }
                _sat.addClause(-var_addedId_is_achiever_of_precond_for_id, var_no_threat_between_adderId_and_id_for_precond);

                // Finally, make the logic for the no_threat variable
                // There is no threat between the adderId and the current action for the precondition if there is not any deleter of the precondition between the adderId and the current action
                // So each deleter of the precondition must be before the adderId OR after the current action
                const NodeHashSet<int>& deleterIds = _deleters[precond];
                for (int deleterId : deleterIds) {
                    if (deleterId == id) continue;  // Skip if the deleter is the same as the current action
                    if (deleterId == adderId) continue;  // Skip if the deleter is the same as the adder
                    _sat.appendClause(-var_no_threat_between_adderId_and_id_for_precond);
                    // Can the deleter be before the adder ?
                    if (canBeBefore(deleterId, adderId)) {
                        _sat.appendClause(getOrderingConstrainVar(deleterId, adderId));
                    }
                    // Can the deleter be after the current action ?
                    if (canBeBefore(id, deleterId)) {
                        _sat.appendClause(getOrderingConstrainVar(id, deleterId));
                    }
                    _sat.endClause();                    
                }

                vars_achievers.push_back(var_addedId_is_achiever_of_precond_for_id);
            }
            // Need at least one achiever for this precondition of the current action
            _sat.addClause(vars_achievers);
        }
    }
}