#include <chrono>
#include <sstream>

#include "algo/separate_tasks_scheduler.h"

SeparateTasksScheduler::SeparateTasksScheduler(HtnInstance& htn)
    : _num_init_tasks_resolved(0),
      _init_task_network_size(htn.getInitReduction().getSubtasks().size()),
      _current_task_index(1),
      _num_tasks_to_solve(1),
      _tcp_exponential_resolving(true),
      _last_time_spend_to_solve_tasks(0),
      _num_failed_sat(0),
      _num_pos_done(0),
      _restart_planner(false),
      _init_state(htn.getInitState()),
      _htn(htn),
      _domain_name(getDomaineNameFromDomainFile(htn.getParams().getDomainFilename()))
{
    if (!_settings_manager.has_setting(_domain_name, "independent_init_tasks")) {
        Log::w("The domain %s does not have the setting independent_init_tasks in the domain_settings.json file. Create it with default value true.\n", _domain_name.c_str());
        _settings_manager.set_setting(_domain_name, "independent_init_tasks", true);
    }
    _add_tasks_as_clauses = _settings_manager.get_setting(_domain_name, "independent_init_tasks");
    _init_time_spend_to_solve_tasks = std::chrono::high_resolution_clock::now();

    // Initialize the init state bitvec
    _init_state_pos_bitvec = BitVec(_htn.getNumPositiveGroundFacts());
    _init_state_neg_bitvec = BitVec(_htn.getNumPositiveGroundFacts());
    for (int i = 0; i < _htn.getNumPositiveGroundFacts(); ++i) {
        const USignature& iSig = _htn.getGroundPositiveFact(i);
        // Log::i("Init Fact %d: %s\n", i, TOSTR(iSig));
        if (_init_state.count(iSig)) {
            _init_state_pos_bitvec.set(i);
        } else {
            _init_state_neg_bitvec.set(i);
        }
    }
}

void SeparateTasksScheduler::displayAdvancementBar() const {
    std::string bar;
    for (int i = 0; i < _init_task_network_size; ++i) {
        if (_num_init_tasks_resolved > i)
            bar += "\033[32m*\033[0m"; // Solved: green star
        else
            bar += "\033[31m-\033[0m"; // Not solved: red dash
    }
    Log::i("\033[34m[%s\033[0m]\n", bar.c_str());
}

void SeparateTasksScheduler::addAssumptionsForSolvedTasks(Encoding &enc) {
    if (!_vars_tasks_accomplished.empty()) {
        enc.addAssumptionsTasksAccomplished(_vars_tasks_accomplished.back(), _add_tasks_as_clauses);
    }
}

int SeparateTasksScheduler::getAssumptionsUntil(int layer_size) const {
    return layer_size - _init_task_network_size - 1 + _current_task_index;
}

bool SeparateTasksScheduler::updateAfterSolved(Encoding &enc, const std::vector<Layer*> &layers, int layer_idx) {
    _num_init_tasks_resolved = _current_task_index;
    if (_num_init_tasks_resolved == _init_task_network_size) {
        displayAdvancementBar();
        Log::i("Solved the problem for all tasks\n");
        return true;
    } else {
        Log::i("Solved the problem for %d/%d tasks\n", _num_init_tasks_resolved, _init_task_network_size);
        int layer_size = layers[layer_idx]->size();
        int solve_positions = layer_size - _init_task_network_size - 1 + _current_task_index;
        _num_pos_done = solve_positions;
        // Save a snapshot of all SAT variables that are true until solve_positions.
        NodeHashSet<int> snapshot = enc.getSnapshotsOpsAndPredsTrue(solve_positions);
        _vars_tasks_accomplished.push_back(snapshot);
        _num_pos_done_at_each_step.push_back(_num_pos_done);
        _num_tasks_solved_at_each_step.push_back(_num_tasks_to_solve);
        updateReachableStateAfterTasksAccomplished(enc, layers, layer_idx, solve_positions);
        
        if (_tcp_exponential_resolving) {
            auto end = std::chrono::high_resolution_clock::now();
            long long durationSolveTasks = std::chrono::duration_cast<std::chrono::milliseconds>(end - _init_time_spend_to_solve_tasks).count();
            Log::i("Time spend to solve those tasks: %lld ms\n", durationSolveTasks);
            Log::i("Time spend on the previous tasks: %lld ms\n", _last_time_spend_to_solve_tasks);
            if (_last_time_spend_to_solve_tasks == 0) {
                _last_time_spend_to_solve_tasks = durationSolveTasks;
            } else {
                if (durationSolveTasks < _last_time_spend_to_solve_tasks * 2) {
                    _num_tasks_to_solve *= 2;
                    Log::w("Double the number of tasks to solve: %d\n", _num_tasks_to_solve);
                }
                if (durationSolveTasks > _last_time_spend_to_solve_tasks * 2 && _num_tasks_to_solve > 1) {
                    _num_tasks_to_solve /= 2;
                    Log::w("Half the number of tasks to solve: %d\n", _num_tasks_to_solve);
                }
            }
            _last_time_spend_to_solve_tasks = durationSolveTasks;
            _init_time_spend_to_solve_tasks = std::chrono::high_resolution_clock::now();

    //         auto  end         = std::chrono::high_resolution_clock::now();
    // auto  duration_ms = static_cast<double>(
    //         std::chrono::duration_cast<std::chrono::milliseconds>(
    //             end - _init_time_spend_to_solve_tasks).count());

    // double throughput = _num_tasks_to_solve / duration_ms;    // tasks per ms
    // size_t remaining  = _init_task_network_size - _current_task_index;

    // switch (_phase) {

    // /* ---------- 1) exploration: keep doubling while things get better ---------- */
    // case Phase::EXPLORE:
    //     if (throughput > _best_tp * (1.0 + EPS)) {            // still improving
    //         _best_tp      = throughput;
    //         _best_batch   = _num_tasks_to_solve;
    //         _lo_batch     = _num_tasks_to_solve;
    //         _num_tasks_to_solve =
    // std::min<size_t>(static_cast<size_t>(_num_tasks_to_solve * 2ULL),
    //                  remaining);
    //     } else {                                              // just passed the peak
    //         _hi_batch     = _num_tasks_to_solve;
    //         _num_tasks_to_solve = (_lo_batch + _hi_batch) / 2;
    //         _phase        = Phase::SEARCH;
    //     }
    //     break;

    // /* ---------- 2) binary search inside the bracket [lo,hi] ---------- */
    // case Phase::SEARCH:
    //     if (throughput > _best_tp) {                          // keep best
    //         _best_tp     = throughput;
    //         _best_batch  = _num_tasks_to_solve;
    //     }

    //     // shrink the bracket depending on which side worsened
    //     if (_num_tasks_to_solve > _best_batch)
    //         _hi_batch = _num_tasks_to_solve;
    //     else
    //         _lo_batch = _num_tasks_to_solve;

    //     if (_hi_batch - _lo_batch <= 2) {                     // bracket tight enough
    //         _num_tasks_to_solve = std::min(_best_batch, remaining);
    //     } else {
    //         _num_tasks_to_solve = (_lo_batch + _hi_batch) / 2;
    //     }
    //     break;
    // }

    // /* housekeeping exactly as you had it */
    // _init_time_spend_to_solve_tasks = std::chrono::high_resolution_clock::now();
        }
        _current_task_index += _num_tasks_to_solve;
        if (_current_task_index > _init_task_network_size) {
            _current_task_index = _init_task_network_size;
        }
        return false;
    }
}

void SeparateTasksScheduler::updateReachableStateAfterTasksAccomplished(Encoding &enc, const std::vector<Layer *> &layers, int layerIdx, int solvePositions)
{
    _reachable_state_pos_after_tasks_accomplished = _init_state;
    _reachable_state_neg_after_tasks_accomplished.clear();

    // TODO FIXME. OTHER TECHNIQUE WORKS FINE, BUT IT IS LESS EFFICIENT
    if (_add_tasks_as_clauses)
    {
        // We can directly compute the state after all accomplished tasks
        Layer &layer = *layers[layerIdx];
        for (int i = 0; i < solvePositions; ++i)
        {

            // To debug, print the current predicate at this position
            // enc.printStatementsAtPosition(layerIdx, i);

            // Get the action true in this position
            const USignature aSig = enc.getDecodingOpHoldingInLayerPos(layerIdx, i);

            // It is maybe a reduction without subtasks, in that case, we skip it
            if (_htn.isReduction(aSig))
            {
                continue;
            }

            Log::d("Action %s is true in layer %d, position %d\n", TOSTR(aSig), layerIdx, i);
            Action action = _htn.toAction(aSig._name_id, aSig._args);
            // First, remove from the current state all the negative effects of the action

            // Verify that all positive preconditions of the action are satisfied
            for (const auto &posPrecondition : action.getPreconditions())
            {
                if (posPrecondition._negated)
                    continue; // Only consider positive preconditions

                if (!_reachable_state_pos_after_tasks_accomplished.count(posPrecondition._usig))
                {
                    int varAction = layer[i].getVariableOrZero(VarType::OP, aSig);
                    int varPosPrecondition = layer[i].getVariableOrZero(VarType::FACT, posPrecondition._usig);
                    Log::e("Action %s (var: %d) has a positive precondition %s (var: %d) that is not satisfied in the reachable state after tasks accomplished\n", TOSTR(action.getSignature()), varAction, TOSTR(posPrecondition._usig), varPosPrecondition);
                    Log::e("Original layer position: (%d,%d)\n", layer[i].getOriginalLayerIndex(), layer[i].getOriginalPositionIndex());
                    Log::e("This means that the action is not applicable in the reachable state after tasks accomplished\n");
                    Log::e("This is a bug in the planner, please report it\n");
                    exit(1);
                }
            }

            for (const auto &negEffect : action.getEffects())
            {
                if (!negEffect._negated)
                    continue; // Only consider negative effects

                Log::d("  Adding negative effect %s to reachable state after tasks accomplished\n", TOSTR(negEffect._usig));
                _reachable_state_pos_after_tasks_accomplished.erase(negEffect._usig);
                _reachable_state_neg_after_tasks_accomplished.insert(negEffect._usig);
            }
            // Then add the positive effects of the action
            for (const auto &posEffect : action.getEffects())
            {
                if (posEffect._negated)
                    continue; // Only consider positive effects

                Log::d("  Adding positive effect %s to reachable state after tasks accomplished\n", TOSTR(posEffect._usig));
                _reachable_state_neg_after_tasks_accomplished.erase(posEffect._usig);
                _reachable_state_pos_after_tasks_accomplished.insert(posEffect._usig);
            }
        }

        // Add it into a bitvec
        _reachable_state_pos_after_tasks_accomplished_bitvec = BitVec(_htn.getNumPositiveGroundFacts());
        _reachable_state_neg_after_tasks_accomplished_bitvec = BitVec(_htn.getNumPositiveGroundFacts());

        for (int i = 0; i < _htn.getNumPositiveGroundFacts(); ++i) {
            const USignature& iSig = _htn.getGroundPositiveFact(i);
            if (_reachable_state_pos_after_tasks_accomplished.count(iSig)) {
                _reachable_state_pos_after_tasks_accomplished_bitvec.set(i);
            } else {
                _reachable_state_neg_after_tasks_accomplished_bitvec.set(i);
            }
        }

        // Clean all the position done
        for (int i = 0; i < solvePositions - 1; ++i) {
            Position &pos = layer[i];
            pos.clearFactSupportsId();
        }
    }
    else
    {

        _reachable_state_pos_after_tasks_accomplished_bitvec = _init_state_pos_bitvec;
        _reachable_state_neg_after_tasks_accomplished_bitvec = _init_state_neg_bitvec;

        // Otherwise, do the classical way
        Layer &layer = *layers[layerIdx];
        for (int i = 0; i < solvePositions; ++i)
        {
            Position &pos = layer[i];

            const BitVec& pos_facts_changed = pos.getFactChangeBitVec(/*negated=*/false);
            const BitVec& neg_facts_changed = pos.getFactChangeBitVec(/*negated=*/true);
            _reachable_state_pos_after_tasks_accomplished_bitvec.or_with(pos_facts_changed);
            _reachable_state_neg_after_tasks_accomplished_bitvec.or_with(neg_facts_changed);
        }
    }

    Log::d("Size of reachable state after tasks accomplished: %zu positive, %zu negative\n",
           _reachable_state_pos_after_tasks_accomplished_bitvec.count(),
           _reachable_state_neg_after_tasks_accomplished_bitvec.count());

    int a = 0;
}

bool SeparateTasksScheduler::handleVirtualPlanFailure(Encoding &enc, int layerSize){
//     _phase      = Phase::EXPLORE;
// _hi_batch   = _lo_batch = _best_batch = 1;
// _best_tp    = 0.0;
    if (_add_tasks_as_clauses) {
        if (_settings_manager.get_setting(_domain_name, "independent_init_tasks") == true) {
            Log::w("The tasks in the initial state may not be independent. Set the setting independent_init_tasks to false, and restart the full planner\n");
            _settings_manager.set_setting(_domain_name, "independent_init_tasks", false);
            _restart_planner = true;
            return false;
        }
    } else { // !_add_tasks_as_clauses: try to relax assumptions
        while (!_vars_tasks_accomplished.empty()) {
            Log::w("Failed to find a virtual plan! Relax the assumptions of the tasks accomplished\n");
            _num_failed_sat++;
            if (!_num_tasks_solved_at_each_step.empty()) {
                int lastSolved = _num_tasks_solved_at_each_step.back();
                _num_init_tasks_resolved -= lastSolved;
                _current_task_index = _num_init_tasks_resolved + _num_tasks_to_solve;
                if (_current_task_index > _init_task_network_size) {
                    _current_task_index = _init_task_network_size;
                }
            }
            _vars_tasks_accomplished.pop_back();
            _num_pos_done_at_each_step.pop_back();
            if (!_num_tasks_solved_at_each_step.empty()) {
                _num_tasks_solved_at_each_step.pop_back();
            }
            if (!_vars_tasks_accomplished.empty()) {
                enc.addAssumptionsTasksAccomplished(_vars_tasks_accomplished.back(), _add_tasks_as_clauses);
            }
            int result = enc.solve();

            bool solved_virtual_plan = (result == 10);
            Log::i("Solved virtual plan: %d\n", solved_virtual_plan);
            if (solved_virtual_plan) {
                _num_pos_done = _num_pos_done_at_each_step.back();
                return true;
            }
        }
        Log::w("No virtual plan found. Problem is impossible! Exiting.\n");
        return false;
    }
    return false;
}

bool SeparateTasksScheduler::mustRestartPlanner() const {
    return _restart_planner;
}
