#include "algo/separate_tasks_scheduler.h"

#include <algorithm>
#include <cstdlib>

#include "algo/fact_analysis.h"
#include "data/htn_instance.h"
#include "data/position.h"
#include "sat/encoding.h"
#include "util/log.h"
#include "util/names.h"

SeparateTasksScheduler::SeparateTasksScheduler(HtnInstance& htn, FactAnalysis& facts, const std::string& domainFilename)
        : _htn(htn),
          _facts(facts),
          _initial_task_count(htn.getInitReduction().getSubtasks().size()),
          _domain_name(getDomaineNameFromDomainFile(domainFilename)),
          _commit_solved_tasks_permanently(false),
          _batch_start_time(std::chrono::high_resolution_clock::now()) {
    constexpr const char* independentTasksSetting = "independent_init_tasks";
    if (!_settings_manager.has_setting(_domain_name, independentTasksSetting)) {
        Log::w("The domain %s has no independent_init_tasks setting; creating it with the default value true.\n", _domain_name.c_str());
        _settings_manager.set_setting(_domain_name, independentTasksSetting, true);
    }
    _commit_solved_tasks_permanently = _settings_manager.get_setting(_domain_name, independentTasksSetting);

    _initial_positive_facts = _facts.getInitialFacts(/*negated=*/false);
    _initial_negative_facts = _facts.getInitialFacts(/*negated=*/true);
}

void SeparateTasksScheduler::displayProgress() const {
    std::string bar;
    for (int taskIndex = 0; taskIndex < _initial_task_count; taskIndex++) {
        bar += taskIndex < _solved_task_count ? "\033[32m*\033[0m" : "\033[31m-\033[0m";
    }
    Log::i("\033[34m[%s\033[0m]\n", bar.c_str());
}

void SeparateTasksScheduler::applySolvedTaskConstraints(Encoding& encoding) {
    if (_solved_task_snapshots.empty()) return;
    encoding.addAssumptionsTasksAccomplished(_solved_task_snapshots.back(), _commit_solved_tasks_permanently);
}

int SeparateTasksScheduler::getPrimitiveAssumptionBoundary(int frontierSize) const {
    return frontierSize - _initial_task_count - 1 + _target_task_count;
}

void SeparateTasksScheduler::saveSolvedBatch(Encoding& encoding, const std::vector<Position*>& leaves, int solvedPositionCount) {
    _solved_position_count = solvedPositionCount;
    _solved_task_snapshots.push_back(encoding.getDecoder().collectTrueVariablesBeforeFrontierIndex(solvedPositionCount));
    _solved_position_count_history.push_back(solvedPositionCount);
    _batch_size_history.push_back(_next_batch_size);
    updateBoundaryState(encoding, leaves, solvedPositionCount);
}

void SeparateTasksScheduler::adaptNextBatchSize() {
    const auto now = std::chrono::high_resolution_clock::now();
    const long long durationMs = std::chrono::duration_cast<std::chrono::milliseconds>(now - _batch_start_time).count();
    Log::i("Time spent solving this batch: %lld ms (previous batch: %lld ms)\n", durationMs, _previous_batch_duration_ms);

    if (_previous_batch_duration_ms > 0 && durationMs < _previous_batch_duration_ms * 2) {
        _next_batch_size *= 2;
        Log::w("Doubling the next task batch to %d.\n", _next_batch_size);
    } else if (_previous_batch_duration_ms > 0 && durationMs > _previous_batch_duration_ms * 2 && _next_batch_size > 1) {
        _next_batch_size /= 2;
        Log::w("Halving the next task batch to %d.\n", _next_batch_size);
    }

    _previous_batch_duration_ms = durationMs;
    _batch_start_time = now;
}

bool SeparateTasksScheduler::updateAfterSolved(Encoding& encoding, const std::vector<Position*>& leaves) {
    _solved_task_count = _target_task_count;
    if (_solved_task_count == _initial_task_count) {
        displayProgress();
        Log::i("Solved the problem for all tasks\n");
        return true;
    }

    Log::i("Solved the problem for %d/%d tasks\n", _solved_task_count, _initial_task_count);
    const int solvedPositionCount = getPrimitiveAssumptionBoundary(leaves.size());
    saveSolvedBatch(encoding, leaves, solvedPositionCount);
    adaptNextBatchSize();
    _target_task_count = std::min(_target_task_count + _next_batch_size, _initial_task_count);
    return false;
}

void SeparateTasksScheduler::updateBoundaryState(Encoding& encoding, const std::vector<Position*>& leaves, int solvedPositionCount) {
    _positive_facts_after_solved_tasks = _initial_positive_facts;
    _negative_facts_after_solved_tasks = _initial_negative_facts;

    if (_commit_solved_tasks_permanently) {
        // The selected prefix cannot change, so its exact decoded state is safe to reuse.
        replaySelectedActions(encoding, leaves, solvedPositionCount);
    } else {
        // Assumptions may later be relaxed. Keep every fact reachable through any
        // operation in the prefix instead of committing to the current SAT model.
        accumulatePossibleEffects(leaves, solvedPositionCount);
    }
}

void SeparateTasksScheduler::replaySelectedActions(Encoding& encoding, const std::vector<Position*>& leaves, int solvedPositionCount) {
    for (int positionIndex = 0; positionIndex < solvedPositionCount; positionIndex++) {
        Position& leaf = *leaves[positionIndex];
        const USignature selectedOperation = encoding.getDecoder().getSelectedDecodedOperation(leaf);
        if (_htn.isReduction(selectedOperation)) continue;

        Log::d("Action %s is selected at position %d\n", TOSTR(selectedOperation), positionIndex);
        const Action action = _htn.toAction(selectedOperation._name_id, selectedOperation._args);
        for (const Signature& precondition : action.getPreconditions()) {
            if (precondition._negated) continue;
            const int factId = _facts.getGroundFactId(precondition._usig, /*negated=*/false);
            if (factId >= 0 && _positive_facts_after_solved_tasks.test(factId)) continue;

            const int actionVariable = leaf.getVariableOrZero(VarType::OP, selectedOperation);
            const int factVariable = leaf.getVariableOrZero(VarType::FACT, precondition._usig);
            Log::e("Action %s (var: %d) has an unsatisfied positive precondition %s (var: %d).\n",
                    TOSTR(action.getSignature()), actionVariable, TOSTR(precondition._usig), factVariable);
            Log::e("Leaf position: (%d,%d). This indicates an internal planner error.\n",
                    static_cast<int>(leaf.getCreationIteration()), static_cast<int>(leaf.getPositionId()));
            std::exit(1);
        }

        for (const Signature& effect : action.getEffects()) {
            if (!effect._negated) continue;
            const int factId = _facts.getGroundFactId(effect._usig, /*negated=*/true);
            if (factId < 0) continue;
            _positive_facts_after_solved_tasks.clear(factId);
            _negative_facts_after_solved_tasks.set(factId);
        }
        for (const Signature& effect : action.getEffects()) {
            if (effect._negated) continue;
            const int factId = _facts.getGroundFactId(effect._usig, /*negated=*/false);
            if (factId < 0) continue;
            _negative_facts_after_solved_tasks.clear(factId);
            _positive_facts_after_solved_tasks.set(factId);
        }
    }

    // Positions strictly before the boundary will never be encoded again.
    for (int positionIndex = 0; positionIndex < solvedPositionCount - 1; positionIndex++) {
        leaves[positionIndex]->getOutgoingEffects().clearSupports();
    }
}

void SeparateTasksScheduler::accumulatePossibleEffects(const std::vector<Position*>& leaves, int solvedPositionCount) {
    for (int positionIndex = 0; positionIndex < solvedPositionCount; positionIndex++) {
        const OutgoingEffects& effects = leaves[positionIndex]->getOutgoingEffects();
        _positive_facts_after_solved_tasks.or_with(effects.getFactChanges(/*negated=*/false));
        _negative_facts_after_solved_tasks.or_with(effects.getFactChanges(/*negated=*/true));
    }
}

bool SeparateTasksScheduler::handleAbstractPlanFailure(Encoding& encoding) {
    if (_commit_solved_tasks_permanently) {
        Log::w("No abstract plan exists with independently committed initial tasks; disabling that domain setting and restarting.\n");
        _settings_manager.set_setting(_domain_name, "independent_init_tasks", false);
        _restart_planner = true;
        return false;
    }

    while (!_solved_task_snapshots.empty()) {
        Log::w("No abstract plan found; relaxing the latest solved-task assumptions.\n");
        _solved_task_count -= _batch_size_history.back();
        _target_task_count = std::min(_solved_task_count + _next_batch_size, _initial_task_count);

        _solved_task_snapshots.pop_back();
        _solved_position_count_history.pop_back();
        _batch_size_history.pop_back();
        if (!_solved_task_snapshots.empty()) {
            encoding.addAssumptionsTasksAccomplished(_solved_task_snapshots.back(), _commit_solved_tasks_permanently);
        }

        if (encoding.solve() != 10) continue;
        _solved_position_count = _solved_position_count_history.empty() ? 0 : _solved_position_count_history.back();
        return true;
    }

    Log::w("No abstract plan found after relaxing every solved-task snapshot.\n");
    return false;
}
