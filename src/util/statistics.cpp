#include "util/statistics.h"

#include <algorithm>
#include <cassert>
#include <utility>

#include "util/log.h"

std::size_t Statistics::stageIndex(EncodingStage stage) {
    const std::size_t index = static_cast<std::size_t>(stage);
    assert(index < NUM_ENCODING_STAGES);
    return index;
}

const char* Statistics::stageName(EncodingStage stage) {
    switch (stage) {
        case EncodingStage::ACTION_CONSTRAINTS: return "action constraints";
        case EncodingStage::ACTION_EFFECTS: return "action effects";
        case EncodingStage::AT_LEAST_ONE_ELEMENT: return "at-least-one constraints";
        case EncodingStage::AT_MOST_ONE_ELEMENT: return "at-most-one constraints";
        case EncodingStage::DIRECT_FRAME_AXIOMS: return "direct frame axioms";
        case EncodingStage::EXPANSIONS: return "expansion constraints";
        case EncodingStage::FACT_VARIABLE_ENCODING: return "fact variables";
        case EncodingStage::FORBIDDEN_OPERATIONS: return "forbidden operations";
        case EncodingStage::INDIRECT_FRAME_AXIOMS: return "indirect frame axioms";
        case EncodingStage::PREDECESSORS: return "predecessor constraints";
        case EncodingStage::Q_CONSTANT_EQUALITY: return "Q-constant equality";
        case EncodingStage::Q_FACT_SEMANTICS: return "Q-fact semantics";
        case EncodingStage::Q_TYPE_CONSTRAINTS: return "Q-constant type constraints";
        case EncodingStage::REDUCTION_CONSTRAINTS: return "reduction constraints";
        case EncodingStage::SUBSTITUTION_CONSTRAINTS: return "substitution constraints";
        case EncodingStage::ASSUMPTIONS: return "assumptions";
        case EncodingStage::PLAN_LENGTH_COUNTING: return "plan-length counting";
        case EncodingStage::MUTEXES: return "mutex constraints";
        case EncodingStage::COUNT: break;
    }
    return "unknown encoding stage";
}

const char* Statistics::timingName(TimingStage stage) {
    switch (stage) {
        case TimingStage::GROUNDING: return "time grounding";
        case TimingStage::MUTEX_COMPUTATION: return "time compute mutexes";
        case TimingStage::EXPANSION: return "time expansion";
        case TimingStage::ENCODING: return "time encoding";
        case TimingStage::SOLVER: return "time solver";
        case TimingStage::TOTAL: return "time total";
    }
    return "unknown timing stage";
}

void Statistics::beginPosition() {
    _previous_num_clauses = _num_clauses;
    _previous_num_literals = _num_literals;
}

void Statistics::endPosition() {
    assert(_current_stages.empty());
    Log::v("  Encoded %llu cls, %llu lits\n",
            static_cast<unsigned long long>(_num_clauses - _previous_num_clauses),
            static_cast<unsigned long long>(_num_literals - _previous_num_literals));
}

void Statistics::begin(EncodingStage stage) {
    if (!_current_stages.empty()) {
        const EncodingStage previousStage = _current_stages.back();
        _num_clauses_per_stage[stageIndex(previousStage)] += _num_clauses - _num_clauses_at_stage_start;
    }
    _num_clauses_at_stage_start = _num_clauses;
    _current_stages.push_back(stage);
}

void Statistics::end(EncodingStage stage) {
    assert(!_current_stages.empty() && _current_stages.back() == stage);
    _current_stages.pop_back();
    _num_clauses_per_stage[stageIndex(stage)] += _num_clauses - _num_clauses_at_stage_start;
    _num_clauses_at_stage_start = _num_clauses;
}

void Statistics::beginTiming(TimingStage stage) {
    if (_active_timings.count(stage) != 0) {
        Log::w("Warning: Attempted to start timing for stage %s which is already running\n", timingName(stage));
        return;
    }
    _active_timings.emplace(stage, Clock::now());
}

void Statistics::endTiming(TimingStage stage) {
    const auto activeTiming = _active_timings.find(stage);
    if (activeTiming == _active_timings.end()) {
        Log::w("Warning: Attempted to end timing for stage %s which was not started\n", timingName(stage));
        return;
    }
    _elapsed_times[stage] += std::chrono::duration_cast<Duration>(Clock::now() - activeTiming->second);
    _active_timings.erase(activeTiming);
}

Statistics::Duration Statistics::getTiming(TimingStage stage) const {
    const auto elapsed = _elapsed_times.find(stage);
    return elapsed == _elapsed_times.end() ? Duration::zero() : elapsed->second;
}

void Statistics::print() const {
    Log::i("Total amount of clauses encoded: %llu\n", static_cast<unsigned long long>(_num_clauses));

    std::vector<std::pair<EncodingStage, Count>> stages;
    for (std::size_t index = 0; index < NUM_ENCODING_STAGES; ++index) {
        if (_num_clauses_per_stage[index] != 0) {
            stages.emplace_back(static_cast<EncodingStage>(index), _num_clauses_per_stage[index]);
        }
    }
    std::sort(stages.begin(), stages.end(), [](const auto& left, const auto& right) {
        if (left.second != right.second) return left.second > right.second;
        return left.first < right.first;
    });
    for (const auto& [stage, count] : stages) {
        Log::i("- %s : %llu cls\n", stageName(stage), static_cast<unsigned long long>(count));
    }

    for (const auto& [stage, duration] : _elapsed_times) {
        Log::i("* %s : %lld ms\n", timingName(stage), static_cast<long long>(std::chrono::duration_cast<std::chrono::milliseconds>(duration).count()));
    }
    if (!_active_timings.empty()) {
        Log::w("\nWarning: Some timing stages were not properly closed:\n");
        for (const auto& [stage, start] : _active_timings) {
            (void) start;
            Log::w("* %s\n", timingName(stage));
        }
    }
}

void Statistics::resetSearchStatistics() {
    _num_clauses = 0;
    _num_literals = 0;
    _num_assumptions = 0;
    _previous_num_clauses = 0;
    _previous_num_literals = 0;
    _num_clauses_at_stage_start = 0;
    _num_clauses_per_stage.fill(0);
    _current_stages.clear();

    _active_timings.erase(TimingStage::EXPANSION);
    _active_timings.erase(TimingStage::ENCODING);
    _active_timings.erase(TimingStage::SOLVER);
    _elapsed_times.erase(TimingStage::EXPANSION);
    _elapsed_times.erase(TimingStage::ENCODING);
    _elapsed_times.erase(TimingStage::SOLVER);
}
