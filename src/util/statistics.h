#ifndef STATISTICS_H
#define STATISTICS_H

#include <vector>
#include <map>
#include <chrono>
#include <assert.h>

// Example of logging; adjust to your own logging utility as needed.
#include "util/log.h"

// Stage constants
const int STAGE_ACTIONCONSTRAINTS    = 0;
const int STAGE_ACTIONEFFECTS        = 1;
const int STAGE_ATLEASTONEELEMENT    = 2;
const int STAGE_ATMOSTONEELEMENT     = 3;
const int STAGE_AXIOMATICOPS         = 4;
const int STAGE_DIRECTFRAMEAXIOMS    = 5;
const int STAGE_EXPANSIONS           = 6;
const int STAGE_FACTPROPAGATION      = 7;
const int STAGE_FACTVARENCODING      = 8;
const int STAGE_FORBIDDENOPERATIONS  = 9;
const int STAGE_INDIRECTFRAMEAXIOMS  = 10;
const int STAGE_INITSUBSTITUTIONS    = 11;
const int STAGE_PREDECESSORS         = 12;
const int STAGE_QCONSTEQUALITY       = 13;
const int STAGE_QFACTSEMANTICS       = 14;
const int STAGE_QTYPECONSTRAINTS     = 15;
const int STAGE_REDUCTIONCONSTRAINTS = 16;
const int STAGE_SUBSTITUTIONCONSTRAINTS = 17;
const int STAGE_TRUEFACTS            = 18;
const int STAGE_ASSUMPTIONS          = 19;
const int STAGE_PLANLENGTHCOUNTING   = 20;
const int STAGE_MUTEX                = 21;

enum class TimingStage {
    INIT_GROUNDING,
    INIT_MUTEXES,
    PLANNER,
    EXPANSION,
    ENCODING,
    SOLVER,
    ENCODING_MUTEXES,
    TOTAL,
    EXPANSION_LEFT_SIMPLFIED,
    EXPANSION_LEFT,
    EXPANSION_ABOVE,
    EXPANSION_INITIALIZED_NEXT_EFFECTS,
    TEST_1,
    TEST_2,
    TEST_3,
    TEST_4,
    TEST_5,
    TEST_6,
    COMPUTE_PFC,
    CLEAN_PFC,
    GET_ALL_PREDS,
    EXPANSION_LEFT_GROUND,
    EXPANSION_LEFT_PSEUDO,
    CLEANING_MEMORY,
};

class Statistics
{
public:
    /**
     * Return the singleton instance of Statistics.
     * Ensures only one instance exists in the entire program.
     */
    static Statistics& getInstance() {
        static Statistics instance;  // Constructed only once
        return instance;
    }

    // Deleted copy/assignment to enforce singleton property
    Statistics(const Statistics&) = delete;
    Statistics& operator=(const Statistics&) = delete;


    void beginPosition() {
        _prev_num_cls  = _num_cls;
        _prev_num_lits = _num_lits;
    }

    void endPosition() {
        assert(_current_stages.empty());
        Log::v("  Encoded %i cls, %i lits\n", 
               _num_cls - _prev_num_cls, 
               _num_lits - _prev_num_lits);
    }

    void begin(int stage) {
        if (!_current_stages.empty()) {
            int oldStage = _current_stages.back();
            _num_cls_per_stage[oldStage] += _num_cls - _num_cls_at_stage_start;
        }
        _num_cls_at_stage_start = _num_cls;
        _current_stages.push_back(stage);
    }

    void end(int stage) {
        assert(!_current_stages.empty() && _current_stages.back() == stage);
        _current_stages.pop_back();
        _num_cls_per_stage[stage] += _num_cls - _num_cls_at_stage_start;
        _num_cls_at_stage_start = _num_cls;
    }

    // Print a summary of stages and timing
    void printStats() {
        Log::i("Total amount of clauses encoded: %i\n", _num_cls);

        // Sort stages in descending order of their clause counts
        std::map<int, int, std::greater<int>> stagesSorted;
        for (size_t stage = 0; stage < _num_cls_per_stage.size(); stage++) {
            if (_num_cls_per_stage[stage] > 0)
                stagesSorted[_num_cls_per_stage[stage]] = static_cast<int>(stage);
        }

        // Print each stage
        for (const auto& [num, stage] : stagesSorted) {
            Log::i("- %s : %i cls\n", STAGES_NAMES[stage], num);
        }
        _num_cls_per_stage.clear();

        // Print timing statistics
        if (!_stage_times_ms.empty()) {
            for (const auto& [stage, time] : _stage_times_ms) {
                Log::i("* %s : %lli ms\n", toString(stage), time / 1000000);
            }
        }

        // Warn if some timing stages were not closed
        if (!_active_timings.empty()) {
            Log::w("\nWarning: Some timing stages were not properly closed:\n");
            for (const auto& [stage, _] : _active_timings) {
                Log::w("* %s\n", toString(stage));
            }
        }
    }


    void beginTiming(TimingStage stage) {
        if (_active_timings.count(stage) > 0) {
            Log::w("Warning: Attempted to start timing for stage %s which is already running\n", 
                toString(stage));
            return;
        }
        _active_timings[stage] = std::chrono::high_resolution_clock::now();
    }


    void endTiming(TimingStage stage) {
        auto it = _active_timings.find(stage);
        if (it == _active_timings.end()) {
            Log::w("Warning: Attempted to end timing for stage %s which was not started\n", 
                toString(stage));
            return;
        }

        auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::high_resolution_clock::now() - it->second).count();
        _stage_times_ms[stage] += duration;
        _active_timings.erase(it);
    }

    long long getTiming(TimingStage stage) {
        return _stage_times_ms[stage];
    }

    // Utility to convert a TimingStage enum to string
    static const char* toString(TimingStage stage) {
        switch (stage) {
            case TimingStage::EXPANSION:        return "time expansion";
            case TimingStage::ENCODING:         return "time encoding";
            case TimingStage::SOLVER:           return "time solver";
            case TimingStage::INIT_GROUNDING:   return "time grounding";
            case TimingStage::INIT_MUTEXES:     return "time compute mutexes";
            case TimingStage::PLANNER:          return "time planner";
            case TimingStage::ENCODING_MUTEXES: return "time encoding mutexes";
            case TimingStage::TOTAL:            return "time total";
            case TimingStage::EXPANSION_LEFT_SIMPLFIED: return "time expansion left simplified";
            case TimingStage::EXPANSION_LEFT:   return "time expansion left";
            case TimingStage::EXPANSION_ABOVE:  return "time expansion above";
            case TimingStage::EXPANSION_INITIALIZED_NEXT_EFFECTS: return "time expansion initialized next effects";
            case TimingStage::TEST_1:           return "time test 1";
            case TimingStage::TEST_2:           return "time test 2";
            case TimingStage::TEST_3:           return "time test 3";
            case TimingStage::TEST_4:           return "time test 4";
            case TimingStage::TEST_5:           return "time test 5";
            case TimingStage::TEST_6:           return "time test 6";
            case TimingStage::COMPUTE_PFC:      return "time compute pfc";
            case TimingStage::CLEAN_PFC:        return "time clean pfc";
            case TimingStage::GET_ALL_PREDS:        return "time get all preds";
            case TimingStage::EXPANSION_LEFT_GROUND: return "time expansion left ground";
            case TimingStage::EXPANSION_LEFT_PSEUDO: return "time expansion left pseudo";
            case TimingStage::CLEANING_MEMORY:  return "time cleaning memory";
            default:                            return "UNKNOWN_TIMING_STAGE";

        }
    }

    // Function to reset all statistics
    void reset() {
        _num_cls = 0;
        _num_lits = 0;
        _num_asmpts = 0;
        _num_cls_per_stage.clear();
        _current_stages.clear();
        _prev_num_cls = 0;
        _prev_num_lits = 0;
        _num_cls_at_stage_start = 0;
        _active_timings.clear();
        _stage_times_ms.clear();
    }

    // Public data members (if needed externally)
    int _num_cls  = 0;
    int _num_lits = 0;
    int _num_asmpts = 0;

private:
    // Private constructor for singleton
    Statistics() {
        _num_cls_per_stage.resize(sizeof(STAGES_NAMES)/sizeof(*STAGES_NAMES));
    }

    // Destructor prints the final stats automatically
    ~Statistics() {
        
    }

private:
    // Stage names
    const char* STAGES_NAMES[22] = {
        "actionconstraints", "actioneffects", "atleastoneelement", "atmostoneelement",
        "axiomaticops", "directframeaxioms", "expansions", "factpropagation",
        "factvarencoding", "forbiddenoperations", "indirectframeaxioms", "initsubstitutions",
        "predecessors", "qconstequality", "qfactsemantics", "qtypeconstraints",
        "reductionconstraints", "substitutionconstraints", "truefacts", "assumptions",
        "planlengthcounting", "mutexes"
    };

    // Tracks the total clauses added per stage
    std::vector<int> _num_cls_per_stage;

    // Stack of current active stages
    std::vector<int> _current_stages;

    // Clause counters
    int _prev_num_cls  = 0;
    int _prev_num_lits = 0;
    int _num_cls_at_stage_start = 0;

    // Timing-related members
    std::map<TimingStage, std::chrono::time_point<std::chrono::high_resolution_clock>> _active_timings;
    std::map<TimingStage, long long> _stage_times_ms;

};

#endif // STATISTICS_H
