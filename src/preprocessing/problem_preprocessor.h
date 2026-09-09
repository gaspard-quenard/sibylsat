#ifndef SIBYLSAT_PROBLEM_PREPROCESSOR_H
#define SIBYLSAT_PROBLEM_PREPROCESSOR_H

#include <memory>

#include "algo/fact_analysis.h"
#include "data/htn_instance.h"
#include "data/tdg.h"

class Parameters;

/** Owns the model and analysis data that remain valid throughout planning. */
struct PlanningContext {
    // Includes inferred method preconditions, possible method effects, mutexes,
    // and macro-action decoding metadata.
    std::unique_ptr<HtnInstance> htn;

    // Owns the immutable ground universe plus mutable search reachability state.
    std::unique_ptr<FactAnalysis> factAnalysis;

    // Optional task-decomposition heuristic required by optimal planning.
    std::unique_ptr<TDG> tdg;

    /** Restore only analysis state that is specific to an abandoned search. */
    void resetForNewSearch();
};

/** Parse, transform, build, and analyze a problem before search begins. */
PlanningContext preprocessProblem(Parameters& params);

#endif
