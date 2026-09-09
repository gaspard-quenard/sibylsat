#ifndef SIBYLSAT_PROBLEM_PREPROCESSOR_H
#define SIBYLSAT_PROBLEM_PREPROCESSOR_H

#include <memory>

#include "algo/fact_analysis.h"
#include "algo/q_constant_manager.h"
#include "data/htn_instance.h"
#include "data/mutex_groups.h"
#include "data/tdg.h"
#include "preprocessing/macro_action_compiler.h"

class Parameters;

/** Owns the model and analysis data that remain valid throughout planning. */
struct PlanningContext {
    // Includes inferred method preconditions and possible method effects.
    std::unique_ptr<HtnInstance> htn;

    // Owns pseudo-constants and their search-time domains.
    std::unique_ptr<QConstantManager> qConstants;

    // Describes how compiled macro actions expand back into primitive actions.
    std::unique_ptr<MacroActionCompiler> macroActions;

    // Owns the immutable ground universe plus mutable search reachability state.
    std::unique_ptr<FactAnalysis> factAnalysis;

    // Optional grounded fact groups used to strengthen state encodings.
    std::unique_ptr<MutexGroups> mutexGroups;

    // Optional task-decomposition heuristic required by optimal planning.
    std::unique_ptr<TDG> tdg;

    /** Restore only analysis state that is specific to an abandoned search. */
    void resetForNewSearch();
};

/** Parse, transform, build, and analyze a problem before search begins. */
PlanningContext preprocessProblem(Parameters& params);

#endif
