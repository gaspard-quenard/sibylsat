#ifndef SIBYLSAT_GROUND_PROBLEM_LOADER_H
#define SIBYLSAT_GROUND_PROBLEM_LOADER_H

#include <string>
#include <utility>

#include "data/signature.h"

class HtnInstance;

/** The positive and explicitly represented negative facts emitted by the grounder. */
class GroundFacts {
private:
    USigSet _positive;
    USigSet _negative;

    friend class GroundProblemLoader;

public:
    USigSet takePositive() { return std::move(_positive); }
    USigSet takeNegative() { return std::move(_negative); }
};

/** Runs the external grounding pipeline and reads its state-feature section. */
class GroundProblemLoader {
public:
    /**
     * Ground the problem and return its state features. When requested, the
     * generated file also retains grounded operations for the TDG heuristic.
     */
    static GroundFacts load(HtnInstance& htn, const std::string& domainFilename, const std::string& problemFilename, bool includeGroundOperations);

private:
    static GroundFacts parseStateFeatures(HtnInstance& htn, const std::string& filename);
};

#endif
