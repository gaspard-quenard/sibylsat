#ifndef SIBYLSAT_PANDA_GROUND_PROBLEM_LOADER_H
#define SIBYLSAT_PANDA_GROUND_PROBLEM_LOADER_H

#include <filesystem>
#include <string>
#include <utility>

#include "data/signature.h"

class HtnInstance;

/** The positive and explicitly represented negative facts emitted by the grounder. */
class GroundFacts {
private:
    USigSet _positive;
    USigSet _negative;

    friend class PandaGroundProblemLoader;

public:
    USigSet takePositive() { return std::move(_positive); }
    USigSet takeNegative() { return std::move(_negative); }
};

/** Runs PandaPIgrounder and reads its state-feature section. */
class PandaGroundProblemLoader {
public:
    /**
     * Ground a PandaPIparser output file and return its state features. When
     * requested, the result also retains operations for the TDG heuristic.
     */
    static GroundFacts load(HtnInstance& htn, const std::filesystem::path& pandaProblemFile, bool includeGroundOperations);

private:
    static GroundFacts parseStateFeatures(HtnInstance& htn, const std::string& filename);
};

#endif
