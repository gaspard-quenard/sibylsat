#ifndef SIBYLSAT_MUTEX_LOADER_H
#define SIBYLSAT_MUTEX_LOADER_H

#include <filesystem>
#include <memory>

class HtnInstance;
class FactAnalysis;
class MutexGroups;

/** Runs the external invariant pipeline and loads its grounded mutex groups. */
class MutexLoader {
public:
    /** Compute, ground, and reachability-filter mutex groups for the configured problem. */
    static std::unique_ptr<MutexGroups> compute(HtnInstance& htn, FactAnalysis& facts, const std::filesystem::path& pandaProblemFile);
};

#endif
