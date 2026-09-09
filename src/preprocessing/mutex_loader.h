#ifndef SIBYLSAT_MUTEX_LOADER_H
#define SIBYLSAT_MUTEX_LOADER_H

#include <memory>

class HtnInstance;
class FactAnalysis;
class Parameters;
class MutexGroups;

/** Runs the external invariant pipeline and loads its grounded mutex groups. */
class MutexLoader {
public:
    /** Compute, ground, and reachability-filter mutex groups for the configured problem. */
    static std::unique_ptr<MutexGroups> compute(const Parameters& params, HtnInstance& htn, const FactAnalysis& facts);
};

#endif
