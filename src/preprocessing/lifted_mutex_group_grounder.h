#ifndef SIBYLSAT_LIFTED_MUTEX_GROUP_GROUNDER_H
#define SIBYLSAT_LIFTED_MUTEX_GROUP_GROUNDER_H

#include <filesystem>
#include <vector>

class FactAnalysis;
class HtnInstance;

/** Reads pandaPIgrounder FAM groups and grounds their positive members. */
class LiftedMutexGroupGrounder {
public:
    /**
     * Return nontrivial mutex groups as FactAnalysis IDs.
     *
     * Fixed (`V`) parameters select a ground group, while counted (`C`)
     * parameters range over the facts inside that group.
     */
    static std::vector<std::vector<int>> groundFile(const std::filesystem::path& mutexFile, HtnInstance& htn, FactAnalysis& facts);
};

#endif
