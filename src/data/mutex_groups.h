#ifndef SIBYLSAT_MUTEX_GROUPS_H
#define SIBYLSAT_MUTEX_GROUPS_H


#include <cstddef>
#include <vector>

/**
 * Immutable index of grounded mutex groups.
 *
 * Facts are represented by FactAnalysis IDs so the planner does not retain a
 * second copy of every fact signature. Construction from lifted invariants is
 * handled by the preprocessing layer.
 */
class MutexGroups {
private:
    std::vector<std::vector<int>> _fact_ids_by_group;
    std::vector<std::vector<int>> _group_ids_by_fact;

public:
    /** Build the two-way lookup and discard groups that cannot impose a mutex. */
    MutexGroups(std::vector<std::vector<int>> factIdsByGroup, size_t numGroundFacts);

    /** Return the IDs of all mutex groups containing the ground fact. */
    const std::vector<int>& getGroupIdsForFact(int factId) const;
    /** Return the ground-fact IDs belonging to one mutex group. */
    const std::vector<int>& getFactIdsInGroup(int groupId) const;
    /** Return whether the ground fact belongs to at least one nontrivial group. */
    bool containsFact(int factId) const;
};


#endif
