#ifndef SIBYLSAT_MUTEX_GROUPS_H
#define SIBYLSAT_MUTEX_GROUPS_H


#include <unordered_map>
#include <vector>

#include "data/signature.h"

// Forward declaration
class HtnInstance;
class MutexLoader;

/** Ground fact groups whose members cannot hold simultaneously. */
class MutexGroups {
private:
    struct LiftedMutexParameter {
        std::string hddl_type;
        bool is_counted_var;
        bool is_constant = false;
        int val;
    };

    struct LiftedMutexPredicate {
        std::string name;
        std::vector<int> idx_params;
    };

    struct LiftedMutexGroup {
        std::vector<LiftedMutexPredicate> preds;
        std::vector<LiftedMutexParameter> params;
    };

    friend class MutexLoader;

    std::vector<LiftedMutexGroup> _lifted_fam_groups;
    HtnInstance& _htn;
    std::vector<USigSet> _groups;
    FlatHashMap<USignature, FlatHashSet<int>, USignatureHasher> _group_ids_by_fact;

    void parseNextLiftedFamGroup(const std::string& line, LiftedMutexGroup& group);
    void parseNextPredicateInLiftedFamGroup(LiftedMutexGroup& group, const std::string& line, int& currentPos, std::unordered_map<std::string, int>& variableIndices);
    void printAllLiftedFamGroups();
    void printLiftedFamGroup(const LiftedMutexGroup& group) const;
    void generateFixedVariableCombinations(LiftedMutexGroup& group, size_t parameterIndex);
    void generateCountedVariableCombinations(LiftedMutexGroup& group, LiftedMutexPredicate& predicate, size_t parameterIndex, USigSet& facts);
    void groundLiftedGroup(LiftedMutexGroup& group);
    void retainReachableFacts(const USigSet& reachableFacts);

public:
    /**
     * Load and ground the lifted FAM groups written by pandaPIgrounder.
     * `V` parameters select one ground group and `C` parameters enumerate
     * all facts within that group.
     */
    MutexGroups(const std::string& mutexFile, HtnInstance& htn);

    /** Return the IDs of all mutex groups containing this fact. */
    const FlatHashSet<int>& getGroupIdsForFact(const USignature& fact) const;
    /** Return all facts belonging to one grounded mutex group. */
    const USigSet& getFactsInGroup(int groupId) const;
    /** Return whether the fact belongs to at least one mutex group. */
    bool containsFact(const USignature& fact) const { return _group_ids_by_fact.count(fact); }
};


#endif
