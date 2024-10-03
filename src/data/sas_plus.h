#ifndef DOMPASCH_TREE_REXX_SAS_PLUS_H
#define DOMPASCH_TREE_REXX_SAS_PLUS_H


#include <vector>
#include <unordered_map>
#include "data/signature.h"

// Forward declaration
class HtnInstance;


struct params_lfg {
    std::string hddl_type;
    bool is_counted_var;
    bool is_constant = false;
    int val; // To assignate specific value when grounding the lifted fam group
};

struct lfg_pred {
    std::string name;
    std::vector<int> idx_params;
};

struct lfg {
    std::vector<lfg_pred> preds;
    std::vector<params_lfg> params;
};


class SASPlus {

private:

    std::vector<lfg> _lifted_fam_groups;
    HtnInstance* _htn;

    void parseNextLiftedFamGroup(const std::string& line, lfg& lfg);
    void parseNextPredicateInLiftedFamGroup(lfg& lfg, const std::string& line, int& current_pos, std::unordered_map<std::string, int>& var_name_to_idx);

    void printAllLiftedFamGroups();
    const void printLiftedFamGroup(const lfg& lfg) const;


    // Function to ground all the lifted fam groups
    void processGroundedPredicate(const lfg_pred& grounded_pred);
    void generateCountedVarCombinations(lfg& my_lfg, size_t param_index, FlatHashSet<USignature, USignatureHasher>& bucket);
    void generateFixedVarCombinations(lfg& my_lfg, size_t param_index);
    void generateCountedVarCombinationsForPred(lfg& my_lfg, lfg_pred& pred, size_t param_index, FlatHashSet<USignature, USignatureHasher>& bucket);
    void groundLFG(lfg& my_lfg);

public:

    /**
     * Takes as intput a SAS+ file:
     * A file where each line contains a lifted fam group in the following format:
     * {<pred1> [V|C]<idx>:<type_arg_1> ... [V|C]<idx>:<type_arg_n>, ..., <pred_n> [V|C]<idx>:<type_arg_1> ... [V/C]<idx>:<type_arg_n>}
     * V for fixed variable, C for counter variable
     * e.g: for blockworld domain:
     * {handempty, holding C0:block}
     * {on V0:block C1:block, ontable V0:block, holding V0:block}
     * {on C1:block V0:block, clear V0:block, holding V0:block}
    */
    SASPlus(const std::string& fileSASPlus, HtnInstance* htn);

    // Create a dictionnary with a USignature in key and a vector of USignature in value
    // The key is the predicate and the value is the list of predicates which are mutex with the key
    // FlatHashMap<USignature, USigSet, USignatureHasher> mutexPredicates;

    // std::vector<std::vector<USignature>> group_mutexes; // All group of mutexes. Each group is a set of predicates which are mutex together
    std::vector<FlatHashSet<USignature, USignatureHasher>> group_mutexes; // All group of mutexes. Each group is a set of predicates which are mutex together
    FlatHashMap<USignature, FlatHashSet<int>, USignatureHasher> pred_to_group_mutexes; // For each predicate, the group of mutexes it belongs to

    const FlatHashSet<int>& getGroupsMutexesOfPred(const USignature& pred) const;
    const FlatHashSet<USignature, USignatureHasher>& getPredsInGroup(int group_id) const;
    const bool isInMutexGroup(const USignature& pred1) const {return pred_to_group_mutexes.find(pred1) != pred_to_group_mutexes.end();}
    void cleanMutexGroupsWithPandaPiGrounderPreprocessingFacts(const USigSet& preprocessed_facts_pos_state_features);


};


#endif //DOMPASCH_TREE_REXX_SAS_PLUS_H
