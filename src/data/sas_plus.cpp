#include <iostream>
#include <fstream>
#include <sstream>
#include <unordered_set>

#include "data/sas_plus.h"
#include "util/log.h"
#include "util/names.h"
#include "data/htn_instance.h"
#include "data/substitution.h"

SASPlus::SASPlus(const std::string& fileSASPlus, HtnInstance* htn) : _htn(htn) {

    // Open the file and read it line by line (one lifted fam group per line)
    std::ifstream file(fileSASPlus);

    // Assert that the file exist
    assert(file.good() || Log::e("File %s does not exist!\n", fileSASPlus.c_str()));

    std::string line;

    // First, parse the lifted fam group

    // A line contains a lifted fam group
    while (std::getline(file, line)) {

        // Get all the predicates in the lines
        lfg lfg;
        parseNextLiftedFamGroup(line, lfg);
        _lifted_fam_groups.push_back(lfg);
    }

    // Then remove all the lifted fam group is there is another lifted fam group which is a super set of the current one
    Log::i("Removing redondant lifted fam groups...\n");
    Log::i("Number of lifted fam groups before removing redondant ones: %d\n", _lifted_fam_groups.size());
    // Remove all lifted fam group, where there is no constant for a specific type
    std::vector<lfg> new_lifted_fam_groups;
    for (lfg& lfg: _lifted_fam_groups) {
        bool ok = true;
        for (const lfg_pred& lfg_pred: lfg.preds) {
            for (const int idx_param: lfg_pred.idx_params) {
                if (!_htn->sortHasConstants(htn->nameId(lfg.params[idx_param].hddl_type))) {
                    Log::i("Sort %s has no constants!\n", lfg.params[idx_param].hddl_type.c_str());
                    ok = false;
                    break;
                }
            }
            if (!ok) break;
        }
        if (ok) {
            new_lifted_fam_groups.push_back(lfg);
        }
    }
    _lifted_fam_groups = new_lifted_fam_groups;
    Log::i("Number of lifted fam groups after removing redondant ones: %d\n", _lifted_fam_groups.size());

    // // Print all the lifted fam groups
    Log::i("After removing:\n");
    printAllLiftedFamGroups();
    Log::i("-------\n");

   
    // Ground all the lifted fam groups and fill the table mutexPredicates which indicate for each predicate the list of predicates which are mutex with it
    for (lfg& lfg: _lifted_fam_groups) {
        groundLFG(lfg);
        int dbg = 0;
    }
    
    Log::i("Done !");
    // assert(false);
}


const FlatHashSet<int>& SASPlus::getGroupsMutexesOfPred(const USignature& pred) const {
    return pred_to_group_mutexes.at(pred);
}

const FlatHashSet<USignature, USignatureHasher>& SASPlus::getPredsInGroup(int group_id) const {
    return group_mutexes[group_id];
}


void SASPlus::parseNextLiftedFamGroup(const std::string& line, lfg& lfg) {
    // Skip '{'
    int currentPos = 1;

    std::unordered_map<std::string, int> var_name_to_idx;

    while (line[currentPos] != '}') {
        parseNextPredicateInLiftedFamGroup(lfg, line, currentPos, var_name_to_idx);
    }
}

void SASPlus::parseNextPredicateInLiftedFamGroup(lfg& lfg, const std::string& line, int& currentPos, std::unordered_map<std::string, int>& var_name_to_idx) {

    // Skip comma and space is there is any
    if (line[currentPos] == ',') currentPos++;
    if (line[currentPos] == ' ') currentPos++;

    // Assert that the first character is either a + or a -
    assert(line[currentPos] == '+' || line[currentPos] == '-');
    bool isPositive = line[currentPos] == '+';
    currentPos++;

    // Get the predicate name
    std::string predName;
    while (line[currentPos] != ' ' && line[currentPos] != '}' && line[currentPos] != ',') {
        predName += line[currentPos];
        currentPos++;
    }

    // If the predicate is negative, skip this predicate for now
    // TODO handle negative predicate for mutexes
    if (!isPositive) {
        // Skip until the end of the predicate
        while (line[currentPos] != '}' && line[currentPos] != ',') {
            currentPos++;
        }
        return;
    }


    // Get the predicate in correct case
    predName = _htn->getPredicateInCorrectCase(predName);

    std::vector<std::string> vars_name;
    std::vector<std::string> hddl_type_args;
    std::vector<bool> is_constant;
    std::vector<bool> is_fixed_var;
    

    // If this predicate has parameters...
    if (line[currentPos] != '}' && line[currentPos] != ',') {

        // parse the parameters
        while (line[currentPos] != '}' && line[currentPos] != ',') {
            // Each paramter is in the form fixed_vars[i]:type_args[i] or name_object (if there is only one object of that type)
            // fixed vars[i] can take the value V<idx> or C<idx>
            // We do not care about the idx of C since it is a counter variable


            // Skip the space
            currentPos++;


            std::string fixed_var;
            std::string type_arg;

            while (line[currentPos] != ':' && line[currentPos] != ' ' && line[currentPos] != '}' && line[currentPos] != ',') {
                fixed_var += line[currentPos];
                currentPos++;
            }

            if (line[currentPos] != ':') {
                // This is a constant. Check if it exists
                bool exist = false;
                int id_const = -1;
                std::string sortConst;
                for (const auto& [sort, constants] : _htn->getConstantsBySort()) {

                    // Print the sort
                    // Log::i("Check constants of Sort %s:\n", _htn->toString(sort).c_str());
                    // Print all the constants
                    // for (const auto& constant: constants) {
                    //     Log::i("   Constant %s\n", _htn->toString(constant).c_str());
                    // }
                    // Check if constants contains fixed_var
                    if (constants.count(_htn->nameId(fixed_var))) {
                        exist = true;
                        id_const = _htn->nameId(fixed_var);
                        sortConst = _htn->toString(sort);
                        break;
                    }
                }

                assert(exist || Log::e("Constant %s does not exist!\n", fixed_var.c_str()));
                vars_name.push_back(fixed_var);
                hddl_type_args.push_back(sortConst);
                is_constant.push_back(true);

                // Go to the next param
                continue;
            }
                
            // Skip the ':'
            currentPos++;

            while (line[currentPos] != ' ' && line[currentPos] != '}' && line[currentPos] != ',') {
                type_arg += line[currentPos];
                currentPos++;
            }

            vars_name.push_back(fixed_var);
            // Check if we have this type arg in our instance 
            if (!_htn->sortHasConstants(_htn->nameId(type_arg))) {
                Log::i("Type arg %s does not exist!\n", type_arg.c_str());
                // Check if we have it in upper case
                std::string type_arg_upper = type_arg;
                for (char& c: type_arg_upper) {
                    c = toupper(c);
                }
                if (!_htn->sortHasConstants(_htn->nameId(type_arg_upper))) {
                    Log::e("We do not have the type arg even in upper case %s!\n", type_arg_upper.c_str());
                    // Skip until the end of the predicate
                    while (line[currentPos] != '}' && line[currentPos] != ',') {
                        currentPos++;
                    }
                    return;
                } else {
                    Log::i("We have the type arg in upper case %s, update it!\n", type_arg_upper.c_str());
                    type_arg = type_arg_upper;
                    
                }
            }
            hddl_type_args.push_back(type_arg);
            is_constant.push_back(false);
        }
    }
    

    lfg.preds.push_back({predName, std::vector<int>()});
    // Check if we already have the type args
    for (int i = 0; i < hddl_type_args.size(); i++) {
        bool isCountedVar = vars_name[i][0] == 'C';
        int idx_param;

        // Check if we already have the type arg
        if (!var_name_to_idx.count(vars_name[i])) {
            // We do not have the type arg
            params_lfg param;
            param.hddl_type = hddl_type_args[i];
            param.is_counted_var = isCountedVar;
            param.is_constant = is_constant[i];
            if (param.is_constant) {
                // Assign the value directly in the val of param
                param.val = _htn->nameId(vars_name[i]);
            }
            lfg.params.push_back(param);
            var_name_to_idx[vars_name[i]] = lfg.params.size() - 1;
            idx_param = lfg.params.size() - 1;
        } else {
            // We already have the type arg
            idx_param = var_name_to_idx[vars_name[i]];
        }
        lfg.preds.back().idx_params.push_back(idx_param);
    }
    int dbg = 0;
}

void SASPlus::printAllLiftedFamGroups() {
    for (int i = 0; i < _lifted_fam_groups.size(); i++) {
        Log::i("Lifted fam group %d:\n", i);
        for (int j = 0; j < _lifted_fam_groups[i].preds.size(); j++) {
            printLiftedFamGroup(_lifted_fam_groups[i]);
        }
    }
}




void SASPlus::generateCountedVarCombinationsForPred(lfg& my_lfg, lfg_pred& pred, size_t param_index, FlatHashSet<USignature, USignatureHasher>& bucket) {
    
    if (param_index == pred.idx_params.size()) {
        // Convert each predicate of the lifted fam group to a USignature
        std::vector<int> args_pred;
        for (int idx_param: pred.idx_params) {
            args_pred.push_back(my_lfg.params[idx_param].val);
        }
        USignature pred_usig(_htn->nameId(pred.name), args_pred);
        bucket.insert(pred_usig);
        
        return;
    }

    if (my_lfg.params[pred.idx_params[param_index]].is_counted_var) {
        for (int val : _htn->getConstantsOfSort(_htn->nameId(my_lfg.params[pred.idx_params[param_index]].hddl_type))) {
            my_lfg.params[pred.idx_params[param_index]].val = val;
            generateCountedVarCombinationsForPred(my_lfg, pred, param_index + 1, bucket);
        }
    } else {
        generateCountedVarCombinationsForPred(my_lfg, pred, param_index + 1, bucket);
    }
}

void SASPlus::generateFixedVarCombinations(lfg& my_lfg, size_t param_index) {
    if (param_index == my_lfg.params.size()) {
        // Get a specific id for this grounded lfg
        // Create a bucket to store the grounded predicates of this lifted fam group with this specific values for the fixed vars
        // We can compute the size of the bucket by multiplying the number of values for each counted var
        size_t size_bucket = 0;
        for (const lfg_pred& pred: my_lfg.preds) {
            size_t size_pred = 1;
            for (const int idx_param: pred.idx_params) {
                if (my_lfg.params[idx_param].is_counted_var) {
                    size_pred *=  _htn->getConstantsOfSort(_htn->nameId(my_lfg.params[idx_param].hddl_type)).size();
                }
            }
            size_bucket += size_pred;
        }
        if (size_bucket == 1 || size_bucket == 0) return;
        // std::vector<USignature> bucket;
        FlatHashSet<USignature, USignatureHasher> bucket;
        bucket.reserve(size_bucket);
        for (lfg_pred& pred: my_lfg.preds) {
            generateCountedVarCombinationsForPred(my_lfg, pred, 0, bucket);
        }
        // generateCountedVarCombinations(my_lfg, 0, bucket);
        // Print the bucket to test if it is correct
        int idx_bucket = group_mutexes.size();
        Log::d("Bucket number %d:\n", idx_bucket);
        Log::d("Size bucket: : %d (and true size: %d)\n", size_bucket, bucket.size());
        Log::d("In the bucket:\n");
        for (const USignature& pred: bucket) {
            Log::d("-> %s\n", TOSTR(pred));

            if (!pred_to_group_mutexes.count(pred)) {
                pred_to_group_mutexes[pred] = FlatHashSet<int>();
            }
            pred_to_group_mutexes[pred].insert(idx_bucket);
        }
        group_mutexes.push_back(bucket);
        Log::d("--------------\n");
        return;
    }

    if (!my_lfg.params[param_index].is_counted_var && !my_lfg.params[param_index].is_constant) {
        for (int val :  _htn->getConstantsOfSort(_htn->nameId(my_lfg.params[param_index].hddl_type))) {
            my_lfg.params[param_index].val = val;
            generateFixedVarCombinations(my_lfg, param_index + 1);
        }
    } else {
        generateFixedVarCombinations(my_lfg, param_index + 1);
    }
}


void SASPlus::groundLFG(lfg& my_lfg) {
    // First, reset the values of the params except for the constants
    for (params_lfg& param: my_lfg.params) {
        if (!param.is_constant)
            param.val = -1;
    }

    Log::d("Genrerate bucket for lifted fam group:\n");
    printLiftedFamGroup(my_lfg);

    generateFixedVarCombinations(my_lfg, 0);
}




const void SASPlus::printLiftedFamGroup(const lfg& lfg) const {
    std::string full_lfg = "{";
    for (int i = 0; i < lfg.preds.size(); i++) {
        full_lfg += lfg.preds[i].name + " ";
        for (const int idx_param: lfg.preds[i].idx_params) {
            std::string name_param = "";
            if (lfg.params[idx_param].is_constant) {
                name_param = _htn->toString(lfg.params[idx_param].val);
            } else {
                name_param = lfg.params[idx_param].is_counted_var ? "C" : "V";
                name_param += std::to_string(idx_param);
                name_param += ':' + lfg.params[idx_param].hddl_type;
            }
            full_lfg += name_param + " ";
        }
        if (i != lfg.preds.size() - 1) full_lfg += ", ";
    }
    full_lfg += "}";
    // std::cout << full_lfg.c_str() << std::endl;
    Log::i("%s\n", full_lfg.c_str());
}

void SASPlus::cleanMutexGroupsWithPandaPiGrounderPreprocessingFacts(const USigSet& preprocessed_facts_pos_state_features) {

    Log::i("Clean mutex groups with pandaPi grounder preprocessing facts...\n");
    // For each group, check if it contains a predicate which is not in the preprocessed facts
    for (int i = 0; i < group_mutexes.size(); i++) {
        bool contains_pred_not_in_preprocessed_facts = false;
        USigSet predToRemoveInGroup;
        for (const USignature& pred: group_mutexes[i]) {
            if (!preprocessed_facts_pos_state_features.count(pred)) {
                predToRemoveInGroup.insert(pred);
            }
        }

        for (const USignature& pred: predToRemoveInGroup) {
            pred_to_group_mutexes[pred].erase(i);
        }

        // Clean the group by removing the pred not in the preprocessed facts
        for (const USignature& pred: predToRemoveInGroup) {
            group_mutexes[i].erase(pred);
        }
    }
}