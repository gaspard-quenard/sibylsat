#include <iostream>
#include <fstream>
#include <sstream>
#include <unordered_set>

#include "data/mutex_groups.h"
#include "util/log.h"
#include "util/names.h"
#include "data/htn_instance.h"
#include "data/substitution.h"

MutexGroups::MutexGroups(const std::string& mutexFile, HtnInstance& htn) : _htn(htn) {
    std::ifstream file(mutexFile);
    assert(file.good() || Log::e("File %s does not exist!\n", mutexFile.c_str()));

    std::string line;
    while (std::getline(file, line)) {
        LiftedMutexGroup group;
        parseNextLiftedFamGroup(line, group);
        _lifted_fam_groups.push_back(std::move(group));
    }

    std::vector<LiftedMutexGroup> usableGroups;
    for (LiftedMutexGroup& group : _lifted_fam_groups) {
        bool hasGrounding = true;
        for (const LiftedMutexPredicate& predicate : group.preds) {
            for (int parameterIndex : predicate.idx_params) {
                if (!_htn.sortHasConstants(_htn.nameId(group.params[parameterIndex].hddl_type))) {
                    hasGrounding = false;
                    break;
                }
            }
            if (!hasGrounding) break;
        }
        if (hasGrounding) usableGroups.push_back(std::move(group));
    }
    _lifted_fam_groups = std::move(usableGroups);

    printAllLiftedFamGroups();
    for (LiftedMutexGroup& group : _lifted_fam_groups) groundLiftedGroup(group);
}

const FlatHashSet<int>& MutexGroups::getGroupIdsForFact(const USignature& fact) const {
    return _group_ids_by_fact.at(fact);
}

const USigSet& MutexGroups::getFactsInGroup(int groupId) const {
    return _groups[groupId];
}

void MutexGroups::parseNextLiftedFamGroup(const std::string& line, LiftedMutexGroup& group) {
    // Skip '{'
    int currentPos = 1;

    std::unordered_map<std::string, int> variableIndices;

    while (line[currentPos] != '}') {
        parseNextPredicateInLiftedFamGroup(group, line, currentPos, variableIndices);
    }
}

void MutexGroups::parseNextPredicateInLiftedFamGroup(LiftedMutexGroup& group, const std::string& line, int& currentPos, std::unordered_map<std::string, int>& variableIndices) {

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
    predName = _htn.getPredicateInCorrectCase(predName);

    std::vector<std::string> variableNames;
    std::vector<std::string> argumentTypes;
    std::vector<bool> constants;
    

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
                std::string sortConst;
                for (const auto& [sort, constantsOfSort] : _htn.getConstantsBySort()) {

                    // Print the sort
                    // Log::i("Check constants of Sort %s:\n", _htn.toString(sort).c_str());
                    // Print all the constants
                    // for (const auto& constant: constants) {
                    //     Log::i("   Constant %s\n", _htn.toString(constant).c_str());
                    // }
                    // Check if constants contains fixed_var
                    if (constantsOfSort.count(_htn.nameId(fixed_var))) {
                        exist = true;
                        sortConst = _htn.toString(sort);
                        break;
                    }
                }

                assert(exist || Log::e("Constant %s does not exist!\n", fixed_var.c_str()));
                variableNames.push_back(fixed_var);
                argumentTypes.push_back(sortConst);
                constants.push_back(true);

                // Go to the next param
                continue;
            }
                
            // Skip the ':'
            currentPos++;

            while (line[currentPos] != ' ' && line[currentPos] != '}' && line[currentPos] != ',') {
                type_arg += line[currentPos];
                currentPos++;
            }

            variableNames.push_back(fixed_var);
            // Check if we have this type arg in our instance 
            if (!_htn.sortHasConstants(_htn.nameId(type_arg))) {
                Log::i("Type arg %s does not exist!\n", type_arg.c_str());
                // Check if we have it in upper case
                std::string type_arg_upper = type_arg;
                for (char& c: type_arg_upper) {
                    c = toupper(c);
                }
                if (!_htn.sortHasConstants(_htn.nameId(type_arg_upper))) {
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
            argumentTypes.push_back(type_arg);
            constants.push_back(false);
        }
    }
    

    group.preds.push_back({predName, std::vector<int>()});
    // Check if we already have the type args
    for (size_t i = 0; i < argumentTypes.size(); i++) {
        bool isCountedVar = variableNames[i][0] == 'C';
        int idx_param;

        // Check if we already have the type arg
        if (!variableIndices.count(variableNames[i])) {
            // We do not have the type arg
            LiftedMutexParameter param;
            param.hddl_type = argumentTypes[i];
            param.is_counted_var = isCountedVar;
            param.is_constant = constants[i];
            if (param.is_constant) {
                // Assign the value directly in the val of param
                param.val = _htn.nameId(variableNames[i]);
            }
            group.params.push_back(param);
            variableIndices[variableNames[i]] = group.params.size() - 1;
            idx_param = group.params.size() - 1;
        } else {
            // We already have the type arg
            idx_param = variableIndices[variableNames[i]];
        }
        group.preds.back().idx_params.push_back(idx_param);
    }
}

void MutexGroups::printAllLiftedFamGroups() {
    for (size_t i = 0; i < _lifted_fam_groups.size(); i++) {
        Log::d("Lifted FAM group %zu:\n", i);
        printLiftedFamGroup(_lifted_fam_groups[i]);
    }
}




void MutexGroups::generateCountedVariableCombinations(LiftedMutexGroup& group, LiftedMutexPredicate& predicate, size_t parameterIndex, USigSet& facts) {
    
    if (parameterIndex == predicate.idx_params.size()) {
        std::vector<int> arguments;
        for (int index : predicate.idx_params) arguments.push_back(group.params[index].val);
        facts.emplace(_htn.nameId(predicate.name), std::move(arguments));
        return;
    }

    LiftedMutexParameter& parameter = group.params[predicate.idx_params[parameterIndex]];
    if (parameter.is_counted_var) {
        for (int value : _htn.getConstantsOfSort(_htn.nameId(parameter.hddl_type))) {
            parameter.val = value;
            generateCountedVariableCombinations(group, predicate, parameterIndex + 1, facts);
        }
    } else {
        generateCountedVariableCombinations(group, predicate, parameterIndex + 1, facts);
    }
}

void MutexGroups::generateFixedVariableCombinations(LiftedMutexGroup& group, size_t parameterIndex) {
    if (parameterIndex == group.params.size()) {
        size_t expectedFactCount = 0;
        for (const LiftedMutexPredicate& predicate : group.preds) {
            size_t predicateGroundingCount = 1;
            for (int index : predicate.idx_params) {
                if (group.params[index].is_counted_var) {
                    predicateGroundingCount *= _htn.getConstantsOfSort(_htn.nameId(group.params[index].hddl_type)).size();
                }
            }
            expectedFactCount += predicateGroundingCount;
        }
        if (expectedFactCount <= 1) return;

        USigSet facts;
        facts.reserve(expectedFactCount);
        for (LiftedMutexPredicate& predicate : group.preds) generateCountedVariableCombinations(group, predicate, 0, facts);

        const int groupId = _groups.size();
        for (const USignature& fact : facts) {
            _group_ids_by_fact[fact].insert(groupId);
        }
        _groups.push_back(std::move(facts));
        return;
    }

    LiftedMutexParameter& parameter = group.params[parameterIndex];
    if (!parameter.is_counted_var && !parameter.is_constant) {
        for (int value : _htn.getConstantsOfSort(_htn.nameId(parameter.hddl_type))) {
            parameter.val = value;
            generateFixedVariableCombinations(group, parameterIndex + 1);
        }
    } else {
        generateFixedVariableCombinations(group, parameterIndex + 1);
    }
}

void MutexGroups::groundLiftedGroup(LiftedMutexGroup& group) {
    for (LiftedMutexParameter& parameter : group.params) {
        if (!parameter.is_constant) parameter.val = -1;
    }
    generateFixedVariableCombinations(group, 0);
}

void MutexGroups::printLiftedFamGroup(const LiftedMutexGroup& group) const {
    std::string full_lfg = "{";
    for (size_t i = 0; i < group.preds.size(); i++) {
        full_lfg += group.preds[i].name + " ";
        for (int parameterIndex : group.preds[i].idx_params) {
            std::string name_param = "";
            if (group.params[parameterIndex].is_constant) {
                name_param = _htn.toString(group.params[parameterIndex].val);
            } else {
                name_param = group.params[parameterIndex].is_counted_var ? "C" : "V";
                name_param += std::to_string(parameterIndex);
                name_param += ':' + group.params[parameterIndex].hddl_type;
            }
            full_lfg += name_param + " ";
        }
        if (i != group.preds.size() - 1) full_lfg += ", ";
    }
    full_lfg += "}";
    Log::d("%s\n", full_lfg.c_str());
}

void MutexGroups::retainReachableFacts(const USigSet& reachableFacts) {
    for (size_t groupId = 0; groupId < _groups.size(); groupId++) {
        USigSet factsToRemove;
        for (const USignature& fact : _groups[groupId]) {
            if (!reachableFacts.count(fact)) factsToRemove.insert(fact);
        }
        for (const USignature& fact : factsToRemove) {
            _groups[groupId].erase(fact);
            FlatHashSet<int>& groupIds = _group_ids_by_fact.at(fact);
            groupIds.erase(groupId);
            if (groupIds.empty()) _group_ids_by_fact.erase(fact);
        }
    }
}
