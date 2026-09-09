#include "data/htn_statistics.h"

#include <algorithm>
#include <limits>

#include "data/htn_instance.h"
#include "util/log.h"

size_t HtnStatistics::countFreeArguments(const HtnInstance& htn, const Reduction& reduction) {
    size_t count = 0;
    for (size_t argumentIndex = 0; argumentIndex < reduction.getArguments().size(); ++argumentIndex) {
        const int argument = reduction.getArguments()[argumentIndex];
        if (std::find(reduction.getTaskArguments().begin(), reduction.getTaskArguments().end(), argument)
                != reduction.getTaskArguments().end()) continue;
        const int sort = htn._signature_sorts_table.at(reduction.getNameId()).at(argumentIndex);
        if (htn._constants_by_sort.at(sort).size() > 1) ++count;
    }
    return count;
}

void HtnStatistics::print(const HtnInstance& htn) {
    size_t maxPredicateArity = 0;
    for (int predicateId : htn._predicate_ids) {
        maxPredicateArity = std::max(maxPredicateArity, htn._signature_sorts_table.at(predicateId).size());
    }

    size_t maxExpansionSize = 0;
    size_t maxReductionPreconditions = 0;
    size_t maxReductionArity = 0;
    size_t maxReductionFreeArgs = 0;
    FlatHashMap<int, size_t> reductionsPerTask;
    size_t numberOfReductions = 0;
    for (const auto& [reductionId, reduction] : htn._methods) {
        (void) reductionId;
        if (htn.toString(reduction.getNameId()).rfind("__top_method", 0) == 0) continue;
        ++numberOfReductions;
        maxExpansionSize = std::max(maxExpansionSize, reduction.getSubtasks().size());
        maxReductionPreconditions = std::max(maxReductionPreconditions, reduction.getPreconditions().size());
        maxReductionArity = std::max(maxReductionArity, reduction.getArguments().size());
        maxReductionFreeArgs = std::max(maxReductionFreeArgs, HtnStatistics::countFreeArguments(htn, reduction));
        ++reductionsPerTask[reduction.getTaskSignature()._name_id];
    }

    size_t maxLiftedBranchingFactor = 0;
    for (const auto& [taskId, numberOfMethods] : reductionsPerTask) {
        (void) taskId;
        maxLiftedBranchingFactor = std::max(maxLiftedBranchingFactor, numberOfMethods);
    }

    size_t numberOfActions = 0;
    size_t maxActionPreconditions = 0;
    size_t maxActionEffects = 0;
    size_t maxActionArity = 0;
    for (const auto& [actionId, action] : htn._operators) {
        const std::string actionName = htn.toString(actionId);
        if (actionName == "__BLANK___" || actionName == "<goal_action>") continue;
        ++numberOfActions;
        maxActionPreconditions = std::max(maxActionPreconditions, action.getPreconditions().size());
        maxActionEffects = std::max(maxActionEffects, action.getEffects().size());
        maxActionArity = std::max(maxActionArity, action.getArguments().size());
    }

    FlatHashSet<int> constants;
    for (const auto& [sort, constantsOfSort] : htn._constants_by_sort) {
        (void) sort;
        constants.insert(constantsOfSort.begin(), constantsOfSort.end());
    }

    Log::e("Domain stats:\n");
    Log::e("STATS numoperators %zu\n", numberOfActions);
    Log::e("STATS nummethods %zu\n", numberOfReductions);
    Log::e("STATS maxexpansionsize %zu\n", maxExpansionSize);
    Log::e("STATS maxliftedbranchingfactor %zu\n", maxLiftedBranchingFactor);
    Log::e("STATS maxreductionfreeargs %zu\n", maxReductionFreeArgs);
    Log::e("STATS maxactionpreconditions %zu\n", maxActionPreconditions);
    Log::e("STATS maxreductionpreconditions %zu\n", maxReductionPreconditions);
    Log::e("STATS maxactioneffects %zu\n", maxActionEffects);
    Log::e("STATS maxpredicatearity %zu\n", maxPredicateArity);
    Log::e("STATS maxactionarity %zu\n", maxActionArity);
    Log::e("STATS maxreductionarity %zu\n", maxReductionArity);
    Log::e("Problem stats:\n");
    Log::e("STATS numconstants %zu\n", constants.size());
    Log::e("STATS numinitfacts %zu\n", htn.getInitState().size());
    Log::e("STATS numinittasks %zu\n", htn.getInitReduction().getSubtasks().size());
}
