#include "preprocessing/lifted_problem_normalizer.h"

#include <cstdlib>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "parser/lifted_problem.h"
#include "util/log.h"

namespace {

constexpr const char* EQUALITY_PREDICATE = "__equal";

/**
 * Give every accomplished-task argument its own method parameter.
 *
 * For example, `(process ?part ?surface ?surface)` becomes
 * `(process ?part ?surface ?surface_2)` and gains the constraint
 * `(= ?surface ?surface_2)`. Distinct formal parameters make later
 * substitutions unambiguous while the equality preserves the semantics.
 */
void normalizeRepeatedTaskArguments(LiftedMethod& reduction) {
    std::unordered_map<std::string, std::string> parameterSorts;
    std::unordered_set<std::string> usedNames;
    for (const auto& [name, sort] : reduction.vars) {
        parameterSorts[name] = sort;
        usedNames.insert(name);
    }

    std::unordered_set<std::string> seenArguments;
    for (size_t argumentIndex = 0; argumentIndex < reduction.atargs.size(); ++argumentIndex) {
        const std::string originalName = reduction.atargs[argumentIndex];
        if (seenArguments.insert(originalName).second) continue;

        std::string renamed = originalName + "_" + std::to_string(argumentIndex);
        while (usedNames.count(renamed)) renamed += "_";
        usedNames.insert(renamed);

        reduction.atargs[argumentIndex] = renamed;
        reduction.vars.emplace_back(renamed, parameterSorts.at(originalName));

        LiftedLiteral equality;
        equality.positive = true;
        equality.predicate = EQUALITY_PREDICATE;
        equality.arguments = {originalName, renamed};
        reduction.constraints.push_back(std::move(equality));
    }
}

/**
 * Put a method's subtasks in a deterministic topological order.
 *
 * More than one currently available subtask means that the constraints permit
 * multiple linearizations, so the method is not totally ordered.
 */
bool orderSubtasks(LiftedMethod& reduction) {
    const size_t numberOfSubtasks = reduction.ps.size();
    std::unordered_map<std::string, size_t> indexById;
    std::vector<std::vector<size_t>> successors(numberOfSubtasks);
    std::vector<size_t> indegrees(numberOfSubtasks, 0);

    for (size_t index = 0; index < numberOfSubtasks; ++index) {
        if (!indexById.emplace(reduction.ps[index].id, index).second) {
            Log::e("Duplicate subtask ID %s in method %s.\n", reduction.ps[index].id.c_str(), reduction.name.c_str());
            exit(1);
        }
    }

    for (const auto& [beforeId, afterId] : reduction.ordering) {
        const auto before = indexById.find(beforeId);
        const auto after = indexById.find(afterId);
        if (before == indexById.end() || after == indexById.end()) {
            Log::e("Unknown subtask in ordering constraint %s < %s of method %s.\n",
                    beforeId.c_str(), afterId.c_str(), reduction.name.c_str());
            exit(1);
        }
        successors[before->second].push_back(after->second);
        ++indegrees[after->second];
    }

    // Original positions break ties deterministically when a partial order has
    // several valid next subtasks.
    std::set<size_t> ready;
    for (size_t index = 0; index < numberOfSubtasks; ++index) {
        if (indegrees[index] == 0) ready.insert(index);
    }

    bool isTotallyOrdered = true;
    std::vector<LiftedSubtask> orderedSubtasks;
    orderedSubtasks.reserve(numberOfSubtasks);
    while (!ready.empty()) {
        if (ready.size() > 1) isTotallyOrdered = false;
        const size_t index = *ready.begin();
        ready.erase(ready.begin());
        orderedSubtasks.push_back(reduction.ps[index]);
        for (size_t successor : successors[index]) {
            if (--indegrees[successor] == 0) ready.insert(successor);
        }
    }

    if (orderedSubtasks.size() != numberOfSubtasks) {
        Log::e("Cyclic subtask ordering in method %s.\n", reduction.name.c_str());
        exit(1);
    }

    reduction.ps = std::move(orderedSubtasks);
    return isTotallyOrdered;
}

}

LiftedProblemProperties LiftedProblemNormalizer::normalize(LiftedProblem& problem) {
    LiftedProblemProperties properties;
    for (LiftedMethod& reduction : problem.methods) {
        normalizeRepeatedTaskArguments(reduction);
        if (!orderSubtasks(reduction)) properties.isTotallyOrdered = false;
    }
    return properties;
}
