#include "preprocessing/htn_instance_builder.h"

#include <algorithm>
#include <cstdlib>
#include <unordered_map>

#include "data/htn_instance.h"
#include "data/htn_statistics.h"
#include "libpanda.hpp"
#include "util/log.h"
#include "util/names.h"
#include "util/params.h"
#include "util/regex.h"

std::unique_ptr<HtnInstance> HtnInstanceBuilder::build(ParsedProblem& problem, Parameters& params) {
    USignatureHasher::seed = params.getIntParam("s");
    std::unique_ptr<HtnInstance> result(new HtnInstance());
    HtnInstance& htn = *result;
    Names::init(htn._name_back_table);
    createBlankAction(htn);

    for (const predicate_definition& predicate : problem.predicate_definitions) extractPredicateSorts(htn, predicate);
    for (const task& action : problem.primitive_tasks) extractTaskSorts(htn, action);
    for (const task& abstractTask : problem.abstract_tasks) extractTaskSorts(htn, abstractTask);
    for (const method& reduction : problem.methods) extractMethodSorts(htn, reduction);
    extractConstants(htn, problem);
    htn._init_state = extractInitialState(htn, problem);
    htn._goals = extractGoals(htn, problem);
    createGoalAction(htn);

    for (const auto& [sortName, constants] : problem.sorts) {
        Log::d(" %s : ", sortName.c_str());
        for (const std::string& constant : constants) Log::d("%s ", constant.c_str());
        Log::d("\n");
    }

    for (const task& action : problem.primitive_tasks) createAction(htn, action);
    for (method& reduction : problem.methods) createReduction(htn, reduction, problem);
    identifyStaticPredicates(htn, problem);

    if (params.isNonzero("stats")) {
        HtnStatistics::print(htn);
        exit(0);
    }
    if (params.isNonzero("psr")) primitivizeSimpleReductions(htn);
    return result;
}

std::vector<int> HtnInstanceBuilder::convertArguments(HtnInstance& htn, int operationId, const std::vector<std::pair<std::string, std::string>>& arguments) {
    std::vector<int> result;
    result.reserve(arguments.size());
    for (const auto& [name, sort] : arguments) {
        const int id = name.front() == '?' ? htn.nameId(name + "_" + std::to_string(operationId)) : htn.nameId(name);
        if (name.front() == '?') htn._sort_by_variable_id[id] = htn.nameId(sort);
        result.push_back(id);
    }
    return result;
}

std::vector<int> HtnInstanceBuilder::convertArguments(HtnInstance& htn, int operationId, const std::vector<std::string>& arguments) {
    std::vector<int> result;
    result.reserve(arguments.size());
    for (const std::string& argument : arguments) {
        result.push_back(argument.front() == '?' ? htn.nameId(argument + "_" + std::to_string(operationId)) : htn.nameId(argument));
    }
    return result;
}

Signature HtnInstanceBuilder::convertCondition(HtnInstance& htn, int operationId, const literal& condition) {
    Signature result(htn.nameId(condition.predicate), convertArguments(htn, operationId, condition.arguments));
    if (!condition.positive) result.negate();
    return result;
}

USigSet HtnInstanceBuilder::extractInitialState(HtnInstance& htn, const ParsedProblem& problem) {
    USigSet result;
    for (const ground_literal& fact : problem.init) {
        if (fact.positive) result.emplace(htn.nameId(fact.predicate), convertArguments(htn, htn.nameId(fact.predicate), fact.args));
    }
    for (int equalityPredicateId : htn._equality_predicates) {
        const std::vector<int>& sorts = htn.getSorts(equalityPredicateId);
        assert(sorts[0] == sorts[1]);
        for (int constant : htn._constants_by_sort.at(sorts[0])) {
            result.emplace(equalityPredicateId, std::vector<int>{constant, constant});
        }
    }
    return result;
}

SigSet HtnInstanceBuilder::extractGoals(HtnInstance& htn, const ParsedProblem& problem) {
    SigSet result;
    for (const ground_literal& goal : problem.goal) {
        Signature signature(htn.nameId(goal.predicate), convertArguments(htn, htn.nameId(goal.predicate), goal.args));
        if (!goal.positive) signature.negate();
        result.insert(std::move(signature));
    }
    return result;
}

void HtnInstanceBuilder::createBlankAction(HtnInstance& htn) {
    const int blankId = htn.nameId("__BLANK___");
    htn._blank_action = Action(blankId, std::vector<int>());
    htn._operators[blankId] = htn._blank_action;
    htn._op_table.addAction(htn._blank_action);
    htn._blank_action_sig = htn._blank_action.getSignature();
    htn._signature_sorts_table[blankId];
}

void HtnInstanceBuilder::createGoalAction(HtnInstance& htn) {
    const int goalId = htn.nameId("<goal_action>");
    htn._goal_action = Action(goalId, std::vector<int>());
    for (const Signature& goal : htn._goals) htn._goal_action.addPrecondition(goal);
    htn._operators[goalId] = htn._goal_action;
    htn._op_table.addAction(htn._goal_action);
    htn._signature_sorts_table[goalId];
}

void HtnInstanceBuilder::extractPredicateSorts(HtnInstance& htn, const predicate_definition& predicate) {
    const int predicateId = htn.nameId(predicate.name);
    htn._predicate_ids.insert(predicateId);
    std::string lowercaseName = predicate.name;
    std::transform(lowercaseName.begin(), lowercaseName.end(), lowercaseName.begin(), ::tolower);
    htn._predicate_names_by_lowercase[lowercaseName] = predicate.name;

    std::vector<int> sorts;
    for (const std::string& sort : predicate.argument_sorts) sorts.push_back(htn.nameId(sort));
    assert(!htn._signature_sorts_table.count(predicateId));
    htn._signature_sorts_table[predicateId] = std::move(sorts);
}

void HtnInstanceBuilder::extractTaskSorts(HtnInstance& htn, const task& task) {
    std::vector<int> sorts;
    for (const auto& [parameter, sort] : task.vars) {
        (void) parameter;
        sorts.push_back(htn.nameId(sort));
    }
    const int taskId = htn.nameId(task.name);
    assert(!htn._signature_sorts_table.count(taskId));
    htn._signature_sorts_table[taskId] = std::move(sorts);
    htn._original_n_taskvars[taskId] = task.number_of_original_vars;
}

void HtnInstanceBuilder::extractMethodSorts(HtnInstance& htn, const method& method) {
    std::vector<int> sorts;
    for (const auto& [parameter, sort] : method.vars) {
        (void) parameter;
        sorts.push_back(htn.nameId(sort));
    }
    const int methodId = htn.nameId(method.name);
    assert(!htn._signature_sorts_table.count(methodId));
    htn._signature_sorts_table[methodId] = std::move(sorts);
}

void HtnInstanceBuilder::extractConstants(HtnInstance& htn, const ParsedProblem& problem) {
    for (const auto& [sortName, constantNames] : problem.sorts) {
        const int sortId = htn.nameId(sortName);
        htn._declared_sort_ids.insert(sortId);
        FlatHashSet<int>& constants = htn._constants_by_sort[sortId];
        for (const std::string& constant : constantNames) constants.insert(htn.nameId(constant));
    }
}

void HtnInstanceBuilder::identifyStaticPredicates(HtnInstance& htn, const ParsedProblem& problem) {
    FlatHashSet<int> affectedPredicates;
    for (const auto& [actionId, action] : htn._operators) {
        (void) actionId;
        for (const Signature& effect : action.getEffects()) affectedPredicates.insert(effect._usig._name_id);
    }
    for (const predicate_definition& predicate : problem.predicate_definitions) {
        const int predicateId = htn.nameId(predicate.name);
        if (!affectedPredicates.count(predicateId)) htn._static_predicates.insert(predicateId);
    }
}

Action& HtnInstanceBuilder::createAction(HtnInstance& htn, const task& task) {
    const int actionId = htn.nameId(task.name);
    assert(!htn._operators.count(actionId));
    htn._operators[actionId] = Action(actionId, convertArguments(htn, actionId, task.vars));
    Action& action = htn._operators.at(actionId);

    for (Signature& constraint : extractEqualityConstraints(htn, actionId, task.constraints, task.vars)) action.addPrecondition(std::move(constraint));
    for (Signature& constraint : extractEqualityConstraints(htn, actionId, task.prec, task.vars)) action.addPrecondition(std::move(constraint));
    for (const literal& precondition : task.prec) action.addPrecondition(convertCondition(htn, actionId, precondition));
    for (const literal& effect : task.eff) action.addEffect(convertCondition(htn, actionId, effect));
    action.removeInconsistentEffects();
    return action;
}

Reduction& HtnInstanceBuilder::createReduction(HtnInstance& htn, method& method, const ParsedProblem& problem) {
    const int reductionId = htn.nameId(method.name);
    const int taskId = htn.nameId(method.at);
    htn._task_id_to_reduction_ids[taskId].push_back(reductionId);
    assert(!htn._methods.count(reductionId));
    htn._methods[reductionId] = Reduction(reductionId, convertArguments(htn, reductionId, method.vars),
            USignature(taskId, convertArguments(htn, reductionId, method.atargs)));
    Reduction& reduction = htn._methods.at(reductionId);

    std::vector<literal> conditions;
    for (const literal& constraint : method.constraints) {
        assert(constraint.predicate == "__equal" || Log::e("Unknown constraint predicate \"%s\"!\n", constraint.predicate.c_str()));
        conditions.push_back(constraint);
    }
    for (const plan_step& subtask : method.ps) {
        std::string normalizedName = subtask.task;
        Regex::extractCoreNameOfSplittingMethod(normalizedName);
        if (normalizedName.rfind(method_precondition_action_name) != std::string::npos) {
            importCompiledPreconditions(htn, method, reduction, findCompiledPreconditionTask(problem, normalizedName), conditions);
        } else {
            reduction.addSubtask(USignature(htn.nameId(subtask.task), convertArguments(htn, reductionId, subtask.args)));
        }
    }

    for (Signature& precondition : extractEqualityConstraints(htn, reductionId, conditions, method.vars)) reduction.addPrecondition(std::move(precondition));
    for (const literal& condition : conditions) {
        if (condition.predicate != dummy_equal_literal) reduction.addPrecondition(convertCondition(htn, reductionId, condition));
    }
    if (method.name.rfind("__top_method", 0) == 0) htn._init_reduction_id = reductionId;
    return reduction;
}

const task& HtnInstanceBuilder::findCompiledPreconditionTask(const ParsedProblem& problem, const std::string& normalizedSubtaskName) {
    const task* bestMatch = nullptr;
    for (const task& candidate : problem.primitive_tasks) {
        std::string normalizedCandidateName = candidate.name;
        Regex::extractCoreNameOfSplittingMethod(normalizedCandidateName);
        if (normalizedSubtaskName.rfind(normalizedCandidateName) == std::string::npos) continue;
        if (bestMatch == nullptr || candidate.name.size() >= bestMatch->name.size()) bestMatch = &candidate;
    }
    assert(bestMatch != nullptr);
    return *bestMatch;
}

void HtnInstanceBuilder::importCompiledPreconditions(HtnInstance& htn, method& source, Reduction& destination, const task& preconditionTask, std::vector<literal>& conditions) {
    conditions.insert(conditions.end(), preconditionTask.prec.begin(), preconditionTask.prec.end());
    conditions.insert(conditions.end(), preconditionTask.constraints.begin(), preconditionTask.constraints.end());
    for (const auto& [name, sort] : preconditionTask.vars) {
        if (name.empty() || name.front() != '?') continue;
        const int parameterId = htn.nameId(name + "_" + std::to_string(destination.getNameId()));
        if (std::find(destination.getArguments().begin(), destination.getArguments().end(), parameterId) != destination.getArguments().end()) continue;
        destination.addArgument(parameterId);
        htn._sort_by_variable_id[parameterId] = htn.nameId(sort);
        htn._signature_sorts_table[destination.getNameId()].push_back(htn.nameId(sort));
        source.vars.emplace_back(name, sort);
    }
}

SigSet HtnInstanceBuilder::extractEqualityConstraints(HtnInstance& htn, int operationId, const std::vector<literal>& conditions, const std::vector<std::pair<std::string, std::string>>& parameters) {
    SigSet result;
    std::unordered_map<std::string, int> sortByParameter;
    for (const auto& [parameter, sort] : parameters) sortByParameter[parameter] = htn.nameId(sort);

    for (const literal& condition : conditions) {
        if (condition.predicate != dummy_equal_literal) continue;
        assert(condition.arguments.size() == 2);
        const int firstSort = sortByParameter.at(condition.arguments[0]);
        const int secondSort = sortByParameter.at(condition.arguments[1]);
        const int equalitySort = htn._constants_by_sort.at(firstSort).size() > htn._constants_by_sort.at(secondSort).size() ? firstSort : secondSort;
        const int predicateId = htn.nameId("__equal_" + htn._name_back_table.at(equalitySort) + "_" + htn._name_back_table.at(equalitySort));
        if (!htn._signature_sorts_table.count(predicateId)) {
            htn._signature_sorts_table[predicateId] = std::vector<int>(2, equalitySort);
            htn._equality_predicates.insert(predicateId);
            htn._predicate_ids.insert(predicateId);
        }
        result.emplace(predicateId, std::vector<int>{
                htn.nameId(condition.arguments[0] + "_" + std::to_string(operationId)),
                htn.nameId(condition.arguments[1] + "_" + std::to_string(operationId))}, !condition.positive);
    }
    return result;
}

void HtnInstanceBuilder::primitivizeSimpleReductions(HtnInstance& htn) {
    for (const auto& [reductionId, reduction] : htn._methods) {
        if (reduction.getSubtasks().size() != 1) continue;
        const USignature& childSignature = reduction.getSubtasks().front();
        const auto childTemplate = htn._operators.find(childSignature._name_id);
        if (childTemplate == htn._operators.end()) continue;

        const Substitution substitution(childTemplate->second.getArguments(), childSignature._args);
        const Action child = childTemplate->second.substitute(substitution);
        const int surrogateId = htn.nameId("__SURROGATE*" + std::string(TOSTR(reductionId)) + "*" + std::string(TOSTR(childSignature._name_id)) + "*");
        Action& surrogate = htn._operators.emplace(surrogateId, Action(surrogateId, reduction.getArguments())).first->second;
        for (const Signature& precondition : reduction.getPreconditions()) surrogate.addPrecondition(precondition);
        for (const Signature& precondition : reduction.getExtraPreconditions()) surrogate.addExtraPrecondition(precondition);
        for (const Signature& precondition : child.getPreconditions()) surrogate.addPrecondition(precondition);
        for (const Signature& precondition : child.getExtraPreconditions()) surrogate.addExtraPrecondition(precondition);
        for (const Signature& effect : child.getEffects()) surrogate.addEffect(effect);
        htn._reduction_to_primitivization[reductionId] = surrogateId;
        htn._signature_sorts_table[surrogateId] = htn._signature_sorts_table[reductionId];
        htn._primitivization_to_parent_and_child[surrogateId] = {reductionId, childSignature._name_id};
    }
}
