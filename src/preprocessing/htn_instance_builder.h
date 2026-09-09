#ifndef SIBYLSAT_HTN_INSTANCE_BUILDER_H
#define SIBYLSAT_HTN_INSTANCE_BUILDER_H

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "data/signature.h"

class HtnInstance;
class Parameters;
class Action;
class Reduction;
struct ParsedProblem;
struct predicate_definition;
struct task;
struct method;
struct literal;

/** Converts a normalized parser result into the integer-based runtime HTN model. */
class HtnInstanceBuilder {
public:
    /** Build SibylSat's internal model from a normalized lifted problem. */
    static std::unique_ptr<HtnInstance> build(ParsedProblem& problem, Parameters& params);

private:
    static std::vector<int> convertArguments(HtnInstance& htn, int operationId, const std::vector<std::pair<std::string, std::string>>& arguments);
    static std::vector<int> convertArguments(HtnInstance& htn, int operationId, const std::vector<std::string>& arguments);
    static Signature convertCondition(HtnInstance& htn, int operationId, const literal& condition);
    static USigSet extractInitialState(HtnInstance& htn, const ParsedProblem& problem);
    static SigSet extractGoals(HtnInstance& htn, const ParsedProblem& problem);
    static void createBlankAction(HtnInstance& htn);
    static void createGoalAction(HtnInstance& htn);
    static void extractPredicateSorts(HtnInstance& htn, const predicate_definition& predicate);
    static void extractTaskSorts(HtnInstance& htn, const task& task);
    static void extractMethodSorts(HtnInstance& htn, const method& method);
    static void extractConstants(HtnInstance& htn, const ParsedProblem& problem);
    static void identifyStaticPredicates(HtnInstance& htn, const ParsedProblem& problem);
    static Action& createAction(HtnInstance& htn, const task& task);
    static Reduction& createReduction(HtnInstance& htn, method& method, const ParsedProblem& problem);
    static const task& findCompiledPreconditionTask(const ParsedProblem& problem, const std::string& normalizedSubtaskName);
    static void importCompiledPreconditions(HtnInstance& htn, method& source, Reduction& destination, const task& preconditionTask, std::vector<literal>& conditions);
    static SigSet extractEqualityConstraints(HtnInstance& htn, int operationId, const std::vector<literal>& conditions, const std::vector<std::pair<std::string, std::string>>& parameters);
    static void primitivizeSimpleReductions(HtnInstance& htn);
};

#endif
