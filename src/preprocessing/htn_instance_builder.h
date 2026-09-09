#ifndef SIBYLSAT_HTN_INSTANCE_BUILDER_H
#define SIBYLSAT_HTN_INSTANCE_BUILDER_H

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "data/signature.h"
#include "parser/lifted_problem.h"

class HtnInstance;
class Parameters;
class Action;
class Reduction;
/** Converts a normalized LiftedProblem into the integer-based runtime HTN model. */
class HtnInstanceBuilder {
public:
    /** Build SibylSat's internal model from a normalized lifted problem. */
    static std::unique_ptr<HtnInstance> build(LiftedProblem& problem, Parameters& params);

private:
    static std::vector<int> convertArguments(HtnInstance& htn, int operationId, const std::vector<std::pair<std::string, std::string>>& arguments);
    static std::vector<int> convertArguments(HtnInstance& htn, int operationId, const std::vector<std::string>& arguments);
    static Signature convertCondition(HtnInstance& htn, int operationId, const LiftedLiteral& condition);
    static USigSet extractInitialState(HtnInstance& htn, const LiftedProblem& problem);
    static SigSet extractGoals(HtnInstance& htn, const LiftedProblem& problem);
    static void createBlankAction(HtnInstance& htn);
    static void createGoalAction(HtnInstance& htn);
    static void extractPredicateSorts(HtnInstance& htn, const LiftedPredicate& predicate);
    static void extractTaskSorts(HtnInstance& htn, const LiftedTask& task);
    static void extractMethodSorts(HtnInstance& htn, const LiftedMethod& method);
    static void extractConstants(HtnInstance& htn, const LiftedProblem& problem);
    static void identifyStaticPredicates(HtnInstance& htn, const LiftedProblem& problem);
    static Action& createAction(HtnInstance& htn, const LiftedTask& task);
    static Reduction& createReduction(HtnInstance& htn, LiftedMethod& method, const LiftedProblem& problem);
    static SigSet extractEqualityConstraints(HtnInstance& htn, int operationId, const std::vector<LiftedLiteral>& conditions, const std::vector<std::pair<std::string, std::string>>& parameters);
    static void primitivizeSimpleReductions(HtnInstance& htn);
};

#endif
