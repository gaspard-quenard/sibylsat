#include <cassert>
#include <initializer_list>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

#include "algo/domination_resolver.h"
#include "algo/q_constant_manager.h"
#include "data/htn_instance.h"
#include "parser/lifted_problem.h"
#include "preprocessing/htn_instance_builder.h"
#include "util/log.h"
#include "util/params.h"

namespace {

std::unique_ptr<HtnInstance> buildTestInstance(Parameters& params) {
    LiftedProblem problem;
    problem.sorts["object"] = {"a", "b"};

    LiftedTask action;
    action.name = "test-action";
    action.vars = {{"?x", "object"}, {"?y", "object"}};
    problem.primitive_tasks.push_back(std::move(action));
    return HtnInstanceBuilder::build(problem, params);
}

USignature instantiateAction(QConstantManager& qConstants, const Action& action, std::initializer_list<FlatHashSet<int>> domains) {
    std::optional<Action> instantiated = qConstants.instantiate(action, std::vector<FlatHashSet<int>>(domains), 1);
    assert(instantiated.has_value());
    return instantiated->getSignature();
}

}

int main() {
    Log::init(0, false);
    Parameters params;
    params.setDefaults();
    params.setParam("psr", "0");

    std::unique_ptr<HtnInstance> htn = buildTestInstance(params);
    QConstantManager qConstants(*htn, false);
    DominationResolver resolver(qConstants);

    const int actionId = htn->nameId("test-action");
    const int a = htn->nameId("a");
    const int b = htn->nameId("b");
    const Action& action = htn->getActionTemplate(actionId);

    const USignature broad = instantiateAction(qConstants, action, {{a, b}, {a, b}});
    const USignature narrow = instantiateAction(qConstants, action, {{a}, {a}});
    assert(resolver.getDominationStatus(broad, narrow).status == DominationResolver::DOMINATING);
    assert(resolver.getDominationStatus(narrow, broad).status == DominationResolver::DOMINATED);

    // Neither signature dominates the other: each has the broader domain for
    // a different argument.
    const USignature broadFirst = instantiateAction(qConstants, action, {{a, b}, {a}});
    const USignature broadSecond = instantiateAction(qConstants, action, {{a}, {a, b}});
    assert(resolver.getDominationStatus(broadFirst, broadSecond).status == DominationResolver::DIFFERENT);
    assert(resolver.getDominationStatus(broadSecond, broadFirst).status == DominationResolver::DIFFERENT);
    return 0;
}
