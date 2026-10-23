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

    // Substituted into the dominating signature, the substitution gives the dominated one: both Q-constants of
    // broad take the value a (a substitution keyed by the dominated arguments would keep only one of them).
    assert(narrow._args == std::vector<int>({a, a}));
    const auto result = resolver.getDominationStatus(narrow, broad);
    assert(result.qconstSubstitutions.size() == 2);
    for (const auto& [target, value] : result.qconstSubstitutions) {
        assert(target == broad._args[0] || target == broad._args[1]);
        assert(value == a);
    }

    // A Q-constant occurring twice takes one value, so it cannot represent two different arguments.
    const USignature repeated(actionId, std::vector<int>({broad._args[0], broad._args[0]}));
    const USignature distinct = instantiateAction(qConstants, action, {{a}, {b}});
    assert(distinct._args == std::vector<int>({a, b}));
    assert(resolver.getDominationStatus(distinct, repeated).status == DominationResolver::DIFFERENT);
    assert(resolver.getDominationStatus(repeated, distinct).status == DominationResolver::DIFFERENT);
    assert(resolver.getDominationStatus(narrow, repeated).status == DominationResolver::DOMINATED);
    return 0;
}
