#include "data/action_costs.h"

#include "data/htn_instance.h"
#include "data/reduction.h"
#include "data/substitution.h"
#include "preprocessing/macro_action_compiler.h"

ActionCosts::ActionCosts(HtnInstance& htn, const MacroActionCompiler* macroActions) : _htn(htn) {
    if (macroActions == nullptr) return;
    for (const auto& [name, expansion] : macroActions->getExpansions()) {
        std::vector<MacroStep>& steps = _macro_steps[htn.nameId(name)];
        for (const MacroPrimitiveStep& step : expansion.primitiveSteps) {
            steps.push_back({htn.nameId(step.actionName), step.macroArgumentIndices});
        }
    }
}

int ActionCosts::of(const USignature& action) const {
    if (_htn.isActionRepetition(action._name_id)) {
        return of(USignature(_htn.getActionNameFromRepetition(action._name_id), action._args));
    }

    if (_htn.isPrimitivizedAction(action._name_id)) {
        // The action has the arguments of the method that it replaces: it costs the method's only action.
        const Reduction& method = _htn.getReductionTemplate(_htn.getReductionAndActionFromPrimitivization(action._name_id).first);
        return of(method.getSubtasks().front().substitute(Substitution(method.getArguments(), action._args)));
    }

    const auto macro = _macro_steps.find(action._name_id);
    if (macro != _macro_steps.end()) {
        int cost = 0;
        for (const MacroStep& step : macro->second) {
            std::vector<int> arguments;
            arguments.reserve(step.argumentIndices.size());
            for (size_t argumentIndex : step.argumentIndices) arguments.push_back(action._args.at(argumentIndex));
            cost += of(USignature(step.actionId, std::move(arguments)));
        }
        return cost;
    }

    return ofDomainAction(action);
}

int ActionCosts::ofDomainAction(const USignature&) const {
    return 1;
}
