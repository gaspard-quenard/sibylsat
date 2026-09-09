#include "preprocessing/macro_action_compiler.h"

#include <algorithm>
#include <cstdlib>
#include <set>
#include <unordered_set>

#include "parser/lifted_problem.h"
#include "util/log.h"

namespace {

constexpr const char* EQUALITY_PREDICATE = "__equal";

struct PrimitiveSegment {
    size_t start;
    size_t length;
};

bool sameAtom(const LiftedLiteral& first, const LiftedLiteral& second) {
    return first.predicate == second.predicate && first.arguments == second.arguments;
}

bool sameLiteral(const LiftedLiteral& first, const LiftedLiteral& second) {
    return first.positive == second.positive && sameAtom(first, second);
}

/** Find maximal runs containing at least two consecutive primitive subtasks. */
std::vector<PrimitiveSegment> findPrimitiveSegments(const LiftedMethod& reduction, const std::unordered_set<std::string>& primitiveNames) {
    std::vector<PrimitiveSegment> segments;
    size_t runStart = 0;
    size_t runLength = 0;

    auto finishRun = [&]() {
        if (runLength >= 2) segments.push_back({runStart, runLength});
        runLength = 0;
    };

    for (size_t index = 0; index < reduction.ps.size(); ++index) {
        const LiftedSubtask& step = reduction.ps[index];
        if (primitiveNames.count(step.task)) {
            if (runLength == 0) runStart = index;
            ++runLength;
        } else {
            finishRun();
        }
    }
    finishRun();
    return segments;
}

void substituteLiteralArguments(LiftedLiteral& value, const std::unordered_map<std::string, std::string>& substitution) {
    for (std::string& argument : value.arguments) {
        const auto replacement = substitution.find(argument);
        if (replacement != substitution.end()) argument = replacement->second;
    }
}

/** Instantiate an action template with the arguments used by its method subtask. */
LiftedTask instantiatePrimitiveTask(const LiftedTask& actionTemplate, const LiftedSubtask& step, const LiftedMethod& reduction) {
    LiftedTask action = actionTemplate;
    std::unordered_map<std::string, std::string> substitution;
    std::unordered_map<std::string, std::string> methodParameterSorts;
    for (const auto& [name, sort] : reduction.vars) methodParameterSorts[name] = sort;

    for (size_t index = 0; index < action.vars.size(); ++index) substitution[action.vars[index].first] = step.args.at(index);
    for (auto& [name, sort] : action.vars) {
        const std::string originalName = name;
        name = substitution.at(originalName);
        const auto methodSort = methodParameterSorts.find(name);
        if (methodSort != methodParameterSorts.end()) sort = methodSort->second;
    }
    for (LiftedLiteral& precondition : action.prec) substituteLiteralArguments(precondition, substitution);
    for (LiftedLiteral& effect : action.eff) substituteLiteralArguments(effect, substitution);
    for (LiftedLiteral& constraint : action.constraints) substituteLiteralArguments(constraint, substitution);
    return action;
}

void addConstraint(LiftedTask& macroAction, const LiftedLiteral& constraint) {
    for (const LiftedLiteral& existing : macroAction.constraints) {
        if (!sameAtom(existing, constraint)) continue;
        if (existing.positive != constraint.positive) {
            Log::e("Macro action %s contains opposite equality constraints.\n", macroAction.name.c_str());
            exit(1);
        }
        return;
    }
    macroAction.constraints.push_back(constraint);
}

void addPreconditions(LiftedTask& macroAction, const LiftedTask& nextAction) {
    for (const LiftedLiteral& precondition : nextAction.prec) {
        bool alreadySatisfied = false;
        for (const LiftedLiteral& effect : macroAction.eff) {
            if (precondition.predicate != effect.predicate || precondition.positive == effect.positive) {
                if (sameLiteral(precondition, effect)) alreadySatisfied = true;
                continue;
            }
            if (precondition.arguments == effect.arguments) {
                Log::e("Macro action %s makes a later precondition false.\n", macroAction.name.c_str());
                exit(1);
            }
            if (precondition.arguments.size() == 1 && effect.arguments.size() == 1) {
                LiftedLiteral inequality;
                inequality.positive = false;
                inequality.predicate = EQUALITY_PREDICATE;
                inequality.arguments = {precondition.arguments.front(), effect.arguments.front()};
                addConstraint(macroAction, inequality);
            }
        }
        if (alreadySatisfied) continue;

        const bool alreadyRequired = std::any_of(macroAction.prec.begin(), macroAction.prec.end(), [&](const LiftedLiteral& existing) {
            return sameLiteral(existing, precondition);
        });
        if (!alreadyRequired) macroAction.prec.push_back(precondition);
    }
    for (const LiftedLiteral& constraint : nextAction.constraints) addConstraint(macroAction, constraint);
}

void addEffects(LiftedTask& macroAction, const LiftedTask& nextAction) {
    auto isCancelledBy = [&](const LiftedLiteral& current, bool currentIsPositive) {
        if (current.positive != currentIsPositive) return false;
        return std::any_of(nextAction.eff.begin(), nextAction.eff.end(), [&](const LiftedLiteral& added) {
            return added.positive != currentIsPositive && sameAtom(current, added);
        });
    };

    macroAction.eff.erase(std::remove_if(macroAction.eff.begin(), macroAction.eff.end(), [&](const LiftedLiteral& effect) {
        return isCancelledBy(effect, false);
    }), macroAction.eff.end());
    for (const LiftedLiteral& effect : nextAction.eff) if (!effect.positive) macroAction.eff.push_back(effect);

    macroAction.eff.erase(std::remove_if(macroAction.eff.begin(), macroAction.eff.end(), [&](const LiftedLiteral& effect) {
        return isCancelledBy(effect, true);
    }), macroAction.eff.end());
    for (const LiftedLiteral& effect : nextAction.eff) if (effect.positive) macroAction.eff.push_back(effect);
}

/** Compose the transition relation of a sequential primitive segment. */
LiftedTask composeMacroAction(const LiftedMethod& reduction, const PrimitiveSegment& segment, const std::vector<LiftedTask>& actions) {
    LiftedTask macroAction;
    macroAction.name = "Macro-" + reduction.name + "__" + std::to_string(segment.start) + "-"
            + std::to_string(segment.start + segment.length - 1);

    for (const LiftedTask& action : actions) {
        macroAction.name += "__" + action.name;
        addPreconditions(macroAction, action);
        addEffects(macroAction, action);
    }

    macroAction.eff.erase(std::remove_if(macroAction.eff.begin(), macroAction.eff.end(), [&](const LiftedLiteral& effect) {
        return std::any_of(macroAction.prec.begin(), macroAction.prec.end(), [&](const LiftedLiteral& precondition) {
            return sameLiteral(effect, precondition);
        });
    }), macroAction.eff.end());

    std::set<std::pair<std::string, std::string>> parameters;
    for (const LiftedTask& action : actions) parameters.insert(action.vars.begin(), action.vars.end());
    macroAction.vars.assign(parameters.begin(), parameters.end());
    macroAction.number_of_original_vars = macroAction.vars.size();
    return macroAction;
}

MacroActionExpansion describeExpansion(const LiftedTask& macroAction, const std::vector<LiftedTask>& actions) {
    MacroActionExpansion expansion;
    for (const LiftedTask& action : actions) {
        MacroPrimitiveStep step;
        step.actionName = action.name;
        for (const auto& [argumentName, unusedSort] : action.vars) {
            const auto argument = std::find_if(macroAction.vars.begin(), macroAction.vars.end(), [&](const auto& variable) {
                return variable.first == argumentName;
            });
            if (argument == macroAction.vars.end()) {
                Log::e("Parameter %s is absent from macro action %s.\n", argumentName.c_str(), macroAction.name.c_str());
                exit(1);
            }
            step.macroArgumentIndices.push_back(std::distance(macroAction.vars.begin(), argument));
        }
        expansion.primitiveSteps.push_back(std::move(step));
    }
    return expansion;
}

void replaceSegment(LiftedMethod& reduction, size_t start, size_t length, const LiftedTask& macroAction) {
    reduction.ps.erase(reduction.ps.begin() + start, reduction.ps.begin() + start + length);
    LiftedSubtask macroStep;
    macroStep.task = macroAction.name;
    macroStep.id = "t" + std::to_string(start + 1);
    for (const auto& [name, unusedSort] : macroAction.vars) macroStep.args.push_back(name);
    reduction.ps.insert(reduction.ps.begin() + start, std::move(macroStep));

    reduction.ordering.clear();
    for (size_t before = 0; before < reduction.ps.size(); ++before) {
        for (size_t after = before + 1; after < reduction.ps.size(); ++after) {
            reduction.ordering.emplace_back(reduction.ps[before].id, reduction.ps[after].id);
        }
    }
}

}

void MacroActionCompiler::compile(LiftedProblem& problem) {
    std::unordered_set<std::string> primitiveNames;
    for (const LiftedTask& action : problem.primitive_tasks) primitiveNames.insert(action.name);

    size_t numberOfMacros = 0;
    for (LiftedMethod& reduction : problem.methods) {
        if (reduction.ps.size() <= 1) continue;

        const std::vector<PrimitiveSegment> segments = findPrimitiveSegments(reduction, primitiveNames);
        size_t removedSteps = 0;
        for (const PrimitiveSegment& originalSegment : segments) {
            const size_t start = originalSegment.start - removedSteps;
            std::vector<LiftedTask> actions;
            actions.reserve(originalSegment.length);
            for (size_t index = start; index < start + originalSegment.length; ++index) {
                const LiftedSubtask& step = reduction.ps[index];
                actions.push_back(instantiatePrimitiveTask(problem.getTask(step.task), step, reduction));
            }

            const LiftedTask macroAction = composeMacroAction(reduction, originalSegment, actions);
            _expansions.emplace(macroAction.name, describeExpansion(macroAction, actions));
            problem.primitive_tasks.push_back(macroAction);
            replaceSegment(reduction, start, originalSegment.length, macroAction);
            removedSteps += originalSegment.length - 1;
            ++numberOfMacros;
        }
    }
    Log::i("Created %zu macro actions.\n", numberOfMacros);
}

bool MacroActionCompiler::isMacroAction(const std::string& actionName) const {
    return _expansions.count(actionName);
}

const MacroActionExpansion& MacroActionCompiler::getExpansion(const std::string& actionName) const {
    return _expansions.at(actionName);
}
