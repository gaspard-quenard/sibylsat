#include "preprocessing/macro_action_compiler.h"

#include <algorithm>
#include <cstdlib>
#include <set>
#include <unordered_set>

#include "libpanda.hpp"
#include "util/log.h"

namespace {

struct PrimitiveSegment {
    size_t start;
    size_t length;
};

bool sameAtom(const literal& first, const literal& second) {
    return first.predicate == second.predicate && first.arguments == second.arguments;
}

bool sameLiteral(const literal& first, const literal& second) {
    return first.positive == second.positive && sameAtom(first, second);
}

/** Find maximal runs containing at least two consecutive primitive subtasks. */
std::vector<PrimitiveSegment> findPrimitiveSegments(const method& reduction, const std::unordered_set<std::string>& primitiveNames) {
    std::vector<PrimitiveSegment> segments;
    size_t runStart = 0;
    size_t runLength = 0;

    auto finishRun = [&]() {
        if (runLength >= 2) segments.push_back({runStart, runLength});
        runLength = 0;
    };

    for (size_t index = 0; index < reduction.ps.size(); ++index) {
        const plan_step& step = reduction.ps[index];
        if (step.task.rfind(method_precondition_action_name) != std::string::npos) continue;
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

void substituteLiteralArguments(literal& value, const std::unordered_map<std::string, std::string>& substitution) {
    for (std::string& argument : value.arguments) {
        const auto replacement = substitution.find(argument);
        if (replacement != substitution.end()) argument = replacement->second;
    }
}

/** Instantiate an action template with the arguments used by its method subtask. */
task instantiatePrimitiveTask(const task& actionTemplate, const plan_step& step, const method& reduction) {
    task action = actionTemplate;
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
    for (literal& precondition : action.prec) substituteLiteralArguments(precondition, substitution);
    for (literal& effect : action.eff) substituteLiteralArguments(effect, substitution);
    for (literal& constraint : action.constraints) substituteLiteralArguments(constraint, substitution);
    return action;
}

void addConstraint(task& macroAction, const literal& constraint) {
    for (const literal& existing : macroAction.constraints) {
        if (!sameAtom(existing, constraint)) continue;
        if (existing.positive != constraint.positive) {
            Log::e("Macro action %s contains opposite equality constraints.\n", macroAction.name.c_str());
            exit(1);
        }
        return;
    }
    macroAction.constraints.push_back(constraint);
}

void addPreconditions(task& macroAction, const task& nextAction) {
    for (const literal& precondition : nextAction.prec) {
        bool alreadySatisfied = false;
        for (const literal& effect : macroAction.eff) {
            if (precondition.predicate != effect.predicate || precondition.positive == effect.positive) {
                if (sameLiteral(precondition, effect)) alreadySatisfied = true;
                continue;
            }
            if (precondition.arguments == effect.arguments) {
                Log::e("Macro action %s makes a later precondition false.\n", macroAction.name.c_str());
                exit(1);
            }
            if (precondition.arguments.size() == 1 && effect.arguments.size() == 1) {
                literal inequality;
                inequality.positive = false;
                inequality.predicate = dummy_equal_literal;
                inequality.arguments = {precondition.arguments.front(), effect.arguments.front()};
                addConstraint(macroAction, inequality);
            }
        }
        if (alreadySatisfied) continue;

        const bool alreadyRequired = std::any_of(macroAction.prec.begin(), macroAction.prec.end(), [&](const literal& existing) {
            return sameLiteral(existing, precondition);
        });
        if (!alreadyRequired) macroAction.prec.push_back(precondition);
    }
    for (const literal& constraint : nextAction.constraints) addConstraint(macroAction, constraint);
}

void addEffects(task& macroAction, const task& nextAction) {
    auto isCancelledBy = [&](const literal& current, bool currentIsPositive) {
        if (current.positive != currentIsPositive) return false;
        return std::any_of(nextAction.eff.begin(), nextAction.eff.end(), [&](const literal& added) {
            return added.positive != currentIsPositive && sameAtom(current, added);
        });
    };

    macroAction.eff.erase(std::remove_if(macroAction.eff.begin(), macroAction.eff.end(), [&](const literal& effect) {
        return isCancelledBy(effect, false);
    }), macroAction.eff.end());
    for (const literal& effect : nextAction.eff) if (!effect.positive) macroAction.eff.push_back(effect);

    macroAction.eff.erase(std::remove_if(macroAction.eff.begin(), macroAction.eff.end(), [&](const literal& effect) {
        return isCancelledBy(effect, true);
    }), macroAction.eff.end());
    for (const literal& effect : nextAction.eff) if (effect.positive) macroAction.eff.push_back(effect);
}

/** Compose the transition relation of a sequential primitive segment. */
task composeMacroAction(const method& reduction, const PrimitiveSegment& segment, const std::vector<task>& actions) {
    task macroAction;
    macroAction.name = "Macro-" + reduction.name + "__" + std::to_string(segment.start) + "-"
            + std::to_string(segment.start + segment.length - 1);

    for (const task& action : actions) {
        macroAction.name += "__" + action.name;
        addPreconditions(macroAction, action);
        addEffects(macroAction, action);
    }

    macroAction.eff.erase(std::remove_if(macroAction.eff.begin(), macroAction.eff.end(), [&](const literal& effect) {
        return std::any_of(macroAction.prec.begin(), macroAction.prec.end(), [&](const literal& precondition) {
            return sameLiteral(effect, precondition);
        });
    }), macroAction.eff.end());

    std::set<std::pair<std::string, std::string>> parameters;
    for (const task& action : actions) parameters.insert(action.vars.begin(), action.vars.end());
    macroAction.vars.assign(parameters.begin(), parameters.end());
    macroAction.number_of_original_vars = macroAction.vars.size();
    return macroAction;
}

MacroActionExpansion describeExpansion(const task& macroAction, const std::vector<task>& actions) {
    MacroActionExpansion expansion;
    for (const task& action : actions) {
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

void replaceSegment(method& reduction, size_t start, size_t length, const task& macroAction) {
    reduction.ps.erase(reduction.ps.begin() + start, reduction.ps.begin() + start + length);
    plan_step macroStep;
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

void MacroActionCompiler::compile(ParsedProblem& problem) {
    std::unordered_set<std::string> primitiveNames;
    for (const parsed_task& action : problem.parsed_primitive) primitiveNames.insert(action.name);

    size_t numberOfMacros = 0;
    for (method& reduction : problem.methods) {
        if (reduction.ps.size() <= 1) continue;

        const std::vector<PrimitiveSegment> segments = findPrimitiveSegments(reduction, primitiveNames);
        size_t removedSteps = 0;
        for (const PrimitiveSegment& originalSegment : segments) {
            const size_t start = originalSegment.start - removedSteps;
            std::vector<task> actions;
            actions.reserve(originalSegment.length);
            for (size_t index = start; index < start + originalSegment.length; ++index) {
                const plan_step& step = reduction.ps[index];
                actions.push_back(instantiatePrimitiveTask(problem.task_name_map.at(step.task), step, reduction));
            }

            const task macroAction = composeMacroAction(reduction, originalSegment, actions);
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
