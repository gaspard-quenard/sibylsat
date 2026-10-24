#include "preprocessing/macro_action_compiler.h"

#include <algorithm>
#include <cstdint>
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

/** Which method variables may denote the same object: their sorts share an object and no inequality separates them. */
class ArgumentRelations {
public:
    ArgumentRelations(const LiftedProblem& problem, std::map<std::pair<std::string, std::string>, bool>& overlaps)
        : _problem(problem), _overlaps(overlaps) {}

    void addVariables(const std::vector<LiftedParameter>& variables) {
        for (const auto& [name, sort] : variables) _sort_of[name] = sort;
    }
    void addConstraints(const std::vector<LiftedLiteral>& constraints) {
        for (const LiftedLiteral& constraint : constraints) {
            if (constraint.predicate != EQUALITY_PREDICATE || constraint.positive || constraint.arguments.size() != 2) continue;
            _distinct.insert({constraint.arguments[0], constraint.arguments[1]});
            _distinct.insert({constraint.arguments[1], constraint.arguments[0]});
        }
    }
    bool mayEqual(const std::string& first, const std::string& second) const {
        if (first == second) return true;
        if (_distinct.count({first, second})) return false;
        const auto firstSort = _sort_of.find(first), secondSort = _sort_of.find(second);
        if (firstSort == _sort_of.end() || secondSort == _sort_of.end()) return firstSort == secondSort;   // two constants
        return overlap(firstSort->second, secondSort->second);
    }
    /** Both are the single object of their sorts. */
    bool mustEqual(const std::string& first, const std::string& second) const {
        if (first == second) return true;
        const std::vector<std::string>* firstObjects = objects(first);
        const std::vector<std::string>* secondObjects = objects(second);
        return firstObjects && secondObjects && firstObjects->size() == 1 && *firstObjects == *secondObjects;
    }
    size_t numObjects(const std::string& variable) const {
        const std::vector<std::string>* result = objects(variable);
        return result ? result->size() : SIZE_MAX;
    }
    /** Whether the two atoms may be the same ground atom. */
    bool mayUnify(const LiftedLiteral& first, const LiftedLiteral& second) const {
        if (first.predicate != second.predicate || first.arguments.size() != second.arguments.size()) return false;
        for (size_t i = 0; i < first.arguments.size(); i++) if (!mayEqual(first.arguments[i], second.arguments[i])) return false;
        return true;
    }

private:
    const LiftedProblem& _problem;
    std::map<std::pair<std::string, std::string>, bool>& _overlaps;
    std::unordered_map<std::string, std::string> _sort_of;
    std::set<std::pair<std::string, std::string>> _distinct;

    const std::vector<std::string>* objects(const std::string& variable) const {
        const auto sort = _sort_of.find(variable);
        if (sort == _sort_of.end()) return nullptr;
        const auto members = _problem.sorts.find(sort->second);
        return members == _problem.sorts.end() ? nullptr : &members->second;
    }
    bool overlap(const std::string& firstSort, const std::string& secondSort) const {
        if (firstSort == secondSort) return true;
        const auto key = std::minmax(firstSort, secondSort);
        const auto cached = _overlaps.find(key);
        if (cached != _overlaps.end()) return cached->second;
        const auto first = _problem.sorts.find(firstSort), second = _problem.sorts.find(secondSort);
        bool result = true;   // unknown sorts may overlap
        if (first != _problem.sorts.end() && second != _problem.sorts.end()) {
            const std::unordered_set<std::string> members(first->second.begin(), first->second.end());
            result = std::any_of(second->second.begin(), second->second.end(), [&](const std::string& o) { return members.count(o); });
        }
        return _overlaps[key] = result;
    }
};

struct OrderedEffect { LiftedLiteral literal; size_t step; };

/** Why an action cannot join the macro of the earlier steps: its meaning depends on whether two arguments are equal
 * (`first`, `second`: the first position where two atoms that may be one ground atom differ), or it can never follow
 * them (`inapplicable`). */
struct Conflict {
    bool found = false;
    bool inapplicable = false;
    std::string first, second;
};

Conflict dependsOn(const LiftedLiteral& first, const LiftedLiteral& second) {
    Conflict conflict;
    conflict.found = true;
    for (size_t i = 0; i < first.arguments.size(); i++) {
        if (first.arguments[i] == second.arguments[i]) continue;
        conflict.first = first.arguments[i];
        conflict.second = second.arguments[i];
        break;
    }
    return conflict;
}

/** Whether the next action (at step `step`) can join the macro of the earlier steps without its meaning depending
 * on an equality of arguments: a precondition is decided by the last earlier effect that may denote its atom, which
 * must be an identical atom (effects of one action are simultaneous, an add beating a delete); a delete must not
 * follow an add that may denote the same atom (the macro is encoded as one action, where the add would win). */
Conflict findConflict(const std::vector<OrderedEffect>& history, const LiftedTask& nextAction, size_t step, const ArgumentRelations& relations) {
    for (const LiftedLiteral& constraint : nextAction.constraints) {
        if (constraint.predicate != EQUALITY_PREDICATE || constraint.arguments.size() != 2) continue;
        const std::string& first = constraint.arguments[0];
        const std::string& second = constraint.arguments[1];
        if (constraint.positive ? !relations.mayEqual(first, second) : first == second) {
            Conflict conflict;
            conflict.found = conflict.inapplicable = true;
            return conflict;
        }
    }
    for (const LiftedLiteral& precondition : nextAction.prec) {
        // The latest step with an effect on the identical atom, and its value after that step (an action that both
        // adds and deletes it leaves it true).
        int latestIdentical = -1;
        for (const OrderedEffect& e : history) if (sameAtom(e.literal, precondition)) latestIdentical = std::max(latestIdentical, (int) e.step);
        bool valueAfter = false;
        for (const OrderedEffect& e : history)
            if (sameAtom(e.literal, precondition) && (int) e.step == latestIdentical && e.literal.positive) valueAfter = true;
        for (const OrderedEffect& e : history) {
            if (sameAtom(e.literal, precondition) || !relations.mayUnify(e.literal, precondition)) continue;
            // A later effect, or an add of the deciding step that would beat its delete.
            if (latestIdentical < 0 || (int) e.step > latestIdentical || ((int) e.step == latestIdentical && e.literal.positive && !valueAfter))
                return dependsOn(e.literal, precondition);
        }
        if (latestIdentical >= 0 && valueAfter != precondition.positive) {   // the precondition is false
            Conflict conflict;
            conflict.found = conflict.inapplicable = true;
            return conflict;
        }
    }
    for (const LiftedLiteral& effect : nextAction.eff) {
        if (effect.positive) continue;
        for (const OrderedEffect& e : history)
            if (e.literal.positive && e.step < step && !sameAtom(e.literal, effect) && relations.mayUnify(e.literal, effect))
                return dependsOn(e.literal, effect);
    }
    return Conflict();
}

void addPreconditions(LiftedTask& macroAction, const LiftedTask& nextAction) {
    // (findConflict() guarantees that each precondition is either untouched by the earlier effects or decided by an
    // identical one.)
    for (const LiftedLiteral& precondition : nextAction.prec) {
        const bool alreadySatisfied = std::any_of(macroAction.eff.begin(), macroAction.eff.end(), [&](const LiftedLiteral& effect) {
            return sameLiteral(precondition, effect);
        });
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

/** Compose the transition relation of a sequential primitive segment (where findConflict() found nothing). */
LiftedTask composeMacroAction(const LiftedMethod& reduction, const PrimitiveSegment& segment, const std::vector<LiftedTask>& actions,
        const ArgumentRelations& relations) {
    LiftedTask macroAction;
    macroAction.name = "Macro-" + reduction.name + "__" + std::to_string(segment.start) + "-"
            + std::to_string(segment.start + segment.length - 1);

    for (const LiftedTask& action : actions) {
        macroAction.name += "__" + action.name;
        addPreconditions(macroAction, action);
        addEffects(macroAction, action);
    }

    // An effect already required by a precondition is dropped, unless an opposite effect may denote the same atom
    // (dropping the add would let that delete win).
    const std::vector<LiftedLiteral> allEffects = macroAction.eff;
    macroAction.eff.erase(std::remove_if(macroAction.eff.begin(), macroAction.eff.end(), [&](const LiftedLiteral& effect) {
        const bool required = std::any_of(macroAction.prec.begin(), macroAction.prec.end(), [&](const LiftedLiteral& precondition) {
            return sameLiteral(effect, precondition);
        });
        const bool contested = std::any_of(allEffects.begin(), allEffects.end(), [&](const LiftedLiteral& other) {
            return other.positive != effect.positive && relations.mayUnify(other, effect);
        });
        return required && !contested;
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

std::vector<LiftedTask> segmentActions(const LiftedMethod& reduction, const PrimitiveSegment& segment, const LiftedProblem& problem) {
    std::vector<LiftedTask> actions;
    for (size_t index = segment.start; index < segment.start + segment.length; ++index)
        actions.push_back(instantiatePrimitiveTask(problem.getTask(reduction.ps[index].task), reduction.ps[index], reduction));
    return actions;
}

ArgumentRelations relationsOf(const LiftedMethod& reduction, const std::vector<std::vector<LiftedTask>>& segments,
        const LiftedProblem& problem, std::map<std::pair<std::string, std::string>, bool>& overlaps) {
    ArgumentRelations relations(problem, overlaps);
    relations.addVariables(reduction.vars);
    relations.addConstraints(reduction.constraints);
    for (const std::vector<LiftedTask>& actions : segments) for (const LiftedTask& action : actions) relations.addConstraints(action.constraints);
    return relations;
}

/** The first conflict in a primitive segment taken as one macro. */
Conflict firstConflict(const std::vector<LiftedTask>& actions, const ArgumentRelations& relations) {
    std::vector<OrderedEffect> history;
    for (size_t k = 0; k < actions.size(); k++) {
        if (k > 0) {
            const Conflict conflict = findConflict(history, actions[k], k, relations);
            if (conflict.found) return conflict;
        }
        for (const LiftedLiteral& effect : actions[k].eff) history.push_back({effect, k});
    }
    return Conflict();
}

void substituteVariable(LiftedMethod& reduction, const std::string& from, const std::string& to) {
    const std::unordered_map<std::string, std::string> substitution{{from, to}};
    for (LiftedSubtask& subtask : reduction.ps) for (std::string& argument : subtask.args) if (argument == from) argument = to;
    for (LiftedLiteral& precondition : reduction.preconditions) substituteLiteralArguments(precondition, substitution);
    for (LiftedLiteral& constraint : reduction.constraints) substituteLiteralArguments(constraint, substitution);
    reduction.constraints.erase(std::remove_if(reduction.constraints.begin(), reduction.constraints.end(), [&](const LiftedLiteral& c) {
        return c.predicate == EQUALITY_PREDICATE && c.positive && c.arguments.size() == 2 && c.arguments[0] == c.arguments[1];
    }), reduction.constraints.end());
}

}

/** Splits a method into cases on the argument equalities its primitive segments depend on, so that every case
 * composes into macros: an equal case (one variable replaces the other in the subtasks, an equality constraint
 * keeps both) and a different case (an inequality constraint). Cases whose segment cannot be executed are dropped.
 * The cases are alternative methods of the same task (no new task); each is named <method>__case<k> and printed
 * as <method> in the plan.
 *
 * Example Blocksworld-GTOHP: m5_do_move(?x ?y ?z) has the segment
 * (unstack ?x ?z) (stack ?x ?y). The precondition (clear ?y) of stack is the (clear ?z) unstack adds if ?y = ?z,
 * the (clear ?x) it deletes if ?y = ?x, and otherwise must hold before the segment. The cases are:
 * - ?y = ?z: stack ?x ?z puts the block back (a macro without effect; (= ?z ?y) keeps ?y in the method);
 * - ?y != ?z, ?y = ?x: stack ?x ?x after unstack deleted (clear ?x): never executable, dropped;
 * - ?y != ?z, ?y != ?x: a real move, the macro requires (clear ?y);
 * - ?x = ?y = ?z: unstack a block from itself (no state allows it, but nothing here knows that).
 * So do_move gets four methods (m4_do_move and the three m5 cases) instead of two. A conflict between variables of
 * disjoint sorts is no conflict (they are never equal). */
std::vector<LiftedMethod> MacroActionCompiler::splitCases(const LiftedMethod& method, const LiftedProblem& problem,
        const std::unordered_set<std::string>& primitiveNames) {
    if (method.at == problem.initial_task_name) return {method};
    std::vector<std::pair<LiftedMethod, bool>> pending{{method, false}};   // (case, whether it is a proper case)
    std::vector<LiftedMethod> cases;
    while (!pending.empty()) {
        auto [current, isCase] = std::move(pending.back());
        pending.pop_back();
        std::vector<std::vector<LiftedTask>> segments;
        for (const PrimitiveSegment& segment : findPrimitiveSegments(current, primitiveNames)) segments.push_back(segmentActions(current, segment, problem));
        const ArgumentRelations relations = relationsOf(current, segments, problem, _sort_overlaps);
        Conflict conflict;
        for (const std::vector<LiftedTask>& actions : segments) if (!conflict.found) conflict = firstConflict(actions, relations);
        if (conflict.found && conflict.inapplicable && isCase) {
            _inapplicable_cases++;
            continue;
        }
        if (!conflict.found || conflict.inapplicable || conflict.first.empty()) {
            cases.push_back(std::move(current));
            continue;
        }
        // The variable with the smaller sort stays.
        std::string kept = conflict.first, replaced = conflict.second;
        if (relations.numObjects(replaced) < relations.numObjects(kept)) std::swap(kept, replaced);
        if (!relations.mustEqual(kept, replaced)) {
            LiftedMethod different = current;
            different.constraints.push_back({EQUALITY_PREDICATE, {kept, replaced}, false});
            pending.push_back({std::move(different), true});
        }
        LiftedMethod equal = std::move(current);
        substituteVariable(equal, replaced, kept);
        equal.constraints.push_back({EQUALITY_PREDICATE, {kept, replaced}, true});
        pending.push_back({std::move(equal), true});
    }
    if (cases.empty()) return {method};   // no executable case: left as it was
    if (cases.size() > 1) {
        for (size_t k = 0; k < cases.size(); k++) {
            cases[k].name = method.name + "__case" + std::to_string(k);
            _original_method_names[cases[k].name] = method.name;
        }
        _case_split_methods++;
    }
    return cases;
}

void MacroActionCompiler::compile(LiftedProblem& problem) {
    std::unordered_set<std::string> primitiveNames;
    for (const LiftedTask& action : problem.primitive_tasks) primitiveNames.insert(action.name);

    size_t numberOfMacros = 0;
    std::vector<LiftedMethod> methods;
    for (const LiftedMethod& original : problem.methods) {
        if (original.ps.size() <= 1 || findPrimitiveSegments(original, primitiveNames).empty()) {
            methods.push_back(original);
            continue;
        }
        for (LiftedMethod& reduction : splitCases(original, problem, primitiveNames)) {
            const std::vector<PrimitiveSegment> segments = findPrimitiveSegments(reduction, primitiveNames);
            std::vector<std::vector<LiftedTask>> segmentTasks;
            for (const PrimitiveSegment& segment : segments) segmentTasks.push_back(segmentActions(reduction, segment, problem));
            const ArgumentRelations relations = relationsOf(reduction, segmentTasks, problem, _sort_overlaps);
            size_t removedSteps = 0;
            for (size_t s = 0; s < segments.size(); s++) {
                const PrimitiveSegment& originalSegment = segments[s];
                const std::vector<LiftedTask>& all = segmentTasks[s];
                // Split the segment where an action cannot join the macro of the previous ones (a case that cannot
                // be executed, or the initial method).
                std::vector<std::pair<size_t, size_t>> runs;   // (first, length) within the segment
                std::vector<OrderedEffect> history;
                size_t first = 0;
                for (size_t k = 0; k < all.size(); k++) {
                    if (k > first && findConflict(history, all[k], k, relations).found) {
                        runs.push_back({first, k - first});
                        first = k;
                        history.clear();
                    }
                    for (const LiftedLiteral& effect : all[k].eff) history.push_back({effect, k});
                }
                runs.push_back({first, all.size() - first});
                for (const auto& [runFirst, runLength] : runs) {
                    if (runLength < 2) continue;
                    const size_t start = originalSegment.start + runFirst - removedSteps;
                    const PrimitiveSegment segment{originalSegment.start + runFirst, runLength};
                    const std::vector<LiftedTask> actions(all.begin() + runFirst, all.begin() + runFirst + runLength);
                    const LiftedTask macroAction = composeMacroAction(reduction, segment, actions, relations);
                    _expansions.emplace(macroAction.name, describeExpansion(macroAction, actions));
                    problem.primitive_tasks.push_back(macroAction);
                    replaceSegment(reduction, start, runLength, macroAction);
                    removedSteps += runLength - 1;
                    ++numberOfMacros;
                }
                if (runs.size() > 1) _split_segments++;
            }
            methods.push_back(std::move(reduction));
        }
    }
    problem.methods = std::move(methods);
    Log::i("Created %zu macro actions (%zu methods split into cases on argument equalities, %zu cases dropped as "
           "inexecutable, %zu segments split).\n", numberOfMacros, _case_split_methods, _inapplicable_cases, _split_segments);
}

const std::string& MacroActionCompiler::originalMethodName(const std::string& methodName) const {
    const auto original = _original_method_names.find(methodName);
    return original == _original_method_names.end() ? methodName : original->second;
}

bool MacroActionCompiler::isMacroAction(const std::string& actionName) const {
    return _expansions.count(actionName);
}

const MacroActionExpansion& MacroActionCompiler::getExpansion(const std::string& actionName) const {
    return _expansions.at(actionName);
}
