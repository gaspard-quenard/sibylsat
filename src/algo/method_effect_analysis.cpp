#include "algo/method_effect_analysis.h"

#include <cassert>
#include <ranges>

#include "util/log.h"
#include "util/names.h"

MethodEffectAnalysis::MethodEffectAnalysis(HtnInstance& htn, FactAnalysis& facts)
        : _htn(htn),
          _facts(facts),
          _traversal(htn) {
    for (const auto& [methodId, method] : _htn.getReductionTemplates()) {
        (void) methodId;
        computePossibleEffects(method);
    }
}

SigSet MethodEffectAnalysis::getPossibleEffects(const USignature& method) const {
    assert(_htn.isReduction(method));
    const SigSet& effects = _possible_effects.at(method._name_id);
    const std::vector<int> placeholders = makePlaceholders(method._args.size());
    return substituteEffects(effects, Substitution(placeholders, method._args));
}

const BitVec& MethodEffectAnalysis::getArgumentIndependentGroundEffects(const USignature& method, bool negated) const {
    assert(_htn.isReduction(method));
    return negated
            ? _possible_ground_negative_effects.at(method._name_id)
            : _possible_ground_positive_effects.at(method._name_id);
}

SigSet MethodEffectAnalysis::instantiateArgumentDependentEffects(const USignature& method) {
    assert(_htn.isReduction(method));
    SigSet result;
    const int methodId = method._name_id;
    const std::vector<int> methodSorts = _htn.getSorts(methodId);
    const std::vector<int> placeholders = makePlaceholders(method._args.size());
    const Substitution instantiateMethod(placeholders, method._args);

    for (const Signature& liftedEffect : _possible_effects.at(methodId)) {
        if (!hasMethodArgument(liftedEffect)) {
            continue;
        }

        Signature effect = liftedEffect.substitute(instantiateMethod);
        const std::vector<int> effectSorts = _htn.getSortsParamsFromSigForFA(liftedEffect._usig);

        const std::vector<FlatHashSet<int>>& domains = _facts.getGroundFactArgumentDomains(effect);

        for (const USignature& grounding : ArgIterator::getFullInstantiation(
                effect._usig,
                _htn,
                effectSorts,
                domains)) {
            if (hasValidGrounding(grounding, effect._negated, methodSorts)) {
                result.emplace(grounding, effect._negated);
            }
        }
    }

    return result;
}

void MethodEffectAnalysis::computePossibleEffects(const Reduction& method) {
    const std::vector<int> placeholders = makePlaceholders(method.getArguments().size());
    const USignature canonicalMethod = method.getSignature().substitute(
            Substitution(method.getArguments(), placeholders));

    SigSet effects = collectPossibleEffects(canonicalMethod);
    removeCoveredEffects(effects);

    Log::d("Possible effects for %s:\n", TOSTR(method.getSignature()));
    for (const Signature& effect : effects) {
        Log::d("  %s\n", TOSTR(effect));
    }

    _possible_effects[method.getNameId()] = std::move(effects);
    computePossibleGroundEffects(method);
}

SigSet MethodEffectAnalysis::collectPossibleEffects(const USignature& method) {
    SigSet effects;
    _traversal.traverse(
            method,
            NetworkTraversal::TRAVERSE_PREORDER,
            [&](const USignature& operation, int depth) {
                (void) depth;
                if (_htn.isAction(operation)) {
                    const Action action = _htn.toAction(operation._name_id, operation._args);
                    effects.insert(action.getEffects().begin(), action.getEffects().end());
                } else if (_htn.isReductionPrimitivizable(operation._name_id)) {
                    const Action& replacement = _htn.getReductionPrimitivization(operation._name_id);
                    const Action action = replacement.substitute(
                            Substitution(replacement.getArguments(), operation._args));
                    effects.insert(action.getEffects().begin(), action.getEffects().end());
                }
            });
    return effects;
}

void MethodEffectAnalysis::removeCoveredEffects(SigSet& effects) {
    for (auto effectIt = effects.begin(); effectIt != effects.end();) {
        const Signature& effect = *effectIt;
        bool covered = false;
        for (const Signature& other : effects) {
            if (other == effect || other._negated != effect._negated) {
                continue;
            }
            if (isCoveredBy(effect._usig, other._usig)) {
                covered = true;
                break;
            }
        }

        if (covered) {
            effectIt = effects.erase(effectIt);
        } else {
            ++effectIt;
        }
    }
}

bool MethodEffectAnalysis::isCoveredBy(
        const USignature& effect,
        const USignature& coveringEffect) const {
    if (effect._name_id != coveringEffect._name_id) {
        return false;
    }

    const std::vector<int> effectSorts = _htn.getSortsParamsFromSigForFA(effect);
    const std::vector<int> coveringSorts = _htn.getSortsParamsFromSigForFA(coveringEffect);

    for (size_t argIndex = 0; argIndex < effect._args.size(); argIndex++) {
        const int effectArg = effect._args[argIndex];
        const int coveringArg = coveringEffect._args[argIndex];
        if (effectArg == coveringArg) {
            continue;
        }

        const std::string coveringName = Names::to_string(coveringArg);
        if (coveringName.empty() || coveringName.back() != '_') {
            return false;
        }
        if (effectSorts[argIndex] == coveringSorts[argIndex]) {
            continue;
        }

        const FlatHashSet<int>& effectConstants = _htn.getConstantsOfSort(effectSorts[argIndex]);
        const FlatHashSet<int>& coveringConstants = _htn.getConstantsOfSort(coveringSorts[argIndex]);
        if (effectConstants.empty()) {
            return false;
        }
        for (int constant : effectConstants) {
            if (!coveringConstants.count(constant)) {
                return false;
            }
        }
    }

    return true;
}

void MethodEffectAnalysis::computePossibleGroundEffects(const Reduction& method) {
    const int methodId = method.getNameId();
    _possible_ground_positive_effects[methodId] = BitVec(_htn.getNumPositiveGroundFacts());
    _possible_ground_negative_effects[methodId] = BitVec(_htn.getNumPositiveGroundFacts());

    for (const Signature& effect : _possible_effects.at(methodId)) {
        if (hasMethodArgument(effect)) {
            continue;
        }

        const std::vector<int> effectSorts = _htn.getSortsParamsFromSigForFA(effect._usig);
        addPossibleGroundEffect(methodId, effect, effectSorts);
    }
}

void MethodEffectAnalysis::addPossibleGroundEffect(
        int methodId,
        const Signature& effect,
        const std::vector<int>& effectSorts) {
    BitVec& groundEffects = effect._negated
            ? _possible_ground_negative_effects.at(methodId)
            : _possible_ground_positive_effects.at(methodId);

    if (_htn.isFullyGround(effect._usig)) {
        const int factId = _htn.getGroundFactId(effect._usig, effect._negated);
        if (factId >= 0) {
            groundEffects.set(factId);
        }
        return;
    }

    const std::vector<int>& sorts = effectSorts.empty()
            ? _htn.getSorts(effect._usig._name_id)
            : effectSorts;
    groundEffects.or_with(_htn.findMatchingGroundFactIds(effect._usig, effect._negated, sorts));
}

bool MethodEffectAnalysis::hasMethodArgument(const Signature& effect) const {
    return std::ranges::any_of(effect._usig._args, [](int arg) { return arg < 0; });
}

bool MethodEffectAnalysis::hasValidGrounding(
        const USignature& effect,
        bool negated,
        const std::vector<int>& methodSorts) {
    if (!_htn.hasQConstants(effect) && _htn.isFullyGround(effect)) {
        return _facts.isInGroundFacts(effect, negated);
    }

    std::vector<int> effectSorts(effect._args.size());
    bool hasPlaceholder = false;
    for (size_t argIndex = 0; argIndex < effect._args.size(); argIndex++) {
        if (effect._args[argIndex] < 0) {
            effectSorts[argIndex] = methodSorts[-effect._args[argIndex] - 1];
            hasPlaceholder = true;
        }
    }

    const std::vector<int> restrictiveSorts = hasPlaceholder ? effectSorts : std::vector<int>();
    for (const USignature& grounding : _htn.enumerateCandidateDecodings(effect, restrictiveSorts)) {
        if (_facts.isInGroundFacts(grounding, negated)) {
            return true;
        }
    }

    Log::d("Discard %s as a possible effect because no decoding is valid\n", TOSTR(effect));
    return false;
}

std::vector<int> MethodEffectAnalysis::makePlaceholders(size_t count) const {
    std::vector<int> placeholders(count);
    for (size_t index = 0; index < count; index++) {
        placeholders[index] = -static_cast<int>(index) - 1;
    }
    return placeholders;
}

SigSet MethodEffectAnalysis::substituteEffects(
        const SigSet& effects,
        const Substitution& substitution) const {
    SigSet substituted;
    substituted.reserve(effects.size());
    for (const Signature& effect : effects) {
        substituted.insert(effect.substitute(substitution));
    }
    return substituted;
}
