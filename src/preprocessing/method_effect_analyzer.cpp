#include "preprocessing/method_effect_analyzer.h"

#include <cassert>
#include <ranges>

#include "util/log.h"
#include "util/names.h"

MethodEffectAnalyzer::MethodEffectAnalyzer(HtnInstance& htn, FactAnalysis& facts)
        : _htn(htn),
          _facts(facts),
          _traversal(htn) {}

void MethodEffectAnalyzer::analyze(HtnInstance& htn, FactAnalysis& facts) {
    MethodEffectAnalyzer analyzer(htn, facts);
    for (auto& [methodId, method] : htn.getReductionTemplates()) {
        (void) methodId;
        analyzer.analyzeMethod(method);
    }
}

void MethodEffectAnalyzer::analyzeMethod(Reduction& method) {
    const std::vector<int> placeholders = makePlaceholders(method.getArguments().size());
    const USignature canonicalMethod = method.getSignature().substitute(
            Substitution(method.getArguments(), placeholders));

    SigSet effects = collectPossibleEffects(canonicalMethod);
    removeCoveredEffects(effects);

    Log::d("Possible effects for %s:\n", TOSTR(method.getSignature()));
    for (const Signature& effect : effects) {
        Log::d("  %s\n", TOSTR(effect));
    }

    PossibleMethodEffects summary;
    summary.argumentIndependentPositive = BitVec(_facts.getNumGroundFacts());
    summary.argumentIndependentNegative = BitVec(_facts.getNumGroundFacts());
    for (const Signature& effect : effects) {
        SigSet& destination = hasMethodArgument(effect)
                ? summary.argumentDependentLiftedEffects
                : summary.argumentIndependentLiftedEffectsForInference;
        destination.insert(effect);
    }
    computeArgumentIndependentGroundEffects(summary);
    method.setPossibleEffectSummary(std::move(summary));
}

SigSet MethodEffectAnalyzer::collectPossibleEffects(const USignature& method) {
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

void MethodEffectAnalyzer::removeCoveredEffects(SigSet& effects) {
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

bool MethodEffectAnalyzer::isCoveredBy(
        const USignature& effect,
        const USignature& coveringEffect) const {
    if (effect._name_id != coveringEffect._name_id) {
        return false;
    }

    const std::vector<int> effectSorts = _htn.getArgumentSorts(effect);
    const std::vector<int> coveringSorts = _htn.getArgumentSorts(coveringEffect);

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

void MethodEffectAnalyzer::computeArgumentIndependentGroundEffects(PossibleMethodEffects& effects) {
    for (const Signature& effect : effects.argumentIndependentLiftedEffectsForInference) {
        const std::vector<int> effectSorts = _htn.getArgumentSorts(effect._usig);
        BitVec& groundEffects = effect._negated
                ? effects.argumentIndependentNegative
                : effects.argumentIndependentPositive;
        addPossibleGroundEffect(groundEffects, effect, effectSorts);
    }
}

void MethodEffectAnalyzer::addPossibleGroundEffect(
        BitVec& groundEffects,
        const Signature& effect,
        const std::vector<int>& effectSorts) {
    if (_htn.isFullyGround(effect._usig)) {
        const int factId = _facts.getGroundFactId(effect._usig, effect._negated);
        if (factId >= 0) {
            groundEffects.set(factId);
        }
        return;
    }

    const std::vector<int>& sorts = effectSorts.empty()
            ? _htn.getSorts(effect._usig._name_id)
            : effectSorts;
    groundEffects.or_with(_facts.findMatchingGroundFactIds(effect._usig, effect._negated, sorts));
}

bool MethodEffectAnalyzer::hasMethodArgument(const Signature& effect) const {
    return std::ranges::any_of(effect._usig._args, [](int arg) { return arg < 0; });
}

std::vector<int> MethodEffectAnalyzer::makePlaceholders(size_t count) const {
    std::vector<int> placeholders(count);
    for (size_t index = 0; index < count; index++) {
        placeholders[index] = -static_cast<int>(index) - 1;
    }
    return placeholders;
}
