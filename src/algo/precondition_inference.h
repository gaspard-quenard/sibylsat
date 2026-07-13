
#ifndef DOMPASCH_LILOTANE_PRECONDITION_INFERENCE_H
#define DOMPASCH_LILOTANE_PRECONDITION_INFERENCE_H

#include "data/htn_instance.h"
#include "algo/method_effect_analysis.h"
#include "algo/network_traversal.h"

class PreconditionInference {

private:
    struct InferredPreconditions {
        USignature signature;
        SigSet preconditions;

        InferredPreconditions substitute(const Substitution& substitution) const {
            InferredPreconditions result;
            result.signature = signature.substitute(substitution);
            for (const Signature& precondition : preconditions) {
                result.preconditions.insert(precondition.substitute(substitution));
            }
            return result;
        }
    };

    struct SubtaskOffsetSummary {
        SigSet preconditions;
        SigSet effects;
    };

    HtnInstance& _htn;
    MethodEffectAnalysis& _method_effects;
    NetworkTraversal _traversal;
    NodeHashMap<int, InferredPreconditions> _inferred_preconditions;

    PreconditionInference(HtnInstance& htn, MethodEffectAnalysis& methodEffects)
        : _htn(htn), _method_effects(methodEffects), _traversal(htn) {}

    SigSet inferPreconditions(const USignature& op) {
        USigSet currentOps;
        return inferPreconditionsForOperation(op, currentOps).preconditions;
    }

    InferredPreconditions inferPreconditionsForOperation(const USignature& sig, USigSet& currentOps) {
        int nameId = sig._name_id;
        if (!_inferred_preconditions.count(nameId)) {
            InferredPreconditions preconditions = computePreconditionsForOperation(sig, currentOps);
            _inferred_preconditions[nameId] = std::move(preconditions);
        }

        const InferredPreconditions& preconditions = _inferred_preconditions.at(nameId);
        return preconditions.substitute(Substitution(preconditions.signature._args, sig._args));
    }

    InferredPreconditions computePreconditionsForOperation(const USignature& sig, USigSet& currentOps) {
        InferredPreconditions result;
        result.signature = makeCanonicalSignature(sig);

        if (_htn.isAction(result.signature)) {
            const Action& action = _htn.toAction(result.signature._name_id, result.signature._args);
            result.preconditions = action.getPreconditions();
            return result;
        }

        if (currentOps.count(result.signature)) {
            const Reduction& reduction = _htn.toReduction(result.signature._name_id, result.signature._args);
            result.preconditions = reduction.getPreconditions();
            _htn.addRecursiveMethod(result.signature._name_id);
            return result;
        }

        currentOps.insert(result.signature);
        const Reduction& reduction = _htn.toReduction(result.signature._name_id, result.signature._args);
        result.preconditions.insert(reduction.getPreconditions().begin(), reduction.getPreconditions().end());

        SigSet precedingEffects;
        for (size_t offset = 0; offset < reduction.getSubtasks().size(); offset++) {
            SubtaskOffsetSummary summary = inferSubtaskOffset(
                    reduction,
                    offset,
                    currentOps,
                    precedingEffects);
            result.preconditions.insert(summary.preconditions.begin(), summary.preconditions.end());
            precedingEffects.insert(summary.effects.begin(), summary.effects.end());
        }

        currentOps.erase(result.signature);
        return result;
    }

    SubtaskOffsetSummary inferSubtaskOffset(
            const Reduction& reduction,
            size_t offset,
            USigSet& currentOps,
            const SigSet& precedingEffects) {
        SubtaskOffsetSummary summary;
        std::vector<USignature> children;
        _traversal.getPossibleChildren(reduction.getSubtasks(), offset, children);

        bool firstChild = true;
        for (const USignature& child : children) {
            const USignature normalizedChild = normalizeChildSignature(child);
            InferredPreconditions childInference = inferPreconditionsForOperation(normalizedChild, currentOps);

            if (firstChild) {
                addUnabsorbedPreconditions(summary.preconditions, childInference.preconditions, precedingEffects);
                firstChild = false;
            } else {
                intersectPreconditions(summary.preconditions, childInference.preconditions);
            }

            const SigSet childEffects = _method_effects.getEffects(normalizedChild);
            summary.effects.insert(childEffects.begin(), childEffects.end());
        }

        return summary;
    }

    USignature makeCanonicalSignature(const USignature& sig) {
        std::vector<int> args(sig._args.size());
        for (size_t i = 0; i < sig._args.size(); i++) {
            args[i] = _htn.nameId("c" + std::to_string(i));
        }
        return USignature(sig._name_id, std::move(args));
    }

    USignature normalizeChildSignature(const USignature& child) {
        std::vector<int> args(child._args);
        for (size_t i = 0; i < args.size(); i++) {
            if (_htn.isVariable(args[i])) {
                args[i] = _htn.nameId("??_");
            }
        }
        return USignature(child._name_id, std::move(args));
    }

    void addUnabsorbedPreconditions(SigSet& destination, const SigSet& preconditions, const SigSet& effects) {
        for (const Signature& precondition : preconditions) {
            if (!isAbsorbedByEffect(precondition, effects)) {
                destination.insert(precondition);
            }
        }
    }

    bool isAbsorbedByEffect(const Signature& precondition, const SigSet& effects) {
        for (const Signature& effect : effects) {
            if (_htn.isUnifiable(effect, precondition) || _htn.isUnifiable(precondition, effect)) {
                return true;
            }
        }
        return false;
    }

    void intersectPreconditions(SigSet& currentIntersection, const SigSet& childPreconditions) {
        SigSet intersection;
        for (const Signature& precondition : childPreconditions) {
            if (currentIntersection.count(precondition)) {
                intersection.insert(precondition);
            }
        }
        currentIntersection = std::move(intersection);
    }

public:
    enum MinePrecMode { NO_MINING, USE_FOR_INSTANTIATION, USE_EVERYWHERE };
    static void infer(HtnInstance& htn, MethodEffectAnalysis& methodEffects, MinePrecMode mode) {
        if (mode == NO_MINING) return;

        PreconditionInference miner(htn, methodEffects);
        int precondsBefore = 0;
        int minedPreconds = 0;
        int initRedId = htn.getInitReduction().getSignature()._name_id;
        for (auto& [rId, r] : htn.getReductionTemplates()) {
            if (initRedId == rId) continue; // FIXME Skip init reduction

            precondsBefore += r.getPreconditions().size();
            // Mine additional preconditions, if possible
            for (auto& pre : miner.inferPreconditions(r.getSignature())) {
                if (r.getPreconditions().count(pre)) continue;
                    
                bool hasFreeArgs = false;
                for (int arg : pre._usig._args) {
                    hasFreeArgs |= arg == htn.nameId("??_");
                    //if (!hasFreeArgs) assert(std::find(r.getSignature()._args.begin(), r.getSignature()._args.end(), arg) != r.getSignature()._args.end());
                }
                if (hasFreeArgs) continue;

                Log::d("%s : MINED_PRE %s\n", TOSTR(r.getSignature()), TOSTR(pre));
                if (mode == USE_FOR_INSTANTIATION) {
                    r.addExtraPrecondition(std::move(pre));
                }
                if (mode == USE_EVERYWHERE) {
                    r.addPrecondition(std::move(pre));
                }
                minedPreconds++;
            }
        }

        float newRatio = precondsBefore == 0 ? std::numeric_limits<float>::infinity() : 
                100.f * (((float)precondsBefore+minedPreconds) / precondsBefore - 1);

        Log::i("Mined %i new reduction preconditions (+%.1f%%).\n", minedPreconds, newRatio);
    }

};

#endif
