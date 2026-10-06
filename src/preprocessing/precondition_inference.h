
#ifndef SIBYLSAT_PRECONDITION_INFERENCE_H
#define SIBYLSAT_PRECONDITION_INFERENCE_H

#include "data/htn_instance.h"
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

    // Canonical arguments of the analysed operation and their sorts.
    struct ParameterDomains {
        const std::vector<int>& args;
        const std::vector<int>& sorts;
        int indexOf(int arg) const {
            for (size_t i = 0; i < args.size(); i++) if (args[i] == arg) return i;
            return -1;
        }
    };

    struct SubtaskOffsetSummary {
        SigSet preconditions;
        SigSet effects;
    };

    HtnInstance& _htn;
    NetworkTraversal _traversal;
    NodeHashMap<int, InferredPreconditions> _inferred_preconditions;

    explicit PreconditionInference(HtnInstance& htn) : _htn(htn), _traversal(htn) {}

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

        const ParameterDomains parameters{result.signature._args, _htn.getSorts(result.signature._name_id)};
        SigSet precedingEffects;
        for (size_t offset = 0; offset < reduction.getSubtasks().size(); offset++) {
            SubtaskOffsetSummary summary = inferSubtaskOffset(
                    reduction,
                    offset,
                    currentOps,
                    precedingEffects,
                    parameters);
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
            const SigSet& precedingEffects,
            const ParameterDomains& parameters) {
        SubtaskOffsetSummary summary;
        std::vector<USignature> children;
        _traversal.getPossibleChildren(reduction.getSubtasks(), offset, children);

        bool firstChild = true;
        for (const USignature& child : children) {
            const USignature normalizedChild = normalizeChildSignature(child);
            InferredPreconditions childInference = inferPreconditionsForOperation(normalizedChild, currentOps);

            if (firstChild) {
                addUnabsorbedPreconditions(summary.preconditions, childInference.preconditions, precedingEffects, parameters);
                firstChild = false;
            } else {
                intersectPreconditions(summary.preconditions, childInference.preconditions);
            }

            const SigSet possibleChildEffects = getPossibleChildEffects(normalizedChild);
            summary.effects.insert(possibleChildEffects.begin(), possibleChildEffects.end());
        }

        return summary;
    }

    SigSet getPossibleChildEffects(const USignature& child) {
        if (_htn.isAction(child)) {
            const Action action = _htn.toAction(child._name_id, child._args);
            return action.getEffects();
        }
        return _htn.getReductionTemplate(child._name_id).getPossibleEffectsForArguments(child._args);
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

    void addUnabsorbedPreconditions(SigSet& destination, const SigSet& preconditions, const SigSet& effects,
            const ParameterDomains& parameters) {
        for (const Signature& precondition : preconditions) {
            if (!isAbsorbedByEffect(precondition, effects, parameters)) {
                destination.insert(precondition);
            }
        }
    }

    // A preceding effect absorbs a precondition if it may produce it, i.e. if
    // their arguments may denote the same objects. Distinct parameters of the
    // analysed operation (canonical placeholders c0, c1, ...) may be bound to
    // the same object, so they must not be compared as distinct constants.
    bool isAbsorbedByEffect(const Signature& precondition, const SigSet& effects, const ParameterDomains& parameters) {
        for (const Signature& effect : effects) {
            if (effect._negated != precondition._negated) continue;
            if (effect._usig._name_id != precondition._usig._name_id) continue;
            if (effect._usig._args.size() != precondition._usig._args.size()) continue;
            bool mayMatch = true;
            for (size_t i = 0; mayMatch && i < effect._usig._args.size(); i++) {
                mayMatch = mayBeEqual(effect._usig._args[i], precondition._usig._args[i], parameters);
            }
            if (mayMatch) return true;
        }
        return false;
    }

    bool mayBeEqual(int a, int b, const ParameterDomains& parameters) {
        if (a == b || _htn.isVariable(a) || _htn.isVariable(b)) return true;
        const int indexA = parameters.indexOf(a), indexB = parameters.indexOf(b);
        if (indexA < 0 && indexB < 0) return false; // two distinct constants
        if (indexA < 0) return _htn.getConstantsOfSort(parameters.sorts[indexB]).count(a);
        if (indexB < 0) return _htn.getConstantsOfSort(parameters.sorts[indexA]).count(b);
        const FlatHashSet<int>& domainA = _htn.getConstantsOfSort(parameters.sorts[indexA]);
        const FlatHashSet<int>& domainB = _htn.getConstantsOfSort(parameters.sorts[indexB]);
        const FlatHashSet<int>& smaller = domainA.size() <= domainB.size() ? domainA : domainB;
        const FlatHashSet<int>& larger = domainA.size() <= domainB.size() ? domainB : domainA;
        for (int constant : smaller) if (larger.count(constant)) return true;
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
    static void infer(HtnInstance& htn, MinePrecMode mode) {
        if (mode == NO_MINING) return;

        PreconditionInference miner(htn);
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
