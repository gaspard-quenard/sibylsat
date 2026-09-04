#ifndef METHOD_EFFECT_ANALYSIS_H
#define METHOD_EFFECT_ANALYSIS_H

#include "algo/arg_iterator.h"
#include "algo/fact_analysis.h"
#include "algo/network_traversal.h"
#include "data/htn_instance.h"
#include "util/bitvec.h"

class MethodEffectAnalysis {
private:
    HtnInstance& _htn;
    FactAnalysis& _facts;
    NetworkTraversal _traversal;

    NodeHashMap<int, SigSet> _possible_effects;
    NodeHashMap<int, BitVec> _possible_ground_positive_effects;
    NodeHashMap<int, BitVec> _possible_ground_negative_effects;

public:
    MethodEffectAnalysis(HtnInstance& htn, FactAnalysis& facts);

    /** Returns the symbolic possible effects, substituting the arguments of this method occurrence. */
    SigSet getPossibleEffects(const USignature& method) const;

    /**
     * Returns possible effects that do not refer to method arguments. These effects
     * are grounded once per method template and reused by every occurrence.
     */
    const BitVec& getArgumentIndependentGroundEffects(const USignature& method, bool negated) const;

    /** Instantiates possible effects that refer to the arguments of this method occurrence. */
    SigSet instantiateArgumentDependentEffects(const USignature& method);

private:
    void computePossibleEffects(const Reduction& method);
    SigSet collectPossibleEffects(const USignature& method);
    void removeCoveredEffects(SigSet& effects);
    bool isCoveredBy(const USignature& effect, const USignature& coveringEffect) const;
    void computePossibleGroundEffects(const Reduction& method);
    void addPossibleGroundEffect(int methodId, const Signature& effect, const std::vector<int>& effectSorts);
    bool hasMethodArgument(const Signature& effect) const;
    bool hasValidGrounding(const USignature& effect, bool negated, const std::vector<int>& methodSorts);
    std::vector<int> makePlaceholders(size_t count) const;
    SigSet substituteEffects(const SigSet& effects, const Substitution& substitution) const;
};

#endif
