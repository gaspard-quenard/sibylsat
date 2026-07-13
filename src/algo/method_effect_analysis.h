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

    NodeHashMap<int, SigSet> _effects;
    NodeHashMap<int, BitVec> _ground_positive_effects;
    NodeHashMap<int, BitVec> _ground_negative_effects;
    BitVec _empty_ground_effects;

public:
    MethodEffectAnalysis(HtnInstance& htn, FactAnalysis& facts);

    SigSet getEffects(const USignature& operation) const;
    const BitVec& getGroundEffects(const USignature& operation, bool negated) const;
    SigSet instantiateEffects(const USignature& operation);

private:
    void computeEffects(const Reduction& method);
    SigSet collectEffects(const USignature& method);
    void removeCoveredEffects(SigSet& effects);
    bool isCoveredBy(const USignature& effect, const USignature& coveringEffect) const;
    void computeGroundEffects(const Reduction& method);
    void addGroundEffect(int methodId, const Signature& effect, const std::vector<int>& effectSorts);
    bool hasMethodArgument(const Signature& effect) const;
    bool hasValidGrounding(const USignature& effect, bool negated, const std::vector<int>& methodSorts);
    std::vector<int> makePlaceholders(size_t count) const;
    SigSet substituteEffects(const SigSet& effects, const Substitution& substitution) const;
};

#endif
