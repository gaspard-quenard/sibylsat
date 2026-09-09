#ifndef SIBYLSAT_METHOD_EFFECT_ANALYZER_H
#define SIBYLSAT_METHOD_EFFECT_ANALYZER_H

#include "algo/fact_analysis.h"
#include "algo/network_traversal.h"
#include "data/htn_instance.h"
#include "util/bitvec.h"

/** Computes the possible-effect summaries attached to reduction templates. */
class MethodEffectAnalyzer {
private:
    HtnInstance& _htn;
    FactAnalysis& _facts;
    NetworkTraversal _traversal;

public:
    /**
     * Compute every method template's possible effects and attach the resulting
     * immutable summary to its Reduction.
     */
    static void analyze(HtnInstance& htn, FactAnalysis& facts);

private:
    MethodEffectAnalyzer(HtnInstance& htn, FactAnalysis& facts);
    void analyzeMethod(Reduction& method);
    SigSet collectPossibleEffects(const USignature& method);
    void removeCoveredEffects(SigSet& effects);
    bool isCoveredBy(const USignature& effect, const USignature& coveringEffect) const;
    void computeArgumentIndependentGroundEffects(PossibleMethodEffects& effects);
    void addPossibleGroundEffect(BitVec& groundEffects, const Signature& effect, const std::vector<int>& effectSorts);
    bool hasMethodArgument(const Signature& effect) const;
    std::vector<int> makePlaceholders(size_t count) const;
};

#endif
