
#ifndef DOMPASCH_TREE_REXX_ENCODING_H
#define DOMPASCH_TREE_REXX_ENCODING_H

extern "C" {
    #include "sat/ipasir.h"
}

#include <initializer_list>
#include <fstream>
#include <string>
#include <iostream>

#include "data/layer.h"
#include "data/signature.h"
#include "data/htn_instance.h"
#include "data/action.h"
#include "sat/variable_domain.h"

#define PRINT_TO_FILE true

typedef std::unordered_map<int, SigSet> State;

struct PlanItem {
    int id;
    Signature abstractTask;
    Signature reduction;
    std::vector<int> subtaskIds;
};

class Encoding {

private:
    HtnInstance& _htn;
    std::vector<Layer>& _layers;
    
    std::unordered_map<Signature, int, SignatureHasher> _substitution_variables;

    void* _solver;
    std::ofstream _out;

    Signature _sig_primitive;
    int _substitute_name_id;

    std::unordered_set<int> _q_constants;
    std::unordered_map<int, std::vector<int>> _q_constants_per_arg;

    bool _var_domain_locked = false;

public:
    Encoding(HtnInstance& htn, std::vector<Layer>& layers);
    ~Encoding();

    void encode(int layerIdx, int pos);
    bool solve();




    /*
    void addInitialClauses(Layer& initLayer);
    void addUniversalClauses(Layer& layer);
    void addTransitionalClauses(Layer& oldLayer, Layer& newLayer);
    */
    void addInitialTaskAlternatives(Layer& layer, int pos); 

    void addAction(Action& a, Layer& layer, int pos);
    void addAction(Action& a, Reduction& parent, Layer& oldLayer, int oldPos, Layer& newLayer, int newPos);
    void propagateAction(Action& a, Layer& oldLayer, int oldPos, Layer& newLayer, int newPos);

    void addReduction(Reduction& r, SigSet& allFactChanges, Layer& layer, int pos);
    void addReduction(Reduction& child, Reduction& parent, SigSet& allFactChanges, 
                        Layer& oldLayer, int oldPos, Layer& newLayer, int newPos);
    void consolidateReductionExpansion(Reduction& r, Layer& oldLayer, int oldPos, Layer& newLayer, int newPos);
    
    void consolidateHtnOps(Layer& layer, int pos);

    void addTrueFacts(SigSet& facts, Layer& layer, int pos);
    void propagateFacts(Layer& oldLayer, int oldPos, Layer& newLayer, int newPos);
    void consolidateFacts(Layer& oldLayer, int oldPos, Layer& newLayer, int newPos);

    void addAssumptions(Layer& layer);

    bool solve();

    std::vector<PlanItem> extractClassicalPlan(Layer& finalLayer);
    std::vector<PlanItem> extractDecompositionPlan(std::vector<Layer>& allLayers);

    void printFailedVars(Layer& layer);

private:

    Signature sigSubstitute(int qConstId, int trueConstId) {
        assert(!_htn._q_constants.count(trueConstId) || trueConstId < qConstId);
        std::vector<int> args(2);
        args[0] = (qConstId);
        args[1] = (trueConstId);
        return Signature(_substitute_name_id, args);
    }

    std::vector<int>& getSupport(int factVar) {
        assert(_supports.count(factVar));
        return _supports[factVar];
    }
    void addToSupport(int factVar, int opVar) {
        if (!_supports.count(factVar)) _supports[factVar];
        _supports[factVar].push_back(opVar);
    }
    /*
    int getNearestPriorOccurrence(Signature factSig, int pos) {
        for (int posBefore = pos-1; posBefore >= 0; posBefore--) {
            if (_occurring_facts[posBefore].count(factSig._name_id)) {
                if (_occurring_facts[posBefore][factSig._name_id].count(factSig)) {
                    return posBefore;
                }
                factSig.negate();
                if (_occurring_facts[posBefore][factSig._name_id].count(factSig)) {
                    return posBefore;
                }
                factSig.negate();
            }
        }
        return -1;
    }
    */
    
    std::vector<int>& getExpansion(int redVar, int offset) {
        assert(_expansions.count(redVar));
        assert(offset < _expansions[redVar].size());
        return _expansions[redVar][offset];
    }
    void addToExpansion(int redVar, int opVar, int offset) {
        if (!_expansions.count(redVar)) _expansions[redVar];
        while (offset >= _expansions[redVar].size()) _expansions[redVar].push_back(std::vector<int>());
        _expansions[redVar][offset].push_back(opVar);
    }

    void addClause(std::initializer_list<int> lits);
    void appendClause(std::initializer_list<int> lits);
    void endClause();
    void assume(int lit);

    bool isEncoded(int layer, int pos, Signature& sig);
    bool isEncodedSubstitution(Signature& sig);
    int var(int layer, int pos, Signature& sig);
    int varPrimitive(int layer, int pos);
    int varSubstitution(Signature sigSubst);

    std::string varName(int layer, int pos, Signature& sig);
    void printVar(int layer, int pos, Signature& sig);

    bool value(int layer, int pos, Signature& sig);
    Signature getDecodedQOp(int layer, int pos, Signature sig);
    void checkAndApply(Action& a, SigSet& state, SigSet& newState, int layer, int pos);

};

#endif