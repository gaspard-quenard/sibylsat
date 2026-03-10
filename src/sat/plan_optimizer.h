
#ifndef DOMPASCH_LILOTANE_PLAN_OPTIMIZER_H
#define DOMPASCH_LILOTANE_PLAN_OPTIMIZER_H

#include "data/position.h"
#include "data/htn_instance.h"
#include "data/plan.h"
#include "sat/sat_interface.h"
#include "sat/variable_provider.h"
#include "sat/encoding.h"

class PlanOptimizer {

private:
    HtnInstance& _htn;
    std::vector<Position*>& _leaf_positions;
    Encoding& _enc;
    SatInterface& _sat;
    Statistics& _stats;

public:
    PlanOptimizer(HtnInstance& htn, std::vector<Position*>& leafPositions, Encoding& enc) : 
            _htn(htn), _leaf_positions(leafPositions), _enc(enc), 
            _sat(_enc.getSatInterface()), _stats(Statistics::getInstance()) {}

    enum ConstraintAddition { TRANSIENT, PERMANENT };

    void optimizePlan(int upperBound, Plan& plan, ConstraintAddition mode);

    int findMinBySat(int lower, int upper, std::function<int(int)> varMap, 
                std::function<int(void)> boundUpdateOnSat, ConstraintAddition mode);

    bool isEmptyAction(const USignature& aSig);
    int getPlanLength(const std::vector<PlanItem>& classicalPlan);
};

#endif
