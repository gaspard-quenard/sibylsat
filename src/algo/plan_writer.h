
#ifndef DOMPASCH_LILOTANE_PLAN_WRITER_H
#define DOMPASCH_LILOTANE_PLAN_WRITER_H

#include <filesystem>
#include <string>

#include "data/htn_instance.h"
#include "data/plan.h"

class PlanWriter {

private:
    HtnInstance& _htn;
    Parameters& _params;

public:
    PlanWriter(HtnInstance& htn, Parameters& params) : _htn(htn), _params(params) {}

    /** Normalize the decoded plan, convert it to the original problem, optionally verify and save it, and print it. */
    void outputPlan(const Plan& decodedPlan);

private:
    /** Return an ID greater than every item and subtask ID already present in the plan. */
    int findNextPlanItemId(const Plan& plan) const;

    /**
     * Convert the decoded internal plan into printable operations: discard the
     * second halves of split actions, restore reductions hidden by surrogate
     * actions, expand macro actions, and rewrite affected hierarchy references.
     */
    Plan normalizePlanForOutput(const Plan& decodedPlan);

    /** Serialize a normalized plan in the hierarchical plan format expected by PandaPIparser. */
    std::string serializeNormalizedPlan(const Plan& normalizedPlan);

    /** Return whether an action is part of the printed plan rather than blank or goal bookkeeping. */
    bool isPrintableAction(const PlanItem& action) const;

    /** Count the primitive action lines that will be printed from a normalized plan. */
    size_t countPrintableActions(const Plan& normalizedPlan) const;

    /** Use PandaPIparser's conversion metadata to map an internal plan back to the original problem. */
    std::string convertPlanToOriginalProblem(const std::string& internalPlan) const;

    /** Write a plan and its closing marker to a file. */
    void writePlanFile(const std::filesystem::path& path, const std::string& planText) const;

    /** Verify a converted plan with a separate, unsimplified PandaPIparser process. */
    bool verifyPlan(const std::string& planText) const;
};

#endif
