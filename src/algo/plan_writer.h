
#ifndef DOMPASCH_LILOTANE_PLAN_WRITER_H
#define DOMPASCH_LILOTANE_PLAN_WRITER_H

#include <filesystem>
#include <string>
#include <utility>

#include "data/htn_instance.h"
#include "data/plan.h"

class MacroActionCompiler;

class PlanWriter {

private:
    HtnInstance& _htn;
    const MacroActionCompiler* _macro_actions;
    const std::string _domain_filename;
    const std::string _problem_filename;
    const bool _verify_plan;
    const bool _write_plan;

public:
    PlanWriter(HtnInstance& htn, const MacroActionCompiler* macroActions, std::string domainFilename, std::string problemFilename, bool verifyPlan, bool writePlan)
        : _htn(htn), _macro_actions(macroActions), _domain_filename(std::move(domainFilename)), _problem_filename(std::move(problemFilename)), _verify_plan(verifyPlan), _write_plan(writePlan) {}

    /** Normalize the decoded plan, convert it to the original problem, optionally verify and save it, and print it. */
    void outputPlan(const Plan& decodedPlan);

private:
    /** Return an ID greater than every item and subtask ID already present in the plan. */
    int findNextPlanItemId(const Plan& plan) const;

    /** Return whether an internal action was produced by macro compilation. */
    bool isMacroAction(const USignature& action) const;

    /** Reconstruct the primitive sequence represented by a selected macro action. */
    std::vector<USignature> expandMacroAction(const USignature& macroAction);

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

    /** Ask PandaPIparser to remove names introduced by its transformations from the internal plan. */
    std::string convertPlanToOriginalProblem(const std::string& internalPlan) const;

    /** Write a plan and its closing marker to a file. */
    void writePlanFile(const std::filesystem::path& path, const std::string& planText) const;

    /** Verify a converted plan with a separate, unsimplified PandaPIparser process. */
    bool verifyPlan(const std::string& planText) const;
};

#endif
