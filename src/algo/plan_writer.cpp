// PandaPIparser
#include "plan.hpp"

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <sstream>
#include <stdexcept>

#include "algo/plan_writer.h"
#include "preprocessing/macro_action_compiler.h"
#include "util/log.h"
#include "util/process_utils.h"
#include "util/project_utils.h"

int PlanWriter::findNextPlanItemId(const Plan& plan) const {
    int nextPlanItemId = 1;
    for (const auto& planPart : {std::cref(plan.first), std::cref(plan.second)}) {
        for (const PlanItem& item : planPart.get()) {
            nextPlanItemId = std::max(nextPlanItemId, item.id + 1);
            for (int subtaskId : item.subtaskIds) nextPlanItemId = std::max(nextPlanItemId, subtaskId + 1);
        }
    }
    return nextPlanItemId;
}

bool PlanWriter::isMacroAction(const USignature& action) const {
    return _macro_actions != nullptr && _macro_actions->isMacroAction(_htn.toString(action._name_id));
}

std::vector<USignature> PlanWriter::expandMacroAction(const USignature& macroAction) {
    const MacroActionExpansion& expansion = _macro_actions->getExpansion(_htn.toString(macroAction._name_id));
    std::vector<USignature> actions;
    actions.reserve(expansion.primitiveSteps.size());
    for (const MacroPrimitiveStep& step : expansion.primitiveSteps) {
        std::vector<int> arguments;
        arguments.reserve(step.macroArgumentIndices.size());
        for (size_t argumentIndex : step.macroArgumentIndices) arguments.push_back(macroAction._args.at(argumentIndex));
        actions.emplace_back(_htn.nameId(step.actionName), std::move(arguments));
    }
    return actions;
}

Plan PlanWriter::normalizePlanForOutput(const Plan& decodedPlan) {
    Plan normalizedPlan;
    auto& [normalizedActions, normalizedHierarchy] = normalizedPlan;
    int nextPlanItemId = findNextPlanItemId(decodedPlan);

    // Removed actions map to no IDs; macro actions map to their expanded action IDs.
    FlatHashMap<int, std::vector<int>> actionIdReplacements;
    // Other hierarchy nodes must refer to the restored reduction, while that
    // reduction itself must continue to refer to its primitive child action.
    FlatHashMap<int, int> primitivizedActionParents;
    std::vector<PlanItem> restoredReductions;

    for (const PlanItem& decodedAction : decodedPlan.first) {
        if (decodedAction.id < 0) continue;

        if (_htn.isSecondSplitAction(decodedAction.abstractTask._name_id)) {
            actionIdReplacements[decodedAction.id] = {};
            continue;
        }

        PlanItem normalizedAction = decodedAction;
        if (_htn.isPrimitivizedAction(normalizedAction.abstractTask._name_id)) {
            const int reductionId = _htn.getReductionAndActionFromPrimitivization(normalizedAction.abstractTask._name_id).first;
            const Reduction reduction = _htn.toReduction(reductionId, normalizedAction.abstractTask._args);

            PlanItem restoredReduction;
            restoredReduction.id = nextPlanItemId++;
            restoredReduction.abstractTask = reduction.getTaskSignature();
            restoredReduction.reduction = reduction.getSignature();
            restoredReduction.subtaskIds = {normalizedAction.id};
            restoredReductions.push_back(std::move(restoredReduction));
            primitivizedActionParents[normalizedAction.id] = restoredReductions.back().id;

            normalizedAction.abstractTask = reduction.getSubtasks().front();
            normalizedAction.reduction = normalizedAction.abstractTask;
        }

        if (isMacroAction(normalizedAction.abstractTask)) {
            std::vector<int>& replacementIds = actionIdReplacements[normalizedAction.id];
            for (const USignature& action : expandMacroAction(normalizedAction.abstractTask)) {
                const int actionId = nextPlanItemId++;
                normalizedActions.emplace_back(actionId, action, action, std::vector<int>());
                replacementIds.push_back(actionId);
            }
        } else {
            normalizedActions.push_back(std::move(normalizedAction));
        }
    }

    std::vector<PlanItem> hierarchy = decodedPlan.second;
    hierarchy.insert(hierarchy.end(), restoredReductions.begin(), restoredReductions.end());
    normalizedHierarchy.reserve(hierarchy.size());

    for (PlanItem& item : hierarchy) {
        if (item.id < 0) continue;

        std::vector<int> normalizedSubtaskIds;
        for (int subtaskId : item.subtaskIds) {
            const auto parent = primitivizedActionParents.find(subtaskId);
            if (parent != primitivizedActionParents.end() && item.id != parent->second) subtaskId = parent->second;

            const auto replacements = actionIdReplacements.find(subtaskId);
            if (replacements == actionIdReplacements.end()) normalizedSubtaskIds.push_back(subtaskId);
            else normalizedSubtaskIds.insert(normalizedSubtaskIds.end(), replacements->second.begin(), replacements->second.end());
        }
        item.subtaskIds = std::move(normalizedSubtaskIds);
        normalizedHierarchy.push_back(std::move(item));
    }

    return normalizedPlan;
}

std::string PlanWriter::serializeNormalizedPlan(const Plan& normalizedPlan) {
    std::ostringstream stream;
    stream << "==>\n";

    FlatHashSet<int> actionIds;
    for (const PlanItem& action : normalizedPlan.first) {
        actionIds.insert(action.id);
        if (!isPrintableAction(action)) continue;
        stream << action.id << " " << Names::to_string_nobrackets(_htn.restoreOriginalTaskArity(action.abstractTask)) << "\n";
    }

    bool writeRoot = true;
    for (const PlanItem& item : normalizedPlan.second) {
        if (writeRoot) {
            stream << "root";
            for (int subtaskId : item.subtaskIds) stream << " " << subtaskId;
            stream << "\n";
            writeRoot = false;
            continue;
        }
        if (item.id <= 0 || actionIds.count(item.id)) continue;

        stream << item.id << " " << Names::to_string_nobrackets(_htn.restoreOriginalTaskArity(item.abstractTask))
                << " -> " << Names::to_string_nobrackets(item.reduction);
        for (int subtaskId : item.subtaskIds) stream << " " << subtaskId;
        stream << "\n";
    }
    stream << "<==\n";
    return stream.str();
}

bool PlanWriter::isPrintableAction(const PlanItem& action) const {
    return action.abstractTask != _htn.getBlankActionSig()
            && action.abstractTask._name_id != _htn.nameId("<goal_action>");
}

size_t PlanWriter::countPrintableActions(const Plan& normalizedPlan) const {
    return std::count_if(normalizedPlan.first.begin(), normalizedPlan.first.end(),
            [this](const PlanItem& action) { return isPrintableAction(action); });
}

std::string PlanWriter::convertPlanToOriginalProblem(const std::string& internalPlan) const {
    std::istringstream input(internalPlan);
    std::ostringstream output;
    convert_plan(input, output);
    return output.str();
}

void PlanWriter::writePlanFile(const std::filesystem::path& path, const std::string& planText) const {
    std::ofstream file(path);
    if (!file) throw std::runtime_error("Could not open plan file: " + path.string());
    file << planText << "<==\n";
}

bool PlanWriter::verifyPlan(const std::string& planText) const {
    TemporaryFile temporaryPlan("sibylsat-plan-");
    writePlanFile(temporaryPlan.getPath(), planText);

    const std::filesystem::path parser = getProjectRootDir() / "lib" / "pandaPIparserOriginal";
    const std::string command = quoteShellArgument(parser.string()) + " -C --verify "
            + quoteShellArgument(_domain_filename) + " "
            + quoteShellArgument(_problem_filename) + " "
            + quoteShellArgument(temporaryPlan.getPath().string());
    return commandSucceedsAndOutputContains(command, "Plan verification result: true");
}


void PlanWriter::outputPlan(const Plan& decodedPlan) {
    const Plan normalizedPlan = normalizePlanForOutput(decodedPlan);
    const std::string internalPlan = serializeNormalizedPlan(normalizedPlan);
    const std::string originalPlan = convertPlanToOriginalProblem(internalPlan);

    if (_verify_plan) {
        if (!verifyPlan(originalPlan)) {
            Log::e("ERROR: Plan declared invalid by pandaPIparser! Exiting.\n");
            std::exit(1);
        }
        Log::i("Plan has been verified by pandaPIparser\n");
    }


    if (_write_plan) {
        const std::filesystem::path planPath = "plan.txt";
        Log::i("Writing plan to file %s\n", planPath.string().c_str());
        writePlanFile(planPath, originalPlan);
    }

    size_t planLength = countPrintableActions(normalizedPlan);

    Log::log_notime(Log::V0_ESSENTIAL, "%s", originalPlan.c_str());
    Log::log_notime(Log::V0_ESSENTIAL, "<==\n");
    Log::i("End of solution plan. (counted length of %zu)\n", planLength);
}
