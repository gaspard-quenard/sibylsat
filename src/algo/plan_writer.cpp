
// PandaPIparser
#include "plan.hpp"
#include "verify.hpp"
#include <filesystem>

#include "sat/variable_domain.h"
#include "algo/plan_writer.h"
#include "util/project_utils.h"

bool checkCommandOutput(const std::string& command, const std::string& searchString) {
    std::array<char, 128> buffer;
    std::string result;
    std::shared_ptr<FILE> pipe(popen(command.c_str(), "r"), pclose);
    if (!pipe) throw std::runtime_error("popen() failed!");

    while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
        result += buffer.data();
    }

    return result.find(searchString) != std::string::npos;
}

void PlanWriter::outputPlan(Plan& _plan) {

    // Create stringstream which is being fed the plan
    std::stringstream stream;

    // Print plan into stream

    // -- primitive part
    stream << "==>\n";
    FlatHashSet<int> actionIds;
    FlatHashSet<int> idsToRemove;

    FlatHashSet<int> primitivizationIds;
    std::vector<PlanItem> decompsToInsert;
    size_t decompsToInsertIdx = 0;
    size_t length = 0;

    // When using macroActions (with flag macroActions), we need to keep track of the macro actions and their corresponding actions
    std::map<int, std::vector<int>> id_macro_action_to_id_actions;
    
    for (PlanItem& item : std::get<0>(_plan)) {

        if (item.id < 0) continue;
        
        if (_htn.toString(item.abstractTask._name_id).rfind("__LLT_SECOND") != std::string::npos) {
            // Second part of a split action: discard
            idsToRemove.insert(item.id);
            continue;
        }
        
        if (_htn.toString(item.abstractTask._name_id).rfind("__SURROGATE") != std::string::npos) {
            // Primitivized reduction: Replace with actual action, remember represented method to include in decomposition

            [[maybe_unused]] const auto& [parentId, childId] = _htn.getReductionAndActionFromPrimitivization(item.abstractTask._name_id);
            const Reduction& parentRed = _htn.toReduction(parentId, item.abstractTask._args);
            primitivizationIds.insert(item.id);
            
            PlanItem parent;
            parent.abstractTask = parentRed.getTaskSignature();  
            parent.id = item.id-1;
            parent.reduction = parentRed.getSignature();
            parent.subtaskIds = std::vector<int>(1, item.id);
            decompsToInsert.push_back(parent);

            const USignature& childSig = parentRed.getSubtasks()[0];
            item.abstractTask = childSig;
        }

        actionIds.insert(item.id);

        // Do not write blank actions or the virtual goal action
        if (item.abstractTask == _htn.getBlankActionSig()) continue;
        if (item.abstractTask._name_id == _htn.nameId("<goal_action>")) continue;

        if (_htn.isMacroTask(item.abstractTask._name_id)) {
            // Reconstruct the sequences of actions from the macro
            std::vector<USignature> actions = _htn.getActionsFromMacro(item.abstractTask);
            id_macro_action_to_id_actions[item.id] = std::vector<int>();
            for (const USignature& action: actions) {
                int id = VariableDomain::nextVar();
                stream << id << " " << Names::to_string_nobrackets(action) << "\n";
                id_macro_action_to_id_actions[item.id].push_back(id);
                length++;
            }
        } else {
            stream << item.id << " " << Names::to_string_nobrackets(_htn.cutNonoriginalTaskArguments(item.abstractTask)) << "\n";
            length++;
        }
        
    }
    // -- decomposition part
    bool root = true;
    for (size_t itemIdx = 0; itemIdx < _plan.second.size() || decompsToInsertIdx < decompsToInsert.size(); itemIdx++) {

        // Pick next plan item to print
        PlanItem item;
        if (decompsToInsertIdx < decompsToInsert.size() && (itemIdx >= _plan.second.size() || decompsToInsert[decompsToInsertIdx].id < _plan.second[itemIdx].id)) {
            // Pick plan item from primitivized decompositions
            item = decompsToInsert[decompsToInsertIdx];
            decompsToInsertIdx++;
            itemIdx--;
        } else {
            // Pick plan item from "normal" plan list
            item = _plan.second[itemIdx];
        }
        if (item.id < 0) continue;

        std::string subtaskIdStr = "";
        for (int subtaskId : item.subtaskIds) {
            if (item.id+1 != subtaskId && primitivizationIds.count(subtaskId)) subtaskId--;
            if (!idsToRemove.count(subtaskId)) {
                if (id_macro_action_to_id_actions.count(subtaskId)) {
                    for (int id_action: id_macro_action_to_id_actions[subtaskId]) {
                        subtaskIdStr += " " + std::to_string(id_action);
                    }
                } else {
                    subtaskIdStr += " " + std::to_string(subtaskId);
                }
            }
        }
        
        if (root) {
            stream << "root " << subtaskIdStr << "\n";
            root = false;
            continue;
        } else if (item.id <= 0 || actionIds.count(item.id)) continue;
        
        stream << item.id << " " << Names::to_string_nobrackets(_htn.cutNonoriginalTaskArguments(item.abstractTask)) << " -> " 
            << Names::to_string_nobrackets(item.reduction) << subtaskIdStr << "\n";
    }
    stream << "<==\n";

    // Feed plan into parser to convert it into a plan to the original problem
    // (w.r.t. previous compilations the parser did)
    std::ostringstream outstream;
    convert_plan(stream, outstream);
    std::string planStr = outstream.str();

    if (_params.isNonzero("vp")) {
        // Verify plan (by copying converted plan stream and putting it back into panda)
        // std::stringstream verifyStream;
        // verifyStream << planStr << std::endl;
        // bool ok = verify_plan(verifyStream, /*useOrderingInfo=*/true, /*lenientMode=*/false, /*debugMode=*/0);
        // if (!ok) {
        //     Log::e("ERROR: Plan declared invalid by pandaPIparser! Exiting.\n");
        //     exit(1);
        // }

        // There is a problem with using the above function for some domain (e.g assembly hierarchical... So we use the executable instead)
        // Explanation: see libmain.cpp in pandaLib. When we parse the problem, we simplify some of its sorts.
        // But in the file, they verify the plan before the simplification... So we cannot use the function
        // verify_plan unless we redo the parsing without the simplification...

        std::ofstream file("plan.txt");
        file << planStr;
        file << "<==\n";
        file.flush();

        // Now run pandaPiParser with the plan.txt file
        std::filesystem::path current_path = getProjectRootDir();

        // Path parser
        filesystem::path filesystem_full_path_parser = current_path / "lib" / "pandaPIparserOriginal";
        std::string full_path_parser = filesystem_full_path_parser.string();

        // -C for no color output
        std::string command = full_path_parser + " -C --verify " + _htn.getParams().getDomainFilename() + " " + _htn.getParams().getProblemFilename() + " plan.txt";

        // Check if the output contains the desired string
        if (checkCommandOutput(command, "Plan verification result: true")) {
            Log::i("Plan has been verified by pandaPIparser\n");
        } else {
            Log::e("ERROR: Plan declared invalid by pandaPIparser! Exiting.\n");
            exit(1);
        }

        // remove the plan.txt file
        std::remove("plan.txt");
    }

    // Write plan to file
    if (_params.isNonzero("wp")) {
        std::string planFile = "plan.txt";
        Log::i("Writing plan to file %s\n", planFile.c_str());
        std::ofstream file(planFile);
        file << planStr;
        file << "<==\n";
        file.flush();
        file.close();
    }
    
    // Print plan
    Log::log_notime(Log::V0_ESSENTIAL, planStr.c_str());
    Log::log_notime(Log::V0_ESSENTIAL, "<==\n");
    
    Log::i("End of solution plan. (counted length of %i)\n", length);
}
