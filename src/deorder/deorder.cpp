#include "deorder/deorder.h"

#include <sys/resource.h>
#include <iostream>
#include <iomanip>
#include <sstream>
#include <algorithm>
#include <filesystem>
#include <queue>
#include <set>
#include <map>
#include "verify.hpp"
#include "parsetree.hpp"
#include "util.hpp"
#include "cwa.hpp"
#include "plan.hpp"

#include "deorder/algo/deorder_algo_SAT.h"
#include "deorder/algo/deorder_algo_PRF.h"

Deorder::Deorder(const std::string &planFile,
                 HtnInstance &htn,
                 DeorderAlgoType algoType,
                 DeorderMode mode) : _htn(htn), _plan_str(planFile)
{
    ifstream plan(planFile);

    map<int, vector<pair<map<string, int>, map<string, string>>>> possibleMethodInstantiations;
    map<int, map<string, string>> chosen_method_matchings;
    vector<pair<int, int>> chosen_non_unique_matchings;
    set<vector<pair<int, int>>> forbidden_matchings;

    // Verify the plan, and get the methods parameters
    // Store the possible method instantiations for later use in hierarchy constraints

    // We MUST relaunch pandaPiParser. Because we launch it with htnInstance class, it did some modification on the global structures in the parser
    // which prevent it from verify the plan afterward... Very ugly...
    clear_parser_data_structures();
    const char *firstArg = "pandaPIparser";
    std::string domainStr = _htn.getParams().getDomainFilename();
    std::string problemStr = _htn.getParams().getProblemFilename();

    int numArgs = 5;
    char *args[5];
    args[0] = (char *)firstArg;
    args[1] = (char *)domainStr.c_str();
    args[2] = (char *)problemStr.c_str();
    args[3] = (char *)planFile.c_str();
    args[4] = (char *)"-v";

    ParsedProblem dummy_pp;
    run_pandaPIparser(numArgs, args, dummy_pp);

    // Verify once again the plan to get the method parameters and linearization
    bool plan_correct = verify_plan(plan, false, 1, 0, &_possibleMethodInstantiations, &chosen_method_matchings, &chosen_non_unique_matchings, &forbidden_matchings);
    if (!plan_correct)
    {
        Log::e("Plan is not correct. Cannot deorder this plan\n");
        return;
    }

    // Now, we can parse the plan
    std::ifstream file(_plan_str);
    parsePlan(file);

    // printOriginalPlan();

    // Set the methods parameters
    for (const method &m_const : _htn.getParsedProblem().methods)
    {
        int name_id_method = _htn.nameId(m_const.name);
        assert(name_id_method != -1 || Log::e("Error, could not find the method %s in the HTN\n", m_const.name.c_str()));
        _id_method_to_parsed_method[name_id_method] = m_const; // Store original method
    }
    // Iterate over the plan_map, and set the parameters
    for (auto &[id, item] : _plan_map)
    {
        if (item.reduction._name_id == -1)
            continue;
        Log::d("Finding parameters for method %s\n", TOSTR(item.reduction));
        USignature &reduction = item.reduction;
        const method &m = _id_method_to_parsed_method.at(reduction._name_id);
        std::vector<int> params;
        for (int i = 0; i < m.vars.size(); i++)
        {
            // Get the value for this parameter
            std::string param_value = chosen_method_matchings[id][m.vars[i].first];
            int param_value_id = _htn.nameId(param_value);
            params.push_back(param_value_id);
        }
        // Set the parameters of the method
        item.reduction._args = params;
        Log::d("Method %s has parameters %s\n", TOSTR(item.reduction), TOSTR(item.reduction._args));
    }

    // Add the action __method_precondition in the correct place in the plan
    addMethodsPreconditionsAsActionsInPlan();

    // printOriginalPlan();

    // Get the constrains order which are forced by the hirearchy
    Log::i("Getting mandatory ordering constrains in hierarchy...\n");
    getMandatoryOrderingConstrainsInHierarchy();

    // Create the init and goal primtive tasks
    int actionInitId = _htn.nameId("<init_action>");
    _init_action = Action(actionInitId, std::vector<int>());
    for (const USignature &init : _htn.getInitState())
    {
        Signature eff = Signature(init._name_id, init._args);
        _init_action.addEffect(eff);
    }

    _goal_action = _htn.getGoalAction();

    _plan_map[_id_init_action] = PlanItem(
        /*id=*/_id_init_action,
        /*task=*/_init_action.getSignature(),
        /*method=*/USignature(),
        /*subtasksIds=*/std::vector<int>());
    _plan_map[_id_goal_action] = PlanItem(
        /*id=*/_id_goal_action,
        /*task=*/_goal_action.getSignature(),
        /*method=*/USignature(),
        /*subtasksIds=*/std::vector<int>());

    // Print the original plan for debugging
    Log::i("Original plan:\n");
    printOriginalPlan();

    // Get the adder and deleter of all predicates which are in the preconditions of the actions in the plan
    Log::i("Computing adders and deleters...\n");
    computeAddersAndDeleters();
    Log::i("Done !\n");
    // Create the plan map only for primitive tasks
    NodeHashMap<int, USignature> plan_map_prim_tasks;
    for (const int &prim_task_id : _prim_plan)
    {
        plan_map_prim_tasks[prim_task_id] = _plan_map[prim_task_id].abstractTask;
    }
    // Add init and goal actions
    plan_map_prim_tasks[_id_init_action] = _init_action.getSignature();
    plan_map_prim_tasks[_id_goal_action] = _goal_action.getSignature();

    Log::i("Deordering the plan...\n");

    DeorderAlgo *deorderAlgo = nullptr;
    switch (algoType)
    {
    case DeorderAlgoType::SAT:
        deorderAlgo = new DeorderAlgoSat(
            /*htn=*/_htn,
            /*mode=*/mode,
            /*prim_plan_ids=*/_prim_plan,
            /*adders=*/adders,
            /*deleters=*/deleters,
            /*consummers=*/consumers,
            /*plan_map=*/plan_map_prim_tasks,
            /*mandatory=*/_mandatory_ordering_constrains,
            /*id_init_action=*/_id_init_action,
            /*id_goal_action=*/_id_goal_action);
        break;
    case DeorderAlgoType::PRF:
        deorderAlgo = new DeorderAlgoPRF(
            /*htn=*/_htn,
            /*mode=*/mode,
            /*prim_plan_ids=*/_prim_plan,
            /*adders=*/adders,
            /*deleters=*/deleters,
            /*consummers=*/consumers,
            /*plan_map=*/plan_map_prim_tasks,
            /*mandatory=*/_mandatory_ordering_constrains,
            /*id_init_action=*/_id_init_action,
            /*id_goal_action=*/_id_goal_action);
        break;
    }

    bool solved = deorderAlgo->solve();
    if (!solved)
    {
        Log::e("Failed to find deordering !\n");
        return;
    }

    // Check if the solution is correct
    if (_htn.getParams().isNonzero("vp"))
    {
        Log::i("Verifying solution...\n");
        bool is_correct = deorderAlgo->verifySolution(/*numSamples=*/100);
        if (!is_correct)
        {
            Log::e("Final solution is not correct.\n");
            return;
        }
        else
        {
            Log::i("Final solution verified.\n");
        }
    }

    NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual> final_ordering = deorderAlgo->getSolutionOrdering(/*remove_method_prec_actions=*/true);

    // Print the length of the critical path*
    int init_size_critical_path = _original_plan_length;
    int new_size_critical_path = getCriticalPath(final_ordering);
    Log::i("Initial size of the critical path: %d\n", init_size_critical_path);
    Log::i("Size of the critical path after deordering: %d\n", new_size_critical_path);

    if (_htn.getParams().isNonzero("wp"))
    {
        // Write the constrains to a file to be able to visualize it
        // Name file should constrains the domain name, and the problem name
        std::string problem_path = _htn.getParams().getProblemFilename();
        std::string problem_name = std::filesystem::path(problem_path).stem(); // Stem to remove the extension for the problem name
        // Remove the extension for the problem name

        std::string domain_name = std::filesystem::path(problem_path).parent_path().filename();

        std::string ordering_file = domain_name + "_" + problem_name + "_deordering.dot";

        Log::i("Writing the final plan to %s\n", ordering_file.c_str());

        writeGraphToFile(final_ordering, ordering_file);
    }

    // Clean up
    delete deorderAlgo;
}

void Deorder::parsePlan(std::ifstream &planFile)
{
    std::string line;

    // Ignore until ==>
    while (std::getline(planFile, line))
    {
        Log::i("%s\n", line.c_str());
        if (line == "==>")
        {
            break;
        }
    }

    // Now, read each actions line
    // Each line should be in the form: id <action_name> <param1_str> <param2_str> ... <paramN_str>
    // Until a line which start with "root" is found

    int max_id = -1;
    int size_plan = 0;

    while (std::getline(planFile, line))
    {
        // Does the line start with "root"?
        if (line.compare(0, 4, "root") == 0)
            break;

        std::istringstream iss(line);
        int id;
        std::string action_name;
        iss >> id >> action_name;
        if (id > max_id)
            max_id = id;
        std::vector<int> params;
        std::string param;
        while (iss >> param)
        {
            params.push_back(_htn.nameId(param));
        }

        // Add potentially missing parameters if this action contains constants
        const Action &temp = _htn.getActionTemplate(_htn.nameId(action_name));
        if (params.size() < temp.getArguments().size())
        {
            Log::d("For action %s, found parameters %s, but template has %d\n", action_name.c_str(), params.size(), temp.getArguments().size());
            Log::d("Try to add missing parameters\n");
            const std::vector<int> &taskSorts = _htn.getSorts(temp.getNameId());
            Log::d("Task sorts: %s\n", TOSTR(taskSorts));
            for (int i = params.size(); i < temp.getArguments().size(); i++)
            {
                // Parameter should be a constant and contains ?var_for_
                std::string param_name = TOSTR(temp.getArguments()[i]);
                Log::d("Param name: %s\n", param_name.c_str());

                // Is there only one object for this parameter ?
                int sortParam = taskSorts[i];
                // Get all the constants of this sort
                const FlatHashSet<int> &constants = _htn.getConstantsOfSort(sortParam);
                if (constants.size() != 1)
                {
                    Log::e("For action %s (at ts: %d), additionnal parameter %s is not a constant\n", action_name.c_str(), _prim_plan.size(), param_name.c_str());
                    exit(1);
                }
                // Get the constant
                int constant_id = *constants.begin();
                Log::d("Assigning constant %s to parameter %s\n", TOSTR(constant_id), param_name.c_str());
                // Add the constant to the parameters
                params.push_back(constant_id);
            }
        }

        // Create the USignature associated with the action and add it to the map
        USignature usig(_htn.nameId(action_name), params);
        // Log::i("Action %s\n", TOSTR(usig));

        // Add the action to the map
        _plan_map[id] = PlanItem(
            /*id=*/id,
            /*task=*/usig,
            /*method=*/USignature(),
            /*subtasksIds=*/std::vector<int>());
        _prim_plan.push_back(id);
    }

    _original_plan_length = _prim_plan.size();

    // After finding "root", parse the initial network IDs
    std::istringstream root_iss(line);
    std::string root_word;
    root_iss >> root_word; // Skip "root"
    USignature task_sig(_htn.nameId("__top"), {});
    USignature method_sig(_htn.nameId("__top_method"), std::vector<int>());

    int network_id;
    while (root_iss >> network_id)
    {
        _initial_network_ids.push_back(network_id);
    }
    // Add the root task to plan map
    _plan_map[0] = PlanItem(
        /*id=*/0,
        /*task=*/task_sig,
        /*method=*/method_sig,
        /*subtasksIds=*/_initial_network_ids);

    // Now parse the hierarchy
    while (std::getline(planFile, line))
    {
        if (line == "<==")
            break;

        // Find the position of "->"
        size_t arrow_pos = line.find("->");
        if (arrow_pos == std::string::npos)
            continue;

        // Split into task part and method part
        std::string task_part = line.substr(0, arrow_pos);
        std::string method_part = line.substr(arrow_pos + 2); // +2 to skip "->"

        // Parse task part
        std::istringstream task_iss(task_part);
        int task_id;
        std::string task_name;
        task_iss >> task_id >> task_name;
        if (task_id > max_id)
            max_id = task_id;
        // Get task parameters
        std::vector<int> task_params;
        std::string param;
        while (task_iss >> param)
        {
            task_params.push_back(_htn.nameId(param));
        }

        // Parse method part
        std::istringstream method_iss(method_part);
        std::string method_name;
        method_iss >> method_name;

        // Get subtask IDs
        std::vector<int> subtask_ids;
        int subtask_id;
        while (method_iss >> subtask_id)
        {
            subtask_ids.push_back(subtask_id);
        }

        // Create signatures
        USignature task_sig(_htn.nameId(task_name), task_params);
        USignature method_sig(_htn.nameId(method_name), std::vector<int>()); // We cannot know the parameters yet (Not indicated in the current format of HTN plan). We will need the subtasks for that

        // Add to plan map
        _plan_map[task_id] = PlanItem(
            /*id=*/task_id,
            /*task=*/task_sig,
            /*method=*/method_sig,
            /*subtasksIds=*/subtask_ids);
    }

    _id_init_action = max_id + 1;
    _id_goal_action = max_id + 2;
    _last_id = _id_goal_action;
}

void Deorder::printOriginalPlan()
{
    std::ostringstream oss;
    oss << "==>\n";

    // First, print the primitive tasks
    for (int id : _prim_plan)
    {
        const PlanItem &item = _plan_map[id];
        oss << std::to_string(item.id) << " " << _htn.toString(item.abstractTask._name_id);
        for (int param : item.abstractTask._args)
        {
            oss << " " << _htn.toString(param);
        }
        oss << "\n";
    }

    // Print root and network IDs
    oss << "root";
    for (int network_id : _initial_network_ids)
    {
        oss << " " << std::to_string(network_id);
    }
    oss << "\n";

    // Now iterate over the hierarchy
    std::queue<int> tasks_to_print;
    for (int network_id : _initial_network_ids)
    {
        tasks_to_print.push(network_id);
    }

    while (!tasks_to_print.empty())
    {
        int task_id = tasks_to_print.front();
        tasks_to_print.pop();
        const PlanItem &item = _plan_map[task_id]; // Use const reference

        // If it is a primitive task, it has already been printed
        if (item.reduction._name_id == -1)
            continue;

        oss << std::to_string(item.id) << " " << _htn.toString(item.abstractTask._name_id);
        for (int param : item.abstractTask._args)
        {
            oss << " " << _htn.toString(param);
        }
        oss << " -> ";
        oss << _htn.toString(item.reduction._name_id);
        for (int param : item.reduction._args)
        {
            oss << " " << _htn.toString(param);
        }

        for (int subtask_id : item.subtaskIds)
        {
            tasks_to_print.push(subtask_id);
            oss << " " << std::to_string(subtask_id);
        }
        oss << "\n";
    }

    oss << "<==\n";

    // Print the final string
    std::string result = oss.str();
    Log::i("\n%s\n", result.c_str());
}

// This function iterates through the primitive actions of the plan. For each action,
// it traverses up the hierarchy. If it finds that the action (or its ancestor task)
// is the first subtask of a method instance, it checks if that method has preconditions.
// If so, it creates a new action for the precondition,
// and inserts it into the plan (_prim_plan and _plan_map) before the corresponding
// primitive action.
void Deorder::addMethodsPreconditionsAsActionsInPlan()
{
    Log::i("Adding method preconditions as actions in the plan...\n");

    // 1. Precompute parent mapping for efficient upward traversal
    std::unordered_map<int, int> child_to_parent;
    for (const auto &[parent_id, item] : _plan_map)
    {
        for (int child_id : item.subtaskIds)
        {
            child_to_parent[child_id] = parent_id;
        }
    }

    std::unordered_set<int> _method_precondition_already_created;

    // 2. Keep track of method instances whose preconditions have been added
    std::unordered_set<int> processed_method_parents;

    // 3. Store updates to apply after iteration to avoid modifying structures during iteration
    std::map<int, PlanItem> updates_to_plan_map_add;
    std::map<int, int> updates_to_parent_subtasks_add; // parent_id -> new_precondition_action_id

    // 4. Iterate through the *original* primitive plan order.
    std::vector<int> original_prim_plan = _prim_plan; // Make a copy before modifying _prim_plan
    int global_insertion_offset = 0;                  // Track total insertions into _prim_plan

    for (int prim_idx = 0; prim_idx < original_prim_plan.size(); ++prim_idx)
    {
        int current_prim_id = original_prim_plan[prim_idx];

        // Determine the insertion point for preconditions related to *this* primitive action
        int current_prim_insertion_point = prim_idx + global_insertion_offset;

        int current_node_id = current_prim_id;

        Log::d("Processing primitive action %d (%s) at original index %d. Insertion point: %d\n",
               current_prim_id, TOSTR(_plan_map[current_prim_id].abstractTask), prim_idx, current_prim_insertion_point);

        // 5. Traverse upwards from the primitive action.
        while (child_to_parent.count(current_node_id))
        {
            int parent_id = child_to_parent[current_node_id];
            // Ensure parent_id exists in _plan_map before accessing
            if (_plan_map.find(parent_id) == _plan_map.end())
            {
                Log::w("Parent ID %d not found in _plan_map for child %d. Stopping upward traversal for this path.\n", parent_id, current_node_id);
                break; // Stop traversal if parent is missing
            }
            const PlanItem &parent_item = _plan_map.at(parent_id);

            Log::d("  Traversing up: Child %d (%s) -> Parent %d (%s)\n",
                   current_node_id, TOSTR(_plan_map[current_node_id].abstractTask),
                   parent_id, TOSTR(parent_item.abstractTask));

            // Check if the parent is reduced by a method.
            if (parent_item.reduction._name_id != -1)
            {
                Log::d("    Parent %d is reduced by method %s\n", parent_id, TOSTR(parent_item.reduction));

                // Check if we've already processed this method instance.
                if (processed_method_parents.count(parent_id))
                {
                    Log::d("    Method instance %d already processed. Stopping upward traversal for this path.\n", parent_id);
                    break; // Stop traversing up this specific path
                }

                // Get the reduction assicated with the parent item
                Reduction reduction = _htn.toReduction(parent_item.reduction._name_id, parent_item.reduction._args);
                Log::d("    Parent reduction: %s\n", TOSTR(reduction));

                if (reduction.getPreconditions().size() > 0)
                {

                    if (!_method_precondition_already_created.count(reduction.getNameId()))
                    {
                        // Create an action with all the preconditions of the method
                        std::string method_precondition_action_name = "<method_prec>" + Names::to_string(reduction.getNameId());

                        Reduction red_template = _htn.getReductionTemplate(reduction.getNameId());

                        int id_action = _htn.nameId(method_precondition_action_name);
                        std::vector<int> args_action = red_template.getArguments();
                        Action action(id_action, args_action);
                        for (const auto &precondition : red_template.getPreconditions())
                        {
                            action.addPrecondition(precondition);
                        }
                        _htn.addAction(action);
                        Log::d("    Created method precondition action %s\n", TOSTR(action));
                        _method_precondition_already_created.insert(reduction.getNameId());
                    }

                    std::string method_precondition_action_name = "<method_prec>" + Names::to_string(reduction.getNameId());
                    int id_action = _htn.nameId(method_precondition_action_name);

                    Action action = _htn.toAction(id_action, parent_item.reduction._args);

                    USignature action_sig = action.getSignature();

                    // Get a new ID and add to _plan_map (store update).
                    _last_id++;
                    int new_action_id = _last_id;
                    _method_precondition_ids.insert(new_action_id);
                    PlanItem precondition_plan_item(new_action_id, action_sig, USignature(), {});
                    updates_to_plan_map_add[new_action_id] = precondition_plan_item;

                    Log::d("    Storing new plan item for ID %d.\n", new_action_id);

                    // Insert the new action ID into _prim_plan at the correct position.
                    _prim_plan.insert(_prim_plan.begin() + current_prim_insertion_point, new_action_id);
                    Log::d("    Inserted new action ID %d into _prim_plan at index %d.\n", new_action_id, current_prim_insertion_point);
                    global_insertion_offset++; // Increment the global offset

                    // Store update to add the new action ID as the *first* subtask of the parent.
                    updates_to_parent_subtasks_add[parent_id] = new_action_id;
                    Log::d("    Storing update to add %d as first subtask of parent %d.\n", new_action_id, parent_id);

                    // Mark this parent method instance as processed.
                    processed_method_parents.insert(parent_id);
                    Log::d("    Marked method instance %d as processed.\n", parent_id);
                }
            } // end if: parent is reduced by method

            // Continue traversing upwards.
            current_node_id = parent_id;
        } // end while: traversing up

    } // end for: iterating original primitive plan

    // 6. Apply stored updates
    Log::i("Applying stored updates to plan map...\n");
    for (const auto &[id, item] : updates_to_plan_map_add)
    {
        _plan_map[id] = item;
        Log::d("  Added/Updated PlanItem for ID %d: %s\n", id, TOSTR(item.abstractTask));
    }
    for (const auto &[parent_id, sub_id] : updates_to_parent_subtasks_add)
    {
        if (_plan_map.count(parent_id))
        {
            _plan_map[parent_id].subtaskIds.insert(_plan_map[parent_id].subtaskIds.begin(), sub_id);
            Log::d("  Inserted subtask %d into parent ID %d subtask list.\n", sub_id, parent_id);
        }
        else
        {
            Log::e("  Cannot insert subtask for parent ID %d: Not found in _plan_map.\n", parent_id);
        }
    }

    Log::i("Method precondition processing complete. Final primitive plan size: %zu\n", _prim_plan.size());
}

// Helper function to compute the transitive closure of ordering constraints
std::vector<std::pair<std::string, std::string>> Deorder::getFullOrdering(const method &m)
{
    // Create adjacency list representation
    std::unordered_map<std::string, std::unordered_set<std::string>> graph;

    // Build the graph from the original ordering
    for (const auto &order : m.ordering)
    {
        const auto &[from, to] = order;
        graph[from].insert(to);

        // Make sure both nodes exist in the graph even if they don't have edges
        if (graph.count(to) == 0)
        {
            graph[to] = std::unordered_set<std::string>();
        }
    }

    // Vector to store all ordering relationships
    std::vector<std::pair<std::string, std::string>> fullOrdering;

    // For each node, do a BFS to find all reachable nodes
    for (const auto &[start, _] : graph)
    {
        std::queue<std::string> q;
        std::unordered_set<std::string> visited;

        q.push(start);
        visited.insert(start);

        while (!q.empty())
        {
            std::string current = q.front();
            q.pop();

            for (const auto &next : graph[current])
            {
                if (visited.count(next) == 0)
                {
                    // Add this ordering relationship if it's not the starting node
                    fullOrdering.push_back({start, next});
                    visited.insert(next);
                    q.push(next);
                }
            }
        }
    }

    return fullOrdering;
}

// Helper function to collect all primitive action descendants of a task
NodeHashSet<int> Deorder::collectChildrenActions(int id)
{
    NodeHashSet<int> children;
    std::stack<int> s;
    s.push(id);
    while (!s.empty())
    {
        int current_id = s.top();
        s.pop();
        // Check if current_id exists in the map before accessing
        if (_plan_map.find(current_id) == _plan_map.end())
        {
            Log::w("Task ID %d not found in _plan_map during collectChildrenActions. Skipping.\n", current_id);
            continue;
        }
        const PlanItem &item = _plan_map.at(current_id);
        if (item.reduction._name_id == -1)
        {
            // It's a primitive task (or a method precondition action treated as primitive here)
            children.insert(current_id);
        }
        else
        {
            for (int subtask_id : item.subtaskIds)
            {
                s.push(subtask_id);
            }
        }
    }
    return children;
}

void Deorder::getMandatoryOrderingConstrainsInHierarchy()
{
    // Iterate in a DFS way from left to right and add the ordering constrains
    std::stack<int> s;

    // Iterate the hierarchy in a depth first search manner from left to right
    // for (int i = _initial_network_ids.size() - 1; i >= 0; i--) {
    s.push(0);
    // }

    while (!s.empty())
    {
        int id = s.top();
        s.pop();

        // Check if id exists in the map before accessing
        if (_plan_map.find(id) == _plan_map.end())
        {
            Log::w("Task ID %d not found in _plan_map during hierarchy traversal. Skipping.\n", id);
            continue;
        }
        const PlanItem &item = _plan_map.at(id);
        Log::d("Hierarchy DFS: Processing task %s(%d)\n", TOSTR(item.abstractTask), id);

        // If primitive task, nothing to do for ordering within its non-existent children
        if (item.reduction._name_id == -1)
            continue;

        // If the first subtask is a method precondition action, then, it must be executed before all the other subtasks
        if (item.subtaskIds.size() > 0 && _method_precondition_ids.count(item.subtaskIds[0]))
        {
            int id_method_prec = item.subtaskIds[0];
            Log::d("  First subtask %s(%d) is a method precondition action. Adding ordering constraints.\n", TOSTR(_plan_map[id_method_prec].abstractTask), id_method_prec);
            for (size_t i = 1; i < item.subtaskIds.size(); i++)
            {
                // Collect children of this subtask
                NodeHashSet<int> children_task = collectChildrenActions(item.subtaskIds[i]);
                for (int child : children_task)
                {
                    Log::d("  MANDATORY ORDERING: %s(%d) before %s(%d)\n", TOSTR(_plan_map[id_method_prec].abstractTask), id_method_prec, TOSTR(_plan_map[child].abstractTask), child);
                    _mandatory_ordering_constrains.insert({id_method_prec, child});
                }
            }
        }

        // Get the method definition
        // Method existence is guaranteed by initial plan verification.
        const method &method_def = _id_method_to_parsed_method.at(item.reduction._name_id);

        // If no ordering constraints for this method, nothing to add from here
        if (method_def.ordering.empty())
        {
            Log::d("  No ordering constrains for method %s\n", TOSTR(item.reduction));
        }
        else
        {
            Log::d("  Processing ordering constraints for method %s\n", TOSTR(item.reduction));
            // Get the linearization/mapping info for this specific instance
            if (_possibleMethodInstantiations.find(id) == _possibleMethodInstantiations.end())
            {
                Log::w("  Linearization info for method instance %d not found in _possibleMethodInstantiations. Skipping hierarchy constraints for this instance.\n", id);
            }
            else
            {
                // Assuming the first element of the vector corresponds to the chosen instantiation
                // And the first map within the pair maps step names to plan subtask IDs
                // Ensure there is at least one instantiation available
                if (_possibleMethodInstantiations.at(id).empty())
                {
                    Log::w("  No instantiation info found for method instance %d in _possibleMethodInstantiations. Skipping hierarchy constraints.\n", id);
                }
                else
                {
                    const auto &instantiation_info = _possibleMethodInstantiations.at(id)[0]; // Use first instantiation
                    const std::map<std::string, int> &step_name_to_plan_id = instantiation_info.first;

                    // Get all implied orderings from the method definition
                    for (const auto &order : getFullOrdering(method_def))
                    {
                        const std::string &before_step_name = order.first;
                        const std::string &after_step_name = order.second;

                        Log::d("    Checking definition order: %s before %s\n", before_step_name.c_str(), after_step_name.c_str());

                        // Find the corresponding plan subtask IDs using the map
                        if (step_name_to_plan_id.count(before_step_name) && step_name_to_plan_id.count(after_step_name))
                        {
                            int before_plan_id = step_name_to_plan_id.at(before_step_name);
                            int after_plan_id = step_name_to_plan_id.at(after_step_name);

                            // Ensure the retrieved IDs are valid plan items
                            if (_plan_map.count(before_plan_id) && _plan_map.count(after_plan_id))
                            {
                                Log::d("      Mapped to plan order: %s(%d) before %s(%d)\n",
                                       TOSTR(_plan_map.at(before_plan_id).abstractTask), before_plan_id,
                                       TOSTR(_plan_map.at(after_plan_id).abstractTask), after_plan_id);

                                // All children of 'before' must come before all children of 'after'
                                NodeHashSet<int> children_task1 = collectChildrenActions(before_plan_id);
                                NodeHashSet<int> children_task2 = collectChildrenActions(after_plan_id);
                                for (int child1 : children_task1)
                                {
                                    for (int child2 : children_task2)
                                    {
                                        Log::d("        MANDATORY ORDERING: %s(%d) before %s(%d)\n", TOSTR(_plan_map[child1].abstractTask), child1, TOSTR(_plan_map[child2].abstractTask), child2);
                                        _mandatory_ordering_constrains.insert({child1, child2});
                                    }
                                }
                            }
                            else
                            {
                                Log::w("      Mapped plan IDs %d or %d not found in _plan_map.\n", before_plan_id, after_plan_id);
                            }
                        }
                        else
                        {
                            // This might happen if the ordering involves the __method_precondition step,
                            // which might not be in the step_name_to_plan_id map from verify_plan.
                            // Or if the step names don't match exactly.
                            Log::d("      Could not map method step names '%s' or '%s' to plan IDs for instance %d.\n", before_step_name.c_str(), after_step_name.c_str(), id);
                            // TODO: Handle potential ordering involving the added __method_precondition action if necessary.
                            // This would require finding the ID of the added precondition action associated with this parent 'id'.
                        }
                    }
                }
            }
        }

        // Add the subtasks of the method to the stack for DFS traversal
        // Iterate in reverse to maintain left-to-right processing order
        for (int i = item.subtaskIds.size() - 1; i >= 0; i--)
        {
            s.push(item.subtaskIds[i]);
        }
    }
    Log::i("Finished getting mandatory ordering constraints. Found %zu constraints.\n", _mandatory_ordering_constrains.size());
}

void Deorder::computeAddersAndDeleters()
{

    // Iterate over the primitive plan + the __init__ action and get all the adders and deleters
    for (const int &id : _prim_plan)
    {
        const PlanItem &item = _plan_map[id];
        const USignature &aSig = item.abstractTask;
        Log::d("For action %d (%s)\n", id, TOSTR(aSig));
        Action action = _htn.toAction(aSig._name_id, aSig._args);
        for (const Signature &eff : action.getEffects())
        {
            // Add current effect as adder and opposite as deleter
            adders[eff].insert(id);
            Signature oppEff = eff.opposite();
            deleters[oppEff].insert(id);
        }
        for (const Signature &prec : action.getPreconditions())
        {
            // Add current precondition as being cons
            consumers[prec].insert(id);
        }
    }

    // Finally, do the same for the __init__ action. But here, we only have the positive effects...
    for (const Signature &eff : _init_action.getEffects())
    {
        adders[eff].insert(_id_init_action);
        // No need for deleters of the init action since it is the first action
    }
    // Get as well all the negative effects of the init actions
    std::vector<int> prim_plan_and_goal = _prim_plan;
    prim_plan_and_goal.push_back(_id_goal_action);

    for (const int &id : prim_plan_and_goal)
    {
        const PlanItem &item = _plan_map[id];
        const USignature &aSig = item.abstractTask;
        Action action = _htn.toAction(aSig._name_id, aSig._args);
        for (const Signature &pre : action.getPreconditions())
        {
            if (!pre._negated)
                continue; // If the precondition is positive we do not care
            // If the associate positive precondition is not in the positive effects of the init action...
            if (!_init_action.getEffects().count(pre.opposite()))
            {
                // Then it means that the init action is an adder of this negative precondition
                adders[pre].insert(_id_init_action);
                // No need for deleters of the init action since it is the first action
            }
        }
    }

    // Add the consummer for the goal action
    for (const Signature &prec : _goal_action.getPreconditions())
    {
        consumers[prec].insert(_id_goal_action);
    }

    // Print all adders and deleters
    // Log::i("Adders and deleters:\n");
    // for (const auto& [eff, adderIds] : adders) {
    //     Log::i("Adder: %s\n", TOSTR(eff));
    //     for (int id : adderIds) {
    //         if (id == -1) {
    //             Log::i("  __init__ (-1)\n");
    //         } else {
    //             Log::i("  %s (%d)\n", TOSTR(_plan_map[id].abstractTask), id);
    //         }
    //     }
    // }
    // for (const auto& [eff, deleterIds] : deleters) {
    //     Log::i("Deleter: %s\n", TOSTR(eff));
    //     for (int id : deleterIds) {
    //         if (id == -1) {
    //             Log::i("  __init__ (-1)\n");
    //         } else {
    //             Log::i("  %s\n", TOSTR(_plan_map[id].abstractTask));
    //         }
    //     }
    // }

    int a = 0;
}

// Function to remove transitive edges from a graph
std::vector<OrderConstraint> removeTransitiveEdges(
    const NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual> &edges,
    const std::set<int> &nodes)
{
    // Create adjacency matrix
    std::map<int, std::set<int>> adj;
    for (const auto &edge : edges)
    {
        adj[edge.before].insert(edge.after);
    }

    // Floyd-Warshall to find all reachable nodes
    std::map<int, std::set<int>> reachable = adj;
    for (int k : nodes)
    {
        for (int i : nodes)
        {
            for (int j : nodes)
            {
                if (reachable[i].count(k) && reachable[k].count(j))
                {
                    reachable[i].insert(j);
                }
            }
        }
    }

    // Keep only direct edges
    // std::vector<std::pair<int, int>> result;
    std::vector<OrderConstraint> result;
    for (const auto &edge : edges)
    {
        bool isTransitive = false;
        for (int k : nodes)
        {
            if (k != edge.before && k != edge.after &&
                reachable[edge.before].count(k) && reachable[k].count(edge.after))
            {
                isTransitive = true;
                break;
            }
        }
        if (!isTransitive)
        {
            result.push_back(edge);
        }
    }

    return result;
}

void Deorder::writeGraphToFile(
    const NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual> &constraints,
    const std::string &filename)
{
    std::ofstream file(filename);

    // Get all unique nodes
    std::set<int> nodes;
    for (const auto &constraint : constraints)
    {
        nodes.insert(constraint.before);
        nodes.insert(constraint.after);
    }

    // Write number of nodes and node information
    file << nodes.size() << "\n";
    for (int node : nodes)
    {
        // file << node << " \"" << labels.at(node) << "\"\n";
        std::string nameAction = TOSTR(_plan_map[node].abstractTask);
        file << node << " \"" << nameAction << "\"\n";
    }

    // Remove transitive edges and write remaining edges
    auto directEdges = removeTransitiveEdges(constraints, nodes);
    file << directEdges.size() << "\n";
    for (const auto &edge : directEdges)
    {
        file << edge.before << " " << edge.after << "\n";
    }
}

int Deorder::getCriticalPath(const NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual> &final_ordering)
{
    // 1. Gather all unique nodes
    std::unordered_set<int> nodes;
    for (const auto &edge : final_ordering)
    {
        nodes.insert(edge.before);
        nodes.insert(edge.after);
    }

    // 2. Build adjacency list and in-degree map
    std::unordered_map<int, std::vector<int>> adj;
    std::unordered_map<int, int> in_degree;

    // Initialize in_degree to 0 for all discovered nodes
    for (auto node : nodes)
    {
        in_degree[node] = 0;
    }

    // Fill adjacency list and compute in-degree
    for (const auto &edge : final_ordering)
    {
        int u = edge.before;
        int v = edge.after;
        adj[u].push_back(v);
        in_degree[v] += 1;
    }

    // 3. Find all nodes with in-degree == 0 to start topological BFS
    std::queue<int> q;
    for (auto node : nodes)
    {
        if (in_degree[node] == 0)
        {
            q.push(node);
        }
    }

    // 4. Initialize distance array (longest-path ending in each node)
    std::unordered_map<int, int> dist;
    for (auto node : nodes)
    {
        dist[node] = 1; // At least the node itself
    }

    // 5. Topological BFS + relaxation of edges
    while (!q.empty())
    {
        int u = q.front();
        q.pop();

        // Relax edges going out of u
        for (int v : adj[u])
        {
            // We found a longer path to 'v' via 'u'
            dist[v] = std::max(dist[v], dist[u] + 1);

            // Decrease in-degree for 'v'
            if (--in_degree[v] == 0)
            {
                q.push(v);
            }
        }
    }

    // 6. The result is the maximum distance
    int longestPath = 0;
    for (auto &kv : dist)
    {
        if (kv.second > longestPath)
        {
            longestPath = kv.second;
        }
    }

    return longestPath;
}