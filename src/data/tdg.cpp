#include <filesystem>
#include <fstream> 
#include <algorithm>
#include <vector>

#include "tdg.h"
#include "util/project_utils.h"
#include "substitution_constraint.h"

TDG::TDG(HtnInstance& htn): _htn(htn), _traversal(htn), _init_state(htn.getInitState()) {

    Log::i("Create TDG\n");

    // The ground file should have already been created by FactAnalysis constructor
    std::filesystem::path groundFile = getProblemProcessingDir() / "problem.sas";

    // Then, load all the actions/methods/abstract tasks from the grounded htn
    std::ifstream file(groundFile);
    int lineIdx = 0;

    // Extract tasks and methods and construct the TDG
    pandaPiGrounderExtractAvailableTasks(file, lineIdx);

    pandaPiGrounderExtractAvailableMethods(file, lineIdx);


    // The creation of lilotane reduction can sometimes add new parameters to the operator (for example for the Childsnack domain)
    // So we need to be able to convert the operator in the htn to the operator in the TDG in that case
    for (const auto& [key, value]: _vertices) {
        int name_id = key._name_id;
        int num_args_tdg = key._args.size();
        if (_htn.isAction(key)) {
            // Get the action by name_id
            const Action& action = _htn.getActionTemplate(name_id);
            int num_args_action = action.getArguments().size();
            if (num_args_tdg != num_args_action) {
                // Log::w("Warning: action %s has %d parameters in the TDG but %d parameters in the htn\n", TOSTR(key), num_args_tdg, num_args_action);
            
                // Assert that the number of params in htn is superior to the number of params in the TDG
                if (num_args_tdg > num_args_action) {
                    Log::e("Error: method %s has %d parameters in the TDG but %d parameters in the htn (%s)\n", TOSTR(key), num_args_tdg, num_args_action, TOSTR(action));
                    exit(1);
                }
                _number_params_to_keep_for_name_id[key._name_id] = num_args_tdg;
            }
            
        }
        else if (_htn.isReduction(key)) {

            // Ignore the top method
            if (_htn.toString(key._name_id).find("__top_method") != std::string::npos) {
                continue;
            }

            // Get the method by name_id
            const Reduction& method = _htn.getReductionTemplate(name_id);
            int num_args_method = method.getArguments().size();
            if (num_args_tdg != num_args_method) {
                Log::w("Warning: method %s has %d parameters in the TDG but %d parameters in the htn (%s)\n", TOSTR(key), num_args_tdg, num_args_method, TOSTR(method));
                // Assert that the number of params in htn is superior to the number of params in the TDG
                if (num_args_tdg > num_args_method) {
                    Log::e("Error: method %s has %d parameters in the TDG but %d parameters in the htn (%s)\n", TOSTR(key), num_args_tdg, num_args_method, TOSTR(method));
                    exit(1);
                }
                _number_params_to_keep_for_name_id[key._name_id] = num_args_tdg;
            }
        }
    }

    // Log::i("It is ok !");
    // exit(0);


    // To debug, print all the vertices with incoming/outgoing edges
    // int idx_vertice = 0;
    // for (auto& [key, value]: _vertices) {
    //     Log::i("Vertex %d %s\n", idx_vertice, TOSTR(key));
    //     idx_vertice++;
    //     Log::i("  Incoming edges:\n");
    //     for (USignature* incoming_edge: value._incoming_edges) {
    //         Log::i("    %s\n", TOSTR(*incoming_edge));
    //     }
    //     Log::i("  Outgoing edges:\n");
    //     for (USignature* outgoing_edge: value._outgoing_edges) {
    //         Log::i("    %s\n", TOSTR(*outgoing_edge));
    //     }
    //     Log::i("\n");
    // }

    // int a = 0;

    // Attribute the heuristic values for each node of the TDG as defined in the paper: "An Admissible HTN Planning Heuristic"

    Log::i("Done ! Compute heuristic values for each node\n");
    computeHeuristicValues();
    Log::i("Done !");

}


/**
 * Compute the heuristic values for each node of the TDG following the paper "An Admissible HTN Planning Heuristic"
 * If a node is a primitive task (action), its heuristic value is 1
 * If a node is an abstract task (method), its heuristic value is the minimum of the heuristic values of all the methods that can accomplish this task
 * If a node is an abstract task (method), its heuristic value is the sum of the heuristic values of its subtasks
*/
void TDG::computeHeuristicValues() {
    // Compute the heuristic values for each node of the TDG
    // The heuristic value of a node is the number of nodes that can be reached from this node
    // The heuristic value of a node is the number of nodes that can reach this node

    computeSCCs();

    // for (int i = 0; i < _sccs.size(); ++i) {
    //     Log::i("SCC %d:\n", i);
    //     for (const USignature* node : _sccs[i]) {
    //         Log::i("  %s\n", TOSTR(*node));
    //     }
    // }

    // Sort the SCCs in topological order
    sortSCCsInTopologicalOrder();

    // Iterate over the SCCs in topological order and print the nodes in each SCC
    // for (int i = 0; i < _sccs.size(); ++i) {
    //     Log::i("SCC %d:\n", i);
    //     for (const USignature* node : _sccs[i]) {
    //         Log::i("  %s\n", TOSTR(*node));
    //     }
    // }

    // Now iterate on the SCCs in the reverse topological order and compute the heuristic values
    for (int i = _sccs.size() - 1; i >= 0; --i) {
        // If the scc size if 1, we can directly compute the heuristic value
        if (_sccs[i].size() == 1) {
            const USignature* node = *_sccs[i].begin();
            TDGVertexInfo& vertexInfo = _vertices.at(*node);

            if (special_noop_action_id != -1 && node->_name_id == special_noop_action_id) {
                //  This noop action is used when method have no subtasks so the cost of the method is 0
                vertexInfo._heuristic_value = 0;
            }
            // If the node is a primitive task (action), the heuristic value is 1
            else if (_htn.isAction(*node)) {
                vertexInfo._heuristic_value = 1;
            } else {
                if (_htn.isReduction(*node)) {
                    // If it is a method, the heuristic value is the sum of the heuristic values of its subtasks
                    int heuristic_value = 0;
                    for (USignature* subtask : vertexInfo._outgoing_edges) {
                        heuristic_value += _vertices.at(*subtask)._heuristic_value;
                    }
                    vertexInfo._heuristic_value = heuristic_value;
                }
                // Else, it means that it is an abstract task
                else {
                    // If it is a task, the heuristic value is the minimum of the heuristic values of all the methods that can accomplish this task
                    int heuristic_value = MAX_WEIGHT;
                    for (USignature* method : vertexInfo._outgoing_edges) {
                        heuristic_value = std::min(heuristic_value, _vertices.at(*method)._heuristic_value);
                    }
                    
                    vertexInfo._heuristic_value = heuristic_value;
                }
            }
        } else {
            // If the SCC has more than one node, we need to iterate until the heuristic values of all the nodes in the SCC do not change anymore (fixed point iteration)
            bool at_least_one_change = true;
            while (at_least_one_change) {
                at_least_one_change = false;
                // Iterate over all the nodes in the SCC
                for (const USignature* node : _sccs[i]) {
                    
                    TDGVertexInfo& vertexInfo = _vertices.at(*node);
                    int old_value = vertexInfo._heuristic_value;
                    int new_value;

                    bool isMethod = _htn.isReduction(*node);
                    // If it is a method...
                    if (isMethod) {
                        // Heuristic value is the sum of the heuristic values of its subtasks
                        new_value = 0;
                        for (USignature* subtask : vertexInfo._outgoing_edges) {
                            if (_vertices.at(*subtask)._heuristic_value == MAX_WEIGHT) {
                                new_value = MAX_WEIGHT;
                                break;
                            }
                            new_value += _vertices.at(*subtask)._heuristic_value;
                        }
                    }
                    // If it is a task...
                    else {
                        // Heurtistic value is the minimum of the heuristic values of all the methods that can accomplish this task
                        new_value = MAX_WEIGHT;
                        for (USignature* outgoing_edge : vertexInfo._outgoing_edges) {
                            new_value = std::min(new_value, _vertices.at(*outgoing_edge)._heuristic_value);
                        }
                    }

                    if (new_value != old_value) {
                        vertexInfo._heuristic_value = new_value;
                        at_least_one_change = true;
                    }
                }
            }
        }
    }

    // Assert that all the nodes in the SCC have a heuristic value different from MAX_WEIGHT
    // Only in debug mode
    if (Log::getVerbosity() >= Log::V4_DEBUG){
        for (auto& [node, info]: _vertices) {
            if (info._heuristic_value == MAX_WEIGHT) {
                Log::e("Error: heuristic value of node %s is %d\n", TOSTR(node), info._heuristic_value);
                exit(1);
            } else {
                Log::i("__ Heuristic value of %s is %d\n", TOSTR(node), info._heuristic_value);
            }
        }    
    } 

    // Compute the best heuristic value for each name_id
    NodeHashSet<int> name_ids;
    for (auto& [node, info]: _vertices) {
        if (name_ids.find(node._name_id) == name_ids.end()) {
            name_ids.insert(node._name_id);
            _min_heuristic_values_for_name_id[node._name_id] = info._heuristic_value;
        } 
        else {
            if (info._heuristic_value < _min_heuristic_values_for_name_id[node._name_id]) {
                _min_heuristic_values_for_name_id[node._name_id] = info._heuristic_value;
            }
        }
    }
}


/**
 * Performs a depth-first search (DFS) on the graph to find and record Strongly Connected Components (SCCs)
 * using Tarjan's algorithm.
 *
 * @param u The current node being visited.
 * @param index The current index value used for setting indices and low-link values.
 * @param stack The stack used to keep track of the current path in the DFS.
 * @param indices Map to store the index of each node.
 * @param lowLinks Map to store the low-link values of each node.
 * @param onStack Map to track whether a node is currently on the stack.
 * @param sccs Vector to store all the SCCs found in the graph.
 */
void TDG::tarjanDFS(const USignature& u, int& index, std::stack<const USignature*>& stack, 
                    std::unordered_map<const USignature*, int, USignaturePtrHasher, USignaturePtrEqual>& indices, 
                    std::unordered_map<const USignature*, int, USignaturePtrHasher, USignaturePtrEqual>& lowLinks, 
                    std::unordered_map<const USignature*, bool, USignaturePtrHasher, USignaturePtrEqual>& onStack, 
                    std::vector<FlatHashSet<const USignature*, USignaturePtrHasher, USignaturePtrEqual>>& sccs) {
    // Assign an index to the current node and set its low-link value
    indices[&u] = index;
    lowLinks[&u] = index;
    index++;
    stack.push(&u); // Push the node onto the stack
    onStack[&u] = true; // Mark the node as being on the stack

    Log::d("Visiting node %s, index %d\n", TOSTR(u), indices[&u]);

    // Get the vertex information associated with the current node
    TDGVertexInfo& vertexInfo = _vertices[u];

    // Explore all outgoing edges from the current node
    for (USignature* v : vertexInfo._outgoing_edges) {
        if (indices.find(v) == indices.end()) {
            Log::d("Neighbor node %s not visited, starting DFS\n", TOSTR(*v));
            // If the neighbor has not been visited, perform DFS on it
            tarjanDFS(*v, index, stack, indices, lowLinks, onStack, sccs);
            // Update the low-link value of the current node
            lowLinks[&u] = std::min(lowLinks[&u], lowLinks[v]);
        } else if (onStack[v]) {
            Log::d("Neighbor node %s is on stack, updating low-link value\n", TOSTR(*v));
            // If the neighbor is on the stack, it is part of the current SCC
            lowLinks[&u] = std::min(lowLinks[&u], indices[v]);
        }
    }

    // If the current node is the root of an SCC, pop nodes from the stack to form the SCC
    if (lowLinks[&u] == indices[&u]) {
        FlatHashSet<const USignature*, USignaturePtrHasher, USignaturePtrEqual> scc;
        const USignature* v;
        do {
            v = stack.top(); // Get the top node from the stack
            stack.pop(); // Remove the top node from the stack
            onStack[v] = false; // Mark the node as no longer being on the stack
            scc.insert(v); // Add the node to the current SCC
            Log::d("Adding node %s to current SCC\n", TOSTR(*v));
        } while (v != &u);
        sccs.push_back(scc); // Add the current SCC to the list of SCCs
        Log::d("Completed SCC: size %d\n", scc.size());
    }
}

/**
 * Computes the strongly connected components (SCCs) of the task decomposition graph (TDG) using Tarjan's algorithm.
 *
 * This function initializes the necessary data structures and performs a depth-first search (DFS)
 * starting from each unvisited node in the graph. It identifies SCCs by tracking the discovery
 * and low-link values of nodes, and collects nodes into SCCs when an SCC root is identified.
 */
void TDG::computeSCCs() {
    int index = 0;
    std::stack<const USignature*> stack;
    // Maps to store indices, low-link values, and on-stack status of nodes using pointers and custom hasher
    std::unordered_map<const USignature*, int, USignaturePtrHasher, USignaturePtrEqual> indices;
    std::unordered_map<const USignature*, int, USignaturePtrHasher, USignaturePtrEqual> lowLinks;
    std::unordered_map<const USignature*, bool, USignaturePtrHasher, USignaturePtrEqual> onStack;
    _sccs.clear(); // Clear any existing SCCs

    // Iterate over all nodes in the graph
    for (const auto& pair : _vertices) {
        const USignature& u = pair.first;
        // If the node has not been visited, start DFS from it
        if (indices.find(&u) == indices.end()) {
            Log::d("Start DFS from node %s (not visited)\n", TOSTR(u));
            tarjanDFS(u, index, stack, indices, lowLinks, onStack, _sccs);
        } else {
            Log::d("Node %s already visited with index %d\n", TOSTR(u), indices[&u]);
        }
    }
}


/**
 * A utility function to perform topological sorting on the condensed graph.
 * 
 * @param v The current vertex being visited.
 * @param condensedGraph The condensed graph where each node represents an SCC.
 * @param visited A set to keep track of visited nodes.
 * @param Stack A stack to store the topological sorting order.
 */
void TDG::topologicalSortUtil(int v, std::unordered_map<int, std::unordered_set<int>>& condensedGraph, 
                              std::unordered_set<int>& visited, std::stack<int>& Stack) {
    // Mark the current node as visited
    visited.insert(v);

    // Recur for all the vertices adjacent to this vertex
    for (int i : condensedGraph[v]) {
        if (visited.find(i) == visited.end()) {
            topologicalSortUtil(i, condensedGraph, visited, Stack);
        }
    }

    // Push the current vertex to the stack which stores the result
    Stack.push(v);
}


/**
 * Sorts the strongly connected components (SCCs) of the task decomposition graph (TDG) in topological order.
 *
 * This function constructs a condensed graph where each SCC is represented as a single node,
 * and edges between SCCs represent dependencies. It then performs a topological sort on the condensed graph
 * to obtain an ordering of SCCs.
 */
void TDG::sortSCCsInTopologicalOrder() {
    // Step 1: Construct the condensed graph
    std::unordered_map<const USignature*, int> nodeToSCC;
    std::unordered_map<int, std::unordered_set<int>> condensedGraph;
    for (int i = 0; i < _sccs.size(); ++i) {
        for (const USignature* node : _sccs[i]) {
            nodeToSCC[node] = i;
        }
    }
    for (int i = 0; i < _sccs.size(); ++i) {
        for (const USignature* node : _sccs[i]) {
            const TDGVertexInfo& vertexInfo = _vertices.at(*node);
            for (const USignature* neighbor : vertexInfo._outgoing_edges) {
                int neighborSCC = nodeToSCC[neighbor];
                if (neighborSCC != i) {
                    condensedGraph[i].insert(neighborSCC);
                }
            }
        }
    }

    // Step 2: Perform topological sort on the condensed graph
    std::stack<int> Stack;
    std::unordered_set<int> visited;
    for (int i = 0; i < _sccs.size(); ++i) {
        if (visited.find(i) == visited.end()) {
            topologicalSortUtil(i, condensedGraph, visited, Stack);
        }
    }

    // Step 3: Extract SCCs in topological order
    std::vector<FlatHashSet<const USignature*, USignaturePtrHasher, USignaturePtrEqual>> sortedSCCs;
    while (!Stack.empty()) {
        sortedSCCs.push_back(_sccs[Stack.top()]);
        Stack.pop();
    }

    // Update _sccs with the sorted SCCs
    _sccs = std::move(sortedSCCs);
}


int TDG::getHeuristicValue(const USignature& u) const {

    if (_number_params_to_keep_for_name_id.find(u._name_id) != _number_params_to_keep_for_name_id.end()) {
        // Create a signature with only the _number_params_to_keep_for_name_id[u._name_id] first parameters
        USignature u_partial = USignature(u._name_id, std::vector<int>(u._args.begin(), u._args.begin() + _number_params_to_keep_for_name_id.at(u._name_id)));
        if (_vertices.find(u_partial) == _vertices.end()) {
            Log::e("Node %s not found in the TDG. Set weight value to inf\n", TOSTR(u));
            return MAX_WEIGHT;
        }
        int heuristic_value = _vertices.at(u_partial)._heuristic_value;
        assert(heuristic_value != -1 || Log::e("Heuristic value of node %s not computed\n", TOSTR(u_partial)));
        return heuristic_value;
    }

    if (_vertices.find(u) == _vertices.end()) {
        Log::e("Node %s not found in the TDG. Set weight value to inf\n", TOSTR(u));
        return MAX_WEIGHT;
    }
    // assert(_vertices.find(u) != _vertices.end() || Log::e("Node %s not found in the TDG\n", TOSTR(u)));
    int heuristic_value = _vertices.at(u)._heuristic_value;
    assert(heuristic_value != -1 || Log::e("Heuristic value of node %s not computed\n", TOSTR(u)));
    return heuristic_value;
}


/**
 * Get the best heuristic value of a lifted operator
*/
int TDG::getBestHeuristicValue(const USignature& usig) {

    if (!_htn.hasQConstants(usig) && _htn.isFullyGround(usig)) {
        // Log::i("Node %s is fully grounded\n", TOSTR(u));
        return getHeuristicValue(usig);
    }

    std::vector<int> sorts = _htn.getSorts(usig._name_id);
    std::vector<std::vector<int>> eligibleArgs = _htn.getEligibleArgs(usig, sorts);
    // Print the eligible args
    // Log::i("Eligible args for %s:\n", TOSTR(u));
    // for (const std::vector<int>& args : eligibleArgs) {
    //     for (int arg : args) {
    //         Log::i("    %d\n", arg);
    //     }
    //     Log::i("---\n");
    // }

    int min_heuristic_value_for_name = _min_heuristic_values_for_name_id[usig._name_id];

    const USignature* best_key;

    int best_heuristic_value = MAX_WEIGHT;
    // Iterate over all the node with the same name_id
    for (const auto& [key, value]: _vertices) {
        if (key._name_id == usig._name_id) {

            // Check if u can be grounded to this node
            bool can_be_grounded = true;

            // assert((key._args.size() == eligibleArgs.size() || _number_params_to_keep_for_name_id[u._name_id] == eligibleArgs.size())  || Log::e("Number of args of node %s is different from the number of eligible args\n", TOSTR(key)));

            // Print the parameters of the node
            // Log::i("Node %s:\n", TOSTR(key));
            for (int i = 0; i < key._args.size(); i++) {
                // Log::i("    %d\n", key._args[i]);
                if (eligibleArgs[i].size() > 0 && std::find(eligibleArgs[i].begin(), eligibleArgs[i].end(), key._args[i]) == eligibleArgs[i].end()) {
                    can_be_grounded = false;
                    break;
                }
            }

            if (!can_be_grounded) {
                continue;
            }

            // if (best_heuristic_value != MAX_WEIGHT && best_heuristic_value != value._heuristic_value) {
            //     Log::w("Two nodes (%s, %s) with the same name_id have different heuristic values: %d and %d\n", TOSTR(*best_key), TOSTR(key), best_heuristic_value, value._heuristic_value);
            // }
            best_heuristic_value = std::min(best_heuristic_value, value._heuristic_value);
            // best_key = &key;

            if (best_heuristic_value == min_heuristic_value_for_name) {
                break;
            }
        }
    }

    return best_heuristic_value;
}

std::vector<USignature> TDG::getAllGrounding(const USignature& u) {

    std::vector<USignature> groundings;

    if (!_htn.hasQConstants(u) && _htn.isFullyGround(u)) {
        // Log::i("Node %s is fully grounded\n", TOSTR(u));
        groundings.push_back(u);
        return groundings;
    }

    std::vector<int> sorts = _htn.getSorts(u._name_id);
    std::vector<std::vector<int>> eligibleArgs = _htn.getEligibleArgs(u, sorts);

    // Construct all the grounding from the eligible args
    for (const auto& [key, value]: _vertices) {
        if (key._name_id == u._name_id) {

            // Check if u can be grounded to this node
            bool can_be_grounded = true;

            assert((key._args.size() == eligibleArgs.size() || _number_params_to_keep_for_name_id[u._name_id] == eligibleArgs.size())  || Log::e("Number of args of node %s is different from the number of eligible args\n", TOSTR(key)));

            // Print the parameters of the node
            // Log::i("Node %s:\n", TOSTR(key));
            for (int i = 0; i < key._args.size(); i++) {
                // Log::i("    %d\n", key._args[i]);
                if (eligibleArgs[i].size() > 0 && std::find(eligibleArgs[i].begin(), eligibleArgs[i].end(), key._args[i]) == eligibleArgs[i].end()) {
                    can_be_grounded = false;
                    break;
                }
            }

            if (!can_be_grounded) {
                continue;
            }

            groundings.push_back(key);
        }
    }

    return groundings;
}

int TDG::getVirtualPlanHeuristicValue(const std::vector<PlanItem>& virtualPlan) const {
    int heuristic_value = 0;

    Log::i("Virtual plan size: %d\n", virtualPlan.size() - 1);
    // Print the virtual plan
    for (int i = 0; i < virtualPlan.size(); i++) {
        Log::i("    Item %d: %s\n", i, TOSTR(virtualPlan[i].reduction));
    }

    // Do not consider the goal_action when computing the heuristic value of the plan
    for (int i = 0; i < virtualPlan.size() - 1; i++) {
        const PlanItem& item = virtualPlan[i];
        int item_heuristic_value;
        // Log::i("Item %s\n", TOSTR(item.reduction));
        // if (_htn.isReductionPrimitivizable(item.reduction._name_id)) {
        //     // Get the corresponding action
        //     const Action& a = _htn.getReductionPrimitivization(item.reduction._name_id);
        //     USignature actionSig = a.getSignature();
        //     item_heuristic_value = getHeuristicValue(actionSig);
        // } else if (item.reduction._name_id == _htn.getBlankActionSig()._name_id) {
        //     item_heuristic_value = 0;
        // } else {
        //     item_heuristic_value = getHeuristicValue(item.reduction);
        // }


        if (_htn.isAction(item.reduction) || _htn.isReductionPrimitivizable(item.reduction._name_id)) {
            // If blank action, heuristic value is 0 else 1
            if (item.reduction._name_id == _htn.getBlankActionSig()._name_id) {
                item_heuristic_value = 0;
            } else {
                item_heuristic_value = 1;
            }
        } else {
            item_heuristic_value = getHeuristicValue(item.reduction);
        }
        Log::i("Item %s heuristic value: %d\n", TOSTR(item.reduction), item_heuristic_value);
        heuristic_value += item_heuristic_value;
    }

    Log::i("Heuristic value of the virtual plan: %d\n", heuristic_value);
    return heuristic_value;
}











// void TDG::computeLiftedTDG() {
//     // Each node contains a lifted Reduction, Action or Task
//     // We start the construction from the Lifted top method
    
//     const Reduction& top_method = _htn.getInitReduction();
//     const USignature& top_method_sig = top_method.getSignature();

//     Log::i("Top method: %s\n", TOSTR(top_method_sig._name_id));

//     // Create the vertex for the top method
//     TDGVertexInfo top_method_vertex;
//     _vertices[top_method_sig] = top_method_vertex;

//     // Now, for all subtasks of the top method, we create the corresponding vertices
//     for (const USignature& subtask : top_method.getSubtasks()) {
//         Log::i("Subtask: %s\n", TOSTR(subtask._name_id));
//     }

//     int a = 0;
// }











void TDG::pandaPiGrounderExtractAvailableTasks(std::ifstream& file, int& lineIdx) {

    std::string line = "";

    // Skip until the line ;; tasks (primitive and abstract) or until the end of the file
    while (std::getline(file, line)) {
        lineIdx++;
        if (line == ";; tasks (primitive and abstract)") {
            break;
        }
    }

    // Next if the number of tasks
    std::getline(file, line);
    lineIdx++;

    _nb_primitive_tasks = std::stoi(line);

    _tasks.reserve(_nb_primitive_tasks);

    bool is_primitive = true;

    // Then, extract all the tasks
    // Each line is in the form:
    // [0/1] <task_name>[arg1,arg2,...] with 0 if it is a primitive task and 1 if it is an abstract task
    while (std::getline(file, line)) {
        lineIdx++;
        if (line.size() == 0) break;


        // Not used for now
        if (line[0] == '1') {
            is_primitive = false;
        } else {
            is_primitive = true;
        }

        int idx = 2;

        std::string task_name = "";
        std::vector<std::string> task_args;

        while (line[idx] != '[' && idx < line.size()) {
            task_name += line[idx];
            idx++;
        }

        if (idx != line.size()) {
            while (line[idx] != ']') {
                idx++; // Ignore the '[' character or ',' character
                std::string arg = "";
                while (line[idx] != ',' && line[idx] != ']') {
                    arg += line[idx];
                    idx++;
                }
                if (arg.size() > 0)
                    task_args.push_back(arg);
            }
        }

        // Create the task as a USignature
        std::vector<int> args_pred;
        for (std::string arg_name: task_args) {
            args_pred.push_back(_htn.nameId(arg_name));
        }
        USignature task_usig(_htn.nameId(task_name), args_pred);

        // Log::i("Task (%s) from panda: %s\n", is_primitive ? "primitive" : "abstract", TOSTR(task_usig));

        if (task_name == "__noop") {
            special_noop_action_id = task_usig._name_id;
        }

        _tasks.push_back(task_usig);
    }
}



void TDG::pandaPiGrounderExtractAvailableMethods(std::ifstream& file, int& lineIdx) {

    std::string line = "";

    // Skip until the line ;; methods or until the end of the file
    while (std::getline(file, line)) {
        lineIdx++;
        if (line == ";; methods") {
            break;
        }
    }

    // Next if the number of methods
    std::getline(file, line);
    lineIdx++;

    int nb_methods = std::stoi(line);

    _methods.reserve(nb_methods);

    // Then, extract all the methods
    // There is a method at each 4 lines
    while (std::getline(file, line)) {
        lineIdx++;
        if (line.size() == 0) break;

        // Method in in the form:
        // <method_name>[arg1,arg2,...]

        std::string method_name = "";
        std::vector<std::string> method_args;
        int idx = 0;
        int num_open_brackets = 0;
        bool specialMethod = false;
        if (line[idx] == '<') {
            num_open_brackets++;
            idx++;
            while (line[idx] == '<') {
                num_open_brackets++;
                idx++;
            }
            specialMethod = true;
        }


        while (line[idx] != '[' && line[idx] != ';') {
            method_name += line[idx];
            idx++;
        }

        // Skip until the '>' if it is a special method
        if (specialMethod) {
            while (num_open_brackets > 0) {
                if (line[idx] == '<') {
                    num_open_brackets++;
                }
                if (line[idx] == '>') {
                    num_open_brackets--;
                }
                idx++;
            }
            // while (line[idx] != '>') {
            //     idx++;
            // }
        }

        // Now, skip until '['
        while (line[idx] != '[') {
            idx++;
        }

        while (line[idx] != ']') {
            idx++; // Ignore the '[' character or ',' character
            std::string arg = "";
            while (line[idx] != ',' && line[idx] != ']') {
                arg += line[idx];
                idx++;
            }
            if (arg.size() > 0)
                method_args.push_back(arg);
        }

        // Create the method as a USignature
        std::vector<int> args_pred;
        for (std::string arg_name: method_args) {
            args_pred.push_back(_htn.nameId(arg_name));
        }
        USignature method_usig(_htn.nameId(method_name), args_pred);

        _methods.push_back(method_usig);

        // New line contains the index of the task that this method can accomplish
        std::getline(file, line);

        int idx_task = std::stoi(line);

        if (idx_task > 0) {
            // Log::i("Method %s can accomplish the task %s\n", TOSTR(method_usig), TOSTR(_tasks[idx_task]));

            // Update TDG
            // Add an edge from the method to the task
            // Add an edge from the task to the method
            _vertices[_tasks[idx_task]]._outgoing_edges.push_back(&_methods.back());
            _vertices[method_usig]._incoming_edges.push_back(&_tasks[idx_task]);
        }

        // New line contains the subtasks of the method in the form: [<idx_subtask1> <idx_subtask2> ... <idx_subtaskN> -1]
        std::getline(file, line);
        int idx_line_subtask = 0;
        int idx_subtask = 0;
        while (line[idx_line_subtask] != '-') {
            std::string idx_subtask_str = "";
            while (line[idx_line_subtask] != ' ') {
                idx_subtask_str += line[idx_line_subtask];
                idx_line_subtask++;
            }
            idx_line_subtask++;
            idx_subtask++;
            int idx_subtask_int = std::stoi(idx_subtask_str);
            
            // If the subtask starts with __method_precondition or <method_prec>, ignore it
            if (idx_subtask == 1 && (_htn.toString(_tasks[idx_subtask_int]._name_id).find("__method_precondition") != std::string::npos || _htn.toString(_tasks[idx_subtask_int]._name_id).find("<method_prec>") != std::string::npos) || _htn.toString(_tasks[idx_subtask_int]._name_id).find("__immediate_method_precondition") != std::string::npos) {
                // Log::i("Ignore subtask %s\n", TOSTR(_tasks[idx_subtask_int]));
                continue;
            }

            // Log::i("Method %s  %d subtask -> %s\n", TOSTR(method_usig), idx_subtask, TOSTR(_tasks[idx_subtask_int]));



            // Update TDG
            // Add an edge from the method to the subtask
            // Add an edge from the subtask to the method
            _vertices[_tasks[idx_subtask_int]]._incoming_edges.push_back(&_methods.back());
            _vertices[method_usig]._outgoing_edges.push_back(&_tasks[idx_subtask_int]);
        }



        std::getline(file, line);
    }
}

// int TDG::getStateDependantHeuristicValue(const USignature& u, const USigSet& pos_facts, const USigSet& neg_facts, int node_budget, FactAnalysis& _analysis) {

//     // First, set all the temporary heuristic values to the existing heuristic values
//     // for (auto& [node, info]: _vertices) {
//     //     info._temp_heuristic_value = info._heuristic_value;
//     // }

//     // Now, check if executable, and if not, set the heuristic value to MAX_WEIGHT
//     // Afterward, we can recompute the heuristic value of the node

//     // Print all pos_facts
//     // Log::i("Positive facts:\n");
//     // for (const USignature& fact: pos_facts) {
//     //     Log::i("    %s\n", TOSTR(fact));
//     // }

//     // Log::i("Init state:\n");
//     // for (const USignature& fact: _init_state) {
//     //     Log::i("    %s\n", TOSTR(fact));
//     // }

//     USigSet current_pos_facts = pos_facts;
//     USigSet current_neg_facts = neg_facts;


//     int originalHeuristicValue = getBestHeuristicValue(u);
//     Log::i("Compute state dependant heuristic value for node %s\n", TOSTR(u));
//     Log::i("For now, its heuristic value is %d\n", originalHeuristicValue);
//     int new_heuristic_value = 0;

//     if (_htn.isReduction(u)) {

//     //     const Reduction& r = _htn.toReduction(u._name_id, u._args);
//     //     // Iterate over all the subtasks of the method

//     //     int num_subtasks = r.getSubtasks().size();
//     //     for (size_t offset = 0; offset < num_subtasks; offset++) {

//     //         Log::i("At offset %d/%d\n", offset, num_subtasks);
//     //         std::vector<USignature> children;
//     //         _traversal.getPossibleChildren(r.getSubtasks(), offset, children);
//     //         // Print all the possible children

//     //         int num_ok_children = 0;
//     //         for (const USignature& child: children) {
//     //             int heuristic_value = getBestHeuristicValue(child);
//     //             if (heuristic_value == MAX_WEIGHT)
//     //                 continue;

//     //             Log::i("    %s: %d\n", TOSTR(child), heuristic_value);
//     //             num_ok_children++;

//     //             // Print the precondition of the child
//     //             if (_htn.isAction(child)) {
//     //                 const Action& a = _htn.toAction(child._name_id, child._args);
//     //                 Log::i("        Preconditions:\n");
//     //                 for (const Signature& precond: a.getPreconditions()) {
//     //                     Log::i("            %s\n", TOSTR(precond));
//     //                 }
//     //             } else {
//     //                 const Reduction& r = _htn.toReduction(child._name_id, child._args);
//     //                 Log::i("        Preconditions:\n");
//     //                 for (const Signature& precond: r.getPreconditions()) {
//     //                     Log::i("            %s\n", TOSTR(precond));
//     //                 }
//     //             }
//     //         }
//     //     }



//         // TIME TO TEST
//         // First, get all grounding of the reduction
//         std::vector<USignature> groundings = getAllGrounding(u);
//         // Print all the groundings
//         Log::i("Groundings of %s:\n", TOSTR(u));
//         int min_value_grounding = MAX_WEIGHT;
//         for (const USignature& grounding: groundings) {
//             int heuristic_value = getBestHeuristicValue(grounding);
//             if (heuristic_value == MAX_WEIGHT) continue;
//             Log::i("    %s (heuristic value: %d)\n", TOSTR(grounding), heuristic_value);

//             // Assert that all their precondition can be satisfied
//             bool can_be_satisfied = true;
//             if (_htn.isAction(grounding)) {
//                 // const Action& a = _htn.toAction(grounding._name_id, grounding._args);
//                 // for (const Signature& precond: a.getPreconditions()) {
//                 //     if (pos_facts.find(precond) == pos_facts.end()) {
//                 //         Log::e("Precondition %s of action %s cannot be satisfied\n", TOSTR(precond), TOSTR(grounding));
//                 //     }
//                 // }
//             } else {
//                 const Reduction& r = _htn.toReduction(grounding._name_id, grounding._args);
//                 for (const Signature& precond: r.getPreconditions()) {
//                     Log::i("Check precondition %s\n", TOSTR(precond));
//                     if (!isReachable(precond._usig, precond._negated, pos_facts, neg_facts)) {
//                         Log::e("Precondition %s of method %s cannot be satisfied\n", TOSTR(precond), TOSTR(grounding));
//                         can_be_satisfied = false;
//                         break;
//                     }
//                 }
//             }

//             if (can_be_satisfied) {
//                 Log::i("All preconditions can be satisfied\n");
//             } else {
//                 Log::i("Not all preconditions can be satisfied\n");
//                 continue;
//             }

//             // Now, check if the first subtask can be satisfied
//             const Reduction& r = _htn.toReduction(grounding._name_id, grounding._args);
//             int num_subtasks = r.getSubtasks().size();
//             bool at_least_one_subtask = false;

//             int state_dependant_heuristic_value_offset_0 = MAX_WEIGHT;
//             new_heuristic_value = 0;
//             for (size_t offset = 0; offset < num_subtasks; offset++) {

//                 Log::i("At offset %d/%d\n", offset, num_subtasks);

//                 int min_heuristic_value_offset = MAX_WEIGHT;

//                 std::vector<USignature> children;
//                 _traversal.getPossibleChildren(r.getSubtasks(), offset, children);
//                 // Print all the possible children

//                 int num_ok_children = 0;
//                 for (const USignature& child: children) {

//                     int heuristic_value = getBestHeuristicValue(child);

//                     // For now, we only do the 0 offset
//                     // if (offset != 0) {
//                     //     min_heuristic_value_offset = std::min(min_heuristic_value_offset, heuristic_value);
//                     //     continue;
//                     // }

//                     int state_dependant_heuristic_value = MAX_WEIGHT;

//                     USigSet new_add;
//                     USigSet new_del;

//                     // Get all grounding of the child
//                     std::vector<USignature> child_groundings = getAllGrounding(child);
//                     for (const USignature& child_grounding: child_groundings) {
//                         Log::i("    Grounding of %s: %s\n", TOSTR(child), TOSTR(child_grounding));
//                         // If it not in the tdg, pass it
//                         if (_vertices.find(child_grounding) == _vertices.end()) {
//                             Log::e("Child %s not found in the TDG\n", TOSTR(child_grounding));
//                             continue;
//                         }
//                         // Check if the precondition of the child can be satisfied

//                         bool can_be_satisfied = true;
//                         if (_htn.isAction(child_grounding)) {
//                             const Action& a = _htn.toAction(child_grounding._name_id, child_grounding._args);
//                             for (const Signature& precond: a.getPreconditions()) {
//                                  if (!isReachable(precond._usig, precond._negated, current_pos_facts, current_neg_facts)) {
//                                     Log::e("Precondition %s of action %s cannot be satisfied\n", TOSTR(precond), TOSTR(child_grounding));
//                                     can_be_satisfied = false;
//                                 }
//                             }


//                             if (can_be_satisfied) {
//                                 for (const Signature& fact: a.getEffects()) {
//                                     if (fact._negated) {
//                                         new_del.insert(fact._usig);
//                                     } else {
//                                         new_add.insert(fact._usig);
//                                     }
//                                 }
//                             }

//                         } else {
//                             const Reduction& r = _htn.toReduction(child_grounding._name_id, child_grounding._args);
//                             for (const Signature& precond: r.getPreconditions()) {
//                                 if (!isReachable(precond._usig, precond._negated, current_pos_facts, current_neg_facts)) {
//                                     Log::e("Precondition %s of method %s cannot be satisfied\n", TOSTR(precond), TOSTR(child_grounding));
//                                     can_be_satisfied = false;
//                                 }
//                             }

//                             if (can_be_satisfied) {
//                                 for (const Signature& fact : _analysis.getPossibleFactChanges(child_grounding)) {
//                                     if (fact._negated) {
//                                         new_del.insert(fact._usig);
//                                     } else {
//                                         new_add.insert(fact._usig);
//                                     }
//                                 }
//                             }
//                         }


//                         if (can_be_satisfied) {
//                             int heuristic_value = getBestHeuristicValue(child_grounding);
//                             state_dependant_heuristic_value = std::min(state_dependant_heuristic_value, heuristic_value);
//                             min_heuristic_value_offset = std::min(min_heuristic_value_offset, heuristic_value);

                            
//                         }
//                     }

//                     current_pos_facts.insert(new_add.begin(), new_add.end());
//                     current_neg_facts.insert(new_del.begin(), new_del.end());
//                     new_add.clear();
//                     new_del.clear();

                    
                    

//                     Log::i("    %s: hV:%d State dependant hV: %d\n", TOSTR(child), heuristic_value, state_dependant_heuristic_value);
//                     num_ok_children++;
//                 }

//                 // if (num_ok_children > 0) {
//                 //     at_least_one_subtask = true;
//                 //     break;
//                 // }

//                 Log::i("Min heuristic value of offset %d: %d\n", offset, min_heuristic_value_offset);
//                 new_heuristic_value += min_heuristic_value_offset;
//             }
//             min_value_grounding = std::min(min_value_grounding, new_heuristic_value);

//         }

//         Log::i("Old heuristic value: %d New heuristic value: %d\n", originalHeuristicValue, min_value_grounding);
//         if (originalHeuristicValue != min_value_grounding) {
//             Log::w("Heuristic value of node %s has changed: %d -> %d\n", TOSTR(u), originalHeuristicValue, min_value_grounding);
//         }


//         int a = 0;
//         return originalHeuristicValue;
//     }

//     Log::i("=======================\n");
//     return 0;
// }


// int TDG::getStateDependantHeuristicValue(const USignature& u, const USigSet& pos_facts, const USigSet& neg_facts, int node_budget, FactAnalysis& _analysis) {

//     // First, set all the temporary heuristic values to the existing heuristic values
//     // for (auto& [node, info]: _vertices) {
//     //     info._temp_heuristic_value = info._heuristic_value;
//     // }

//     // Now, check if executable, and if not, set the heuristic value to MAX_WEIGHT
//     // Afterward, we can recompute the heuristic value of the node

//     // Print all pos_facts
//     // Log::i("Positive facts:\n");
//     // for (const USignature& fact: pos_facts) {
//     //     Log::i("    %s\n", TOSTR(fact));
//     // }

//     // Log::i("Init state:\n");
//     // for (const USignature& fact: _init_state) {
//     //     Log::i("    %s\n", TOSTR(fact));
//     // }

//     USigSet current_pos_facts = pos_facts;
//     USigSet current_neg_facts = neg_facts;


//     int originalHeuristicValue = getBestHeuristicValue(u);
//     Log::i("<<<<<<<<<<<<<<<<<<<<<<<<---------------------->>>>>>>>>>>>>>>>>>>>>>>>>>\n");
//     Log::i("Compute state dependant heuristic value for node %s\n", TOSTR(u));
//     Log::i("For now, its heuristic value is %d\n", originalHeuristicValue);
//     int new_heuristic_value = 0;

//     if (_htn.isReduction(u)) {

//         // TIME TO TEST
//         // First, get all grounding of the reduction
//         std::vector<USignature> groundings = getAllGrounding(u);
//         // Print all the groundings
//         Log::i("Groundings of %s:\n", TOSTR(u));
//         int min_value_grounding = MAX_WEIGHT;
//         for (const USignature& grounding: groundings) {
//             int heuristic_value_grounding = getHeuristicValue(grounding);
//             if (heuristic_value_grounding == MAX_WEIGHT) {
//                 Log::i("Cannot be grounded\n");
//                 continue;
//             }
//             Log::i("    %s (heuristic value: %d)\n", TOSTR(grounding), heuristic_value_grounding);

//             // Assert that all their precondition can be satisfied
//             bool can_be_satisfied = true;
//             if (_htn.isAction(grounding)) {
//                 // const Action& a = _htn.toAction(grounding._name_id, grounding._args);
//                 // for (const Signature& precond: a.getPreconditions()) {
//                 //     if (pos_facts.find(precond) == pos_facts.end()) {
//                 //         Log::e("Precondition %s of action %s cannot be satisfied\n", TOSTR(precond), TOSTR(grounding));
//                 //     }
//                 // }
//             } else {
//                 const Reduction& r = _htn.toReduction(grounding._name_id, grounding._args);
//                 for (const Signature& precond: r.getPreconditions()) {
//                     // Log::i("Check precondition %s\n", TOSTR(precond));
//                     if (!isReachable(precond._usig, precond._negated, pos_facts, neg_facts)) {
//                         Log::e("Precondition %s of method %s cannot be satisfied\n", TOSTR(precond), TOSTR(grounding));
//                         can_be_satisfied = false;
//                         break;
//                     }
//                 }
//             }

//             if (can_be_satisfied) {
//                 Log::i("All preconditions can be satisfied for this grounding\n");
//             } else {
//                 Log::i("Not all preconditions can be satisfied for this grounding\n");
//                 continue;
//             }

//             // Get the tdg node of the grounding
//             TDGVertexInfo& grounding_vertex = _vertices[grounding];

//             if (grounding_vertex._outgoing_edges.size() == 0) {
//                 Log::i("No outgoing edges for %s\n", TOSTR(grounding));
//                 min_value_grounding = heuristic_value_grounding;
//                 break;
//             }

//             // Get the first task of the grounding
//             const USignature* first_task = grounding_vertex._outgoing_edges[0];

//             int orignal_heuristic_value_first_task = getBestHeuristicValue(*first_task);

//             Log::i("First task of %s: %s with heuristic value:%d\n", TOSTR(grounding), TOSTR(*first_task), orignal_heuristic_value_first_task);


//             int new_heuristic_value = MAX_WEIGHT;

//             // If it is an action, check if the precondition can be satisfied
//             if (_htn.isAction(*first_task)) {
//                 Log::i("This is an action\n");
//                 const Action& a = _htn.toAction(first_task->_name_id, first_task->_args);
//                 for (const Signature& precond: a.getPreconditions()) {
//                     if (!isReachable(precond._usig, precond._negated, current_pos_facts, current_neg_facts)) {
//                         Log::e("Precondition %s of action %s cannot be satisfied\n", TOSTR(precond), TOSTR(*first_task));
//                         can_be_satisfied = false;
//                         break;
//                     }
//                 }
//                 if (can_be_satisfied) {
//                     new_heuristic_value = orignal_heuristic_value_first_task;
//                 }
//             } else {

//                 // Get all the methods which can accomplish it
//                 const std::vector<USignature*> methods = _vertices[*first_task]._outgoing_edges;

//                 Log::i("Number of methods that can accomplish the task: %d\n", methods.size());

//                 // Print all the methods which can accomplish the task with their heuristic value
//                 for (const USignature* method: methods) {
//                     int method_heuristic_value = getBestHeuristicValue(*method);
//                     Log::i("    Method %s: %d\n", TOSTR(*method), method_heuristic_value);
//                     // Check if the precondition of the method can be satisfied
//                     bool can_be_satisfied = true;
//                     if (_htn.isAction(*method)) {
//                         const Action& a = _htn.toAction(method->_name_id, method->_args);
//                         for (const Signature& precond: a.getPreconditions()) {
//                             if (!isReachable(precond._usig, precond._negated, current_pos_facts, current_neg_facts)) {
//                                 Log::e("Precondition %s of action %s cannot be satisfied\n", TOSTR(precond), TOSTR(*method));
//                                 can_be_satisfied = false;
//                                 break;
//                             }
//                         }
//                     } else {
//                         const Reduction& r = _htn.toReduction(method->_name_id, method->_args);
//                         for (const Signature& precond: r.getPreconditions()) {
//                             if (!isReachable(precond._usig, precond._negated, current_pos_facts, current_neg_facts)) {
//                                 Log::e("Precondition %s of method %s cannot be satisfied\n", TOSTR(precond), TOSTR(*method));
//                                 can_be_satisfied = false;
//                                 break;
//                             }
//                         }
//                     }
//                     if (can_be_satisfied) {
//                         Log::i("      -> All preconditions can be satisfied\n");
//                         new_heuristic_value = std::min(new_heuristic_value, method_heuristic_value);
//                         if (new_heuristic_value == orignal_heuristic_value_first_task) break;
//                     } else {
//                         Log::i("      -> Not all preconditions can be satisfied\n");
//                     }
//                 }
//             }

//             if (new_heuristic_value == MAX_WEIGHT) {
//                 Log::i("No method can accomplish the first task\n");
//                 heuristic_value_grounding = MAX_WEIGHT;
//             } else if (new_heuristic_value != orignal_heuristic_value_first_task) {
//                 Log::i("New heuristic value first task: %d\n", new_heuristic_value);
//                 int diff = new_heuristic_value - orignal_heuristic_value_first_task;
//                 Log::i("So new heuristic value for %s: %d\n", TOSTR(grounding), heuristic_value_grounding + diff);
//                 heuristic_value_grounding += diff;
//             }

//             min_value_grounding = std::min(min_value_grounding, heuristic_value_grounding);
//             if (min_value_grounding == originalHeuristicValue) break;
//         }
        


//         if (originalHeuristicValue != min_value_grounding) {
//             Log::w("Heuristic value of node %s has changed: %d -> %d\n", TOSTR(u), originalHeuristicValue, min_value_grounding);
//             originalHeuristicValue = min_value_grounding;
//         }

//             // Now, check if the first subtask can be satisfied
//         //     const Reduction& r = _htn.toReduction(grounding._name_id, grounding._args);
//         //     int num_subtasks = r.getSubtasks().size();
//         //     bool at_least_one_subtask = false;

//         //     int state_dependant_heuristic_value_offset_0 = MAX_WEIGHT;
//         //     new_heuristic_value = 0;
//         //     for (size_t offset = 0; offset < num_subtasks; offset++) {

//         //         Log::i("At offset %d/%d\n", offset, num_subtasks);

//         //         int min_heuristic_value_offset = MAX_WEIGHT;

//         //         std::vector<USignature> children;
//         //         _traversal.getPossibleChildren(r.getSubtasks(), offset, children);
//         //         // Print all the possible children

//         //         int num_ok_children = 0;
//         //         for (const USignature& child: children) {

//         //             int heuristic_value = getBestHeuristicValue(child);

//         //             // For now, we only do the 0 offset
//         //             // if (offset != 0) {
//         //             //     min_heuristic_value_offset = std::min(min_heuristic_value_offset, heuristic_value);
//         //             //     continue;
//         //             // }

//         //             int state_dependant_heuristic_value = MAX_WEIGHT;

//         //             USigSet new_add;
//         //             USigSet new_del;

//         //             // Get all grounding of the child
//         //             std::vector<USignature> child_groundings = getAllGrounding(child);
//         //             for (const USignature& child_grounding: child_groundings) {
//         //                 Log::i("    Grounding of %s: %s\n", TOSTR(child), TOSTR(child_grounding));
//         //                 // If it not in the tdg, pass it
//         //                 if (_vertices.find(child_grounding) == _vertices.end()) {
//         //                     Log::e("Child %s not found in the TDG\n", TOSTR(child_grounding));
//         //                     continue;
//         //                 }
//         //                 // Check if the precondition of the child can be satisfied

//         //                 bool can_be_satisfied = true;
//         //                 if (_htn.isAction(child_grounding)) {
//         //                     const Action& a = _htn.toAction(child_grounding._name_id, child_grounding._args);
//         //                     for (const Signature& precond: a.getPreconditions()) {
//         //                          if (!isReachable(precond._usig, precond._negated, current_pos_facts, current_neg_facts)) {
//         //                             Log::e("Precondition %s of action %s cannot be satisfied\n", TOSTR(precond), TOSTR(child_grounding));
//         //                             can_be_satisfied = false;
//         //                         }
//         //                     }


//         //                     if (can_be_satisfied) {
//         //                         for (const Signature& fact: a.getEffects()) {
//         //                             if (fact._negated) {
//         //                                 new_del.insert(fact._usig);
//         //                             } else {
//         //                                 new_add.insert(fact._usig);
//         //                             }
//         //                         }
//         //                     }

//         //                 } else {
//         //                     const Reduction& r = _htn.toReduction(child_grounding._name_id, child_grounding._args);
//         //                     for (const Signature& precond: r.getPreconditions()) {
//         //                         if (!isReachable(precond._usig, precond._negated, current_pos_facts, current_neg_facts)) {
//         //                             Log::e("Precondition %s of method %s cannot be satisfied\n", TOSTR(precond), TOSTR(child_grounding));
//         //                             can_be_satisfied = false;
//         //                         }
//         //                     }

//         //                     if (can_be_satisfied) {
//         //                         for (const Signature& fact : _analysis.getPossibleFactChanges(child_grounding)) {
//         //                             if (fact._negated) {
//         //                                 new_del.insert(fact._usig);
//         //                             } else {
//         //                                 new_add.insert(fact._usig);
//         //                             }
//         //                         }
//         //                     }
//         //                 }


//         //                 if (can_be_satisfied) {
//         //                     int heuristic_value = getBestHeuristicValue(child_grounding);
//         //                     state_dependant_heuristic_value = std::min(state_dependant_heuristic_value, heuristic_value);
//         //                     min_heuristic_value_offset = std::min(min_heuristic_value_offset, heuristic_value);

                            
//         //                 }
//         //             }

//         //             current_pos_facts.insert(new_add.begin(), new_add.end());
//         //             current_neg_facts.insert(new_del.begin(), new_del.end());
//         //             new_add.clear();
//         //             new_del.clear();

                    
                    

//         //             Log::i("    %s: hV:%d State dependant hV: %d\n", TOSTR(child), heuristic_value, state_dependant_heuristic_value);
//         //             num_ok_children++;
//         //         }

//         //         // if (num_ok_children > 0) {
//         //         //     at_least_one_subtask = true;
//         //         //     break;
//         //         // }

//         //         Log::i("Min heuristic value of offset %d: %d\n", offset, min_heuristic_value_offset);
//         //         new_heuristic_value += min_heuristic_value_offset;
//         //     }
//         //     min_value_grounding = std::min(min_value_grounding, new_heuristic_value);

//         // }

//         // Log::i("Old heuristic value: %d New heuristic value: %d\n", originalHeuristicValue, min_value_grounding);
//         // if (originalHeuristicValue != min_value_grounding) {
//         //     Log::w("Heuristic value of node %s has changed: %d -> %d\n", TOSTR(u), originalHeuristicValue, min_value_grounding);
//         // }


//         // int a = 0;
//         // return originalHeuristicValue;
//     }

//     Log::i("=======================\n");
//     return originalHeuristicValue;
// }