#ifndef SIBYLSAT_TDG_H
#define SIBYLSAT_TDG_H

#include <stack>
#include <unordered_set>

#include "data/htn_instance.h"
#include "algo/network_traversal.h"
#include "data/plan.h"
#include "algo/fact_analysis.h"

const int MAX_WEIGHT = 10000;

// Create a class for the vertices of the TDG with outgoing/incoming edges + the label of the vertice
class TDGVertexInfo
{
    // Let the TDG class access the private members of this class
    friend class TDG;

    int _heuristic_value = MAX_WEIGHT;
    int _temp_heuristic_value = MAX_WEIGHT;
    std::vector<USignature*> _outgoing_edges;
    std::vector<USignature*> _incoming_edges;
};

class TDG
{

private:
    HtnInstance& _htn;
    NodeHashMap<USignature, TDGVertexInfo, USignatureHasher> _vertices; // The key is the label of the vertice (a ground task or method), the value is the info on the vertice

    NodeHashMap<int, int> _min_heuristic_values_for_name_id; // The key is the name_id of the vertice (correspond to unique method or task name), the value is the best heuristic value of the vertice

    NodeHashMap<int, int> _number_params_to_keep_for_name_id; // If the TDG has less parameters than the operator in _htn, this map stores the number of parameters to keep to convert the operator in 
    // _htn to the operator in the TDG

    int special_noop_action_id = -1; // The id of the special noop action if it exists (panda use it for tasks that have no methods which can accomplish them)

    NetworkTraversal _traversal;

    USigSet _init_state;

    // All the operators
    std::vector<USignature> _methods;
    std::vector<USignature> _tasks; // The first <nb_primitive_tasks> tasks are primitive tasks, the rest are compound tasks
    int _nb_primitive_tasks;

    std::vector<FlatHashSet<const USignature*, USignaturePtrHasher, USignaturePtrEqual>> _sccs;

    void tarjanDFS(const USignature& u, int& index, std::stack<const USignature*>& stack, 
                   std::unordered_map<const USignature* , int, USignaturePtrHasher, USignaturePtrEqual>& indices, 
                   std::unordered_map<const USignature* , int, USignaturePtrHasher, USignaturePtrEqual>& lowLinks, 
                   std::unordered_map<const USignature* , bool, USignaturePtrHasher, USignaturePtrEqual>& onStack, 
                   std::vector<FlatHashSet<const USignature*, USignaturePtrHasher, USignaturePtrEqual>>& sccs);

    void topologicalSortUtil(int v, std::unordered_map<int, std::unordered_set<int>>& condensedGraph, 
                             std::unordered_set<int>& visited, std::stack<int>& Stack);

    void computeLiftedTDG();

    std::vector<USignature> getAllGrounding(const USignature& u);

public:



    /**
     * Constructor.
     * Construct the TDG as defined in the paper: "An Admissible HTN Planning Heuristic"
     * @param htn The HTN instance
    */
    explicit TDG(HtnInstance& htn);

    void pandaPiGrounderExtractAvailableMethods(std::ifstream& file, int& lineIdx);
    void pandaPiGrounderExtractAvailableTasks(std::ifstream& file, int& lineIdx);
    void computeHeuristicValues();
    void computeSCCs();
    void sortSCCsInTopologicalOrder();
    int getHeuristicValue(const USignature& u) const;
    int getBestHeuristicValue(const USignature& u);
    int getVirtualPlanHeuristicValue(const std::vector<PlanItem>& virtualPlan) const;
    // int getStateDependantHeuristicValue(const USignature& u, const USigSet& pos_facts, const USigSet& neg_facts, int node_budget, FactAnalysis& _analysis);
    const int getMaxWeight() const { return MAX_WEIGHT; }
};

#endif // SIBYLSAT_TDG_H