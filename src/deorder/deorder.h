
#ifndef DEORDER_TWO_H
#define DEORDER_TWO_H

#include <string>
#include <vector>
#include <map>
#include <set>
#include <stack>
#include <unordered_set>

#include "deorder/deorder.h"

#include "data/htn_instance.h"
#include "data/plan.h"
#include "sat/sat_interface.h"
#include "libpanda.hpp"
#include "deorder/algo/deorder_algo.h"

/**
 * @brief Enumeration to select which solver to use.
 */
enum class DeorderAlgoType
{
    SAT,
    PRF,
};

class Deorder
{
private:
    HtnInstance &_htn;
    std::string _plan_str;

    const bool _only_deordering = true;
    int _original_plan_length;

    std::unordered_map<int, PlanItem> _plan_map;
    std::unordered_map<int, std::vector<plan_step>> _plan_map_linearized;
    std::unordered_map<int, method> _id_method_to_parsed_method;
    std::vector<int> _initial_network_ids;
    std::vector<int> _prim_plan;
    std::unordered_set<int> _method_precondition_ids;
    std::unordered_map<std::string, std::set<std::vector<plan_step>>> _linearizations;

    // Indicate for each predicate the ids of the primitive tasks that add or delete it
    NodeHashMap<Signature, NodeHashSet<int>, SignatureHasher> adders;
    NodeHashMap<Signature, NodeHashSet<int>, SignatureHasher> deleters;
    NodeHashMap<Signature, NodeHashSet<int>, SignatureHasher> consumers;

    int _last_id;

    int _id_init_action;
    int _id_goal_action;
    Action _init_action;
    Action _goal_action;

    // Store linearization info from plan verification
    std::map<int, std::vector<std::pair<std::map<std::string, int>, std::map<std::string, std::string>>>> _possibleMethodInstantiations;

    // Store mandatory ordering constraints derived from hierarchy
    NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual> _mandatory_ordering_constrains;

    // Store required Sat variables

    struct PairHasher
    {
        template <class T1, class T2>
        std::size_t operator()(const std::pair<T1, T2> &p) const
        {
            // Cantor pairing function for unique mapping of two integers
            auto t1 = p.first;
            auto t2 = p.second;
            return ((t1 + t2) * (t1 + t2 + 1)) / 2 + t2;
        }
    };

public:
    /**
     * @brief Create a Deorder coordinator with chosen solver & mode.
     * @param planFile Path to the plan file.
     * @param htn      Reference to the HTN instance.
     * @param solverType Which underlying solver to instantiate (SAT, etc.).
     * @param mode       Whether we do DEORDERING or REORDERING.
     */
    Deorder(const std::string &planFile,
             HtnInstance &htn,
             DeorderAlgoType algoType,
             DeorderMode mode);

private:
    void parsePlan(std::ifstream &planFile);
    void printOriginalPlan();
    void addMethodsPreconditionsAsActionsInPlan();
    void getMandatoryOrderingConstrainsInHierarchy();
    NodeHashSet<int> collectChildrenActions(int id);
    void computeAddersAndDeleters();
    int getCriticalPath(const NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual> &final_ordering);
    void writeGraphToFile(const NodeHashSet<OrderConstraint, OrderConstraintHasher, OrderConstraintEqual> &final_ordering, const std::string &filename);
    std::vector<std::pair<std::string, std::string>> getFullOrdering(const method &m);
};

#endif