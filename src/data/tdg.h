#ifndef SIBYLSAT_TDG_H
#define SIBYLSAT_TDG_H

#include <cstddef>
#include <filesystem>
#include <istream>
#include <string>
#include <utility>
#include <vector>

#include "data/htn_instance.h"
#include "data/plan.h"
#include "algo/q_constant_manager.h"

/**
 * Admissible task-decomposition heuristic built from the grounded TDG emitted
 * by pandaPIgrounder.
 *
 * Primitive tasks cost one, methods cost the sum of their subtasks, and
 * abstract tasks cost the cheapest applicable method. Recursive components are
 * evaluated to a fixed point.
 */
class TDG {
private:
    using VertexId = size_t;
    static constexpr int UNREACHABLE_COST = 10000;

    class Vertex {
    public:
        explicit Vertex(USignature signature) : signature(std::move(signature)) {}

        USignature signature;
        std::vector<VertexId> children;
        int cost = UNREACHABLE_COST;
    };

    HtnInstance& _htn;
    QConstantManager& _q_constants;
    std::vector<Vertex> _vertices;
    NodeHashMap<USignature, VertexId, USignatureHasher> _vertex_ids;
    NodeHashMap<int, std::vector<VertexId>> _vertices_by_name;
    NodeHashMap<int, int> _minimum_cost_by_name;
    NodeHashMap<int, size_t> _grounded_arity_by_name;
    std::vector<std::vector<VertexId>> _strongly_connected_components;
    int _noop_action_id = -1;

    void loadGroundedGraph(const std::filesystem::path& filename);
    std::vector<VertexId> loadTasks(std::istream& input, size_t& lineNumber);
    void loadMethods(std::istream& input, size_t& lineNumber, const std::vector<VertexId>& taskVertices);
    void recordGroundedArities();

    VertexId getOrCreateVertex(USignature signature);
    void addEdge(VertexId source, VertexId destination);
    USignature parseTask(const std::string& line, size_t lineNumber);
    USignature parseMethod(const std::string& line, size_t lineNumber);
    USignature parseSignature(const std::string& line, size_t nameStart, size_t nameEnd, size_t argumentsStart, size_t lineNumber);
    bool shouldIgnoreCompiledPrecondition(VertexId task, size_t subtaskNumber) const;

    void computeHeuristicValues();
    void visitForStronglyConnectedComponents(VertexId vertex, int& nextIndex, std::vector<int>& indices, std::vector<int>& lowLinks, std::vector<bool>& onStack, std::vector<VertexId>& stack);
    void orderStronglyConnectedComponents();
    void visitComponent(size_t component, const std::vector<std::vector<size_t>>& componentEdges, std::vector<bool>& visited, std::vector<size_t>& order) const;
    int evaluateVertexCost(VertexId vertex) const;
    int addCosts(int left, int right) const;

    USignature normalizeToGroundedArity(const USignature& signature) const;
    bool isCompatibleGrounding(const USignature& grounding, const std::vector<std::vector<int>>& eligibleArguments) const;

public:
    /** Load the grounded task-decomposition graph and compute its heuristic. */
    TDG(HtnInstance& htn, QConstantManager& qConstants);

    /** Return the heuristic cost of an exact grounded graph vertex. */
    int getHeuristicValue(const USignature& signature) const;
    /** Return the cheapest graph vertex compatible with a lifted or pseudo-ground operation. */
    int getBestHeuristicValue(const USignature& signature);
    /** Sum the admissible costs of a decoded abstract frontier plan. */
    int getVirtualPlanHeuristicValue(const std::vector<PlanItem>& virtualPlan) const;
};

#endif
