#include "data/tdg.h"

#include <algorithm>
#include <cctype>
#include <fstream>
#include <sstream>
#include <stdexcept>

#include "util/log.h"
#include "util/names.h"
#include "util/project_utils.h"

namespace {

std::string readRequiredLine(std::istream& input, size_t& lineNumber, const std::string& description) {
    std::string line;
    if (!std::getline(input, line)) {
        throw std::runtime_error("Unexpected end of grounded problem while reading " + description);
    }
    lineNumber++;
    return line;
}

void seekSection(std::istream& input, size_t& lineNumber, const std::string& section) {
    std::string line;
    while (std::getline(input, line)) {
        lineNumber++;
        if (line == section) return;
    }
    throw std::runtime_error("Section '" + section + "' not found in grounded problem");
}

int parseInteger(const std::string& line, size_t lineNumber, const std::string& description) {
    std::istringstream parser(line);
    int value;
    if (!(parser >> value)) {
        throw std::runtime_error("Invalid " + description + " at grounded-problem line " + std::to_string(lineNumber));
    }

    std::string trailing;
    if (parser >> trailing) {
        throw std::runtime_error("Unexpected text after " + description + " at grounded-problem line " + std::to_string(lineNumber));
    }
    return value;
}

} // namespace

TDG::TDG(HtnInstance& htn, QConstantManager& qConstants) : _htn(htn), _q_constants(qConstants) {
    Log::i("Create TDG\n");
    loadGroundedGraph(getProblemProcessingDir() / "problem.sas");
    recordGroundedArities();
    computeHeuristicValues();
    Log::i("TDG heuristic values computed\n");
}

void TDG::loadGroundedGraph(const std::filesystem::path& filename) {
    std::ifstream input(filename);
    if (!input) {
        throw std::runtime_error("Could not open grounded problem: " + filename.string());
    }

    size_t lineNumber = 0;
    std::vector<VertexId> taskVertices = loadTasks(input, lineNumber);
    loadMethods(input, lineNumber, taskVertices);
}

std::vector<TDG::VertexId> TDG::loadTasks(std::istream& input, size_t& lineNumber) {
    seekSection(input, lineNumber, ";; tasks (primitive and abstract)");

    const std::string primitiveCountLine = readRequiredLine(input, lineNumber, "the primitive task count");
    const int primitiveTaskCount = parseInteger(primitiveCountLine, lineNumber, "primitive task count");
    if (primitiveTaskCount < 0) {
        throw std::runtime_error("Negative primitive task count at grounded-problem line " + std::to_string(lineNumber));
    }

    std::vector<VertexId> tasks;
    std::string line;
    while (std::getline(input, line)) {
        lineNumber++;
        if (line.empty()) break;

        USignature task = parseTask(line, lineNumber);
        if (_htn.toString(task._name_id) == "__noop") _noop_action_id = task._name_id;
        tasks.push_back(getOrCreateVertex(std::move(task)));
    }
    return tasks;
}

void TDG::loadMethods(std::istream& input, size_t& lineNumber, const std::vector<VertexId>& taskVertices) {
    seekSection(input, lineNumber, ";; methods");

    const std::string methodCountLine = readRequiredLine(input, lineNumber, "the method count");
    const int methodCount = parseInteger(methodCountLine, lineNumber, "method count");
    if (methodCount < 0) {
        throw std::runtime_error("Negative method count at grounded-problem line " + std::to_string(lineNumber));
    }

    for (int methodNumber = 0; methodNumber < methodCount; methodNumber++) {
        const std::string methodLine = readRequiredLine(input, lineNumber, "method " + std::to_string(methodNumber));
        const VertexId method = getOrCreateVertex(parseMethod(methodLine, lineNumber));

        const std::string achievedTaskLine = readRequiredLine(input, lineNumber, "the method's achieved task");
        const int achievedTask = parseInteger(achievedTaskLine, lineNumber, "achieved task index");
        if (achievedTask >= static_cast<int>(taskVertices.size())) {
            throw std::runtime_error("Achieved task index out of range at grounded-problem line " + std::to_string(lineNumber));
        }
        // Index zero is the grounder's artificial top task and has no parent edge.
        if (achievedTask > 0) addEdge(taskVertices[achievedTask], method);

        const std::string subtasksLine = readRequiredLine(input, lineNumber, "the method's subtasks");
        std::istringstream subtasks(subtasksLine);
        int subtaskIndex;
        size_t subtaskNumber = 0;
        bool foundTerminator = false;
        while (subtasks >> subtaskIndex) {
            if (subtaskIndex == -1) {
                foundTerminator = true;
                break;
            }
            subtaskNumber++;
            if (subtaskIndex < 0 || subtaskIndex >= static_cast<int>(taskVertices.size())) {
                throw std::runtime_error("Subtask index out of range at grounded-problem line " + std::to_string(lineNumber));
            }
            const VertexId subtask = taskVertices[subtaskIndex];
            if (!shouldIgnoreCompiledPrecondition(subtask, subtaskNumber)) addEdge(method, subtask);
        }
        if (!foundTerminator) {
            throw std::runtime_error("Missing -1 after subtasks at grounded-problem line " + std::to_string(lineNumber));
        }

        // Ordering constraints are irrelevant because the heuristic sums all subtasks.
        readRequiredLine(input, lineNumber, "the method's ordering constraints");
    }
}

TDG::VertexId TDG::getOrCreateVertex(USignature signature) {
    auto existing = _vertex_ids.find(signature);
    if (existing != _vertex_ids.end()) return existing->second;

    const VertexId id = _vertices.size();
    _vertices.emplace_back(std::move(signature));
    _vertex_ids.emplace(_vertices.back().signature, id);
    _vertices_by_name[_vertices.back().signature._name_id].push_back(id);
    return id;
}

void TDG::addEdge(VertexId source, VertexId destination) {
    // Keep duplicate subtask edges: a method containing the same task twice
    // must also count that task twice in its heuristic value.
    _vertices[source].children.push_back(destination);
}

USignature TDG::parseTask(const std::string& line, size_t lineNumber) {
    if (line.size() < 3 || (line[0] != '0' && line[0] != '1') || !std::isspace(static_cast<unsigned char>(line[1]))) {
        throw std::runtime_error("Invalid task at grounded-problem line " + std::to_string(lineNumber));
    }

    const size_t argumentsStart = line.find('[', 2);
    const size_t nameEnd = argumentsStart == std::string::npos ? line.size() : argumentsStart;
    return parseSignature(line, 2, nameEnd, argumentsStart, lineNumber);
}

USignature TDG::parseMethod(const std::string& line, size_t lineNumber) {
    if (line.empty()) {
        throw std::runtime_error("Empty method at grounded-problem line " + std::to_string(lineNumber));
    }

    size_t nameStart = 0;
    size_t nameEnd = line.find_first_of("[;");
    size_t argumentsStart = line.find('[');

    // Special grounder-generated methods use <...;name>[...] notation. Match the
    // name representation used by the lifted reader while skipping the prefix.
    if (line.front() == '<') {
        while (nameStart < line.size() && line[nameStart] == '<') nameStart++;
        nameEnd = line.find_first_of("[;", nameStart);

        int depth = static_cast<int>(nameStart);
        size_t prefixEnd = nameEnd;
        while (prefixEnd < line.size() && depth > 0) {
            if (line[prefixEnd] == '<') depth++;
            if (line[prefixEnd] == '>') depth--;
            prefixEnd++;
        }
        argumentsStart = line.find('[', prefixEnd);
    }

    if (nameEnd == std::string::npos) nameEnd = line.size();
    return parseSignature(line, nameStart, nameEnd, argumentsStart, lineNumber);
}

USignature TDG::parseSignature(const std::string& line, size_t nameStart, size_t nameEnd, size_t argumentsStart, size_t lineNumber) {
    if (nameStart >= nameEnd || nameEnd > line.size()) {
        throw std::runtime_error("Missing operation name at grounded-problem line " + std::to_string(lineNumber));
    }

    std::vector<int> arguments;
    if (argumentsStart != std::string::npos) {
        const size_t argumentsEnd = line.find(']', argumentsStart + 1);
        if (argumentsEnd == std::string::npos) {
            throw std::runtime_error("Missing ']' at grounded-problem line " + std::to_string(lineNumber));
        }

        size_t argumentStart = argumentsStart + 1;
        while (argumentStart < argumentsEnd) {
            const size_t separator = line.find(',', argumentStart);
            const size_t argumentEnd = separator == std::string::npos || separator > argumentsEnd ? argumentsEnd : separator;
            if (argumentEnd == argumentStart) {
                throw std::runtime_error("Empty argument at grounded-problem line " + std::to_string(lineNumber));
            }
            arguments.push_back(_htn.nameId(line.substr(argumentStart, argumentEnd - argumentStart)));
            argumentStart = argumentEnd + 1;
        }
    }

    return USignature(_htn.nameId(line.substr(nameStart, nameEnd - nameStart)), std::move(arguments));
}

bool TDG::shouldIgnoreCompiledPrecondition(VertexId task, size_t subtaskNumber) const {
    const std::string name = _htn.toString(_vertices[task].signature._name_id);
    const bool firstMethodPrecondition = subtaskNumber == 1 && (name.find("__method_precondition") != std::string::npos || name.find("<method_prec>") != std::string::npos);
    return firstMethodPrecondition || name.find("__immediate_method_precondition") != std::string::npos;
}

void TDG::recordGroundedArities() {
    for (const Vertex& vertex : _vertices) {
        const USignature& signature = vertex.signature;
        size_t liftedArity;

        if (_htn.isAction(signature)) {
            liftedArity = _htn.getActionTemplate(signature._name_id).getArguments().size();
        } else if (_htn.isReduction(signature)) {
            if (_htn.toString(signature._name_id).find("__top_method") != std::string::npos) continue;
            liftedArity = _htn.getReductionTemplate(signature._name_id).getArguments().size();
        } else {
            continue;
        }

        const size_t groundedArity = signature._args.size();
        if (groundedArity > liftedArity) {
            throw std::runtime_error("Grounded operation has more arguments than its lifted template: " + _htn.toString(signature._name_id));
        }
        if (groundedArity < liftedArity) _grounded_arity_by_name[signature._name_id] = groundedArity;
    }
}

void TDG::computeHeuristicValues() {
    const size_t vertexCount = _vertices.size();
    std::vector<int> indices(vertexCount, -1);
    std::vector<int> lowLinks(vertexCount, -1);
    std::vector<bool> onStack(vertexCount, false);
    std::vector<VertexId> stack;
    int nextIndex = 0;

    _strongly_connected_components.clear();
    for (VertexId vertex = 0; vertex < vertexCount; vertex++) {
        if (indices[vertex] == -1) visitForStronglyConnectedComponents(vertex, nextIndex, indices, lowLinks, onStack, stack);
    }
    orderStronglyConnectedComponents();

    // Dependencies occur later in topological order, so evaluate components in reverse.
    for (auto component = _strongly_connected_components.rbegin(); component != _strongly_connected_components.rend(); ++component) {
        bool changed = true;
        while (changed) {
            changed = false;
            for (VertexId vertex : *component) {
                const int cost = evaluateVertexCost(vertex);
                if (cost != _vertices[vertex].cost) {
                    _vertices[vertex].cost = cost;
                    changed = true;
                }
            }
        }
    }

    _minimum_cost_by_name.clear();
    for (const Vertex& vertex : _vertices) {
        auto [entry, inserted] = _minimum_cost_by_name.emplace(vertex.signature._name_id, vertex.cost);
        if (!inserted) entry->second = std::min(entry->second, vertex.cost);
        Log::d("TDG heuristic value of %s is %d\n", TOSTR(vertex.signature), vertex.cost);
    }
}

void TDG::visitForStronglyConnectedComponents(VertexId vertex, int& nextIndex, std::vector<int>& indices, std::vector<int>& lowLinks, std::vector<bool>& onStack, std::vector<VertexId>& stack) {
    indices[vertex] = nextIndex;
    lowLinks[vertex] = nextIndex;
    nextIndex++;
    stack.push_back(vertex);
    onStack[vertex] = true;

    for (VertexId child : _vertices[vertex].children) {
        if (indices[child] == -1) {
            visitForStronglyConnectedComponents(child, nextIndex, indices, lowLinks, onStack, stack);
            lowLinks[vertex] = std::min(lowLinks[vertex], lowLinks[child]);
        } else if (onStack[child]) {
            lowLinks[vertex] = std::min(lowLinks[vertex], indices[child]);
        }
    }

    if (lowLinks[vertex] != indices[vertex]) return;

    std::vector<VertexId> component;
    VertexId member;
    do {
        member = stack.back();
        stack.pop_back();
        onStack[member] = false;
        component.push_back(member);
    } while (member != vertex);
    _strongly_connected_components.push_back(std::move(component));
}

void TDG::orderStronglyConnectedComponents() {
    const size_t componentCount = _strongly_connected_components.size();
    std::vector<size_t> componentOfVertex(_vertices.size());
    for (size_t component = 0; component < componentCount; component++) {
        for (VertexId vertex : _strongly_connected_components[component]) componentOfVertex[vertex] = component;
    }

    std::vector<std::vector<size_t>> componentEdges(componentCount);
    for (size_t component = 0; component < componentCount; component++) {
        for (VertexId vertex : _strongly_connected_components[component]) {
            for (VertexId child : _vertices[vertex].children) {
                const size_t destination = componentOfVertex[child];
                if (destination == component) continue;
                std::vector<size_t>& edges = componentEdges[component];
                if (std::find(edges.begin(), edges.end(), destination) == edges.end()) edges.push_back(destination);
            }
        }
    }

    std::vector<bool> visited(componentCount, false);
    std::vector<size_t> order;
    for (size_t component = 0; component < componentCount; component++) {
        if (!visited[component]) visitComponent(component, componentEdges, visited, order);
    }
    std::reverse(order.begin(), order.end());

    std::vector<std::vector<VertexId>> orderedComponents;
    orderedComponents.reserve(componentCount);
    for (size_t component : order) orderedComponents.push_back(std::move(_strongly_connected_components[component]));
    _strongly_connected_components = std::move(orderedComponents);
}

void TDG::visitComponent(size_t component, const std::vector<std::vector<size_t>>& componentEdges, std::vector<bool>& visited, std::vector<size_t>& order) const {
    visited[component] = true;
    for (size_t child : componentEdges[component]) {
        if (!visited[child]) visitComponent(child, componentEdges, visited, order);
    }
    order.push_back(component);
}

int TDG::evaluateVertexCost(VertexId vertex) const {
    const Vertex& current = _vertices[vertex];
    if (current.signature._name_id == _noop_action_id) return 0;
    if (_htn.isAction(current.signature)) return 1;

    if (_htn.isReduction(current.signature)) {
        int cost = 0;
        for (VertexId child : current.children) cost = addCosts(cost, _vertices[child].cost);
        return cost;
    }

    int cost = UNREACHABLE_COST;
    for (VertexId child : current.children) cost = std::min(cost, _vertices[child].cost);
    return cost;
}

int TDG::addCosts(int left, int right) const {
    if (left >= UNREACHABLE_COST || right >= UNREACHABLE_COST || left > UNREACHABLE_COST - right) return UNREACHABLE_COST;
    return left + right;
}

USignature TDG::normalizeToGroundedArity(const USignature& signature) const {
    auto arity = _grounded_arity_by_name.find(signature._name_id);
    if (arity == _grounded_arity_by_name.end()) return signature;
    if (signature._args.size() < arity->second) return signature;
    return USignature(signature._name_id, std::vector<int>(signature._args.begin(), signature._args.begin() + arity->second));
}

int TDG::getHeuristicValue(const USignature& signature) const {
    const USignature normalized = normalizeToGroundedArity(signature);
    auto vertex = _vertex_ids.find(normalized);
    if (vertex == _vertex_ids.end()) {
        Log::e("Node %s not found in the TDG. Set weight value to inf\n", TOSTR(signature));
        return UNREACHABLE_COST;
    }
    return _vertices[vertex->second].cost;
}

bool TDG::isCompatibleGrounding(const USignature& grounding, const std::vector<std::vector<int>>& eligibleArguments) const {
    if (grounding._args.size() > eligibleArguments.size()) return false;
    for (size_t argument = 0; argument < grounding._args.size(); argument++) {
        const std::vector<int>& eligible = eligibleArguments[argument];
        if (!eligible.empty() && std::find(eligible.begin(), eligible.end(), grounding._args[argument]) == eligible.end()) return false;
    }
    return true;
}

int TDG::getBestHeuristicValue(const USignature& signature) {
    if (!_q_constants.containsAny(signature) && _htn.isFullyGround(signature)) return getHeuristicValue(signature);

    auto namedVertices = _vertices_by_name.find(signature._name_id);
    if (namedVertices == _vertices_by_name.end()) return UNREACHABLE_COST;

    const std::vector<int> sorts = _htn.getSorts(signature._name_id);
    const std::vector<std::vector<int>> eligibleArguments = _q_constants.getCandidateArgumentDomains(signature, sorts);
    const int minimumPossibleCost = _minimum_cost_by_name.at(signature._name_id);

    int bestCost = UNREACHABLE_COST;
    for (VertexId vertex : namedVertices->second) {
        if (!isCompatibleGrounding(_vertices[vertex].signature, eligibleArguments)) continue;
        bestCost = std::min(bestCost, _vertices[vertex].cost);
        if (bestCost == minimumPossibleCost) break;
    }
    return bestCost;
}

int TDG::getVirtualPlanHeuristicValue(const std::vector<PlanItem>& virtualPlan) const {
    int cost = 0;

    // The last item is the synthetic goal action and is not part of the plan cost.
    for (size_t index = 0; index + 1 < virtualPlan.size(); index++) {
        const USignature& operation = virtualPlan[index].reduction;
        int operationCost;
        if (_htn.isAction(operation) || _htn.isReductionPrimitivizable(operation._name_id)) {
            operationCost = operation._name_id == _htn.getBlankActionSig()._name_id ? 0 : 1;
        } else {
            operationCost = getHeuristicValue(operation);
        }
        cost = addCosts(cost, operationCost);
    }

    Log::d("Heuristic value of the virtual plan: %d\n", cost);
    return cost;
}

// Future experiment: refine compatible TDG vertices using the current
// over-approximation of the reachable state before evaluating their cost.
