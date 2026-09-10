#include "parser/aiplan_lifted_problem_reader.h"

#include <algorithm>
#include <fstream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <unordered_set>

#include "util/json.hpp"

namespace {

using json = nlohmann::json;

constexpr const char* ARTEFACT_SEPARATOR = "---AIPL-HEADER---";
constexpr const char* EQUALITY_PREDICATE = "__equal";
constexpr const char* INITIAL_TASK = "__aiplan_initial_task";
constexpr const char* INITIAL_METHOD = "__aiplan_initial_method";

size_t readId(const json& value) {
    if (value.is_string()) return std::stoull(value.get<std::string>());
    return value.get<size_t>();
}

class Reader {
private:
    const json& _input;
    const json& _entries;
    const json& _symbols;
    LiftedProblem _problem;
    std::vector<std::vector<size_t>> _type_parents;
    std::unordered_set<std::string> _objects;
    std::map<std::string, std::vector<std::string>> _schemaConstantsByTask;

    const json& entry(const json& id) const {
        const size_t index = readId(id);
        if (index >= _entries.size()) throw std::runtime_error("Invalid expression ID in aiplan4rust output: " + std::to_string(index));
        return _entries[index];
    }

    std::pair<std::string, const json*> kind(const json& expression) const {
        const json& value = expression.at("kind");
        if (value.is_string()) return {value.get<std::string>(), nullptr};
        const auto member = value.begin();
        return {member.key(), &member.value()};
    }

    std::string symbol(size_t symbolId) const {
        return _symbols.at(symbolId).get<std::string>();
    }

    std::string registrySymbol(const json& registry, size_t localId) const {
        return symbol(registry.at("elements").at(localId).get<size_t>());
    }

    std::string typeSymbolName(size_t typeId) const {
        return registrySymbol(_input.at("type_symbols"), typeId);
    }

    std::string parameterTypeName(const json& type) {
        std::vector<std::string> members;
        for (const json& member : type.at("members")) members.push_back(typeSymbolName(readId(member)));
        if (members.empty()) return "object";
        if (members.size() == 1) return members.front();

        std::sort(members.begin(), members.end());
        std::string unionName = "__either";
        std::set<std::string> objects;
        for (const std::string& member : members) {
            unionName += "_" + member;
            const std::vector<std::string>& memberObjects = _problem.sorts.at(member);
            objects.insert(memberObjects.begin(), memberObjects.end());
        }
        _problem.sorts[unionName] = {objects.begin(), objects.end()};
        return unionName;
    }

    std::string variableName(const json& variableRegistry, size_t variableId) const {
        return registrySymbol(variableRegistry, variableId);
    }

    std::string argument(const json& expressionId, const json& variableRegistry) const {
        const json& expression = entry(expressionId);
        const auto [name, value] = kind(expression);
        if (name == "Variable") return variableName(variableRegistry, readId(*value));
        if (name == "Object") return registrySymbol(_input.at("object_symbols"), readId(*value));
        throw std::runtime_error("Unsupported aiplan4rust argument expression: " + name);
    }

    std::vector<LiftedParameter> parameters(const json& owner, const json& variableRegistry) {
        std::vector<LiftedParameter> result;
        for (const json& parameter : owner.at("parameters").at("typed_symbols")) {
            result.emplace_back(variableName(variableRegistry, readId(parameter.at("symbol"))), parameterTypeName(parameter.at("ty")));
        }
        return result;
    }

    void addObjectToTypeAndParents(const std::string& object, size_t typeId, std::unordered_set<size_t>& visited) {
        if (!visited.insert(typeId).second) return;
        _problem.sorts[typeSymbolName(typeId)].push_back(object);
        for (size_t parent : _type_parents.at(typeId)) addObjectToTypeAndParents(object, parent, visited);
    }

    void readSorts() {
        const json& typeDefinitions = _input.at("type_defs").at("typed_symbols");
        _type_parents.resize(_input.at("type_symbols").at("elements").size());
        for (const json& definition : typeDefinitions) {
            const size_t typeId = readId(definition.at("symbol"));
            _problem.sorts[typeSymbolName(typeId)];
            for (const json& parent : definition.at("ty").at("members")) _type_parents[typeId].push_back(readId(parent));
        }

        for (const json& definition : _input.at("object_defs").at("typed_symbols")) {
            const std::string object = registrySymbol(_input.at("object_symbols"), readId(definition.at("symbol")));
            _objects.insert(object);
            for (const json& member : definition.at("ty").at("members")) {
                std::unordered_set<size_t> visited;
                addObjectToTypeAndParents(object, readId(member), visited);
            }
        }
        for (auto& [name, objects] : _problem.sorts) {
            std::sort(objects.begin(), objects.end());
            objects.erase(std::unique(objects.begin(), objects.end()), objects.end());
        }
    }

    std::string singletonSort(const std::string& object) {
        const std::string sort = "__aiplan_singleton_" + object;
        _problem.sorts[sort] = {object};
        return sort;
    }

    /** Replace constants in an operation schema with singleton-typed parameters. */
    template<class VisitArguments>
    std::vector<std::string> parameterizeConstants(std::vector<LiftedParameter>& parameters, VisitArguments visitArguments) {
        std::map<std::string, std::string> variableByObject;
        std::vector<std::string> constants;
        visitArguments([&](std::vector<std::string>& arguments) {
            for (std::string& argument : arguments) {
                if (!_objects.count(argument)) continue;
                auto [entry, inserted] = variableByObject.emplace(argument, "?__aiplan_constant_" + std::to_string(variableByObject.size()));
                if (inserted) {
                    parameters.emplace_back(entry->second, singletonSort(argument));
                    constants.push_back(argument);
                }
                argument = entry->second;
            }
        });
        return constants;
    }

    void parameterizeConstants() {
        for (LiftedTask& task : _problem.primitive_tasks) {
            _schemaConstantsByTask[task.name] = parameterizeConstants(task.vars, [&](const auto& visit) {
                for (LiftedLiteral& literal : task.prec) visit(literal.arguments);
                for (LiftedLiteral& literal : task.eff) visit(literal.arguments);
                for (LiftedLiteral& literal : task.constraints) visit(literal.arguments);
            });
        }
        for (LiftedMethod& method : _problem.methods) {
            for (LiftedSubtask& subtask : method.ps) {
                const auto constants = _schemaConstantsByTask.find(subtask.task);
                if (constants != _schemaConstantsByTask.end()) {
                    subtask.args.insert(subtask.args.end(), constants->second.begin(), constants->second.end());
                }
            }
            parameterizeConstants(method.vars, [&](const auto& visit) {
                visit(method.atargs);
                for (LiftedSubtask& subtask : method.ps) visit(subtask.args);
                for (LiftedLiteral& literal : method.preconditions) visit(literal.arguments);
                for (LiftedLiteral& literal : method.constraints) visit(literal.arguments);
            });
        }
    }

    void readPredicates() {
        for (const json& definition : _input.at("predicate_defs")) {
            LiftedPredicate predicate;
            predicate.name = registrySymbol(_input.at("predicate_symbols"), readId(definition.at("header").at("symbol")));
            for (const json& parameter : definition.at("header").at("parameters").at("typed_symbols")) {
                predicate.argument_sorts.push_back(parameterTypeName(parameter.at("ty")));
            }
            _problem.predicate_definitions.push_back(std::move(predicate));
        }
    }

    LiftedLiteral literal(const json& expression, const json& variableRegistry, bool positive) const {
        const auto [name, value] = kind(expression);
        if (name == "AtomicFormula") {
            const json& predicateDefinition = _input.at("predicate_defs").at(readId(*value));
            LiftedLiteral result;
            result.predicate = registrySymbol(_input.at("predicate_symbols"), readId(predicateDefinition.at("header").at("symbol")));
            result.positive = positive;
            const json& children = expression.at("children");
            for (size_t index = 1; index < children.size(); ++index) result.arguments.push_back(argument(children[index], variableRegistry));
            return result;
        }
        if (name == "Comparison") {
            const std::string comparison = value->get<std::string>();
            if (comparison != "Equal" && comparison != "NotEqual") throw std::runtime_error("Unsupported aiplan4rust comparison: " + comparison);
            LiftedLiteral result;
            result.predicate = EQUALITY_PREDICATE;
            result.positive = comparison == "Equal" ? positive : !positive;
            for (const json& child : expression.at("children")) result.arguments.push_back(argument(child, variableRegistry));
            return result;
        }
        throw std::runtime_error("Expected an atomic formula in aiplan4rust output, found: " + name);
    }

    void readConjunction(const json& expressionId, const json& variableRegistry, std::vector<LiftedLiteral>& literals, std::vector<LiftedLiteral>* constraints = nullptr, bool positive = true) const {
        const json& expression = entry(expressionId);
        const auto [name, value] = kind(expression);
        if (name == "And") {
            for (const json& child : expression.at("children")) readConjunction(child, variableRegistry, literals, constraints, positive);
            return;
        }
        if (name == "Or" && expression.at("children").empty()) return;
        if (name == "Not") {
            if (expression.at("children").size() != 1) throw std::runtime_error("Malformed negation in aiplan4rust output");
            readConjunction(expression.at("children").front(), variableRegistry, literals, constraints, !positive);
            return;
        }

        LiftedLiteral result = literal(expression, variableRegistry, positive);
        if (result.predicate == EQUALITY_PREDICATE && constraints != nullptr) constraints->push_back(std::move(result));
        else literals.push_back(std::move(result));
    }

    LiftedSubtask task(const json& expressionId, const json& variableRegistry, const std::string& fallbackId, const json* taskLabelRegistry = nullptr) const {
        const json& expression = entry(expressionId);
        const auto [name, value] = kind(expression);
        if (name == "LabeledTask") {
            const json& children = expression.at("children");
            if (children.size() != 2 || taskLabelRegistry == nullptr) throw std::runtime_error("Malformed labeled task in aiplan4rust output");
            const auto [labelKind, labelValue] = kind(entry(children.front()));
            if (labelKind != "TaskLabel") throw std::runtime_error("Expected an aiplan4rust task label");
            if (kind(entry(children.back())).first == "TaskLabel") {
                throw std::runtime_error("Malformed aiplan4rust output: labeled task contains its label twice and no task body");
            }
            return task(children.back(), variableRegistry, registrySymbol(*taskLabelRegistry, readId(*labelValue)), taskLabelRegistry);
        }
        if (name != "Task") throw std::runtime_error("Expected a task in aiplan4rust output, found: " + name);

        const json& taskDefinition = _input.at("task_defs").at(readId(*value));
        LiftedSubtask result;
        result.task = registrySymbol(_input.at("task_symbols"), readId(taskDefinition.at("header").at("symbol")));
        result.id = fallbackId;
        const json& children = expression.at("children");
        for (size_t index = 1; index < children.size(); ++index) result.args.push_back(argument(children[index], variableRegistry));
        return result;
    }

    void collectTaskExpressions(const json& expressionId, std::vector<json>& taskExpressionIds) const {
        const json& expression = entry(expressionId);
        const auto [name, value] = kind(expression);
        (void) value;
        if (name == "And" || name == "Serial" || name == "Parallel") {
            for (const json& child : expression.at("children")) collectTaskExpressions(child, taskExpressionIds);
            return;
        }
        if (name == "Or" && expression.at("children").empty()) return;
        taskExpressionIds.push_back(expressionId);
    }

    std::vector<LiftedSubtask> tasks(const json& network, const json& variableRegistry, const json& taskLabelRegistry) const {
        std::vector<json> taskExpressionIds;
        collectTaskExpressions(network.at("tasks"), taskExpressionIds);
        if (taskLabelRegistry.at("elements").size() != taskExpressionIds.size()) {
            throw std::runtime_error("Inconsistent aiplan4rust task network: task and label counts differ");
        }
        std::vector<LiftedSubtask> result;
        result.reserve(taskExpressionIds.size());
        for (size_t index = 0; index < taskExpressionIds.size(); ++index) {
            std::string fallbackId = "t" + std::to_string(index);
            LiftedSubtask subtask = task(taskExpressionIds[index], variableRegistry, fallbackId, &taskLabelRegistry);
            const std::string label = registrySymbol(taskLabelRegistry, index);
            if (subtask.id != fallbackId && subtask.id != label) {
                throw std::runtime_error("Inconsistent aiplan4rust task network: serialized task order disagrees with its label registry");
            }
            if (subtask.id == fallbackId && label != subtask.task) {
                throw std::runtime_error("Inconsistent aiplan4rust task network: serialized task order disagrees with its label registry");
            }
            subtask.id = label;
            result.push_back(std::move(subtask));
        }
        return result;
    }

    void collectOrderings(const json& expressionId, const json& taskLabelRegistry, std::vector<std::pair<std::string, std::string>>& result) const {
        const json& expression = entry(expressionId);
        const auto [name, value] = kind(expression);
        if ((name == "And" || name == "Or") && expression.at("children").empty()) return;
        if (name == "And") {
            for (const json& child : expression.at("children")) collectOrderings(child, taskLabelRegistry, result);
            return;
        }
        if (name != "TaskOrderingConstraint" || value->get<std::string>() != "Less") {
            throw std::runtime_error("Unsupported aiplan4rust task ordering expression: " + name);
        }
        const json& children = expression.at("children");
        if (children.size() != 2) throw std::runtime_error("Malformed aiplan4rust task ordering");
        const auto [firstKind, firstValue] = kind(entry(children[0]));
        const auto [secondKind, secondValue] = kind(entry(children[1]));
        if (firstKind != "TaskLabel" || secondKind != "TaskLabel") throw std::runtime_error("Expected task labels in aiplan4rust ordering");
        result.emplace_back(registrySymbol(taskLabelRegistry, readId(*firstValue)), registrySymbol(taskLabelRegistry, readId(*secondValue)));
    }

    void readTaskNetwork(const json& network, const json& variableRegistry, const json& taskLabelRegistry, LiftedMethod& method) const {
        method.ps = tasks(network, variableRegistry, taskLabelRegistry);
        if (network.at("is_declared_total_ordered").get<bool>()) {
            for (size_t index = 1; index < method.ps.size(); ++index) method.ordering.emplace_back(method.ps[index - 1].id, method.ps[index].id);
        } else {
            collectOrderings(network.at("ordering_constraints"), taskLabelRegistry, method.ordering);
        }
        readConjunction(network.at("logical_constraints"), variableRegistry, method.preconditions, &method.constraints);
    }

    void readTasksAndActions() {
        std::unordered_set<std::string> actionNames;
        for (const json& definition : _input.at("action_defs")) {
            LiftedTask action;
            action.name = registrySymbol(_input.at("action_symbols"), readId(definition.at("header").at("symbol")));
            actionNames.insert(action.name);
            action.vars = parameters(definition.at("header"), definition.at("variable_symbols"));
            action.number_of_original_vars = action.vars.size();
            const json& body = definition.at("body");
            if (body.at("typing") != "Snap") throw std::runtime_error("Durative aiplan4rust actions are not supported yet");
            readConjunction(body.at("precondition"), definition.at("variable_symbols"), action.prec, &action.constraints);
            readConjunction(body.at("effect"), definition.at("variable_symbols"), action.eff);
            _problem.primitive_tasks.push_back(std::move(action));
        }

        for (const json& definition : _input.at("task_defs")) {
            LiftedTask taskDefinition;
            taskDefinition.name = registrySymbol(_input.at("task_symbols"), readId(definition.at("header").at("symbol")));
            if (actionNames.count(taskDefinition.name)) continue;
            taskDefinition.vars = parameters(definition.at("header"), definition.at("variable_symbols"));
            taskDefinition.number_of_original_vars = taskDefinition.vars.size();
            _problem.abstract_tasks.push_back(std::move(taskDefinition));
        }
    }

    void readMethods() {
        for (const json& definition : _input.at("method_defs")) {
            LiftedMethod method;
            method.name = registrySymbol(_input.at("method_symbols"), readId(definition.at("header").at("symbol")));
            method.vars = parameters(definition.at("header"), definition.at("variable_symbols"));
            const LiftedSubtask accomplishedTask = task(definition.at("task"), definition.at("variable_symbols"), "accomplished");
            method.at = accomplishedTask.task;
            method.atargs = accomplishedTask.args;
            readConjunction(definition.at("precondition"), definition.at("variable_symbols"), method.preconditions, &method.constraints);
            readTaskNetwork(definition.at("task_network"), definition.at("variable_symbols"), definition.at("task_label_symbols"), method);
            _problem.methods.push_back(std::move(method));
        }
    }

    void readGroundLiterals(const json& expressionId, std::vector<LiftedGroundLiteral>& result, bool positive = true) const {
        const json& expression = entry(expressionId);
        const auto [name, value] = kind(expression);
        if (name == "And") {
            for (const json& child : expression.at("children")) readGroundLiterals(child, result, positive);
            return;
        }
        if (name == "Or" && expression.at("children").empty()) return;
        if (name == "Not") {
            readGroundLiterals(expression.at("children").front(), result, !positive);
            return;
        }
        if (name != "AtomicFormula") throw std::runtime_error("Unsupported ground formula in aiplan4rust output: " + name);

        const json& predicateDefinition = _input.at("predicate_defs").at(readId(*value));
        LiftedGroundLiteral literal;
        literal.predicate = registrySymbol(_input.at("predicate_symbols"), readId(predicateDefinition.at("header").at("symbol")));
        literal.positive = positive;
        const json& children = expression.at("children");
        const json emptyVariableRegistry = {{"elements", json::array()}};
        for (size_t index = 1; index < children.size(); ++index) literal.args.push_back(argument(children[index], emptyVariableRegistry));
        result.push_back(std::move(literal));
    }

    void createInitialMethod() {
        const json& initialNetwork = _input.at("initial_task_network");
        LiftedTask initialTask;
        initialTask.name = INITIAL_TASK;
        initialTask.vars = parameters(initialNetwork, initialNetwork.at("variable_symbols"));
        initialTask.number_of_original_vars = initialTask.vars.size();
        _problem.abstract_tasks.push_back(initialTask);
        _problem.initial_task_name = INITIAL_TASK;

        LiftedMethod initialMethod;
        initialMethod.name = INITIAL_METHOD;
        initialMethod.vars = initialTask.vars;
        initialMethod.at = INITIAL_TASK;
        for (const LiftedParameter& parameter : initialTask.vars) initialMethod.atargs.push_back(parameter.first);
        readTaskNetwork(initialNetwork.at("task_network"), initialNetwork.at("variable_symbols"), initialNetwork.at("task_label_symbols"), initialMethod);
        _problem.methods.push_back(std::move(initialMethod));
    }

public:
    explicit Reader(const json& input) : _input(input), _entries(input.at("store").at("entries")), _symbols(input.at("interner").at(0)) {}

    LiftedProblem read() {
        readSorts();
        readPredicates();
        readTasksAndActions();
        readMethods();
        readGroundLiterals(_input.at("init"), _problem.init);
        readGroundLiterals(_input.at("goal"), _problem.goal);
        createInitialMethod();
        // SibylSat represents schema-level constants as variables whose domain
        // is the singleton containing that constant, as PandaPIparser does.
        parameterizeConstants();
        return std::move(_problem);
    }
};

json readArtefactBody(const std::filesystem::path& filename) {
    std::ifstream input(filename);
    if (!input) throw std::runtime_error("Could not open aiplan4rust output: " + filename.string());

    std::string line;
    while (std::getline(input, line) && line != ARTEFACT_SEPARATOR) {}
    if (!input) throw std::runtime_error("Missing aiplan4rust artefact separator in: " + filename.string());
    return json::parse(input);
}

}

LiftedProblem AiplanLiftedProblemReader::read(const std::filesystem::path& filename) {
    const json artefact = readArtefactBody(filename);
    return Reader(artefact).read();
}
