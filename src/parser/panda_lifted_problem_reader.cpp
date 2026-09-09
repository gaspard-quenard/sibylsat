#include "parser/panda_lifted_problem_reader.h"

#include <algorithm>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>

namespace {

class TokenReader {
private:
    std::ifstream _input;
    std::istringstream _line;
    size_t _line_number = 0;

public:
    explicit TokenReader(const std::filesystem::path& filename) : _input(filename) {
        if (!_input) throw std::runtime_error("Could not open parsed problem: " + filename.string());
    }

    std::string next() {
        std::string token;
        while (!(_line >> token)) {
            std::string line;
            if (!std::getline(_input, line)) throw std::runtime_error("Unexpected end of PandaPIparser output");
            _line_number++;
            if (line.empty() || line.front() == '#') continue;
            _line.clear();
            _line.str(line);
        }
        return token;
    }

    int nextInt() {
        const std::string token = next();
        size_t parsedCharacters = 0;
        const int value = std::stoi(token, &parsedCharacters);
        if (parsedCharacters != token.size()) throw std::runtime_error("Expected an integer at parsed-problem line " + std::to_string(_line_number));
        return value;
    }
};

std::string parameterName(int index) {
    return "?v" + std::to_string(index);
}

LiftedLiteral readTaskLiteral(TokenReader& input, const std::vector<LiftedPredicate>& predicates, const LiftedTask& task, bool added) {
    const LiftedPredicate& predicate = predicates.at(input.nextInt());
    LiftedLiteral result;
    result.predicate = predicate.name.substr(1);
    result.positive = (predicate.name.front() == '+') == added;
    for (size_t argument = 0; argument < predicate.argument_sorts.size(); argument++) {
        result.arguments.push_back(task.vars.at(input.nextInt()).first);
    }
    return result;
}

LiftedGroundLiteral readGroundLiteral(TokenReader& input, const std::vector<LiftedPredicate>& predicates, const std::vector<std::string>& constants) {
    const LiftedPredicate& predicate = predicates.at(input.nextInt());
    LiftedGroundLiteral result;
    result.predicate = predicate.name.substr(1);
    result.positive = predicate.name.front() == '+';
    for (size_t argument = 0; argument < predicate.argument_sorts.size(); argument++) {
        result.args.push_back(constants.at(input.nextInt()));
    }
    return result;
}

void requireNoConditionalEffects(int count) {
    if (count != 0) throw std::runtime_error("Conditional effects must be compiled by PandaPIparser before SibylSat reads the problem");
}

LiftedLiteral readConstraint(TokenReader& input, const std::vector<LiftedParameter>& parameters) {
    const std::string relation = input.next();
    if (relation != "=" && relation != "!=") throw std::runtime_error("Unknown PandaPI variable constraint: " + relation);
    return {"__equal", {parameters.at(input.nextInt()).first, parameters.at(input.nextInt()).first}, relation == "="};
}

bool isCompiledMethodPrecondition(const std::string& taskName) {
    return taskName.starts_with("__method_precondition_") || taskName.starts_with("__immediate_method_precondition_");
}

const LiftedTask* findCompiledPreconditionTask(const LiftedProblem& problem, const std::string& subtaskName) {
    for (const LiftedTask& task : problem.primitive_tasks) {
        if (task.name == subtaskName) return &task;
    }
    return nullptr;
}

void substituteArguments(LiftedLiteral& literal, const std::unordered_map<std::string, std::string>& substitution) {
    for (std::string& argument : literal.arguments) {
        const auto replacement = substitution.find(argument);
        if (replacement != substitution.end()) argument = replacement->second;
    }
}

/** Convert Panda's artificial precondition actions into parser-independent method preconditions. */
void importMethodPreconditions(LiftedProblem& problem) {
    for (LiftedMethod& method : problem.methods) {
        std::unordered_set<std::string> removedSubtaskIds;
        std::vector<LiftedSubtask> retainedSubtasks;
        retainedSubtasks.reserve(method.ps.size());

        for (const LiftedSubtask& subtask : method.ps) {
            const LiftedTask* preconditionTask = isCompiledMethodPrecondition(subtask.task)
                    ? findCompiledPreconditionTask(problem, subtask.task) : nullptr;
            if (preconditionTask == nullptr) {
                retainedSubtasks.push_back(subtask);
                continue;
            }

            if (preconditionTask->vars.size() != subtask.args.size()) {
                throw std::runtime_error("Invalid PandaPIparser method-precondition arguments for task: " + subtask.task);
            }

            std::unordered_map<std::string, std::string> substitution;
            for (size_t index = 0; index < preconditionTask->vars.size(); index++) {
                substitution[preconditionTask->vars[index].first] = subtask.args[index];
            }
            for (LiftedLiteral precondition : preconditionTask->prec) {
                substituteArguments(precondition, substitution);
                method.preconditions.push_back(std::move(precondition));
            }
            for (LiftedLiteral constraint : preconditionTask->constraints) {
                substituteArguments(constraint, substitution);
                method.constraints.push_back(std::move(constraint));
            }
            removedSubtaskIds.insert(subtask.id);
        }

        method.ps = std::move(retainedSubtasks);
        method.ordering.erase(std::remove_if(method.ordering.begin(), method.ordering.end(), [&](const auto& ordering) {
            return removedSubtaskIds.count(ordering.first) || removedSubtaskIds.count(ordering.second);
        }), method.ordering.end());
    }
}

}

LiftedProblem PandaLiftedProblemReader::read(const std::filesystem::path& filename) {
    TokenReader input(filename);
    LiftedProblem problem;

    const int constantCount = input.nextInt();
    const int sortCount = input.nextInt();
    std::vector<std::string> constants(constantCount);
    for (std::string& constant : constants) constant = input.next();

    std::vector<std::string> sorts(sortCount);
    for (int sortIndex = 0; sortIndex < sortCount; sortIndex++) {
        const std::string sortName = input.next();
        sorts[sortIndex] = sortName;
        const int memberCount = input.nextInt();
        std::vector<std::string>& members = problem.sorts[sortName];
        members.reserve(memberCount);
        for (int member = 0; member < memberCount; member++) members.push_back(constants.at(input.nextInt()));
    }

    const int predicateCount = input.nextInt();
    std::vector<LiftedPredicate> outputPredicates;
    outputPredicates.reserve(predicateCount);
    for (int predicateIndex = 0; predicateIndex < predicateCount; predicateIndex++) {
        LiftedPredicate predicate;
        predicate.name = input.next();
        if (predicate.name.size() < 2 || (predicate.name.front() != '+' && predicate.name.front() != '-')) {
            throw std::runtime_error("Expected a signed predicate in PandaPIparser output: " + predicate.name);
        }
        const int arity = input.nextInt();
        for (int argument = 0; argument < arity; argument++) predicate.argument_sorts.push_back(sorts.at(input.nextInt()));
        outputPredicates.push_back(predicate);
        if (predicate.name.front() == '+') {
            predicate.name.erase(predicate.name.begin());
            problem.predicate_definitions.push_back(std::move(predicate));
        }
    }

    const int predicateMutexCount = input.nextInt();
    for (int mutex = 0; mutex < predicateMutexCount; mutex++) {
        input.nextInt();
        input.nextInt();
    }

    const int functionCount = input.nextInt();
    std::vector<int> functionArities(functionCount);
    for (int functionIndex = 0; functionIndex < functionCount; functionIndex++) {
        input.next();
        functionArities[functionIndex] = input.nextInt();
        for (int argument = 0; argument < functionArities[functionIndex]; argument++) input.nextInt();
    }

    const int primitiveTaskCount = input.nextInt();
    const int abstractTaskCount = input.nextInt();
    std::vector<LiftedTask*> tasks;
    tasks.reserve(primitiveTaskCount + abstractTaskCount);
    problem.primitive_tasks.reserve(primitiveTaskCount);
    problem.abstract_tasks.reserve(abstractTaskCount);
    for (int taskIndex = 0; taskIndex < primitiveTaskCount + abstractTaskCount; taskIndex++) {
        LiftedTask task;
        task.name = input.next();
        task.number_of_original_vars = input.nextInt();
        const int parameterCount = input.nextInt();
        const bool primitive = taskIndex < primitiveTaskCount;
        for (int parameter = 0; parameter < parameterCount; parameter++) task.vars.push_back({parameterName(parameter), sorts.at(input.nextInt())});

        if (primitive) {
            // LiftedProblem does not expose action costs yet, but consume them
            // here so that extending the neutral model later stays local.
            const int costCount = input.nextInt();
            for (int cost = 0; cost < costCount; cost++) {
                const std::string kind = input.next();
                if (kind == "const") input.nextInt();
                else if (kind == "var") {
                    const int functionIndex = input.nextInt();
                    for (int argument = 0; argument < functionArities.at(functionIndex); argument++) input.nextInt();
                } else throw std::runtime_error("Unknown PandaPI cost expression: " + kind);
            }

            const int preconditionCount = input.nextInt();
            for (int precondition = 0; precondition < preconditionCount; precondition++) task.prec.push_back(readTaskLiteral(input, outputPredicates, task, true));
            const int addEffectCount = input.nextInt();
            for (int effect = 0; effect < addEffectCount; effect++) task.eff.push_back(readTaskLiteral(input, outputPredicates, task, true));
            requireNoConditionalEffects(input.nextInt());
            const int deleteEffectCount = input.nextInt();
            for (int effect = 0; effect < deleteEffectCount; effect++) task.eff.push_back(readTaskLiteral(input, outputPredicates, task, false));
            requireNoConditionalEffects(input.nextInt());
            const int constraintCount = input.nextInt();
            for (int constraint = 0; constraint < constraintCount; constraint++) task.constraints.push_back(readConstraint(input, task.vars));
            problem.primitive_tasks.push_back(std::move(task));
            tasks.push_back(&problem.primitive_tasks.back());
        } else {
            problem.abstract_tasks.push_back(std::move(task));
            tasks.push_back(&problem.abstract_tasks.back());
        }
    }

    const int methodCount = input.nextInt();
    problem.methods.reserve(methodCount);
    for (int methodIndex = 0; methodIndex < methodCount; methodIndex++) {
        LiftedMethod method;
        method.name = input.next();
        const int taskIndex = input.nextInt();
        method.at = tasks.at(taskIndex)->name;
        const int parameterCount = input.nextInt();
        for (int parameter = 0; parameter < parameterCount; parameter++) method.vars.push_back({parameterName(parameter), sorts.at(input.nextInt())});
        for (size_t argument = 0; argument < tasks.at(taskIndex)->vars.size(); argument++) method.atargs.push_back(method.vars.at(input.nextInt()).first);

        const int subtaskCount = input.nextInt();
        for (int subtaskIndex = 0; subtaskIndex < subtaskCount; subtaskIndex++) {
            LiftedSubtask subtask;
            subtask.id = "t" + std::to_string(subtaskIndex);
            const LiftedTask& subtaskTemplate = *tasks.at(input.nextInt());
            subtask.task = subtaskTemplate.name;
            for (size_t argument = 0; argument < subtaskTemplate.vars.size(); argument++) subtask.args.push_back(method.vars.at(input.nextInt()).first);
            method.ps.push_back(std::move(subtask));
        }

        const int orderingCount = input.nextInt();
        for (int ordering = 0; ordering < orderingCount; ordering++) {
            const int before = input.nextInt();
            const int after = input.nextInt();
            method.ordering.emplace_back(method.ps.at(before).id, method.ps.at(after).id);
        }
        const int constraintCount = input.nextInt();
        for (int constraint = 0; constraint < constraintCount; constraint++) method.constraints.push_back(readConstraint(input, method.vars));
        problem.methods.push_back(std::move(method));
    }

    const int initialFactCount = input.nextInt();
    const int goalCount = input.nextInt();
    for (int fact = 0; fact < initialFactCount; fact++) problem.init.push_back(readGroundLiteral(input, outputPredicates, constants));
    for (int goal = 0; goal < goalCount; goal++) problem.goal.push_back(readGroundLiteral(input, outputPredicates, constants));

    const int initialFunctionCount = input.nextInt();
    for (int function = 0; function < initialFunctionCount; function++) {
        const int functionIndex = input.nextInt();
        for (int argument = 0; argument < functionArities.at(functionIndex); argument++) input.nextInt();
        input.nextInt();
    }
    const int initialTaskIndex = input.nextInt();
    if (initialTaskIndex >= 0) problem.initial_task_name = tasks.at(initialTaskIndex)->name;
    importMethodPreconditions(problem);
    return problem;
}
