#ifndef SIBYLSAT_LIFTED_PROBLEM_H
#define SIBYLSAT_LIFTED_PROBLEM_H

#include <map>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using LiftedParameter = std::pair<std::string, std::string>;

struct LiftedLiteral {
    std::string predicate;
    std::vector<std::string> arguments;
    bool positive = true;
};

struct LiftedTask {
    std::string name;
    int number_of_original_vars = 0;
    std::vector<LiftedParameter> vars;
    std::vector<LiftedLiteral> prec;
    std::vector<LiftedLiteral> eff;
    std::vector<LiftedLiteral> constraints;
};

struct LiftedSubtask {
    std::string task;
    std::string id;
    std::vector<std::string> args;
};

struct LiftedMethod {
    std::string name;
    std::vector<LiftedParameter> vars;
    std::string at;
    std::vector<std::string> atargs;
    std::vector<LiftedSubtask> ps;
    std::vector<LiftedLiteral> preconditions;
    std::vector<LiftedLiteral> constraints;
    std::vector<std::pair<std::string, std::string>> ordering;
};

struct LiftedPredicate {
    std::string name;
    std::vector<std::string> argument_sorts;
};

struct LiftedGroundLiteral {
    std::string predicate;
    bool positive = true;
    std::vector<std::string> args;
};

/**
 * Minimal parser-independent lifted representation currently needed by
 * preprocessing. It can grow without exposing a parser library's own types.
 */
struct LiftedProblem {
    std::map<std::string, std::vector<std::string>> sorts;
    std::vector<LiftedPredicate> predicate_definitions;
    std::vector<LiftedTask> primitive_tasks;
    std::vector<LiftedTask> abstract_tasks;
    std::vector<LiftedMethod> methods;
    std::vector<LiftedGroundLiteral> init;
    std::vector<LiftedGroundLiteral> goal;
    std::string initial_task_name;

    const LiftedTask& getTask(const std::string& name) const {
        for (const LiftedTask& task : primitive_tasks) if (task.name == name) return task;
        for (const LiftedTask& task : abstract_tasks) if (task.name == name) return task;
        throw std::out_of_range("Unknown lifted task: " + name);
    }
};

#endif
