#include <algorithm>
#include <stdexcept>
#include <string>

#include "parser/lifted_problem.h"
#include "preprocessing/macro_action_compiler.h"

namespace {

void checkAt(bool condition, int line) {
    if (!condition) throw std::runtime_error("Macro action case test failed at line " + std::to_string(line));
}
#define check(condition) checkAt(condition, __LINE__)

LiftedLiteral literal(const std::string& predicate, std::vector<std::string> arguments, bool positive = true) {
    return {predicate, std::move(arguments), positive};
}

LiftedTask action(const std::string& name, std::vector<LiftedParameter> vars, std::vector<LiftedLiteral> prec, std::vector<LiftedLiteral> eff) {
    LiftedTask task;
    task.name = name;
    task.vars = std::move(vars);
    task.number_of_original_vars = task.vars.size();
    task.prec = std::move(prec);
    task.eff = std::move(eff);
    return task;
}

/** Blocksworld: unstack a block from ?z, then stack it on ?y. Its meaning depends on whether ?y is ?z (the add of
 * (clear ?z) then decides the precondition (clear ?y)) and whether ?y is ?x (the precondition was deleted). */
LiftedProblem makeProblem(const std::string& targetSort) {
    LiftedProblem problem;
    problem.initial_task_name = "initial";
    problem.sorts = {{"block", {"a", "b", "c"}}, {"pallet", {"p"}}, {"surface", {"a", "b", "c", "p"}}};
    problem.primitive_tasks.push_back(action("unstack", {{"?b", "block"}, {"?from", "surface"}},
            {literal("on", {"?b", "?from"}), literal("clear", {"?b"}), literal("handempty", {})},
            {literal("on", {"?b", "?from"}, false), literal("clear", {"?b"}, false), literal("handempty", {}, false),
             literal("holding", {"?b"}), literal("clear", {"?from"})}));
    problem.primitive_tasks.push_back(action("stack", {{"?b", "block"}, {"?to", "surface"}},
            {literal("holding", {"?b"}), literal("clear", {"?to"})},
            {literal("holding", {"?b"}, false), literal("clear", {"?to"}, false), literal("clear", {"?b"}),
             literal("on", {"?b", "?to"}), literal("handempty", {})}));
    LiftedTask move;
    move.name = "move";
    move.vars = {{"?x", "block"}, {"?y", targetSort}};
    problem.abstract_tasks.push_back(move);
    LiftedMethod method;
    method.name = "m-move";
    method.at = "move";
    method.vars = {{"?x", "block"}, {"?y", targetSort}, {"?z", "block"}};
    method.atargs = {"?x", "?y"};
    method.ps = {{"unstack", "t0", {"?x", "?z"}}, {"stack", "t1", {"?x", "?y"}}};
    method.ordering = {{"t0", "t1"}};
    problem.methods.push_back(method);
    return problem;
}

bool hasConstraint(const LiftedMethod& method, bool positive) {
    return std::any_of(method.constraints.begin(), method.constraints.end(), [&](const LiftedLiteral& c) { return c.positive == positive; });
}

bool needs(const LiftedTask& macro, const LiftedLiteral& precondition) {
    return std::any_of(macro.prec.begin(), macro.prec.end(), [&](const LiftedLiteral& p) {
        return p.predicate == precondition.predicate && p.arguments == precondition.arguments && p.positive == precondition.positive;
    });
}

}

int main() {
    // Executable cases: a real move (?y different from ?x and ?z), putting the block back (?y = ?z), and the
    // degenerate ?x = ?y = ?z (no state has a block on itself, the compiler does not know); ?y = ?x alone is dropped.
    LiftedProblem problem = makeProblem("surface");
    MacroActionCompiler compiler;
    compiler.compile(problem);
    check(problem.methods.size() == 3);
    const LiftedTask* macroOf[4] = {nullptr, nullptr, nullptr, nullptr};   // by number of macro parameters
    for (const LiftedMethod& method : problem.methods) {
        check(method.name != "m-move" && compiler.originalMethodName(method.name) == "m-move");
        check(method.at == "move" && method.atargs == std::vector<std::string>({"?x", "?y"}));
        check(method.ps.size() == 1 && compiler.isMacroAction(method.ps.front().task));
        check(compiler.getExpansion(method.ps.front().task).primitiveSteps.size() == 2);
        const LiftedTask& macro = problem.getTask(method.ps.front().task);
        check(macro.vars.size() <= 3 && macroOf[macro.vars.size()] == nullptr);
        macroOf[macro.vars.size()] = &macro;
        check(hasConstraint(method, true) == (macro.vars.size() < 3));
    }
    check(macroOf[1] && macroOf[2] && macroOf[3]);
    // Putting the block back: no precondition on another surface, and the block stays where it was.
    check(!needs(*macroOf[2], literal("clear", {"?y"})));
    check(std::none_of(macroOf[2]->eff.begin(), macroOf[2]->eff.end(), [](const LiftedLiteral& e) {
        return e.predicate == "on" && !e.positive;
    }));
    // A real move needs the target to be clear.
    check(needs(*macroOf[3], literal("clear", {"?y"})));
    check(compiler.originalMethodName("unrelated") == "unrelated");

    // A target sort without blocks: ?y can be neither ?x nor ?z, so the method keeps its name and one macro.
    LiftedProblem pallets = makeProblem("pallet");
    MacroActionCompiler palletCompiler;
    palletCompiler.compile(pallets);
    check(pallets.methods.size() == 1 && pallets.methods.front().name == "m-move");
    check(pallets.methods.front().ps.size() == 1 && palletCompiler.isMacroAction(pallets.methods.front().ps.front().task));
    check(needs(pallets.getTask(pallets.methods.front().ps.front().task), literal("clear", {"?y"})));
    return 0;
}
