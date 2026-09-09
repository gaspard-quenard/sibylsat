#include "preprocessing/problem_preprocessor.h"

#include "preprocessing/method_effect_analyzer.h"
#include "preprocessing/precondition_inference.h"
#include "preprocessing/htn_instance_builder.h"
#include "preprocessing/lifted_problem_normalizer.h"
#include "parser/panda_problem_reader.h"
#include "libpanda.hpp"
#include "preprocessing/macro_action_compiler.h"
#include "preprocessing/mutex_loader.h"
#include "util/log.h"
#include "util/params.h"
#include "util/statistics.h"

namespace {

/** Compile macros only when the normalized task networks are totally ordered. */
std::unique_ptr<MacroActionCompiler> compileMacroActions(ParsedProblem& problem, const LiftedProblemProperties& properties, const Parameters& params) {
    if (!params.isNonzero("macroActions")) return nullptr;
    if (!properties.isTotallyOrdered) {
        Log::w("Macro actions are disabled because the problem contains partially ordered methods.\n");
        return nullptr;
    }

    Log::i("Rewrite consecutive primitive tasks in method task networks into macro actions.\n");
    auto compiler = std::make_unique<MacroActionCompiler>();
    compiler->compile(problem);
    return compiler;
}

/** Compute mutex groups and immediately filter them through grounded facts. */
void computeMutexGroups(HtnInstance& htn, FactAnalysis& facts, Parameters& params) {
    if (!params.isNonzero("mutex")) return;

    Statistics& statistics = Statistics::getInstance();
    statistics.beginTiming(TimingStage::INIT_MUTEXES);
    htn.setMutexGroups(MutexLoader::compute(params, htn, facts));
    statistics.endTiming(TimingStage::INIT_MUTEXES);
}

}

PlanningContext preprocessProblem(Parameters& params) {
    // Parse HDDL into the parser's lifted representation.
    std::unique_ptr<ParsedProblem> parsedProblem = PandaProblemReader::read(params.getDomainFilename(), params.getProblemFilename());

    // Establish representation invariants and select a deterministic subtask order.
    const LiftedProblemProperties properties = LiftedProblemNormalizer::normalize(*parsedProblem);
    if (!properties.isTotallyOrdered) {
        Log::w("Partial-order methods are not fully supported; the planner will use one deterministic linearization.\n");
    }

    // Replace eligible primitive sequences with macro actions.
    std::unique_ptr<MacroActionCompiler> macroActions = compileMacroActions(*parsedProblem, properties, params);

    // Convert the lifted parser representation into SibylSat's internal model.
    std::unique_ptr<HtnInstance> htn = HtnInstanceBuilder::build(*parsedProblem, std::move(macroActions), params);
    Log::i("%zu operators and %zu methods created.\n", htn->getActionTemplates().size(), htn->getReductionTemplates().size());

    // Ground reachable predicates and initialize the model's ground-fact index.
    auto factAnalysis = std::make_unique<FactAnalysis>(*htn, params.getDomainFilename(), params.getProblemFilename(), params.isNonzero("optimal"));

    // Compute mutex groups and remove groups invalidated by grounded reachability.
    computeMutexGroups(*htn, *factAnalysis, params);

    // Compute and attach the possible effects of every method template.
    MethodEffectAnalyzer::analyze(*htn, *factAnalysis);

    // Infer necessary method preconditions and attach them to the reductions.
    PreconditionInference::infer(*htn, PreconditionInference::MinePrecMode(params.getIntParam("mp")));

    // Build the task-decomposition heuristic only for optimal planning.
    std::unique_ptr<TDG> tdg;
    if (params.isNonzero("optimal")) tdg = std::make_unique<TDG>(*htn);

    return {std::move(htn), std::move(factAnalysis), std::move(tdg)};
}

void PlanningContext::resetForNewSearch() {
    factAnalysis->resetForNewSearch();
}
