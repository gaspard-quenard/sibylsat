#include "preprocessing/problem_preprocessor.h"

#include <utility>

#include "preprocessing/panda_ground_problem_loader.h"
#include "preprocessing/method_effect_analyzer.h"
#include "preprocessing/precondition_inference.h"
#include "preprocessing/htn_instance_builder.h"
#include "preprocessing/lifted_problem_normalizer.h"
#include "parser/panda_lifted_problem_reader.h"
#include "parser/panda_parser.h"
#include "parser/lifted_problem.h"
#include "preprocessing/macro_action_compiler.h"
#include "preprocessing/mutex_loader.h"
#include "util/log.h"
#include "util/params.h"
#include "util/project_utils.h"
#include "util/statistics.h"

namespace {

/** Compile macros only when the normalized task networks are totally ordered. */
std::unique_ptr<MacroActionCompiler> compileMacroActions(LiftedProblem& problem, const LiftedProblemProperties& properties, const Parameters& params) {
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
std::unique_ptr<MutexGroups> computeMutexGroups(HtnInstance& htn, FactAnalysis& facts, const std::filesystem::path& pandaProblemFile, Parameters& params) {
    if (!params.isNonzero("mutex")) return nullptr;

    Statistics& statistics = Statistics::getInstance();
    statistics.beginTiming(TimingStage::INIT_MUTEXES);
    std::unique_ptr<MutexGroups> mutexGroups = MutexLoader::compute(htn, facts, pandaProblemFile);
    statistics.endTiming(TimingStage::INIT_MUTEXES);
    return mutexGroups;
}

}

PlanningContext preprocessProblem(Parameters& params) {
    // Produce PandaPIgrounder's input independently of the in-memory parser representation.
    const std::filesystem::path pandaProblemFile = getProblemProcessingDir() / "problem.parsed";
    PandaParser::parse(params.getDomainFilename(), params.getProblemFilename(), pandaProblemFile);

    // PandaPIparser is currently also the selected frontend for LiftedProblem.
    LiftedProblem parsedProblem = PandaLiftedProblemReader::read(pandaProblemFile);

    // Establish representation invariants and select a deterministic subtask order.
    const LiftedProblemProperties properties = LiftedProblemNormalizer::normalize(parsedProblem);
    if (!properties.isTotallyOrdered) {
        Log::w("Partial-order methods are not fully supported; the planner will use one deterministic linearization.\n");
    }

    // Replace eligible primitive sequences with macro actions.
    std::unique_ptr<MacroActionCompiler> macroActions = compileMacroActions(parsedProblem, properties, params);

    // Convert the lifted parser representation into SibylSat's internal model.
    std::unique_ptr<HtnInstance> htn = HtnInstanceBuilder::build(parsedProblem, params);
    Log::i("%zu operators and %zu methods created.\n", htn->getActionTemplates().size(), htn->getReductionTemplates().size());

    // Own pseudo-constants introduced later during search.
    auto qConstants = std::make_unique<QConstantManager>(*htn, params.isNonzero("sqq"));

    // Ground reachable predicates and initialize the ground-fact analysis.
    Statistics& statistics = Statistics::getInstance();
    statistics.beginTiming(TimingStage::INIT_GROUNDING);
    GroundFacts groundFacts = PandaGroundProblemLoader::load(*htn, pandaProblemFile, params.isNonzero("optimal"));
    auto factAnalysis = std::make_unique<FactAnalysis>(*htn, *qConstants, std::move(groundFacts));
    statistics.endTiming(TimingStage::INIT_GROUNDING);
    const double groundingSeconds = static_cast<double>(statistics.getTiming(TimingStage::INIT_GROUNDING)) / 1'000'000'000.0;
    Log::i("Grounding time: %.3f s\n", groundingSeconds);

    // Compute mutex groups and remove groups invalidated by grounded reachability.
    std::unique_ptr<MutexGroups> mutexGroups = computeMutexGroups(*htn, *factAnalysis, pandaProblemFile, params);

    // Compute and attach the possible effects of every method template.
    MethodEffectAnalyzer::analyze(*htn, *factAnalysis);

    // Infer necessary method preconditions and attach them to the reductions.
    PreconditionInference::infer(*htn, PreconditionInference::MinePrecMode(params.getIntParam("mp")));

    // Build the task-decomposition heuristic only for optimal planning.
    std::unique_ptr<TDG> tdg;
    if (params.isNonzero("optimal")) tdg = std::make_unique<TDG>(*htn, *qConstants);

    return {std::move(htn), std::move(qConstants), std::move(macroActions), std::move(factAnalysis), std::move(mutexGroups), std::move(tdg)};
}

void PlanningContext::resetForNewSearch() {
    factAnalysis->resetForNewSearch();
}
