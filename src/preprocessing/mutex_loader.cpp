#include "preprocessing/mutex_loader.h"

#include <cstdlib>
#include <filesystem>

#include "algo/fact_analysis.h"
#include "data/htn_instance.h"
#include "data/mutex_groups.h"
#include "util/log.h"
#include "util/params.h"
#include "util/process_utils.h"
#include "util/project_utils.h"

std::unique_ptr<MutexGroups> MutexLoader::compute(const Parameters& params, HtnInstance& htn, const FactAnalysis& facts) {
    const std::filesystem::path projectRoot = getProjectRootDir();
    const std::filesystem::path processingDirectory = getProblemProcessingDir();
    const std::filesystem::path parsedProblem = processingDirectory / "problem.parsed";
    const std::filesystem::path mutexFile = processingDirectory / "lfg.txt";

    const std::string parserCommand = quoteShellArgument((projectRoot / "lib" / "pandaPIparserOriginal").string()) + " "
            + quoteShellArgument(params.getDomainFilename()) + " " + quoteShellArgument(params.getProblemFilename()) + " "
            + quoteShellArgument(parsedProblem.string());
    Log::i("Parsing the problem for mutex analysis.\n");
    if (!commandSucceeds(parserCommand)) {
        Log::e("Could not parse the problem for mutex analysis.\n");
        exit(1);
    }

    const std::string grounderCommand = quoteShellArgument((projectRoot / "lib" / "pandaPIgrounder").string())
            + " --invariants --out-invariants " + quoteShellArgument(mutexFile.string())
            + " --exit-after-invariants " + quoteShellArgument(parsedProblem.string());
    Log::i("Computing lifted mutex groups.\n");
    if (!commandSucceeds(grounderCommand)) {
        Log::e("Could not compute lifted mutex groups.\n");
        exit(1);
    }

    Log::i("Loading and grounding lifted mutex groups.\n");
    auto mutexGroups = std::make_unique<MutexGroups>(mutexFile.string(), htn);
    mutexGroups->retainReachableFacts(facts.getGroundPosFacts());
    return mutexGroups;
}
