#include "preprocessing/mutex_loader.h"

#include <cstdlib>
#include <filesystem>

#include "algo/fact_analysis.h"
#include "data/htn_instance.h"
#include "data/mutex_groups.h"
#include "preprocessing/lifted_mutex_group_grounder.h"
#include "util/log.h"
#include "util/process_utils.h"
#include "util/project_utils.h"

std::unique_ptr<MutexGroups> MutexLoader::compute(HtnInstance& htn, FactAnalysis& facts, const std::filesystem::path& pandaProblemFile) {
    const std::filesystem::path projectRoot = getProjectRootDir();
    const std::filesystem::path mutexFile = getProblemProcessingDir() / "lfg.txt";

    const std::string grounderCommand = quoteShellArgument((projectRoot / "lib" / "grounder" / "pandaPIgrounder").string())
            + " --invariants --out-invariants " + quoteShellArgument(mutexFile.string())
            + " --exit-after-invariants " + quoteShellArgument(pandaProblemFile.string());
    Log::i("Computing lifted mutex groups.\n");
    if (!commandSucceeds(grounderCommand)) {
        Log::e("Could not compute lifted mutex groups.\n");
        exit(1);
    }

    Log::i("Loading and grounding lifted mutex groups.\n");
    std::vector<std::vector<int>> factIdsByGroup = LiftedMutexGroupGrounder::groundFile(mutexFile, htn, facts);
    return std::make_unique<MutexGroups>(std::move(factIdsByGroup), facts.getNumGroundFacts());
}
