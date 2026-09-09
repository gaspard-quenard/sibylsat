#include "preprocessing/panda_ground_problem_loader.h"

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <stdexcept>
#include <system_error>
#include <vector>

#include "data/htn_instance.h"
#include "util/log.h"
#include "util/names.h"
#include "util/process_utils.h"
#include "util/project_utils.h"

namespace {

USignature parseGroundFact(HtnInstance& htn, const std::string& line, size_t lineNumber) {
    const size_t argumentsBegin = line.find('[', 1);
    const size_t argumentsEnd = line.find(']', argumentsBegin);
    if (line.size() < 3 || argumentsBegin == std::string::npos || argumentsEnd == std::string::npos) {
        throw std::runtime_error("Malformed state feature at line " + std::to_string(lineNumber));
    }

    std::vector<int> arguments;
    size_t argumentBegin = argumentsBegin + 1;
    while (argumentBegin < argumentsEnd) {
        const size_t separator = line.find(',', argumentBegin);
        const size_t argumentEnd = std::min(separator, argumentsEnd);
        arguments.push_back(htn.nameId(line.substr(argumentBegin, argumentEnd - argumentBegin)));
        argumentBegin = argumentEnd + 1;
    }
    return USignature(htn.nameId(line.substr(1, argumentsBegin - 1)), std::move(arguments));
}

void runRequiredCommand(const std::string& description, const std::string& command) {
    Log::i("%s...\n", description.c_str());
    if (!commandSucceeds(command)) {
        throw std::runtime_error(description + " failed. Command: " + command);
    }
    Log::i("Done!\n");
}

}

GroundFacts PandaGroundProblemLoader::load(HtnInstance& htn, const std::filesystem::path& pandaProblemFile, bool includeGroundOperations) {
    const std::filesystem::path projectRoot = getProjectRootDir();
    const std::filesystem::path processingDirectory = getProblemProcessingDir();
    const std::filesystem::path grounderOutput = processingDirectory / "problem.sas";
    const std::filesystem::path grounder = projectRoot / "lib" / "grounder" / "pandaPIgrounder";

    std::error_code removalError;
    std::filesystem::remove(grounderOutput, removalError);

    const std::string options = includeGroundOperations
            ? "--no-literal-pruning --no-abstract-expansion --write-full-methods-name --quiet"
            : "--no-literal-pruning --only-write-state-features --quick-compute-state-features --quiet";
    const std::string grounderCommand = quoteShellArgument(grounder.string()) + " " + options + " "
            + quoteShellArgument(pandaProblemFile.string()) + " " + quoteShellArgument(grounderOutput.string());
    Log::i("Grounder command: %s\n", grounderCommand.c_str());
    runRequiredCommand("Grounding the parsed problem", grounderCommand);

    Log::i("Reading ground state features...\n");
    GroundFacts facts = parseStateFeatures(htn, grounderOutput.string());
    Log::i("Done!\n");
    return facts;
}

GroundFacts PandaGroundProblemLoader::parseStateFeatures(HtnInstance& htn, const std::string& filename) {
    std::ifstream input(filename);
    if (!input) throw std::runtime_error("Could not open grounded problem: " + filename);

    constexpr const char* sectionHeader = ";; #state features";
    std::string line;
    size_t lineNumber = 0;
    while (std::getline(input, line) && line != sectionHeader) lineNumber++;
    if (!input) throw std::runtime_error("State-feature section not found in grounded problem: " + filename);

    lineNumber++;
    if (!std::getline(input, line)) throw std::runtime_error("Missing state-feature count in grounded problem: " + filename);
    lineNumber++;

    GroundFacts result;
    while (std::getline(input, line)) {
        lineNumber++;
        if (line.empty()) break;
        if (line.front() != '+' && line.front() != '-') {
            throw std::runtime_error("Invalid state-feature polarity at line " + std::to_string(lineNumber));
        }

        USignature fact = parseGroundFact(htn, line, lineNumber);
        result._negative.insert(fact);
        if (line.front() == '+') {
            result._positive.insert(fact);
            Log::d("%zu -> %s\n", result._positive.size(), TOSTR(fact));
        } else {
            Log::d("-> not %s\n", TOSTR(fact));
        }
    }

    Log::i("There are %zu positive state features (which can also be negative) for this problem.\n", result._positive.size());
    Log::i("There are %zu negative state features for this problem.\n", result._negative.size());
    return result;
}
