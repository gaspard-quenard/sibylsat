#include "parser/aiplan_parser.h"

#include <filesystem>
#include <stdexcept>

#include "util/process_utils.h"
#include "util/project_utils.h"

void AiplanParser::parse(const std::string& domainFile, const std::string& problemFile, const std::filesystem::path& outputFile) {
    const std::filesystem::path executable = getProjectRootDir() / "lib" / "parser" / "aiplan4rust" / "aiplan";
    if (!std::filesystem::exists(executable)) {
        throw std::runtime_error("aiplan4rust is not built. Run `make aiplan4rust-parser` first");
    }

    const std::string command = quoteShellArgument(executable.string()) + " link " + quoteShellArgument(domainFile) + " "
            + quoteShellArgument(problemFile) + " --output " + quoteShellArgument(outputFile.filename().string())
            + " --out-dir " + quoteShellArgument(outputFile.parent_path().string()) + " --format json";
    if (!commandSucceeds(command)) throw std::runtime_error("aiplan4rust failed: " + command);
    if (!std::filesystem::exists(outputFile)) throw std::runtime_error("aiplan4rust did not produce its expected output: " + outputFile.string());
}
