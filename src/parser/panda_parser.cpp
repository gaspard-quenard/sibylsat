#include "parser/panda_parser.h"

#include <stdexcept>

#include "util/process_utils.h"
#include "util/project_utils.h"

void PandaParser::parse(const std::string& domainFile, const std::string& problemFile, const std::filesystem::path& outputFile) {
    const std::filesystem::path executable = getProjectRootDir() / "lib" / "parser" / "pandaPIparser";
    const std::string command = quoteShellArgument(executable.string()) + " " + quoteShellArgument(domainFile) + " "
            + quoteShellArgument(problemFile) + " " + quoteShellArgument(outputFile.string());
    if (!commandSucceeds(command)) throw std::runtime_error("PandaPIparser failed: " + command);
}
