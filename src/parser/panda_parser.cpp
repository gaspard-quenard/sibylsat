#include "parser/panda_parser.h"

#include <stdexcept>

#include "util/process_utils.h"
#include "util/project_utils.h"

namespace {
void runParser(const std::string& executableName, const std::string& domainFile, const std::string& problemFile, const std::filesystem::path& outputFile) {
    const std::filesystem::path executable = getProjectRootDir() / "lib" / "parser" / executableName;
    const std::string command = quoteShellArgument(executable.string()) + " " + quoteShellArgument(domainFile) + " "
            + quoteShellArgument(problemFile) + " " + quoteShellArgument(outputFile.string());
    if (!commandSucceeds(command)) throw std::runtime_error("PandaPIparser failed: " + command);
}
}

void PandaParser::parse(const std::string& domainFile, const std::string& problemFile, const std::filesystem::path& outputFile) {
    runParser("pandaPIparser", domainFile, problemFile, outputFile);
}

void PandaParser::parseForStateFeatures(const std::string& domainFile, const std::string& problemFile, const std::filesystem::path& outputFile) {
    runParser("pandaPIparserOriginal", domainFile, problemFile, outputFile);
}
