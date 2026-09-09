#include "parser/panda_problem_reader.h"

#include <cstdlib>
#include <getopt.h>
#include <sys/stat.h>

#include "libpanda.hpp"
#include "util/log.h"

std::unique_ptr<ParsedProblem> PandaProblemReader::read(const std::string& domainFile, const std::string& problemFile) {
    struct stat fileInfo;
    if (stat(domainFile.c_str(), &fileInfo) != 0 || !S_ISREG(fileInfo.st_mode)) {
        Log::e("Domain file \"%s\" is not a regular file. Exiting.\n", domainFile.c_str());
        exit(1);
    }
    if (stat(problemFile.c_str(), &fileInfo) != 0 || !S_ISREG(fileInfo.st_mode)) {
        Log::e("Problem file \"%s\" is not a regular file. Exiting.\n", problemFile.c_str());
        exit(1);
    }

    auto problem = std::make_unique<ParsedProblem>();
    char parserName[] = "pandaPIparser";
    char* arguments[] = {parserName, const_cast<char*>(domainFile.c_str()), const_cast<char*>(problemFile.c_str())};
    optind = 1;
    run_pandaPIparser(3, arguments, *problem);
    return problem;
}
