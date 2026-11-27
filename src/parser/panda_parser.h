#ifndef SIBYLSAT_PANDA_PARSER_H
#define SIBYLSAT_PANDA_PARSER_H

#include <filesystem>
#include <string>

/** Runs PandaPIparser and writes its documented lifted output format. */
class PandaParser {
public:
    /** The planner's input: method preconditions stay attached to their methods. */
    static void parse(const std::string& domainFile, const std::string& problemFile, const std::filesystem::path& outputFile);
    /**
     * The input of PandaPIgrounder when only its state features are read: the unmodified parser, whose parameter
     * splitting also splits methods through the variables of their preconditions, as in the published planner.
     * Large methods split this way are grounded much faster.
     */
    static void parseForStateFeatures(const std::string& domainFile, const std::string& problemFile, const std::filesystem::path& outputFile);
};

#endif
