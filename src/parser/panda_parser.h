#ifndef SIBYLSAT_PANDA_PARSER_H
#define SIBYLSAT_PANDA_PARSER_H

#include <filesystem>
#include <string>

/** Runs PandaPIparser and writes its documented lifted output format. */
class PandaParser {
public:
    static void parse(const std::string& domainFile, const std::string& problemFile, const std::filesystem::path& outputFile);
};

#endif
