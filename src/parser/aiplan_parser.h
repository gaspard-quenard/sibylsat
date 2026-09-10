#ifndef SIBYLSAT_AIPLAN_PARSER_H
#define SIBYLSAT_AIPLAN_PARSER_H

#include <filesystem>
#include <string>

/** Runs aiplan4rust and writes its linked lifted-problem artefact as JSON. */
class AiplanParser {
public:
    static void parse(const std::string& domainFile, const std::string& problemFile, const std::filesystem::path& outputFile);
};

#endif
