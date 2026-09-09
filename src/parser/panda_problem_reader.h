#ifndef SIBYLSAT_PANDA_PROBLEM_READER_H
#define SIBYLSAT_PANDA_PROBLEM_READER_H

#include <memory>
#include <string>

struct ParsedProblem;

/** Adapter around pandaPIparser, kept separate from the internal HTN model. */
class PandaProblemReader {
public:
    /** Parse the given HDDL files and return ownership of the parser result. */
    static std::unique_ptr<ParsedProblem> read(const std::string& domainFile, const std::string& problemFile);
};

#endif
