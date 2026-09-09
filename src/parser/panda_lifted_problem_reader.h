#ifndef SIBYLSAT_PANDA_LIFTED_PROBLEM_READER_H
#define SIBYLSAT_PANDA_LIFTED_PROBLEM_READER_H

#include <filesystem>

#include "parser/lifted_problem.h"

/** Deserializes PandaPIparser's documented lifted output into LiftedProblem. */
class PandaLiftedProblemReader {
public:
    static LiftedProblem read(const std::filesystem::path& filename);
};

#endif
