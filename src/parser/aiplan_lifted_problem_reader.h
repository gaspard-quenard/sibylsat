#ifndef SIBYLSAT_AIPLAN_LIFTED_PROBLEM_READER_H
#define SIBYLSAT_AIPLAN_LIFTED_PROBLEM_READER_H

#include <filesystem>

#include "parser/lifted_problem.h"

/** Converts an aiplan4rust linked JSON artefact into SibylSat's neutral model. */
class AiplanLiftedProblemReader {
public:
    static LiftedProblem read(const std::filesystem::path& filename);
};

#endif
