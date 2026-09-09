#ifndef SIBYLSAT_LIFTED_PROBLEM_NORMALIZER_H
#define SIBYLSAT_LIFTED_PROBLEM_NORMALIZER_H

struct ParsedProblem;

/** Properties discovered while establishing the internal lifted representation. */
struct LiftedProblemProperties {
    bool isTotallyOrdered = true;
};

/** Applies representation invariants required by the internal HTN model. */
class LiftedProblemNormalizer {
public:
    /**
     * Normalize the parser result in place before it is converted to integer IDs.
     *
     * Every method's subtasks are placed in one deterministic topological order.
     * The result reports whether each of those orders was uniquely imposed by
     * the corresponding task network.
     */
    static LiftedProblemProperties normalize(ParsedProblem& problem);
};

#endif
