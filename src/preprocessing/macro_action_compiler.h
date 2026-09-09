#ifndef SIBYLSAT_MACRO_ACTION_COMPILER_H
#define SIBYLSAT_MACRO_ACTION_COMPILER_H

#include <cstddef>
#include <string>
#include <unordered_map>
#include <vector>

struct ParsedProblem;

/** One primitive action represented inside a compiled macro action. */
struct MacroPrimitiveStep {
    std::string actionName;
    std::vector<size_t> macroArgumentIndices;
};

/** Parser-independent information needed to decode a selected macro action. */
struct MacroActionExpansion {
    std::vector<MacroPrimitiveStep> primitiveSteps;
};

/**
 * Compiles consecutive primitive subtasks and records how to expand them in plans.
 * Input methods must already be normalized and totally ordered.
 */
class MacroActionCompiler {
private:
    std::unordered_map<std::string, MacroActionExpansion> _expansions;

public:
    /** Rewrite eligible primitive sequences in the parsed problem in place. */
    void compile(ParsedProblem& problem);

    /** Return whether the named primitive task is a generated macro action. */
    bool isMacroAction(const std::string& actionName) const;

    /** Return the primitive sequence represented by a generated macro action. */
    const MacroActionExpansion& getExpansion(const std::string& actionName) const;
};

#endif
