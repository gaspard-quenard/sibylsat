#ifndef SIBYLSAT_MACRO_ACTION_COMPILER_H
#define SIBYLSAT_MACRO_ACTION_COMPILER_H

#include <cstddef>
#include <map>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

struct LiftedProblem;
struct LiftedMethod;

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
    std::unordered_map<std::string, std::string> _original_method_names;   // case of a method -> the method
    std::map<std::pair<std::string, std::string>, bool> _sort_overlaps;
    size_t _split_segments = 0;
    size_t _case_split_methods = 0;
    size_t _inapplicable_cases = 0;

    std::vector<LiftedMethod> splitCases(const LiftedMethod& method, const LiftedProblem& problem,
            const std::unordered_set<std::string>& primitiveNames);

public:
    /** Rewrite eligible primitive sequences in the parsed problem in place. */
    void compile(LiftedProblem& problem);

    /** Return whether the named primitive task is a generated macro action. */
    bool isMacroAction(const std::string& actionName) const;

    /** Return the primitive sequence represented by a generated macro action. */
    const MacroActionExpansion& getExpansion(const std::string& actionName) const;

    /** The method a case created by the compilation belongs to (the name itself for other methods). */
    const std::string& originalMethodName(const std::string& methodName) const;
};

#endif
