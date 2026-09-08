#ifndef SIBYLSAT_VARIABLE_ALLOCATOR_H
#define SIBYLSAT_VARIABLE_ALLOCATOR_H

#include <string>

class Parameters;

/**
 * Owns the SAT variable ID sequence for one encoding.
 *
 * All semantic and auxiliary SAT variables are allocated here, which guarantees
 * that their identifiers share one collision-free sequence.
 */
class VariableAllocator {
private:
    int _next_variable = 1;
    const bool _print_variable_names;

public:
    explicit VariableAllocator(const Parameters& params);

    int allocateVariable(const std::string& name = "");
    int getMaxVariable() const { return _next_variable - 1; }
};

#endif
