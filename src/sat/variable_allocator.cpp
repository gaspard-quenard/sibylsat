#include "sat/variable_allocator.h"

#include "util/log.h"
#include "util/params.h"

VariableAllocator::VariableAllocator(const Parameters& params)
    : _print_variable_names(params.isNonzero("pvn")) {}

int VariableAllocator::allocateVariable(const std::string& name) {
    const int variable = _next_variable++;
    if (_print_variable_names && !name.empty()) {
        Log::d("VARMAP %i %s\n", variable, name.c_str());
    }
    return variable;
}
