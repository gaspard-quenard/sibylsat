
#include "binary_amo.h"

#include <cassert>
#include <string>

#include "sat/variable_allocator.h"
#include "util/log.h"

BinaryAtMostOne::BinaryAtMostOne(const std::vector<int>& states, size_t numStates, VariableAllocator& variables) : _states(states), _num_states(numStates) {

    // Set up helper variables for a binary number representation
    _num_repr_states = 1;
    while (_num_repr_states < _num_states) {
        const std::string name = "(__amo_" + std::to_string(states.front()) + "-"
                + std::to_string(states.back()) + "_" + std::to_string(_bin_num_vars.size()) + ")";
        int var = variables.allocateVariable(name);
        _bin_num_vars.push_back(var);
        _num_repr_states *= 2;
    }
}

std::vector<std::vector<int>> BinaryAtMostOne::encode() {
    std::vector<std::vector<int>> cls;
    
    if (_num_states <= 1) return cls;

    // For each possible state with a variable representing it
    for (size_t state = 0; state < _states.size(); state++) {
        // Encode direction "=>"
        assert(!_bin_num_vars.empty());
        auto digitVars = getClause(state, false);
        for (int digitVar : digitVars) {
            std::vector<int> ifStateThenDigit(2);
            ifStateThenDigit[0] = -_states[state];
            ifStateThenDigit[1] = -digitVar;
            cls.push_back(std::move(ifStateThenDigit));
        }
        // Encode direction "<="
        auto& ifDigitsThenState = digitVars;
        ifDigitsThenState.push_back(_states[state]);
        cls.push_back(std::move(ifDigitsThenState));
    }

    // Forbid all representable but invalid states
    // by forming blocks of digit combinations that must be false
    int blockSize = _bin_num_vars.size();
    size_t firstForbiddenState = _num_repr_states;
    while (blockSize >= 0) {
        int diff = firstForbiddenState - _num_states;
        if (diff == 0) break;
        int expBlockSize = 1 << blockSize;
        if (diff >= expBlockSize) {
            firstForbiddenState -= expBlockSize;
            Log::d("BAMO forbid block [%i,%i)\n", firstForbiddenState, firstForbiddenState+expBlockSize);
            auto clause = getClause(firstForbiddenState, false);
            std::vector<int> constraint;
            for (size_t i = 0; i < _bin_num_vars.size() - blockSize; i++) {
                constraint.push_back(clause[clause.size()-i-1]);
            }
            cls.push_back(constraint);
        }
        blockSize--;
    }
    assert(firstForbiddenState == _num_states);

    return cls;
}

std::vector<int> BinaryAtMostOne::getClause(int state, bool sign) const {
    assert(!_bin_num_vars.empty());
    std::vector<int> cls(_bin_num_vars.size());
    for (size_t i = 0; i < _bin_num_vars.size(); i++) {
        bool mod = (state & 0x1);
        cls[i] = (!sign ^ mod ? 1 : -1) * _bin_num_vars[i];
        state >>= 1;
    }
    return cls;
}
