
#include "algo/arg_iterator.h"
#include "data/htn_instance.h"

ArgIterator ArgIterator::getFullInstantiation(const USignature& sig, HtnInstance& _htn, const std::vector<int>& sortsInput, const std::vector<FlatHashSet<int>>& constantsAllowedPerSorts) {
    std::vector<std::vector<int>> constantsPerArg;

    // Use the provided sorts if available, otherwise fetch from _htn
    std::vector<int> sorts = sortsInput.empty() ? _htn.getSorts(sig._name_id) : sortsInput;

    if (sig._args.empty()) {
        return ArgIterator(sig._name_id, std::move(constantsPerArg));
    }

    assert(sorts.size() == sig._args.size() || Log::e("Sorts table of predicate %s has an invalid size\n", TOSTR(sig)));

    for (size_t pos = 0; pos < sorts.size(); pos++) {
        int arg = sig._args[pos];
        
        if (arg > 0 && _htn.isVariable(arg)) {
            int sort = sorts[pos];
            std::vector<int> eligibleConstants;
            for (int arg : _htn.getConstantsOfSort(sort)) {
                if (_htn.isQConstant(arg)) continue;
                // If constant allowed per sort is empty, all constants are allowed
                if (constantsAllowedPerSorts.empty() || constantsAllowedPerSorts[pos].count(arg))
                    eligibleConstants.push_back(arg);
            }

            if (eligibleConstants.empty()) {
                constantsPerArg.clear();
                return ArgIterator(sig._name_id, std::move(constantsPerArg));
            }

            constantsPerArg.push_back(eligibleConstants);
        } else {
            // constant
            constantsPerArg.push_back(std::vector<int>(1, arg));
        }
    }

    return ArgIterator(sig._name_id, std::move(constantsPerArg));
}
