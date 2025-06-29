
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


BitVec ArgIterator2::getFullInstantiation2(const USignature& sig, bool negated,
                                    HtnInstance& _htn,
                                    const std::vector<int>& sortsInput)
{
    std::vector<int> sorts = sortsInput.empty() ? _htn.getSorts(sig._name_id)
                                                : sortsInput;


    // Log::i("Get full instantiation for %s with sorts %s\n",
        //    TOSTR(sig), TOSTR(sorts));

    std::vector<int> restrictiveSorts(sig._args.size(), -1);
    std::vector<int> fixed(sig._args.size(), -1);
    for (size_t i = 0; i < sig._args.size(); ++i) {
        // if (/*sig._args[i] <= 0 ||*/ !_htn.isVariable(sig._args[i]))
        //     fixed[i] = sig._args[i];
        if (_htn.isQConstant(sig._args[i])) {
            // Restrict the sorts with the domain of the q-constant
            int domain = _htn.getPrimarySortOfQConstant(sig._args[i]);
            restrictiveSorts[i] = domain;
        } else if (!_htn.isVariable(sig._args[i])) {
            // Constant, set fixed value
            fixed[i] = sig._args[i];
        }
    }

    return _htn.getAllPredicatesId(sig._name_id, negated, sorts, restrictiveSorts, fixed);
}