#ifndef SIBYLSAT_ACTION_COSTS_H
#define SIBYLSAT_ACTION_COSTS_H

#include <cstddef>
#include <vector>

#include "data/signature.h"
#include "util/hashmap.h"

class HtnInstance;
class MacroActionCompiler;

/**
 * What an action costs: the measure that the optimal search minimizes.
 *
 * A cost belongs to an action with its arguments. An action of the domain costs one: the domain's own action costs are
 * not read, and ofDomainAction is the one place to change when they are. The actions that the planner makes out of
 * the domain's cost what they stand for: a macro action the sum of its steps, a method reduced to its only action
 * what that action costs, a repetition what its action costs.
 */
class ActionCosts {
public:
    ActionCosts(HtnInstance& htn, const MacroActionCompiler* macroActions);

    /** The cost of an action with these arguments. */
    int of(const USignature& action) const;

private:
    const HtnInstance& _htn;
    /** A step of a macro action: an action and, for each of its arguments, the index of the macro action's argument. */
    struct MacroStep {
        int actionId;
        std::vector<size_t> argumentIndices;
    };
    FlatHashMap<int, std::vector<MacroStep>> _macro_steps;   // macro action -> its steps

    int ofDomainAction(const USignature& action) const;
};

#endif
