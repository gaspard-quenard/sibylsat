
#include "retroactive_pruning.h"

#include <unordered_map>
#include <unordered_set>

namespace {
struct PositionedOp {
    Position* position;
    USignature usig;

    bool operator==(const PositionedOp& other) const {
        return position == other.position && usig == other.usig;
    }
};

struct PositionedOpHasher {
    std::size_t operator()(const PositionedOp& value) const {
        return std::hash<Position*>()(value.position) ^ (USignatureHasher()(value.usig) << 1);
    }
};
}

void RetroactivePruning::prune(const USignature& op, Position& position) {

    std::unordered_set<PositionedOp, PositionedOpHasher> opsToRemove;
    std::unordered_set<PositionedOp, PositionedOpHasher> openOps;
    openOps.insert({&position, op});
    std::unordered_map<PositionedOp, USigSet, PositionedOpHasher> removedExpansionsOfParents;

    // Traverse the hierarchy upwards, removing expansions/predecessors
    // and marking all "root" operations whose induces subtrees should be pruned 

    while (!openOps.empty()) {
        PositionedOp current = *openOps.begin();
        openOps.erase(current);
        Log::d("PRUNE_UP %s@(%zu,%zu)\n", TOSTR(current.usig), current.position->getLayerIndex(), current.position->getPositionIndex());

        Position* currentPosition = current.position;
        assert(currentPosition->hasAction(current.usig) || currentPosition->hasReduction(current.usig));

        Position* parentPosition = currentPosition->getParentPosition();
        if (parentPosition == nullptr) {
            // Top of the hierarchy hit
            opsToRemove.insert(current);
            continue;
        }

        bool pruneSomeParent = false;
        assert(currentPosition->getPredecessors().count(current.usig) || Log::e("%s has no predecessors!\n", TOSTR(current.usig)));
        for (const auto& parent : currentPosition->getPredecessors().at(current.usig)) {
            PositionedOp parentOp{parentPosition, parent};
            assert(parentPosition->hasAction(parent) || parentPosition->hasReduction(parent) || Log::e("%s@(%zu,%zu)\n", TOSTR(parent), parentPosition->getLayerIndex(), parentPosition->getPositionIndex()));
            const auto& siblings = currentPosition->getExpansions().at(parent);

            // Mark op for removal from expansion of the parent
            assert(siblings.count(current.usig));
            removedExpansionsOfParents[parentOp].insert(current.usig);

            if (removedExpansionsOfParents[parentOp].size() == siblings.size()) {
                // Siblings become empty -> prune parent as well
                openOps.insert(parentOp);
                pruneSomeParent = true;
            }
        }

        // No parent pruned? -> This op is a root of a subtree to be pruned
        if (!pruneSomeParent) opsToRemove.insert(current);
    }

    // Traverse the hierarchy downwards, pruning all children who became impossible

    while (!opsToRemove.empty()) {
        PositionedOp current = *opsToRemove.begin();
        opsToRemove.erase(current);
        Position* currentPosition = current.position;
        Log::d("PRUNE_DOWN %s@(%zu,%zu)\n", TOSTR(current.usig), currentPosition->getLayerIndex(), currentPosition->getPositionIndex());
        assert(currentPosition->hasAction(current.usig) || currentPosition->hasReduction(current.usig));

        // Visit all tree children and mark those that became impossible.
        for (Position* childPos : currentPosition->getChildrenPositions()) {
            Position& below = *childPos;
            if (below.getExpansions().count(current.usig)) for (auto& child : below.getExpansions().at(current.usig)) {
                assert(below.getPredecessors().at(child).count(current.usig));
                if (&below == &position && child == op) {
                    // Arrived back at original op to prune
                    opsToRemove.insert({&position, op});
                } else if (below.getPredecessors().at(child).size() == 1) {
                    // Child has this op as its only predecessor -> prune
                    opsToRemove.insert({&below, child});
                } else {
                    Log::d("PRUNE %i pred left for %s@(%i,%i)\n",
                        below.getPredecessors().at(child).size()-1,
                        TOSTR(child),
                        (int) below.getLayerIndex(),
                        (int) below.getPositionIndex());
                    below.getPredecessors().at(child).erase(current.usig);
                }
            } else {
                Log::d("PRUNE No expansions for %s @ (%i,%i)\n", TOSTR(current.usig), (int) below.getLayerIndex(), (int) below.getPositionIndex());
            }
        }

        // Remove the operation's occurrence itself,
        // together with its expansions and predecessors
        int opVar = currentPosition->getVariableOrZero(VarType::OP, current.usig);
        if (opVar != 0) _enc.addUnitConstraint(-opVar);
        currentPosition->removeActionOccurrence(current.usig);
        currentPosition->removeReductionOccurrence(current.usig);
        _num_retroactively_pruned_ops++;
    }

    _num_retroactive_prunings++;
}
