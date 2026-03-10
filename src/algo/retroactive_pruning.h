
#ifndef DOMPASCH_LILOTANE_RETROACTIVE_PRUNING_H
#define DOMPASCH_LILOTANE_RETROACTIVE_PRUNING_H

#include <vector>

#include "data/position.h"
#include "sat/encoding.h"

class RetroactivePruning {

private:
    Encoding& _enc;

    // statistics
    size_t _num_retroactive_prunings = 0;
    size_t _num_retroactively_pruned_ops = 0;

public:
    RetroactivePruning(Encoding& enc) : _enc(enc) {}

    void prune(const USignature& op, Position& position);

    size_t getNumRetroactivePunings() const {return _num_retroactive_prunings;}
    size_t getNumRetroactivelyPrunedOps() const {return _num_retroactively_pruned_ops;}
};

#endif
