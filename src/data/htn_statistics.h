#ifndef SIBYLSAT_HTN_STATISTICS_H
#define SIBYLSAT_HTN_STATISTICS_H

#include <cstddef>

class HtnInstance;
class Reduction;

/** Computes and prints descriptive statistics for a built HTN instance. */
class HtnStatistics {
private:
    static size_t countFreeArguments(const HtnInstance& htn, const Reduction& reduction);

public:
    static void print(const HtnInstance& htn);
};

#endif
