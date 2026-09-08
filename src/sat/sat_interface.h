#ifndef DOMPASCH_LILOTANE_SAT_INTERFACE_H
#define DOMPASCH_LILOTANE_SAT_INTERFACE_H

#include <cstddef>
#include <cstdint>
#include <fstream>
#include <initializer_list>
#include <map>
#include <vector>

class Parameters;
class Statistics;

class SatInterface {
private:
    void* _solver = nullptr;
    std::ofstream _formula_stream;
    Statistics& _stats;

    const bool _write_formula;
    const bool _write_wcnf;
    bool _clause_open = false;
    bool _formula_written = false;

    std::vector<int> _pending_assumptions;
    std::vector<int> _last_solved_assumptions;
    std::map<int, std::uint64_t> _soft_literal_weights;

    void addHardLiteralToSolver(int literalOrZero);
    void beginClause();
    const std::vector<int>& getFormulaAssumptions() const;
    void writeFormulaHeader(int maxVariable, std::size_t numClauses);

public:
    explicit SatInterface(Parameters& params);
    ~SatInterface();

    // Each instance exclusively owns its solver handle; copying or moving it
    // would risk releasing the same solver twice.
    SatInterface(const SatInterface&) = delete;
    SatInterface& operator=(const SatInterface&) = delete;
    SatInterface(SatInterface&&) = delete;
    SatInterface& operator=(SatInterface&&) = delete;

    /** Submit one complete hard clause to the solver. */
    void addClause(int literal);
    void addClause(int firstLiteral, int secondLiteral);
    void addClause(int firstLiteral, int secondLiteral, int thirdLiteral);
    void addClause(std::initializer_list<int> literals);
    void addClause(const std::vector<int>& literals);

    /** Build a hard clause incrementally; finish it with endClause(). */
    void appendClause(int literal);
    void appendClause(int firstLiteral, int secondLiteral);
    void appendClause(std::initializer_list<int> literals);
    void endClause();

    void addSoftLit(int literal, int weight);
    void clearSoftLits();
    int getObjectiveValue() const;

    /** Add an assumption for the next solve call. */
    void assume(int literal);
    bool holds(int literal) const;
    bool didAssumptionFail(int literal) const;
    bool hasFormulaAssumptions() const;

    void setTerminateCallback(void* state, int (*terminate)(void* state));
    void setLearnCallback(int maxLength, void* state, void (*learn)(void* state, int* clause));

    int solve();

    /** If formula output is enabled, write hard clauses, relevant assumptions, and soft literals to f.cnf or f.wcnf. */
    void writeFormulaFile(int maxVariable);
};

#endif
