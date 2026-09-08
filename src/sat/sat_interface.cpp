#include "sat/sat_interface.h"

#include <cassert>
#include <cstdlib>
#include <sstream>
#include <string>

#include "util/log.h"
#include "util/params.h"
#include "util/statistics.h"

extern "C" {
    #ifdef USE_IPAMIR
    #include "sat/ipamir.h"
    #else
    #include "sat/ipasir.h"
    #endif
}

namespace {
constexpr const char* CNF_OUTPUT_PATH = "f.cnf";
constexpr const char* WCNF_OUTPUT_PATH = "f.wcnf";
constexpr std::size_t FORMULA_HEADER_WIDTH = 80;
}

SatInterface::SatInterface(Parameters& params)
        : _stats(Statistics::getInstance()),
          _write_formula(params.isNonzero("wf")),
          _write_wcnf(params.isNonzero("optimal")) {
    #ifdef USE_IPAMIR
    const bool reusePreviousCores = params.isNonzero("reusePreviousCores");
    Log::i("Reuse previous cores: %d\n", reusePreviousCores);
    _solver = ipamir_init(reusePreviousCores);
    #else
    _solver = ipasir_init();
    ipasir_set_seed(_solver, params.getIntParam("s"));
    #endif

    if (_solver == nullptr) {
        Log::e("Could not initialize the SAT solver\n");
        std::exit(1);
    }

    if (_write_formula) {
        const char* outputPath = _write_wcnf ? WCNF_OUTPUT_PATH : CNF_OUTPUT_PATH;
        _formula_stream.open(outputPath);
        if (!_formula_stream) {
            Log::e("Could not open %s for formula output\n", outputPath);
            std::exit(1);
        }
        // Reserve space for the header line, which will be written later
        _formula_stream << std::string(FORMULA_HEADER_WIDTH, ' ') << "\n";
    }
}

SatInterface::~SatInterface() {
    assert(!_clause_open);
    #ifdef USE_IPAMIR
    ipamir_release(_solver);
    #else
    ipasir_release(_solver);
    #endif
}

void SatInterface::addHardLiteralToSolver(int literalOrZero) {
    #ifdef USE_IPAMIR
    ipamir_add_hard(_solver, literalOrZero);
    #else
    ipasir_add(_solver, literalOrZero);
    #endif
}

void SatInterface::beginClause() {
    assert(!_formula_written);
    assert(!_clause_open);
    _clause_open = true;
    if (_write_formula && _write_wcnf) _formula_stream << "h ";
}

void SatInterface::addClause(int literal) {
    beginClause();
    appendClause(literal);
    endClause();
}

void SatInterface::addClause(int firstLiteral, int secondLiteral) {
    beginClause();
    appendClause(firstLiteral, secondLiteral);
    endClause();
}

void SatInterface::addClause(int firstLiteral, int secondLiteral, int thirdLiteral) {
    beginClause();
    appendClause({firstLiteral, secondLiteral, thirdLiteral});
    endClause();
}

void SatInterface::addClause(std::initializer_list<int> literals) {
    beginClause();
    appendClause(literals);
    endClause();
}

void SatInterface::addClause(const std::vector<int>& literals) {
    beginClause();
    for (int literal : literals) appendClause(literal);
    endClause();
}

void SatInterface::appendClause(int literal) {
    assert(literal != 0);
    assert(!_formula_written);
    if (!_clause_open) beginClause();

    addHardLiteralToSolver(literal);
    if (_write_formula) _formula_stream << literal << " ";
    _stats._num_lits++;
}

void SatInterface::appendClause(int firstLiteral, int secondLiteral) {
    appendClause(firstLiteral);
    appendClause(secondLiteral);
}

void SatInterface::appendClause(std::initializer_list<int> literals) {
    if (literals.size() == 0 && !_clause_open) beginClause();
    for (int literal : literals) appendClause(literal);
}

void SatInterface::endClause() {
    assert(_clause_open);
    assert(!_formula_written);

    addHardLiteralToSolver(0);
    if (_write_formula) _formula_stream << "0\n";
    _clause_open = false;
    _stats._num_cls++;
}

void SatInterface::addSoftLit(int literal, int weight) {
    assert(literal != 0);
    assert(weight > 0);
    assert(!_clause_open);
    assert(!_formula_written);
    assert(!_write_formula || _write_wcnf);

    #ifdef USE_IPAMIR
    ipamir_add_soft_lit(_solver, literal, weight);
    _soft_literal_weights[literal] = static_cast<std::uint64_t>(weight);
    #else
    Log::e("Soft literals are not supported by the used SAT solver. Please compile with the uwrmaxsat solver\n");
    std::exit(1);
    #endif
}

void SatInterface::clearSoftLits() {
    assert(!_clause_open);
    assert(!_formula_written);

    #ifdef USE_IPAMIR
    for (const auto& [literal, weight] : _soft_literal_weights) {
        (void) weight;
        ipamir_add_soft_lit(_solver, literal, 0);
    }
    _soft_literal_weights.clear();
    #else
    Log::e("Soft literals are not supported by the used SAT solver. Please compile with the uwrmaxsat solver\n");
    std::exit(1);
    #endif
}

int SatInterface::getObjectiveValue() const {
    #ifdef USE_IPAMIR
    return ipamir_val_obj(_solver);
    #else
    Log::e("Soft literals are not supported by the used SAT solver. Please compile with the uwrmaxsat solver\n");
    std::exit(1);
    #endif
}

void SatInterface::assume(int literal) {
    assert(literal != 0);
    assert(!_clause_open);
    assert(!_formula_written);

    #ifdef USE_IPAMIR
    ipamir_assume(_solver, literal);
    #else
    ipasir_assume(_solver, literal);
    #endif
    _pending_assumptions.push_back(literal);
    _stats._num_asmpts++;
}

bool SatInterface::holds(int literal) const {
    assert(literal != 0);
    #ifdef USE_IPAMIR
    return ipamir_val_lit(_solver, literal) > 0;
    #else
    return ipasir_val(_solver, literal) > 0;
    #endif
}

bool SatInterface::didAssumptionFail(int literal) const {
    assert(literal != 0);
    #ifdef USE_IPAMIR
    return false;
    #else
    return ipasir_failed(_solver, literal);
    #endif
}

bool SatInterface::hasFormulaAssumptions() const {
    return !_pending_assumptions.empty() || !_last_solved_assumptions.empty();
}

void SatInterface::setTerminateCallback(void* state, int (*terminate)(void* state)) {
    #ifdef USE_IPAMIR
    ipamir_set_terminate(_solver, state, terminate);
    #else
    ipasir_set_terminate(_solver, state, terminate);
    #endif
}

void SatInterface::setLearnCallback(int maxLength, void* state, void (*learn)(void* state, int* clause)) {
    #ifdef USE_IPAMIR
    (void) maxLength;
    (void) state;
    (void) learn;
    Log::w("Learn callback is not supported by the IPAMIR interface\n");
    #else
    ipasir_set_learn(_solver, state, maxLength, learn);
    #endif
}

int SatInterface::solve() {
    assert(!_clause_open);
    assert(!_formula_written);

    _stats.beginTiming(TimingStage::SOLVER);
    _last_solved_assumptions = _pending_assumptions;

    #ifdef USE_IPAMIR
    int result = ipamir_solve(_solver);
    if (result == 30) {
        Log::i("An optimal weighted solution has been found\n");
        Log::i("Objective value: %lu\n", ipamir_val_obj(_solver));
        result = 10;
    }
    #else
    const int result = ipasir_solve(_solver);
    #endif

    _pending_assumptions.clear();
    _stats._num_asmpts = 0;
    _stats.endTiming(TimingStage::SOLVER);
    return result;
}

const std::vector<int>& SatInterface::getFormulaAssumptions() const {
    return _pending_assumptions.empty() ? _last_solved_assumptions : _pending_assumptions;
}

void SatInterface::writeFormulaHeader(int maxVariable, std::size_t numClauses) {
    std::ostringstream header;
    if (_write_wcnf) header << "c ";
    header << "p cnf " << maxVariable << " " << numClauses;

    const std::string headerText = header.str();
    if (headerText.size() > FORMULA_HEADER_WIDTH) {
        Log::e("Formula header exceeds its reserved width\n");
        std::exit(1);
    }

    // We kept the first line empty to reserve space for the header, so we can now overwrite it with the actual header text.
    _formula_stream.seekp(0);
    _formula_stream << headerText << std::string(FORMULA_HEADER_WIDTH - headerText.size(), ' ') << "\n";
}

void SatInterface::writeFormulaFile(int maxVariable) {
    if (!_write_formula || _formula_written) return;
    assert(!_clause_open);

    const std::vector<int>& assumptions = getFormulaAssumptions();
    for (int assumption : assumptions) {
        if (_write_wcnf) _formula_stream << "h ";
        _formula_stream << assumption << " 0\n";
    }

    if (_write_wcnf) {
        for (const auto& [literal, weight] : _soft_literal_weights) {
            _formula_stream << weight << " " << -literal << " 0\n";
        }
    }

    const std::size_t numClauses = static_cast<std::size_t>(_stats._num_cls)
            + assumptions.size() + _soft_literal_weights.size();
    writeFormulaHeader(maxVariable, numClauses);
    _formula_stream.close();
    _formula_written = true;
}
