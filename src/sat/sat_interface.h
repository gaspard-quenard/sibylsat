
#ifndef DOMPASCH_LILOTANE_SAT_INTERFACE_H
#define DOMPASCH_LILOTANE_SAT_INTERFACE_H

#include <initializer_list>
#include <fstream>
#include <string>
#include <iostream>
#include <assert.h>
#include <vector>

#include "util/params.h"
#include "util/log.h"
#include "sat/variable_domain.h"
#include "util/statistics.h"

extern "C" {
    #ifdef USE_IPAMIR
    #include "sat/ipamir.h"
    #else
    #include "sat/ipasir.h"
    #endif
}

class SatInterface {

private:
    Parameters& _params;
    void* _solver;
    std::ofstream _out;
    Statistics& _stats;

    const bool _print_formula;    
    bool _began_line = false;

    std::vector<int> _last_assumptions;
    std::vector<int> _no_decision_variables;
    std::map<int, int> _soft_literals_to_weights;

public:
    SatInterface(Parameters& params) : 
                _params(params), _stats(Statistics::getInstance()), _print_formula(params.isNonzero("wf")) {
        #ifdef USE_IPAMIR
        bool reuse_previous_cores = params.isNonzero("reusePreviousCores");
        printf("Reuse previous cores: %d\n", reuse_previous_cores);
        _solver = ipamir_init(reuse_previous_cores);
        #else
        _solver = ipasir_init();
        ipasir_set_seed(_solver, params.getIntParam("s"));
        #endif
        if (_print_formula) _out.open("formula.cnf");
    }
    
    inline void addClause(int lit) {
        assert(lit != 0);
        #ifdef USE_IPAMIR
        ipamir_add_hard(_solver, lit); ipamir_add_hard(_solver, 0);
        #else
        ipasir_add(_solver, lit); ipasir_add(_solver, 0);
        #endif
        if (_print_formula) _out << lit << " 0\n";
        _stats._num_lits++; _stats._num_cls++;
    }
    inline void addClause(int lit1, int lit2) {
        assert(lit1 != 0);
        assert(lit2 != 0);
        #ifdef USE_IPAMIR
        ipamir_add_hard(_solver, lit1); ipamir_add_hard(_solver, lit2); ipamir_add_hard(_solver, 0);
        #else
        ipasir_add(_solver, lit1); ipasir_add(_solver, lit2); ipasir_add(_solver, 0);
        #endif
        if (_print_formula) _out << lit1 << " " << lit2 << " 0\n";
        _stats._num_lits += 2; _stats._num_cls++;
    }
    inline void addClause(int lit1, int lit2, int lit3) {
        assert(lit1 != 0);
        assert(lit2 != 0);
        assert(lit3 != 0);
        #ifdef USE_IPAMIR
        ipamir_add_hard(_solver, lit1); ipamir_add_hard(_solver, lit2); ipamir_add_hard(_solver, lit3); ipamir_add_hard(_solver, 0);
        #else
        ipasir_add(_solver, lit1); ipasir_add(_solver, lit2); ipasir_add(_solver, lit3); ipasir_add(_solver, 0);
        #endif
        if (_print_formula) _out << lit1 << " " << lit2 << " " << lit3 << " 0\n";
        _stats._num_lits += 3; _stats._num_cls++;
    }
    inline void addClause(const std::initializer_list<int>& lits) {
        for (int lit : lits) {
            assert(lit != 0);
            #ifdef USE_IPAMIR
            ipamir_add_hard(_solver, lit);
            #else
            ipasir_add(_solver, lit);
            #endif
            if (_print_formula) _out << lit << " ";
        } 
        #ifdef USE_IPAMIR
        ipamir_add_hard(_solver, 0);
        #else
        ipasir_add(_solver, 0);
        #endif
        if (_print_formula) _out << "0\n";
        _stats._num_cls++;
        _stats._num_lits += lits.size();
    }
    inline void addClause(const std::vector<int>& cls) {
        for (int lit : cls) {
            assert(lit != 0);
            #ifdef USE_IPAMIR
            ipamir_add_hard(_solver, lit);
            #else
            ipasir_add(_solver, lit);
            #endif
            if (_print_formula) _out << lit << " ";
        } 
        #ifdef USE_IPAMIR
        ipamir_add_hard(_solver, 0);
        #else
        ipasir_add(_solver, 0);
        #endif
        if (_print_formula) _out << "0\n";
        _stats._num_cls++;
        _stats._num_lits += cls.size();
    }
    inline void appendClause(int lit) {
        _began_line = true;
        assert(lit != 0);
        #ifdef USE_IPAMIR
        ipamir_add_hard(_solver, lit);
        #else
        ipasir_add(_solver, lit);
        #endif
        if (_print_formula) _out << lit << " ";
        _stats._num_lits++;
    }
    inline void appendClause(int lit1, int lit2) {
        _began_line = true;
        assert(lit1 != 0);
        assert(lit2 != 0);
        #ifdef USE_IPAMIR
        ipamir_add_hard(_solver, lit1); ipamir_add_hard(_solver, lit2);
        #else
        ipasir_add(_solver, lit1); ipasir_add(_solver, lit2);
        #endif
        if (_print_formula) _out << lit1 << " " << lit2 << " ";
        _stats._num_lits += 2;
    }
    inline void appendClause(const std::initializer_list<int>& lits) {
        _began_line = true;
        for (int lit : lits) {
            assert(lit != 0);
            #ifdef USE_IPAMIR
            ipamir_add_hard(_solver, lit);
            #else
            ipasir_add(_solver, lit);
            #endif
            if (_print_formula) _out << lit << " ";
            //log("%i ", lit);
        } 

        _stats._num_lits += lits.size();
    }
    inline void endClause() {
        assert(_began_line);
        #ifdef USE_IPAMIR
        ipamir_add_hard(_solver, 0);
        #else
        ipasir_add(_solver, 0);
        #endif
        if (_print_formula) _out << "0\n";
        //log("0\n");
        _began_line = false;

        _stats._num_cls++;
    }
    inline void addSoftLit(int lit, int weight) {
        assert(lit != 0);
        assert(weight >= 0);
        #ifdef USE_IPAMIR
        ipamir_add_soft_lit(_solver, lit, weight);
        _soft_literals_to_weights[lit] = weight;
        #else
        Log::e("Soft literals are not supported by the used SAT solver. Please compile with the uwrmaxsat solver\n");
        exit(1);
        #endif
    }
    inline void clearSoftLits() {
        #ifdef USE_IPAMIR
        for (auto it = _soft_literals_to_weights.begin(); it != _soft_literals_to_weights.end(); it++) {
            ipamir_add_soft_lit(_solver, it->first, 0);
        }
        _soft_literals_to_weights.clear();
        #else
        Log::e("Soft literals are not supported by the used SAT solver. Please compile with the uwrmaxsat solver\n");
        exit(1);
        #endif
    }
    inline int getObjectiveValue() {
        #ifdef USE_IPAMIR
        return ipamir_val_obj(_solver);
        #else
        Log::e("Soft literals are not supported by the used SAT solver. Please compile with the uwrmaxsat solver\n");
        exit(1);
        #endif
    }
    inline void assume(int lit) {
        if (_stats._num_asmpts == 0) _last_assumptions.clear();
        #ifdef USE_IPAMIR
        ipamir_assume(_solver, lit);
        #else
        ipasir_assume(_solver, lit);
        #endif
        //log("CNF !%i\n", lit);
        _last_assumptions.push_back(lit);
        _stats._num_asmpts++;
    }

    inline bool holds(int lit) {
        #ifdef USE_IPAMIR
        return ipamir_val_lit(_solver, lit) > 0;
        #else
        return ipasir_val(_solver, lit) > 0;
        #endif
    }

    inline bool didAssumptionFail(int lit) {
        #ifdef USE_IPAMIR
        // Log::w("Checking if assumption failed is not supported by the IPAMIR interface\n");
        return false;
        #else
        return ipasir_failed(_solver, lit);
        #endif
    }

    bool hasLastAssumptions() {
        return !_last_assumptions.empty();
    }

    void setTerminateCallback(void * state, int (*terminate)(void * state)) {
        #ifdef USE_IPAMIR
        ipamir_set_terminate(_solver, state, terminate);
        #else
        ipasir_set_terminate(_solver, state, terminate);
        #endif
    }

    void setLearnCallback(int maxLength, void* state, void (*learn)(void * state, int * clause)) {
        #ifdef USE_IPAMIR
        Log::w("Learn Callback is not supported by the IPAMIR interface\n");
        #else
        ipasir_set_learn(_solver, state, maxLength, learn);
        #endif
    }

    int solve() {
        _stats.beginTiming(TimingStage::SOLVER);
        #ifdef USE_IPAMIR
        int result = ipamir_solve(_solver);
        if (result == 30) {
            Log::i("An optimal weighted solution has been found\n");
            Log::i("Objective value: %lu\n", ipamir_val_obj(_solver));
            // Set to solution has been found instead of optimal solution has been found to use the same return value as ipasir
            result = 10; 
        }
        #else        
        int result = ipasir_solve(_solver);
        #endif
        if (_stats._num_asmpts == 0) _last_assumptions.clear();
        _stats._num_asmpts = 0;
        _stats.endTiming(TimingStage::SOLVER);
        return result;
    }

    inline void print_formula(std::string filename) {

        // std::cout << "WRITING FORMULA TO FILE: " << filename << std::endl;

        // Create final formula file
        std::ofstream ffile;
        ffile.open(filename);

        ffile << "p cnf " << VariableDomain::getMaxVar() << " " << (_stats._num_cls+_last_assumptions.size()) << "\n";

        ffile << "c assumptions\n";
        for (int asmpt : _last_assumptions) {
            ffile << asmpt << " 0\n";
        }
        ffile << "c end assumptions\n";

        // Write the content of _out to the file
        _out.flush();
        std::ifstream oldfile;
        oldfile.open("formula.cnf");
        std::string line;
        while (std::getline(oldfile, line)) {
            line = line + "\n";
            ffile.write(line.c_str(), line.size());
        }

        // Finish
        ffile.flush();
        ffile.close();

    }

    ~SatInterface() {

        bool wcnf_format = _soft_literals_to_weights.size() > 0;

        
        if (_params.isNonzero("wf")) {

            for (int asmpt : _last_assumptions) {
                _out << asmpt << " 0\n";
            }
            _out.flush();
            _out.close();

            // Create final formula file
            std::ofstream ffile;
            std::string filename = wcnf_format ? "f.wcnf" : "f.cnf";
            ffile.open(filename);
            
            // Append header to formula file
            if (wcnf_format) ffile << "p wcnf " << VariableDomain::getMaxVar() << " " << (_stats._num_cls+_last_assumptions.size()+_soft_literals_to_weights.size()) << " 156116" <<  "\n";
            else ffile << "p cnf " << VariableDomain::getMaxVar() << " " << (_stats._num_cls+_last_assumptions.size()) << "\n";

            // Append main content to formula file (reading from "old" file)
            std::ifstream oldfile;
            oldfile.open("formula.cnf");
            std::string line;
            while (std::getline(oldfile, line)) {
                if (wcnf_format && line[0] != 'c') line = "156116 " + line + "\n";
                else line = line + "\n";
                ffile.write(line.c_str(), line.size());
            }

            if (wcnf_format) {
                // Write all the soft literals with their weights
                for (auto it = _soft_literals_to_weights.begin(); it != _soft_literals_to_weights.end(); it++) {
                    ffile << it->second << " " << (-it->first) << " 0\n";
                }
            }

            oldfile.close();
            remove("formula.cnf");

            // Finish
            ffile.flush();
            ffile.close();
        }

        // Release SAT solver
        #ifdef USE_IPAMIR
        ipamir_release(_solver);
        #else
        ipasir_release(_solver);
        #endif
    }
};

#endif
