
#ifndef DOMPASCH_LILOTANE_SUBSTITUTION_CONSTRAINT_H
#define DOMPASCH_LILOTANE_SUBSTITUTION_CONSTRAINT_H

#include "data/htn_instance.h"
#include "sat/literal_tree.h"
#include "util/log.h"

typedef LiteralTree<IntPair, IntPairHasher> IntPairTree;

class SubstitutionConstraint {

public:
    enum Representation {UNDECIDED, ALLOWED_ASSIGNMENTS, FORBIDDEN_ASSIGNMENTS};

private:
    std::vector<int> _q_constants;
    IntPairTree _allowed_assignments;
    IntPairTree _forbidden_assignments;
    Representation _representation = UNDECIDED;

public:
    SubstitutionConstraint(const std::vector<int>& qConstants) : _q_constants(qConstants) {}
    SubstitutionConstraint(std::vector<int>&& qConstants) : _q_constants(std::move(qConstants)) {}
    SubstitutionConstraint(const SubstitutionConstraint& other) : 
        _q_constants(other._q_constants),
        _allowed_assignments(other._allowed_assignments),
        _forbidden_assignments(other._forbidden_assignments),
        _representation(other._representation) {}
    SubstitutionConstraint(SubstitutionConstraint&& other) : 
        _q_constants(std::move(other._q_constants)),
        _allowed_assignments(std::move(other._allowed_assignments)),
        _forbidden_assignments(std::move(other._forbidden_assignments)),
        _representation(other._representation) {}

    SubstitutionConstraint& operator=(const SubstitutionConstraint& other) {
        _q_constants = other._q_constants;
        _allowed_assignments = other._allowed_assignments;
        _forbidden_assignments = other._forbidden_assignments;
        _representation = other._representation;
        return *this;
    }

    void allow(const std::vector<IntPair>& assignment) {
        _allowed_assignments.insert(assignment);
    }

    void forbid(const std::vector<IntPair>& assignment) {
        _forbidden_assignments.insert(assignment);
    }

    void chooseRepresentation(Representation representation = UNDECIDED) {
        const size_t forbiddenEncodingSize = _forbidden_assignments.getSizeOfNegationEncoding();
        const size_t allowedEncodingSize = _allowed_assignments.getSizeOfEncoding();
        if (representation == ALLOWED_ASSIGNMENTS || (representation == UNDECIDED && forbiddenEncodingSize > allowedEncodingSize)) {
            _forbidden_assignments = IntPairTree();
            _representation = ALLOWED_ASSIGNMENTS;
        } else {
            _allowed_assignments = IntPairTree();
            _representation = FORBIDDEN_ASSIGNMENTS;
        }
    }

    bool involvesSupersetOf(const std::vector<int>& qConstants) const {
        // Every q-constant in the query must also be in the involved q-constants
        // (in the same order), otherwise no meaningful check can be done
        size_t j = 0;
        for (size_t i = 0; i < qConstants.size(); i++) {
            while (j < _q_constants.size() && _q_constants[j] != qConstants[i])
                j++;
            if (j == _q_constants.size()) return false;
        }
        return true;
    }

    bool isValid(const std::vector<IntPair>& sub, bool sameReference) const {
        if (_representation == ALLOWED_ASSIGNMENTS) {
            // Same involved q-constants: Can perform exact (in)validity check
            return sameReference ? _allowed_assignments.contains(sub) : _allowed_assignments.subsumes(sub);
        } else {
            return sameReference ? !_forbidden_assignments.contains(sub) : !_forbidden_assignments.hasPathSubsumedBy(sub);
        }
    }

    bool canMerge(const SubstitutionConstraint& other) const {
        if (_representation != other._representation) return false;
        if (_representation == UNDECIDED) return false;
        return _q_constants == other._q_constants;
    }

    void merge(SubstitutionConstraint&& other) {
        if (_representation == ALLOWED_ASSIGNMENTS) {
            _allowed_assignments.intersect(std::move(other._allowed_assignments));
        }
        if (_representation == FORBIDDEN_ASSIGNMENTS) {
            _forbidden_assignments.merge(std::move(other._forbidden_assignments));
        }
    }

    std::vector<std::vector<IntPair>> getEncoding(Representation representation = UNDECIDED) const {
        if (representation == ALLOWED_ASSIGNMENTS) return _allowed_assignments.encode();
        if (representation == FORBIDDEN_ASSIGNMENTS) return _forbidden_assignments.encodeNegation();
        if (_representation == ALLOWED_ASSIGNMENTS) return _allowed_assignments.encode();
        return _forbidden_assignments.encodeNegation();
    }

    size_t getEncodedSize() const {
        return _allowed_assignments.getSizeOfEncoding() + _forbidden_assignments.getSizeOfNegationEncoding();
    }

    Representation getRepresentation() const {return _representation;}

    const std::vector<int>& getQConstants() const {return _q_constants;}

    static std::vector<int> getQArgumentIndicesByDomainSize(HtnInstance& htn, const std::vector<int>& arguments, const std::vector<int>& sorts) {

        // Collect indices of arguments which will be substituted
        std::vector<int> argIndices;
        for (size_t i = 0; i < arguments.size(); i++) {
            if (htn.isQConstant(arguments[i])) argIndices.push_back(i);
        }

        // Sort argument indices by the potential size of their domain
        std::sort(argIndices.begin(), argIndices.end(), 
                [&](int i, int j) {return htn.getConstantsOfSort(sorts[i]).size() < htn.getConstantsOfSort(sorts[j]).size();});
        return argIndices;
    }

    static std::vector<IntPair> toAssignmentPath(const std::vector<int>& qArguments, const std::vector<int>& decodedArguments, const std::vector<int>& qArgumentIndices) {
        
        // Write argument substitutions into the result in correct order
        std::vector<IntPair> path;
        path.reserve(qArgumentIndices.size());
        for (int argumentIndex : qArgumentIndices) {
            path.emplace_back(qArguments[argumentIndex], decodedArguments[argumentIndex]);
        }
        return path;
    }
};

#endif
