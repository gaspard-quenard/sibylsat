#include "preprocessing/lifted_mutex_group_grounder.h"

#include <algorithm>
#include <cctype>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>

#include "algo/fact_analysis.h"
#include "data/htn_instance.h"
#include "util/bitvec.h"
#include "util/hashmap.h"
#include "util/log.h"

namespace {

enum class MutexParameterKind {
    FIXED,
    COUNTED,
    CONSTANT
};

struct LiftedMutexParameter {
    MutexParameterKind kind;
    int sortId = -1;
    int value = -1;
};

struct LiftedMutexPredicate {
    int predicateId;
    std::vector<int> parameterIndices;
};

struct LiftedMutexGroup {
    std::vector<LiftedMutexPredicate> predicates;
    std::vector<LiftedMutexParameter> parameters;
    bool usable = true;
};

std::string trim(std::string value) {
    const size_t begin = value.find_first_not_of(" \t\r\n");
    if (begin == std::string::npos) return {};
    const size_t end = value.find_last_not_of(" \t\r\n");
    return value.substr(begin, end - begin + 1);
}

std::string uppercase(std::string value) {
    std::transform(value.begin(), value.end(), value.begin(), [](unsigned char character) { return std::toupper(character); });
    return value;
}

class GroundingContext {
private:
    HtnInstance& _htn;
    FactAnalysis& _facts;
    std::vector<std::vector<int>> _ground_groups;
    FlatHashMap<size_t, std::vector<size_t>> _ground_group_ids_by_hash;

    int resolveSortId(const std::string& sortName) {
        int sortId = _htn.nameId(sortName);
        if (_htn.sortHasConstants(sortId)) return sortId;

        sortId = _htn.nameId(uppercase(sortName));
        if (_htn.sortHasConstants(sortId)) return sortId;
        return -1;
    }

    LiftedMutexGroup parseGroup(const std::string& line, size_t lineNumber) {
        if (line.size() < 2 || line.front() != '{' || line.back() != '}') {
            throw std::runtime_error("Malformed lifted mutex group at line " + std::to_string(lineNumber));
        }

        LiftedMutexGroup group;
        std::unordered_map<std::string, int> parameterIndexByName;
        const std::string contents = line.substr(1, line.size() - 2);
        size_t literalBegin = 0;
        while (literalBegin <= contents.size()) {
            const size_t literalEnd = contents.find(',', literalBegin);
            const std::string literal = trim(contents.substr(literalBegin, literalEnd - literalBegin));
            if (literal.empty() || (literal.front() != '+' && literal.front() != '-')) {
                throw std::runtime_error("Expected a signed predicate in lifted mutex group at line " + std::to_string(lineNumber));
            }

            // SibylSat encodes positive state facts. Negative FAM literals are
            // safely omitted: every subset of a mutex group remains a mutex.
            if (literal.front() == '+') parsePositivePredicate(literal, lineNumber, group, parameterIndexByName);
            if (literalEnd == std::string::npos) break;
            literalBegin = literalEnd + 1;
        }
        return group;
    }

    void parsePositivePredicate(const std::string& literal, size_t lineNumber, LiftedMutexGroup& group, std::unordered_map<std::string, int>& parameterIndexByName) {
        std::istringstream tokens(literal.substr(1));
        std::string predicateName;
        if (!(tokens >> predicateName)) throw std::runtime_error("Missing predicate name in lifted mutex group at line " + std::to_string(lineNumber));

        predicateName = _htn.getPredicateInCorrectCase(predicateName);
        LiftedMutexPredicate predicate{_htn.nameId(predicateName), {}};
        std::string argument;
        while (tokens >> argument) {
            const size_t colon = argument.find(':');
            MutexParameterKind kind = MutexParameterKind::CONSTANT;
            int sortId = -1;
            std::string parameterName = "#" + argument;
            if (colon != std::string::npos) {
                parameterName = argument.substr(0, colon);
                if (parameterName.empty() || (parameterName.front() != 'V' && parameterName.front() != 'C')) {
                    throw std::runtime_error("Unknown mutex parameter '" + argument + "' at line " + std::to_string(lineNumber));
                }
                kind = parameterName.front() == 'V' ? MutexParameterKind::FIXED : MutexParameterKind::COUNTED;
                sortId = resolveSortId(argument.substr(colon + 1));
                if (sortId < 0) {
                    group.usable = false;
                    return;
                }
            }

            auto [match, inserted] = parameterIndexByName.emplace(parameterName, group.parameters.size());
            if (inserted) {
                const int value = kind == MutexParameterKind::CONSTANT ? _htn.nameId(argument) : -1;
                group.parameters.push_back({kind, sortId, value});
            } else {
                const LiftedMutexParameter& existing = group.parameters[match->second];
                if (existing.kind != kind || existing.sortId != sortId) {
                    throw std::runtime_error("Inconsistent mutex parameter '" + parameterName + "' at line " + std::to_string(lineNumber));
                }
            }
            predicate.parameterIndices.push_back(match->second);
        }

        if (predicate.parameterIndices.size() != _htn.getSorts(predicate.predicateId).size()) {
            throw std::runtime_error("Wrong predicate arity in lifted mutex group at line " + std::to_string(lineNumber));
        }
        group.predicates.push_back(std::move(predicate));
    }

    bool countedArgumentsMatch(const LiftedMutexGroup& group, const LiftedMutexPredicate& predicate, const USignature& fact) const {
        for (size_t argumentIndex = 0; argumentIndex < predicate.parameterIndices.size(); ++argumentIndex) {
            const int parameterIndex = predicate.parameterIndices[argumentIndex];
            const LiftedMutexParameter& parameter = group.parameters[parameterIndex];
            if (parameter.kind != MutexParameterKind::COUNTED) continue;
            if (!_htn.getConstantsOfSort(parameter.sortId).count(fact._args[argumentIndex])) return false;

            // A repeated C parameter denotes the same object at every one of
            // its occurrences, but it is local to this predicate grounding.
            for (size_t previousIndex = 0; previousIndex < argumentIndex; ++previousIndex) {
                if (predicate.parameterIndices[previousIndex] == parameterIndex && fact._args[previousIndex] != fact._args[argumentIndex]) return false;
            }
        }
        return true;
    }

    void collectFactsForFixedAssignment(const LiftedMutexGroup& group) {
        std::vector<int> groupFactIds;
        for (const LiftedMutexPredicate& predicate : group.predicates) {
            std::vector<int> fixedArguments(predicate.parameterIndices.size(), -1);
            for (size_t argumentIndex = 0; argumentIndex < predicate.parameterIndices.size(); ++argumentIndex) {
                const LiftedMutexParameter& parameter = group.parameters[predicate.parameterIndices[argumentIndex]];
                if (parameter.kind != MutexParameterKind::COUNTED) fixedArguments[argumentIndex] = parameter.value;
            }

            // Querying the existing fact index replaces a Cartesian product
            // over C parameters and never materializes unreachable facts.
            const BitVec matchingFactIds = _facts.findMatchingPositiveFactIds(predicate.predicateId, fixedArguments);
            for (int factId : matchingFactIds) {
                if (countedArgumentsMatch(group, predicate, _facts.getGroundFact(factId))) groupFactIds.push_back(factId);
            }
        }
        std::sort(groupFactIds.begin(), groupFactIds.end());
        groupFactIds.erase(std::unique(groupFactIds.begin(), groupFactIds.end()), groupFactIds.end());
        if (groupFactIds.size() < 2) return;

        // Store only group indices in the deduplication table. Keeping the
        // complete vectors there would almost double mutex-group memory.
        std::vector<size_t>& sameHashGroupIds = _ground_group_ids_by_hash[IntVecHasher{}(groupFactIds)];
        for (size_t groupId : sameHashGroupIds) {
            if (_ground_groups[groupId] == groupFactIds) return;
        }
        sameHashGroupIds.push_back(_ground_groups.size());
        _ground_groups.push_back(std::move(groupFactIds));
    }

    void enumerateFixedAssignments(LiftedMutexGroup& group, size_t parameterIndex) {
        if (parameterIndex == group.parameters.size()) {
            collectFactsForFixedAssignment(group);
            return;
        }

        LiftedMutexParameter& parameter = group.parameters[parameterIndex];
        if (parameter.kind != MutexParameterKind::FIXED) {
            enumerateFixedAssignments(group, parameterIndex + 1);
            return;
        }

        for (int constant : _htn.getConstantsOfSort(parameter.sortId)) {
            parameter.value = constant;
            enumerateFixedAssignments(group, parameterIndex + 1);
        }
    }

public:
    GroundingContext(HtnInstance& htn, FactAnalysis& facts) : _htn(htn), _facts(facts) {}

    std::vector<std::vector<int>> groundFile(const std::filesystem::path& mutexFile) {
        std::ifstream input(mutexFile);
        if (!input) throw std::runtime_error("Could not open lifted mutex groups: " + mutexFile.string());

        std::string line;
        size_t lineNumber = 0;
        while (std::getline(input, line)) {
            ++lineNumber;
            if (trim(line).empty()) continue;
            LiftedMutexGroup group = parseGroup(line, lineNumber);
            if (!group.usable) continue;
            Log::d("Grounding lifted mutex group %zu.\n", lineNumber);
            enumerateFixedAssignments(group, 0);
        }
        return std::move(_ground_groups);
    }
};

}

std::vector<std::vector<int>> LiftedMutexGroupGrounder::groundFile(const std::filesystem::path& mutexFile, HtnInstance& htn, FactAnalysis& facts) {
    return GroundingContext(htn, facts).groundFile(mutexFile);
}
