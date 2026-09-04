
#include "fact_analysis.h"

#include <fstream>
#include <filesystem>

#include "util/project_utils.h"
#include "util/statistics.h"

FactAnalysis::FactAnalysis(HtnInstance& htn)
        : _htn(htn),
          _init_state(_htn.getInitState()) {
    Statistics& stats = Statistics::getInstance();
    stats.beginTiming(TimingStage::INIT_GROUNDING);
    getGroundFacts(_htn.getParams().isNonzero("optimal"));

    std::vector<USignature> positiveFacts(_ground_pos_facts.begin(), _ground_pos_facts.end());
    std::vector<USignature> exclusiveNegativeFacts;
    for (const USignature& fact : _ground_neg_facts) {
        if (!_ground_pos_facts.count(fact)) {
            exclusiveNegativeFacts.push_back(fact);
        }
    }

    Log::i("Found %zu exclusive negative facts.\n", exclusiveNegativeFacts.size());
    _cutoff_neg_facts = positiveFacts.size();
    _htn.setGroundPosAndNegFacts(positiveFacts, exclusiveNegativeFacts);

    const int numGroundFacts = _htn.getNumPositiveGroundFacts();
    _reachable_pos_facts = BitVec(numGroundFacts);
    _reachable_neg_facts = BitVec(numGroundFacts);
    _init_state_pos = BitVec(numGroundFacts);
    _init_state_neg = BitVec(numGroundFacts);
    _relevant_facts = BitVec(numGroundFacts);
    for (int factId = 0; factId < numGroundFacts; factId++) {
        if (_init_state.count(_htn.getGroundPositiveFact(factId))) {
            _init_state_pos.set(factId);
        } else {
            _init_state_neg.set(factId);
        }
    }

    stats.endTiming(TimingStage::INIT_GROUNDING);
    Log::i("Grounding time: %f\n", stats.getTiming(TimingStage::INIT_GROUNDING));
    resetReachability();
}

std::optional<std::vector<FlatHashSet<int>>> FactAnalysis::computeReachableArgumentDomains(const HtnOp& operation)
{
    const std::vector<int>& args = operation.getArguments();
    const std::vector<int>& sorts = _htn.getSorts(operation.getNameId());
    std::vector<FlatHashSet<int>> domainPerVariable(args.size());
    std::vector<bool> occursInPreconditions(args.size(), false);

    // Check each precondition regarding its valid decodings w.r.t. current state
    struct PreconditionConstraint
    {
        std::vector<int> varIndices;              // indices in op args
        std::vector<std::vector<int>> tuples;     // aligned with varIndices
    };

    std::vector<PreconditionConstraint> constraints;

    // Extra preconditions validate candidates but do not restrict argument domains.
    for (const auto& preSig : operation.getPreconditions())
        {

            // Find mapping from precond args to op args
            std::vector<int> opArgIndices(preSig._usig._args.size(), -1);
            for (size_t preIdx = 0; preIdx < preSig._usig._args.size(); preIdx++)
            {
                const int &arg = preSig._usig._args[preIdx];
                for (size_t i = 0; i < args.size(); i++)
                {
                    if (args[i] == arg)
                    {
                        opArgIndices[preIdx] = i;
                        occursInPreconditions[i] = true;
                        break;
                    }
                }
            }

            PreconditionConstraint constraint;
            std::vector<int> preArgToVarPos(preSig._usig._args.size(), -1);
            FlatHashMap<int, int> varIndexToPos;
            for (size_t preIdx = 0; preIdx < opArgIndices.size(); ++preIdx)
            {
                int opArgIdx = opArgIndices[preIdx];
                if (opArgIdx < 0)
                    continue;
                auto it = varIndexToPos.find(opArgIdx);
                if (it == varIndexToPos.end())
                {
                    int pos = static_cast<int>(constraint.varIndices.size());
                    varIndexToPos[opArgIdx] = pos;
                    constraint.varIndices.push_back(opArgIdx);
                    preArgToVarPos[preIdx] = pos;
                }
                else
                {
                    preArgToVarPos[preIdx] = it->second;
                }
            }

            std::vector<int> preSorts(preSig._usig._args.size());
            for (size_t i = 0; i < preSorts.size(); i++)
            {
                preSorts[i] = opArgIndices[i] >= 0 ? sorts[opArgIndices[i]] : _htn.getSorts(preSig._usig._name_id)[i];
            }

            // Check possible decodings of precondition
            bool any = false;
            bool anyValid = false;

            auto addTuple = [&](const USignature &decUSig) {
                if (constraint.varIndices.empty())
                    return;
                std::vector<int> tuple(constraint.varIndices.size(), -1);
                for (size_t i = 0; i < preArgToVarPos.size(); ++i)
                {
                    int pos = preArgToVarPos[i];
                    if (pos < 0)
                        continue;
                    int val = decUSig._args[i];
                    if (tuple[pos] >= 0 && tuple[pos] != val)
                        return; // same variable appears twice with different values
                    tuple[pos] = val;
                }
                constraint.tuples.push_back(std::move(tuple));
            };

            if (_htn.isEqualityPredicate(preSig._usig._name_id))
            {
                if (!_htn.hasQConstants(preSig._usig) && _htn.isFullyGround(preSig._usig))
                {
                    bool equality_correct = preSig._negated ? preSig._usig._args[0] != preSig._usig._args[1] : preSig._usig._args[0] == preSig._usig._args[1];
                    if (!equality_correct) continue;
                    addTuple(preSig._usig);
                    any = true; anyValid = true;
                }
                else
                {
                    for (const auto &decUSig : _htn.enumerateCandidateDecodings(preSig._usig, preSorts))
                    {
                        any = true;
                        bool equality_correct = preSig._negated ? decUSig._args[0] != decUSig._args[1] : decUSig._args[0] == decUSig._args[1];
                        if (!equality_correct) continue;
                        anyValid = true;
                        addTuple(decUSig);
                    }
                }
            }
            else
            {
                if (!_htn.hasQConstants(preSig._usig) && _htn.isFullyGround(preSig._usig)) {
                    int predId = _htn.getGroundFactId(preSig._usig, preSig._negated);
                    if (predId >= 0 && isReachable(predId, preSig._negated))
                    {
                        addTuple(preSig._usig);
                        any = true; anyValid = true;
                    }
                }
                else
                {
                    BitVec result = _htn.findMatchingGroundFactIds(preSig._usig, preSig._negated, preSorts);
                    for (std::size_t pred_idx : result)
                    {
                        any = true;
                        const USignature &decUSig = _htn.getGroundPositiveFact(pred_idx);
                        // Log::i("___ Decoding %s of precondition %s\n", TOSTR(decUSig), TOSTR(preSig._usig));
                        if (!isReachable(pred_idx, preSig._negated))
                        {
                            // Log::i("___ Discard %s as decoding of precondition %s because it is not reachable\n", TOSTR(decUSig), TOSTR(preSig._usig));
                            continue;
                        }
                        anyValid = true;
                        addTuple(decUSig);
                    }
                }
            }

            if (any && !anyValid)
                return std::nullopt;

            if (!constraint.varIndices.empty())
                constraints.push_back(std::move(constraint));
        }

    // Initialize domains from constraints
    for (const auto &c : constraints)
    {
        if (c.tuples.empty())
            return std::nullopt;
        for (size_t pos = 0; pos < c.varIndices.size(); ++pos)
        {
            int varIdx = c.varIndices[pos];
            for (const auto &t : c.tuples)
                domainPerVariable[varIdx].insert(t[pos]);
        }
    }

    // Propagate constraints until fixpoint
    bool changed = true;
    while (changed)
    {
        changed = false;
        for (const auto &c : constraints)
        {
            for (size_t pos = 0; pos < c.varIndices.size(); ++pos)
            {
                int varIdx = c.varIndices[pos];
                FlatHashSet<int> supported;
                supported.reserve(domainPerVariable[varIdx].size());
                for (const auto &t : c.tuples)
                {
                    bool ok = true;
                    for (size_t other = 0; other < c.varIndices.size(); ++other)
                    {
                        if (other == pos) continue;
                        int otherVarIdx = c.varIndices[other];
                        if (domainPerVariable[otherVarIdx].count(t[other]) == 0)
                        {
                            ok = false;
                            break;
                        }
                    }
                    if (ok)
                        supported.insert(t[pos]);
                }
                if (supported.size() < domainPerVariable[varIdx].size())
                {
                    domainPerVariable[varIdx] = std::move(supported);
                    if (domainPerVariable[varIdx].empty())
                        return std::nullopt;
                    changed = true;
                }
            }
        }
    }

    for (size_t i = 0; i < args.size(); i++)
    {
        if (!occursInPreconditions[i])
            domainPerVariable[i] = _htn.getConstantsOfSort(sorts[i]);
    }

    return domainPerVariable;
}

void FactAnalysis::getGroundFacts(bool getAlsoGroundOps)
{

    std::filesystem::path current_path = getProjectRootDir();

    // Path parser
    // If we need the groundOps, we need to get the same ops than what we parsed when we modified the parser
    std::string pandaExecutable = getAlsoGroundOps ? "pandaPIparser" : "pandaPIparserOriginal";
    std::filesystem::path filesystem_full_path_parser = current_path / "lib" / pandaExecutable;
    std::string full_path_parser = filesystem_full_path_parser.string();

    // Path parser output
    std::filesystem::path filesystem_parser_output = getProblemProcessingDir() / "problem.parsed";
    std::string parser_output = filesystem_parser_output.string();

    std::string commandParser = full_path_parser + " " + _htn.getParams().getDomainFilename() + " " + _htn.getParams().getProblemFilename() + " " + parser_output;

    Log::i("Parsing the domain and problem files with the parser...\n");
    int result = std::system(commandParser.c_str());
    if (result != 0)
    {
        Log::e("Error while parsing the domain and problem files with the parser. Command: %s\n", commandParser.c_str());
        throw std::runtime_error("Error while parsing the domain and problem files with the parser.");
    }
    Log::i("Done !\n");

    // Path grounder
    std::filesystem::path filesystem_full_path_grounder = current_path / "lib" / "pandaPIgrounder";
    std::string full_path_grounder = filesystem_full_path_grounder.string();

    // Path grounder output
    std::filesystem::path filesystem_problem_sas = getProblemProcessingDir() / "problem.sas";
    std::string grounder_output = filesystem_problem_sas.string();

    // Remove the file if exists
    if (std::filesystem::exists(grounder_output))
    {
        std::filesystem::remove(grounder_output);
    }

    // The option --no-literal-pruning disables removal of statically true or false literals.
    // The option --only-write-state-features is used to only write the state features in the file (no ground task or methods are written in the output file)
    // The option --quick-compute-state-features is used to compute more quickly the state features but can produce a less precise result (will only be used if the grounding is too slow)
    // The option --write-full-methods-name is used to write the name and parameters of the methods instead of just the name of the methods in the output file
    Log::i("Grounding the parsed file with the grounder...\n");
    std::string options = "";
    if (!getAlsoGroundOps)
    {
        options = "--no-literal-pruning --only-write-state-features --quick-compute-state-features --quiet";
    }
    else
    {
        options = "--no-literal-pruning --no-abstract-expansion --write-full-methods-name --quiet";
    }
    std::string commandGrounder = full_path_grounder + " " + options + " " + parser_output + " " + grounder_output;
    Log::i("commandGrounder: %s\n", commandGrounder.c_str());
    result = std::system(commandGrounder.c_str());
    if (result != 0)
    {
        Log::e("Error while grounding the parsed file with the grounder. Command: %s\n", commandGrounder.c_str());
        throw std::runtime_error("Error while grounding the parsed file with the grounder.");
    }
    Log::i("Done !\n");

    // Assert that the file exist
    std::ifstream file(grounder_output);
    assert(file.good() || Log::e("File %s does not exist!\n", grounder_output.c_str()));

    // Now, read the file Proprocessing_sas/problem.sas and extract the facts
    Log::i("Extract ground facts from ground file...\n");
    extractGroundFactsFromPandaPiGrounderFile(grounder_output);
    Log::i("Done !\n");
}

void FactAnalysis::extractGroundFactsFromPandaPiGrounderFile(const std::string &filename)
{
    std::ifstream file(filename);
    int lineIdx = 0;
    std::string line;

    // First, read until the line which start with ";; #state features"
    while (std::getline(file, line))
    {
        lineIdx++;
        if (line == ";; #state features")
        {
            break;
        }
    }

    // Skip the next line which contains the number of state features
    std::getline(file, line);
    lineIdx++;

    while (std::getline(file, line))
    {
        lineIdx++;
        if (line.size() == 0)
            break;
        else
        {
            // Each fact is in the form [+-]fact_name\[arg1,arg2,...\]
            bool isPositive = line[0] == '+';
            std::string fact_name = "";
            std::vector<std::string> fact_args;
            int idx = 1; // Ignore the first character, which is + or -
            while (line[idx] != '[')
            {
                fact_name += line[idx];
                idx++;
            }
            idx++; // Skip the '[' character
            while (line[idx] != ']')
            {
                std::string arg = "";
                while (line[idx] != ',' && line[idx] != ']')
                {
                    arg += line[idx];
                    idx++;
                }
                fact_args.push_back(arg);
                if (line[idx] == ',')
                    idx++; // Skip the ',' character
            }

            // Create the fact as a USignature
            std::vector<int> args_pred;
            for (std::string arg_name : fact_args)
            {
                args_pred.push_back(_htn.nameId(arg_name));
            }
            USignature pred_usig(_htn.nameId(fact_name), args_pred);
            if (isPositive)
            {
                _ground_pos_facts.insert(pred_usig);
                // Add it as well as a negative state feature
                _ground_neg_facts.insert(pred_usig);
                Log::d("%d -> %s\n", _ground_pos_facts.size(), TOSTR(pred_usig));
            }
            else
            {
                Log::d("-> not %s\n", TOSTR(pred_usig));
                // Only add it as a negative state feature
                _ground_neg_facts.insert(pred_usig);
                // For now, add it as a positive state feature as well
                // _ground_pos_facts.insert(pred_usig);
            }
        }
    }

    Log::i("There are %d positive state features (which can also be negative) for this problem.\n", _ground_pos_facts.size());
    Log::i("There are %d negative state features for this problem.\n", _ground_neg_facts.size());
}

const std::vector<FlatHashSet<int>> &FactAnalysis::getGroundFactArgumentDomains(const Signature &sig)
{
    // If it is in the cache, return it
    if (sig._negated)
    {
        if (_allowed_domain_per_neg_lift_facts.count(sig._usig._name_id) > 0)
        {
            return _allowed_domain_per_neg_lift_facts[sig._usig._name_id];
        }
    }
    else
    {
        if (_allowed_domain_per_pos_lift_facts.count(sig._usig._name_id) > 0)
        {
            return _allowed_domain_per_pos_lift_facts[sig._usig._name_id];
        }
    }

    const USigSet &preprocessed_facts = sig._negated ? _ground_neg_facts : _ground_pos_facts;

    std::vector<FlatHashSet<int>> domainPerVariable(sig._usig._args.size());

    for (const USignature &pSig : preprocessed_facts)
    {
        if (pSig._name_id != sig._usig._name_id)
            continue;

        // Increate each domain per variable
        for (int i = 0; i < pSig._args.size(); i++)
        {
            domainPerVariable[i].insert(pSig._args[i]);
        }
    }

    if (sig._negated)
    {
        _allowed_domain_per_neg_lift_facts[sig._usig._name_id] = domainPerVariable;
        return _allowed_domain_per_neg_lift_facts[sig._usig._name_id];
    }
    else
    {
        _allowed_domain_per_pos_lift_facts[sig._usig._name_id] = domainPerVariable;
        return _allowed_domain_per_pos_lift_facts[sig._usig._name_id];
    }
}
