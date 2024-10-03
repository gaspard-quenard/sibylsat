
#include "fact_analysis.h"

#include <chrono>
#include <fstream>
#include <filesystem>

#include "util/project_utils.h"

const SigSet& FactAnalysis::getPossibleFactChanges(const USignature& sig, FactInstantiationMode mode, OperationType opType) {
    
    if (opType == UNKNOWN) opType = _htn.isAction(sig) ? ACTION : REDUCTION;
    
    if (opType == ACTION) return _htn.getOpTable().getAction(sig).getEffects();
    if (_fact_changes_cache.count(sig)) return _fact_changes_cache[sig];

    int nameId = sig._name_id;
    
    // Substitution mapping
    std::vector<int> placeholderArgs;
    USignature normSig = _htn.getNormalizedLifted(sig, placeholderArgs);
    Substitution sFromPlaceholder(placeholderArgs, sig._args);

    auto& factChanges = mode == FULL ? _fact_changes : _lifted_fact_changes;
    if (!factChanges.count(nameId)) {
        // Compute fact changes for origSig
        
        NodeHashSet<Signature, SignatureHasher> facts;

        if (_htn.isActionRepetition(nameId)) {
            // Special case: Action repetition
            Action a = _htn.getActionFromRepetition(nameId);
            a = a.substitute(Substitution(a.getArguments(), placeholderArgs));
            for (const Signature& eff : a.getEffects()) {
                facts.insert(eff);
            }
        } else {
            // Normal traversal to find possible fact changes
            _traversal.traverse(normSig.substitute(Substitution(normSig._args, placeholderArgs)), 
            NetworkTraversal::TRAVERSE_PREORDER,
            [&](const USignature& nodeSig, int depth) { // NOLINT
                if (_htn.isAction(nodeSig)) {
                    
                    Action a;
                    if (_htn.isActionRepetition(nameId)) {
                        // Special case: Action repetition
                        a = _htn.toAction(_htn.getActionNameFromRepetition(nameId), nodeSig._args);
                    } else {
                        a = _htn.toAction(nodeSig._name_id, nodeSig._args);
                    }
                    for (const Signature& eff : a.getEffects()) facts.insert(eff);
                
                } else if (_htn.isReductionPrimitivizable(nodeSig._name_id)) {

                    const Action& op = _htn.getReductionPrimitivization(nodeSig._name_id);
                    Action action = op.substitute(Substitution(op.getArguments(), nodeSig._args));
                    for (const Signature& eff : action.getEffects()) facts.insert(eff);
                }
            });
        }

        // Convert result to vector
        SigSet& liftedResult = _lifted_fact_changes[nameId];
        SigSet& result = _fact_changes[nameId];
        bool restrictSortInFA = _htn.getParams().isNonzero("restrictSortsInFA");
        bool isInitReduction = sig._name_id == _htn.getInitReduction().getNameId();
        bool getReducedConstantsPerSort = _preprocess_facts && opType == REDUCTION && sig._name_id != _htn.getInitReduction().getNameId();
        for (const Signature& fact : facts) {
            liftedResult.insert(fact);
            std::vector<int> trueSortsFact;
            if (restrictSortInFA && opType == REDUCTION && !isInitReduction) {
                trueSortsFact = _htn.getSortsParamsFromSigForFA(fact);
            }
            if (fact._usig._args.empty()) {
                if (opType == REDUCTION && _preprocess_facts && !isInGroundFacts(fact._usig, fact._negated)) {
                    continue;
                }
                result.insert(fact);
            }
            // else for (const USignature& sigGround : ArgIterator::getFullInstantiation(fact._usig, _htn)) {
            else for (const USignature& sigGround : ArgIterator::getFullInstantiation(fact._usig, _htn, trueSortsFact, getReducedConstantsPerSort ? getMaxAllowedDomainForLiftFactParams(fact) : std::vector<FlatHashSet<int>>())) {
                if (_preprocess_facts && opType == REDUCTION) {

                    if (_htn.isFullyGround(sigGround)) {
                        if (!isInGroundFacts(sigGround, fact._negated)) {
                            // Log::i("Discard %s as possible eff because it is not in the preprocessed facts\n", TOSTR(sigGround));
                            continue;
                        }
                    } 
                    else {
                        // Check if at least one decoding is correct
                        bool atLeastOneDecodingIsCorrect = false;
                        std::vector<int> sortsMethod = _htn.getSorts(sig._name_id);

                        std::vector<int> sigSorts(sigGround._args.size());
                        for (size_t sigIdx = 0; sigIdx < sigSorts.size(); sigIdx++) {
                            for (size_t opIdx = 0; opIdx < sig._args.size(); opIdx++) {
                                if (sigGround._args[sigIdx] < 0) {
                                    // Found
                                    sigSorts[sigIdx] = sortsMethod[-sigGround._args[sigIdx] - 1];
                                    break;
                                }
                            }
                        }

                        // Log::i("Sorts of the condition: %s\n", TOSTR(sigSorts));
                        
                        auto eligibleArgs = _htn.getEligibleArgs(sigGround, sigSorts);
                        // Log::i("Eleigible args: %s\n", TOSTR(eligibleArgs));

                        for (const USignature& decFactAbs : _htn.decodeObjects(sigGround, eligibleArgs)) {

                            // Log::i("Possible decoding: %s\n", TOSTR(decFactAbs));
                            if (isInGroundFacts(decFactAbs, fact._negated)) {
                                atLeastOneDecodingIsCorrect = true;
                                break;
                            }
                            
                        }

                        if (!atLeastOneDecodingIsCorrect) {
                            Log::d("Discard %s as possible pseudo eff because no decoding is correct\n", TOSTR(sigGround));
                            continue;
                        }
                    }
                }
                
                result.emplace(sigGround, fact._negated);
            }
        }
    }

    // Get fact changes, substitute arguments
    _fact_changes_cache[sig] = factChanges.at(nameId);
    for (Signature& s : _fact_changes_cache[sig]) {
        s.apply(sFromPlaceholder);
    }
    return _fact_changes_cache[sig];
}

void FactAnalysis::eraseCachedPossibleFactChanges(const USignature& sig) {
    _fact_changes_cache.erase(sig);
}


std::vector<FlatHashSet<int>> FactAnalysis::getReducedArgumentDomains(const HtnOp& op) {

    const std::vector<int>& args = op.getArguments();
    const std::vector<int>& sorts = _htn.getSorts(op.getNameId());
    std::vector<FlatHashSet<int>> domainPerVariable(args.size());
    std::vector<bool> occursInPreconditions(args.size(), false);

    // Check each precondition regarding its valid decodings w.r.t. current state
    //const SigSet* preSets[2] = {&op.getPreconditions(), &op.getExtraPreconditions()};
    const SigSet* preSets[1] = {&op.getPreconditions()};
    for (const auto& preSet : preSets) for (const auto& preSig : *preSet) {

        // Find mapping from precond args to op args
        std::vector<int> opArgIndices(preSig._usig._args.size(), -1);
        for (size_t preIdx = 0; preIdx < preSig._usig._args.size(); preIdx++) {
            const int& arg = preSig._usig._args[preIdx];
            for (size_t i = 0; i < args.size(); i++) {
                if (args[i] == arg) {
                    opArgIndices[preIdx] = i;
                    occursInPreconditions[i] = true;
                    break;
                }
            }
        }

        if (!_htn.hasQConstants(preSig._usig) && _htn.isFullyGround(preSig._usig)) {
            // Check base condition; if unsatisfied, discard op 
            if (!isReachable(preSig)) return std::vector<FlatHashSet<int>>();
            // Add constants to respective argument domains
            for (size_t i = 0; i < preSig._usig._args.size(); i++) {
                domainPerVariable[opArgIndices[i]].insert(preSig._usig._args[i]);
            }
            continue;
        }

        // Compute sorts of the condition's args w.r.t. op signature
        std::vector<int> preSorts(preSig._usig._args.size());
        for (size_t i = 0; i < preSorts.size(); i++) {
            preSorts[i] = sorts[opArgIndices[i]];
        }

        // Check possible decodings of precondition
        bool any = false;
        bool anyValid = false;
        for (const auto& decUSig : _htn.decodeObjects(preSig._usig, _htn.getEligibleArgs(preSig._usig, preSorts))) {
            any = true;
            assert(_htn.isFullyGround(decUSig));

            // Valid?
            if (!isReachable(decUSig, preSig._negated)) continue;
            
            // Valid precondition decoding found: Increase domain of concerned variables
            anyValid = true;
            for (size_t i = 0; i < opArgIndices.size(); i++) {
                int opArgIdx = opArgIndices[i];
                if (opArgIdx >= 0) {
                    domainPerVariable[opArgIdx].insert(decUSig._args[i]);
                }
            }
        }
        if (any && !anyValid) return std::vector<FlatHashSet<int>>();
    }

    for (size_t i = 0; i < args.size(); i++) {
        if (!occursInPreconditions[i]) domainPerVariable[i] = _htn.getConstantsOfSort(sorts[i]);
    }

    return domainPerVariable;
}

FactFrame FactAnalysis::getFactFrame(const USignature& sig, USigSet& currentOps) {
    static USigSet EMPTY_USIG_SET;

    //Log::d("GET_FACT_FRAME %s\n", TOSTR(sig));

    int nameId = sig._name_id;
    if (!_fact_frames.count(nameId)) {

        FactFrame result;

        std::vector<int> newArgs(sig._args.size());
        for (size_t i = 0; i < sig._args.size(); i++) {
            newArgs[i] = _htn.nameId("c" + std::to_string(i));
        }
        USignature op(sig._name_id, std::move(newArgs));
        result.sig = op;

        if (_htn.isAction(op)) {

            // Action
            const Action& a = _htn.toAction(op._name_id, op._args);
            result.preconditions = a.getPreconditions();
            result.effects = a.getEffects();

        } else if (currentOps.count(op)) {

            // Handle recursive call of same reduction: Conservatively add preconditions and effects
            // without recursing on subtasks
            const Reduction& r = _htn.toReduction(op._name_id, op._args);
            result.preconditions = r.getPreconditions();
            result.effects = getPossibleFactChanges(r.getSignature(), LIFTED);
            //Log::d("RECURSIVE_FACT_FRAME %s\n", TOSTR(result.effects));

            _htn.addRecursiveMethod(op._name_id);

        } else {
            currentOps.insert(op);
            
            const Reduction& r = _htn.toReduction(op._name_id, op._args);
            result.preconditions.insert(r.getPreconditions().begin(), r.getPreconditions().end());
            
            // For each subtask position ("offset")
            for (size_t offset = 0; offset < r.getSubtasks().size(); offset++) {
                
                FactFrame frameOfOffset;
                std::vector<USignature> children;
                _traversal.getPossibleChildren(r.getSubtasks(), offset, children);
                bool firstChild = true;

                // Assemble fact frame of this offset by iterating over all possible children at the offset
                for (const auto& child : children) {

                    // Assemble unified argument names
                    std::vector<int> newChildArgs(child._args);
                    for (size_t i = 0; i < child._args.size(); i++) {
                        if (_htn.isVariable(child._args[i])) newChildArgs[i] = _htn.nameId("??_");
                    }

                    // Recursively get child frame of the child
                    FactFrame childFrame = getFactFrame(USignature(child._name_id, std::move(newChildArgs)), currentOps);
                    
                    if (firstChild) {
                        // Add all preconditions of child that are not yet part of the parent's effects
                        for (const auto& pre : childFrame.preconditions) {
                            bool isNew = true;
                            for (const auto& eff : result.effects) {
                                if (_htn.isUnifiable(eff, pre) || _htn.isUnifiable(pre, eff)) {
                                    isNew = false;
                                    //Log::d("FACT_FRAME Precondition %s absorbed by effect %s of %s\n", TOSTR(pre), TOSTR(eff), TOSTR(child));
                                    break;
                                } 
                            }
                            if (isNew) frameOfOffset.preconditions.insert(pre);
                        }
                        firstChild = false;
                    } else {
                        // Intersect preconditions
                        SigSet newPrec;
                        for (auto& pre : childFrame.preconditions) {
                            if (frameOfOffset.preconditions.count(pre)) newPrec.insert(pre);
                        }
                        frameOfOffset.preconditions = std::move(newPrec);
                    }

                    // Add all of the child's effects to the parent's effects
                    frameOfOffset.effects.insert(childFrame.effects.begin(), childFrame.effects.end());
                }

                // Write into parent's fact frame
                result.preconditions.insert(frameOfOffset.preconditions.begin(), frameOfOffset.preconditions.end());
                result.effects.insert(frameOfOffset.effects.begin(), frameOfOffset.effects.end());
            }

        }

        currentOps.erase(sig);
        _fact_frames[nameId] = std::move(result);

        //Log::d("FACT_FRAME %s\n", TOSTR(_fact_frames[nameId]));
    }

    const FactFrame& f = _fact_frames[nameId];
    return f.substitute(Substitution(f.sig._args, sig._args));
}

void FactAnalysis::getGroundFacts() {

    auto start = std::chrono::high_resolution_clock::now();

    std::filesystem::path current_path = getProjectRootDir();

    // Path parser
    std::filesystem::path filesystem_full_path_parser = current_path / "lib" / "pandaPIparserOriginal";
    std::string full_path_parser = filesystem_full_path_parser.string();

    // Path parser output
    std::filesystem::path filesystem_parser_output = current_path / "problem.parsed";
    std::string parser_output = filesystem_parser_output.string();

    std::string commandParser = full_path_parser + " " + _htn.getParams().getDomainFilename() + " " + _htn.getParams().getProblemFilename() + " " + parser_output;

    Log::i("Parsing the domain and problem files with the parser...\n");
    std::system(commandParser.c_str());
    Log::i("Done !\n");


    // Path grounder 
    std::filesystem::path filesystem_full_path_grounder = current_path / "lib" / "pandaPIgrounder";
    std::string full_path_grounder = filesystem_full_path_grounder.string();

    // Path grounder output
    std::filesystem::path filesystem_problem_sas = current_path / "problem.sas";
    std::string grounder_output = filesystem_problem_sas.string();

    // Remove the file if exists
    if (std::filesystem::exists(grounder_output)) {
        std::filesystem::remove(grounder_output);
    }


    // The option --only-write-state-features is used to only write the state features in the file (no ground task or methods are written in the output file)
    // The option --quick-compute-state-features is used to compute more quickly the state features but can produce a less precise result (will only be used if the grounding is too slow)
    Log::i("Grounding the parsed file with the grounder...\n");
    std::string command2 = full_path_grounder + " --no-literal-pruning --only-write-state-features --quick-compute-state-features --quiet " + parser_output + " " + grounder_output;
    // Log::i("Command2: %s\n", command2.c_str());
    std::system(command2.c_str());
    Log::i("Done !\n");


    // Assert that the file exist
    std::ifstream file(grounder_output);
    assert(file.good() || Log::e("File %s does not exist!\n", grounder_output.c_str()));

    // Now, read the file Proprocessing_sas/problem.sas and extract the facts
    Log::i("Extract ground facts from ground file...\n");
    extractGroundFactsFromPandaPiGrounderFile(grounder_output);
    Log::i("Done !\n");

    auto end = std::chrono::high_resolution_clock::now();
    _time_grounding_facts = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

    Log::i("Grounding facts took %lld ms\n", _time_grounding_facts);
}

void FactAnalysis::extractGroundFactsFromPandaPiGrounderFile(const std::string& filename) {
    std::ifstream file(filename);
    int lineIdx = 0;
    std::string line;

    // First, read until the line which start with ";; #state features"
    while (std::getline(file, line)) {
        lineIdx++;
        if (line == ";; #state features") {
            break;
        }
    }

    // Skip the next line which contains the number of state features
    std::getline(file, line);
    lineIdx++;


    while (std::getline(file, line)) {
        lineIdx++;
        if (line.size() == 0) break;
        else {
            // Each fact is in the form [+-]fact_name\[arg1,arg2,...\]
            bool isPositive = line[0] == '+';
            std::string fact_name = "";
            std::vector<std::string> fact_args;
            int idx = 1; // Ignore the first character, which is + or -
            while (line[idx] != '[') {
                fact_name += line[idx];
                idx++;
            }
            idx++; // Skip the '[' character
            while (line[idx] != ']') {
                std::string arg = "";
                while (line[idx] != ',' && line[idx] != ']') {
                    arg += line[idx];
                    idx++;
                }
                fact_args.push_back(arg);
                if (line[idx] == ',') idx++; // Skip the ',' character
            }

            // Create the fact as a USignature
            std::vector<int> args_pred;
            for (std::string arg_name: fact_args) {
                args_pred.push_back(_htn.nameId(arg_name));
            }
            USignature pred_usig(_htn.nameId(fact_name), args_pred);
            if (isPositive) {
                _ground_pos_facts.insert(pred_usig);
                // Add it as well as a negative state feature
                _ground_neg_facts.insert(pred_usig);
                Log::d("%d -> %s\n", _ground_pos_facts.size(), TOSTR(pred_usig));
            } else {
                Log::d("-> not %s\n", TOSTR(pred_usig));
                // Only add it as a negative state feature
                _ground_neg_facts.insert(pred_usig);
            }
        }
    }

    Log::i("There are %d positive state features (which can also be negative) for this problem.\n", _ground_pos_facts.size());
    Log::i("There are %d negative state features for this problem.\n", _ground_neg_facts.size());
}

const std::vector<FlatHashSet<int>>& FactAnalysis::getMaxAllowedDomainForLiftFactParams(const Signature& sig) {
    // If it is in the cache, return it
    if (sig._negated) {
        if (_allowed_domain_per_neg_lift_facts.count(sig._usig._name_id) > 0) {
            return _allowed_domain_per_neg_lift_facts[sig._usig._name_id];
        }
    } else {
        if (_allowed_domain_per_pos_lift_facts.count(sig._usig._name_id) > 0) {
            return _allowed_domain_per_pos_lift_facts[sig._usig._name_id];
        }
    }


    const USigSet& preprocessed_facts = sig._negated ? _ground_neg_facts : _ground_pos_facts;


    std::vector<FlatHashSet<int>> domainPerVariable(sig._usig._args.size());

    for (const USignature& pSig: preprocessed_facts) {
        if (pSig._name_id != sig._usig._name_id) continue;


        // Increate each domain per variable
        for (int i = 0; i < pSig._args.size(); i++) {
            domainPerVariable[i].insert(pSig._args[i]);
        }
    }

    if (sig._negated) {
        _allowed_domain_per_neg_lift_facts[sig._usig._name_id] = domainPerVariable;
        return _allowed_domain_per_neg_lift_facts[sig._usig._name_id];
    } else {
        _allowed_domain_per_pos_lift_facts[sig._usig._name_id] = domainPerVariable;
        return _allowed_domain_per_pos_lift_facts[sig._usig._name_id];
    }
}

