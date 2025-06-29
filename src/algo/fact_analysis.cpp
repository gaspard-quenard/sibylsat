
#include "fact_analysis.h"

#include <fstream>
#include <filesystem>

#include "util/project_utils.h"

const SigSet &FactAnalysis::getPossibleFactChanges(const USignature &sig, FactInstantiationMode mode, OperationType opType)
{

    if (opType == UNKNOWN)
        opType = _htn.isAction(sig) ? ACTION : REDUCTION;

    if (opType == ACTION)
        return _htn.getOpTable().getAction(sig).getEffects();
    if (_fact_changes_cache.count(sig))
        return _fact_changes_cache[sig];

    int nameId = sig._name_id;

    // Substitution mapping
    std::vector<int> placeholderArgs;
    USignature normSig = _htn.getNormalizedLifted(sig, placeholderArgs);
    Substitution sFromPlaceholder(placeholderArgs, sig._args);

    auto &factChanges = mode == FULL ? _fact_changes : _lifted_fact_changes;
    if (!factChanges.count(nameId))
    {
        // _stats.beginTiming(TimingStage::COMPUTE_PFC);
        // Compute fact changes for origSig

        NodeHashSet<Signature, SignatureHasher> facts;

        if (_htn.isActionRepetition(nameId))
        {
            // Special case: Action repetition
            Action a = _htn.getActionFromRepetition(nameId);
            a = a.substitute(Substitution(a.getArguments(), placeholderArgs));
            for (const Signature &eff : a.getEffects())
            {
                facts.insert(eff);
            }
        }
        else
        {
            // Normal traversal to find possible fact changes
            _traversal.traverse(normSig.substitute(Substitution(normSig._args, placeholderArgs)),
                                NetworkTraversal::TRAVERSE_PREORDER,
                                [&](const USignature &nodeSig, int depth) { // NOLINT
                                    if (_htn.isAction(nodeSig))
                                    {

                                        Action a;
                                        if (_htn.isActionRepetition(nameId))
                                        {
                                            // Special case: Action repetition
                                            a = _htn.toAction(_htn.getActionNameFromRepetition(nameId), nodeSig._args);
                                        }
                                        else
                                        {
                                            a = _htn.toAction(nodeSig._name_id, nodeSig._args);
                                        }
                                        for (const Signature &eff : a.getEffects())
                                            facts.insert(eff);
                                    }
                                    else if (_htn.isReductionPrimitivizable(nodeSig._name_id))
                                    {

                                        const Action &op = _htn.getReductionPrimitivization(nodeSig._name_id);
                                        Action action = op.substitute(Substitution(op.getArguments(), nodeSig._args));
                                        for (const Signature &eff : action.getEffects())
                                            facts.insert(eff);
                                    }
                                });
        }

        // Convert result to vector
        SigSet &liftedResult = _lifted_fact_changes[nameId];

        Log::d("Lifted Fact changes for %s:\n", TOSTR(normSig));
        for (const Signature &fact : facts)
        {
            Log::d("  %s\n", TOSTR(fact));
            liftedResult.insert(fact);
        }

        removeDuplicatesInLiftedFactChanges(nameId);

        SigSet &result = _fact_changes[nameId];
        bool restrictSortInFA = _htn.getParams().isNonzero("restrictSortsInFA");
        bool isInitReduction = sig._name_id == _htn.getInitReduction().getNameId();
        bool getReducedConstantsPerSort = _preprocess_facts && !isInitReduction;
        for (const Signature &fact : liftedResult)
        {

            bool pseudo_params = std::ranges::any_of(fact._usig._args, [](int arg)
                                                     { return arg < 0; });

            std::vector<int> trueSortsFact;
            if (restrictSortInFA && !isInitReduction)
            {
                trueSortsFact = _htn.getSortsParamsFromSigForFA(fact._usig);
            }
            if (fact._usig._args.empty())
            {
                if (_preprocess_facts && !isInGroundFacts(fact._usig, fact._negated))
                {
                    continue;
                }
                result.insert(fact);
            }
            // else for (const USignature& sigGround : ArgIterator::getFullInstantiation(fact._usig, _htn)) {
            else
                for (const USignature &sigGround : ArgIterator::getFullInstantiation(fact._usig, _htn, trueSortsFact, getReducedConstantsPerSort ? getMaxAllowedDomainForLiftFactParams(fact) : std::vector<FlatHashSet<int>>()))
                {

                    // Log::i("*** Decoding of %s: %s\n", TOSTR(fact._usig), TOSTR(sigGround));
                    if (_preprocess_facts)
                    {

                        if (_htn.isFullyGround(sigGround))
                        {
                            if (!isInGroundFacts(sigGround, fact._negated))
                            {
                                // Log::i("Discard %s as possible eff because it is not in the preprocessed facts\n", TOSTR(sigGround));
                                continue;
                            }
                        }
                        else
                        {
                            // Check if at least one decoding is correct
                            bool atLeastOneDecodingIsCorrect = false;
                            std::vector<int> sortsMethod = _htn.getSorts(sig._name_id);

                            std::vector<int> sigSorts(sigGround._args.size());
                            for (size_t sigIdx = 0; sigIdx < sigSorts.size(); sigIdx++)
                            {
                                for (size_t opIdx = 0; opIdx < sig._args.size(); opIdx++)
                                {
                                    if (sigGround._args[sigIdx] < 0)
                                    {
                                        // Found
                                        sigSorts[sigIdx] = sortsMethod[-sigGround._args[sigIdx] - 1];
                                        break;
                                    }
                                }
                            }

                            // Log::i("Sorts of the condition: %s\n", TOSTR(sigSorts));

                            auto eligibleArgs = _htn.getEligibleArgs(sigGround, sigSorts);
                            // Log::i("Eleigible args: %s\n", TOSTR(eligibleArgs));

                            for (const USignature &decFactAbs : _htn.decodeObjects(sigGround, eligibleArgs))
                            {

                                // Log::i("Possible decoding: %s\n", TOSTR(decFactAbs));
                                if (isInGroundFacts(decFactAbs, fact._negated))
                                {
                                    atLeastOneDecodingIsCorrect = true;
                                    break;
                                }
                            }

                            // Log::i("Sorts of the condition: %s\n", TOSTR(sigSorts));
                            // BitVec result = ArgIterator2::getFullInstantiation2(sigGround, fact._negated, _htn, sigSorts);
                            // Log::i("__ Possible decodings using bit vec\n");
                            // for (std::size_t idx : result)
                            // {
                            // const USignature &decFactAbs = _htn.getGroundPositiveFact(idx);
                            // Log::i("___ Possible decoding: %s\n", TOSTR(decFactAbs));
                            // }
                            // if (result.none())
                            // {
                            //     Log::d("Discard %s as possible pseudo eff because no decoding is correct\n", TOSTR(sigGround));
                            //     continue;
                            // }

                            if (!atLeastOneDecodingIsCorrect)
                            {
                                Log::d("Discard %s as possible pseudo eff because no decoding is correct\n", TOSTR(sigGround));
                                continue;
                            }
                        }
                    }

                    // Log::i("*** Adding %s as possible eff\n", TOSTR(sigGround));
                    result.emplace(sigGround, fact._negated);

                    if (pseudo_params)
                        _fact_change_pseudo_facts[nameId].emplace(sigGround, fact._negated);
                }
            if (!pseudo_params)
            {
                // Initialize the BitVec if not exists for this nameId
                if (!_fact_changes_ground_pos_bitvec.count(nameId))
                {
                    _fact_changes_ground_pos_bitvec[nameId] = BitVec(_htn.getNumPositiveGroundFacts());
                    _fact_changes_ground_neg_bitvec[nameId] = BitVec(_htn.getNumPositiveGroundFacts());
                }

                BitVec &fact_change_ground = fact._negated ? _fact_changes_ground_neg_bitvec[nameId] : _fact_changes_ground_pos_bitvec[nameId];

                if (_htn.isFullyGround(fact._usig)) {
                    int predId = _htn.getGroundFactId(fact._usig, fact._negated);
                    if (predId >= 0) fact_change_ground.set(predId);
                } else {


                // } else {
                // Log::i("Get all ground instantiations of %s for %s (%d)\n", TOSTR(fact._usig), TOSTR(sig), nameId);
                // Log::i("Sorts of the fact: %s\n", isInitReduction ? TOSTR(_htn.getSorts(fact._usig._name_id)) : TOSTR(trueSortsFact));
                    BitVec result = ArgIterator2::getFullInstantiation2(fact._usig, fact._negated, _htn, isInitReduction ? _htn.getSorts(fact._usig._name_id) : trueSortsFact);
                // for (std::size_t idx : result)
                // {
                    // const USignature &sigGround = _htn.getGroundPositiveFact(idx);
                    // Log::i("___ Adding %s as possible eff\n", TOSTR(sigGround));
                // }
                    fact_change_ground.or_with(result);
                // Print the fact change ground for debugging
                // Log::i("+++ Possible ground fact changes for %s (%d):\n", TOSTR(sig), nameId);
                // for (size_t factId : fact_change_ground) {
                //     const USignature &fact = _htn.getGroundPositiveFact(factId);
                //     Log::i("Possible fact change: %s\n", TOSTR(fact));
                // }
                }
            }
        }
        // _stats.endTiming(TimingStage::COMPUTE_PFC);
    }

    // Get fact changes, substitute arguments
    const SigSet &src = factChanges.at(nameId);

    // Print all fact changes for debugging
    // Log::i("Fact changes for %s (%d):\n", TOSTR(sig), nameId);
    // for (const Signature &fact : _fact_changes[nameId])
    // {
    //     Log::i("  %s\n", TOSTR(fact));
    // }

    SigSet subst;
    subst.reserve(src.size());

    for (const Signature &s : src)
    {
        Signature tmp = s;
        tmp.apply(sFromPlaceholder);
        // if (!_htn.hasQConstants(tmp._usig) && !_htn.isEqualityPredicate(tmp._usig._name_id) && !isInGroundFacts(tmp._usig, tmp._negated)) continue;
        subst.insert(std::move(tmp));
    }

    // Put the finished set in the cache
    auto &dst = _fact_changes_cache[sig];
    dst = std::move(subst);

    return dst;
}

void FactAnalysis::removeDuplicatesInLiftedFactChanges(int nameId)
{
    // _stats.beginTiming(TimingStage::CLEAN_PFC);

    SigSet &liftedResult = _lifted_fact_changes[nameId];

    // Log::i("Removing duplicates in lifted fact changes for %d\n", nameId);
    // Log::i("Current lifted fact changes:\n");
    // for (const Signature &fact : liftedResult)
    // {
    //     Log::i("  %s\n", TOSTR(fact));
    // }

    // Iterate to remove in place
    for (auto it = liftedResult.begin(); it != liftedResult.end();)
    {
        const Signature &fact = *it;
        // Check if there is another fact that is a superset of this fact
        bool isSuperset = false;
        for (const Signature &otherFact : liftedResult)
        {
            if (otherFact == fact || fact._negated != otherFact._negated)
                continue; // Skip self or different negation
            if (isLiftedFactSuperset(/*fact_to_test=*/fact._usig, /*possible_superset=*/otherFact._usig))
            {
                isSuperset = true;
                Log::d("Found superset %s for lifted fact %s\n", TOSTR(otherFact._usig), TOSTR(fact._usig));
                break;
            }
        }
        if (isSuperset)
        {
            // Log::i("Removing %s as it is a superset of another lifted effect\n", TOSTR(fact._usig));
            it = liftedResult.erase(it);
        }
        else
        {
            ++it;
        }
    }

    // Log::i("Lifted fact changes after removing duplicates:\n");
    // for (const Signature &fact : liftedResult)
    // {
    //     Log::i("  %s\n", TOSTR(fact));
    // }
    // _stats.endTiming(TimingStage::CLEAN_PFC);
}

bool FactAnalysis::isLiftedFactSuperset(const USignature &liftedFact, const USignature &possibleSuperset)
{
    if (liftedFact._name_id != possibleSuperset._name_id)
        return false; // Different fact names cannot be supersets

    std::vector<int> liftedSort = _htn.getSortsParamsFromSigForFA(liftedFact);
    std::vector<int> possibleSupersetSort = _htn.getSortsParamsFromSigForFA(possibleSuperset);

    // Log::i("Sorting lifted fact %s: %s\n", TOSTR(liftedFact), TOSTR(liftedSort));
    // Log::i("Sorting possible superset %s: %s\n", TOSTR(possibleSuperset), TOSTR(possibleSupersetSort));
    
    bool isSuperset = true;
    for (int i = 0; i < liftedFact._args.size(); ++i)
    {
        int liftedArg = liftedFact._args[i];
        int possibleSupersetArg = possibleSuperset._args[i];

        bool liftedArgIsAnyVariable = Names::to_string(liftedArg).back() == '_';
        bool possibleSupersetArgIsAnyVariable = Names::to_string(possibleSupersetArg).back() == '_';

        // Same arg, so continue
        if (liftedArg == possibleSupersetArg)
            continue;

        // If not equal, the second fact must be a superset of the first one
        if (!possibleSupersetArgIsAnyVariable) {
            isSuperset = false;
            break;
        }

        // If same sort, then it is ok
        if (liftedSort[i] == possibleSupersetSort[i])
            continue;

        // The difficult case here, if not the same sort, then the possible superset must be a oversort of the sort of the lifted fact for this parameter
        bool isOversort = false;
        // Get the constant of the first sort
        FlatHashSet<int> constantsOfLiftedSort = _htn.getConstantsOfSort(liftedSort[i]);
        FlatHashSet<int> constantsOfPossibleSupersetSort = _htn.getConstantsOfSort(possibleSupersetSort[i]);
        // OverSort if all constants of the lifted sort are also in the possible superset sort
        for (int liftedConstant : constantsOfLiftedSort)
        {
            if (constantsOfPossibleSupersetSort.count(liftedConstant) == 0)
            {
                isOversort = false;
                break;
            }
            isOversort = true;
        }
        if (!isOversort)
        {
            isSuperset = false;
            break;
        }
    
    }
    return isSuperset;
}

const BitVec &FactAnalysis::getPossibleGroundFactChanges(const USignature &sig, bool negated, FactInstantiationMode mode, OperationType opType)
{
    if (opType == UNKNOWN)
        opType = _htn.isAction(sig) ? ACTION : REDUCTION;

    if (opType == ACTION)
        return _empty;

    if (!_fact_changes_ground_pos_bitvec.count(sig._name_id))
    {
        // If not exists, compute the fact changes
        getPossibleFactChanges(sig, mode, opType);
    }

    if (negated)
        return _fact_changes_ground_neg_bitvec[sig._name_id];
    else
    {
        // Print all the fact to debug
        // Log::i("== Fact changes for %s (%d):\n", TOSTR(sig), sig._name_id);
        for (size_t factId : _fact_changes_ground_pos_bitvec[sig._name_id])
        {
            const USignature &fact = _htn.getGroundPositiveFact(factId);
            // Log::i("Possible fact change: %s\n", TOSTR(fact));
        }
        return _fact_changes_ground_pos_bitvec[sig._name_id];
    }
}

const SigSet &FactAnalysis::getPossiblePseudoGroundFactChanges(const USignature &sig, FactInstantiationMode mode, OperationType opType)
{
    if (opType == UNKNOWN)
        opType = _htn.isAction(sig) ? ACTION : REDUCTION;

    if (opType == ACTION)
        return _htn.getOpTable().getAction(sig).getEffects();


    if (_pseudo_fact_changes_cache.count(sig))
        return _pseudo_fact_changes_cache[sig];

    int nameId = sig._name_id;

    // Substitution mapping
    std::vector<int> placeholderArgs;
    USignature normSig = _htn.getNormalizedLifted(sig, placeholderArgs);
    Substitution sFromPlaceholder(placeholderArgs, sig._args);

    auto &factChanges = mode == FULL ? _fact_changes : _lifted_fact_changes;

    const SigSet &src = _fact_change_pseudo_facts[nameId];

    SigSet subst;
    subst.reserve(src.size());

    for (const Signature &s : src)
    {
        Signature tmp = s;
        tmp.apply(sFromPlaceholder);
        subst.insert(std::move(tmp));
    }

    // Put the finished set in the cache
    auto &dst = _pseudo_fact_changes_cache[sig];
    dst = std::move(subst);

    return dst;
}

void FactAnalysis::eraseCachedPossibleFactChanges(const USignature &sig)
{
    _fact_changes_cache.erase(sig);
}

std::vector<FlatHashSet<int>> FactAnalysis::getReducedArgumentDomains(const HtnOp &op)
{

    const std::vector<int> &args = op.getArguments();
    const std::vector<int> &sorts = _htn.getSorts(op.getNameId());
    std::vector<FlatHashSet<int>> domainPerVariable(args.size());
    std::vector<bool> occursInPreconditions(args.size(), false);

    // Check each precondition regarding its valid decodings w.r.t. current state
    // const SigSet* preSets[2] = {&op.getPreconditions(), &op.getExtraPreconditions()};
    const SigSet *preSets[1] = {&op.getPreconditions()};
    for (const auto &preSet : preSets)
        for (const auto &preSig : *preSet)
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

            // if (!_htn.hasQConstants(preSig._usig) && _htn.isFullyGround(preSig._usig))
            // {
            //     // Check base condition; if unsatisfied, discard op
            //     if (!isReachable(preSig))
            //         return std::vector<FlatHashSet<int>>();
            //     // Add constants to respective argument domains
            //     for (size_t i = 0; i < preSig._usig._args.size(); i++)
            //     {
            //         domainPerVariable[opArgIndices[i]].insert(preSig._usig._args[i]);
            //     }
            //     continue;
            // }

            // Compute sorts of the condition's args w.r.t. op signature
            std::vector<int> preSorts(preSig._usig._args.size());
            for (size_t i = 0; i < preSorts.size(); i++)
            {
                preSorts[i] = sorts[opArgIndices[i]];
            }

            // Check possible decodings of precondition
            bool any = false;
            bool anyValid = false;
            // for (const auto &decUSig : _htn.decodeObjects(preSig._usig, _htn.getEligibleArgs(preSig._usig, preSorts)))
            // {
            //     any = true;
            //     assert(_htn.isFullyGround(decUSig));

            //     Log::i("*** Decoding %s of precondition %s\n", TOSTR(decUSig), TOSTR(preSig._usig));

            //     // Valid?
            //     if (!isReachable(decUSig, preSig._negated))
            //     {
            //         Log::i("*** Discard %s as decoding of precondition %s because it is not reachable\n", TOSTR(decUSig), TOSTR(preSig._usig));
            //         continue;
            //     }

            //     // Valid precondition decoding found: Increase domain of concerned variables
            //     anyValid = true;
            //     for (size_t i = 0; i < opArgIndices.size(); i++)
            //     {
            //         int opArgIdx = opArgIndices[i];
            //         if (opArgIdx >= 0)
            //         {
            //             domainPerVariable[opArgIdx].insert(decUSig._args[i]);
            //         }
            //     }
            // }


            // Special case with equality predicate since I do not store all their possible values in ground facts as it could be very large
            if (_htn.isEqualityPredicate(preSig._usig._name_id))
            {
                // Log::i("Equality predicate %s\n", TOSTR(preSig._usig));
                // Check if the precondition is fully grounded
                if (!_htn.hasQConstants(preSig._usig) && _htn.isFullyGround(preSig._usig))
                {
                    bool equality_correct = preSig._negated ? preSig._usig._args[0] != preSig._usig._args[1] : preSig._usig._args[0] == preSig._usig._args[1];
                    if (!equality_correct) continue;
                    for (size_t i = 0; i < preSig._usig._args.size(); i++)
                    {
                        domainPerVariable[opArgIndices[i]].insert(preSig._usig._args[i]);
                    }
                    continue;
                } else {
                    for (const auto &decUSig : _htn.decodeObjects(preSig._usig, _htn.getEligibleArgs(preSig._usig, preSorts)))
                    {
                        any = true;
                        // Valid?
                        bool equality_correct = preSig._negated ? decUSig._args[0] != decUSig._args[1] : decUSig._args[0] == decUSig._args[1];
                        if (!equality_correct) continue;
                        // Valid precondition decoding found: Increase domain of concerned variables
                        anyValid = true;
                        for (size_t i = 0; i < opArgIndices.size(); i++)
                        {
                            int opArgIdx = opArgIndices[i];
                            if (opArgIdx >= 0)
                            {
                                domainPerVariable[opArgIdx].insert(decUSig._args[i]);
                            }
                        }
                    }
                }
            } else {

                if (!_htn.hasQConstants(preSig._usig) && _htn.isFullyGround(preSig._usig)) {
                    // Get directly the predicateId
                    int predId = _htn.getGroundFactId(preSig._usig, preSig._negated);
                    if (predId >= 0 && isReachableBitVec(predId, preSig._negated))
                    {
                        for (size_t i = 0; i < preSig._usig._args.size(); i++)
                        {
                            domainPerVariable[opArgIndices[i]].insert(preSig._usig._args[i]);
                        }
                    } 
                    continue;
                }

                // Test with the BitVec. Can work even if the predicate is fully grounded
                // Log::i("Sorts: %s\n", TOSTR(preSorts));
                BitVec result = ArgIterator2::getFullInstantiation2(preSig._usig, preSig._negated, _htn, preSorts);
                for (std::size_t pred_idx : result)
                {
                    any = true;
                    const USignature &decUSig = _htn.getGroundPositiveFact(pred_idx);
                    // Log::i("___ Decoding %s of precondition %s\n", TOSTR(decUSig), TOSTR(preSig._usig));
                    if (!isReachableBitVec(pred_idx, preSig._negated))
                    {
                        // Log::i("___ Discard %s as decoding of precondition %s because it is not reachable\n", TOSTR(decUSig), TOSTR(preSig._usig));
                        // printReachableFactsBitVec();
                        continue;
                    }
                    anyValid = true;
                    for (size_t i = 0; i < opArgIndices.size(); i++)
                    {
                        int opArgIdx = opArgIndices[i];
                        if (opArgIdx >= 0)
                        {
                            domainPerVariable[opArgIdx].insert(decUSig._args[i]);
                        }
                    }
                }
            }

            if (any && !anyValid)
                return std::vector<FlatHashSet<int>>();
        }

    for (size_t i = 0; i < args.size(); i++)
    {
        if (!occursInPreconditions[i])
            domainPerVariable[i] = _htn.getConstantsOfSort(sorts[i]);
    }

    return domainPerVariable;
}

FactFrame FactAnalysis::getFactFrame(const USignature &sig, USigSet &currentOps)
{
    static USigSet EMPTY_USIG_SET;

    // Log::d("GET_FACT_FRAME %s\n", TOSTR(sig));

    int nameId = sig._name_id;
    if (!_fact_frames.count(nameId))
    {

        FactFrame result;

        std::vector<int> newArgs(sig._args.size());
        for (size_t i = 0; i < sig._args.size(); i++)
        {
            newArgs[i] = _htn.nameId("c" + std::to_string(i));
        }
        USignature op(sig._name_id, std::move(newArgs));
        result.sig = op;

        if (_htn.isAction(op))
        {

            // Action
            const Action &a = _htn.toAction(op._name_id, op._args);
            result.preconditions = a.getPreconditions();
            result.effects = a.getEffects();
        }
        else if (currentOps.count(op))
        {

            // Handle recursive call of same reduction: Conservatively add preconditions and effects
            // without recursing on subtasks
            const Reduction &r = _htn.toReduction(op._name_id, op._args);
            result.preconditions = r.getPreconditions();
            result.effects = getPossibleFactChanges(r.getSignature(), LIFTED);
            // Log::d("RECURSIVE_FACT_FRAME %s\n", TOSTR(result.effects));

            _htn.addRecursiveMethod(op._name_id);
        }
        else
        {
            currentOps.insert(op);

            const Reduction &r = _htn.toReduction(op._name_id, op._args);
            result.preconditions.insert(r.getPreconditions().begin(), r.getPreconditions().end());

            // For each subtask position ("offset")
            for (size_t offset = 0; offset < r.getSubtasks().size(); offset++)
            {

                FactFrame frameOfOffset;
                std::vector<USignature> children;
                _traversal.getPossibleChildren(r.getSubtasks(), offset, children);
                bool firstChild = true;

                // Assemble fact frame of this offset by iterating over all possible children at the offset
                for (const auto &child : children)
                {

                    // Assemble unified argument names
                    std::vector<int> newChildArgs(child._args);
                    for (size_t i = 0; i < child._args.size(); i++)
                    {
                        if (_htn.isVariable(child._args[i]))
                            newChildArgs[i] = _htn.nameId("??_");
                    }

                    // Recursively get child frame of the child
                    FactFrame childFrame = getFactFrame(USignature(child._name_id, std::move(newChildArgs)), currentOps);

                    if (firstChild)
                    {
                        // Add all preconditions of child that are not yet part of the parent's effects
                        for (const auto &pre : childFrame.preconditions)
                        {
                            bool isNew = true;
                            for (const auto &eff : result.effects)
                            {
                                if (_htn.isUnifiable(eff, pre) || _htn.isUnifiable(pre, eff))
                                {
                                    isNew = false;
                                    // Log::d("FACT_FRAME Precondition %s absorbed by effect %s of %s\n", TOSTR(pre), TOSTR(eff), TOSTR(child));
                                    break;
                                }
                            }
                            if (isNew)
                                frameOfOffset.preconditions.insert(pre);
                        }
                        firstChild = false;
                    }
                    else
                    {
                        // Intersect preconditions
                        SigSet newPrec;
                        for (auto &pre : childFrame.preconditions)
                        {
                            if (frameOfOffset.preconditions.count(pre))
                                newPrec.insert(pre);
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

        // Log::d("FACT_FRAME %s\n", TOSTR(_fact_frames[nameId]));
    }

    const FactFrame &f = _fact_frames[nameId];
    return f.substitute(Substitution(f.sig._args, sig._args));
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

const std::vector<FlatHashSet<int>> &FactAnalysis::getMaxAllowedDomainForLiftFactParams(const Signature &sig)
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
