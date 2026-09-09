
#include <algorithm>
#include <iomanip>
#include <unordered_map>

#include "data/htn_instance.h"
#include "preprocessing/macro_action_compiler.h"

HtnInstance::HtnInstance(bool shareQConstants) : _share_q_constants(shareQConstants) {}

int HtnInstance::nameId(const std::string& name) {
    auto existing = _name_table.find(name);
    if (existing != _name_table.end()) return existing->second;

    const int id = _name_table_running_id++;
    if (name[0] == '?') _var_ids.insert(id);
    _name_table[name] = id;
    _name_back_table[id] = name;
    return id;
}

std::string HtnInstance::toString(int id) const {
    return _name_back_table.at(id);
}

int HtnInstance::createRenamedArgument(int argumentId, const std::string& suffix) {
    const int renamedId = nameId(toString(argumentId) + suffix);
    if (_var_ids.count(argumentId)) _sort_by_variable_id[renamedId] = _sort_by_variable_id.at(argumentId);
    return renamedId;
}

bool HtnInstance::isVariable(int argument) const {
    if (argument < 0) return true;
    assert(_name_back_table.count(argument));
    return _var_ids.count(argument);
}

bool HtnInstance::hasQConstants(const USignature& signature) const {
    return std::any_of(signature._args.begin(), signature._args.end(), [&](int argument) {
        return isQConstant(argument);
    });
}

bool HtnInstance::isUnifiable(const Signature& from, const Signature& to, FlatHashMap<int, int>* substitution) const {
    return from._negated == to._negated && isUnifiable(from._usig, to._usig, substitution);
}

bool HtnInstance::isUnifiable(const USignature& from, const USignature& to, FlatHashMap<int, int>* substitution) const {
    if (from._name_id != to._name_id || from._args.size() != to._args.size()) return false;
    for (size_t argumentIndex = 0; argumentIndex < from._args.size(); ++argumentIndex) {
        const int sourceArgument = from._args[argumentIndex];
        const int targetArgument = to._args[argumentIndex];
        if (!isVariable(sourceArgument)) {
            if (sourceArgument != targetArgument) return false;
        } else if (substitution != nullptr) {
            (*substitution)[sourceArgument] = targetArgument;
        }
    }
    return true;
}

bool HtnInstance::isFullyGround(const USignature& signature) const {
    return std::none_of(signature._args.begin(), signature._args.end(), [&](int argument) {
        return isVariable(argument);
    });
}

bool HtnInstance::hasSomeInstantiation(const USignature& signature) const {
    const std::vector<int>& sorts = getSorts(signature._name_id);
    assert(sorts.size() == signature._args.size());
    return std::all_of(sorts.begin(), sorts.end(), [&](int sort) {
        return !getConstantsOfSort(sort).empty();
    });
}

bool HtnInstance::hasConsistentlyTypedArgs(const USignature& signature) const {
    const std::vector<int>& sorts = getSorts(signature._name_id);
    for (size_t argumentIndex = 0; argumentIndex < signature._args.size(); ++argumentIndex) {
        const int argument = signature._args[argumentIndex];
        if (isVariable(argument)) continue;
        const FlatHashSet<int>& validConstants = getConstantsOfSort(sorts[argumentIndex]);
        if (!isQConstant(argument) && !validConstants.count(argument)) return false;
        if (isQConstant(argument) && std::none_of(getDomainOfQConstant(argument).begin(),
                getDomainOfQConstant(argument).end(), [&](int constant) { return validConstants.count(constant); })) return false;
    }
    return true;
}

std::vector<TypeConstraint> HtnInstance::getQConstantTypeConstraints(const USignature& signature) const {
    std::vector<TypeConstraint> constraints;
    const std::vector<int>& sorts = getSorts(signature._name_id);
    for (size_t argumentIndex = 0; argumentIndex < signature._args.size(); ++argumentIndex) {
        const int argument = signature._args[argumentIndex];
        const int requiredSort = sorts[argumentIndex];
        if (!isQConstant(argument)) {
            assert(getConstantsOfSort(requiredSort).count(argument));
            continue;
        }
        if (getSortsOfQConstant(argument).count(requiredSort)) continue;

        std::vector<int> valid;
        std::vector<int> invalid;
        const FlatHashSet<int>& validConstants = getConstantsOfSort(requiredSort);
        for (int constant : getDomainOfQConstant(argument)) {
            (validConstants.count(constant) ? valid : invalid).push_back(constant);
        }
        if (valid.size() >= invalid.size()) constraints.emplace_back(argument, true, std::move(valid));
        else constraints.emplace_back(argument, false, std::move(invalid));
    }
    return constraints;
}

const Reduction& HtnInstance::getInitReduction() const {
    return _methods.at(_init_reduction_id);
}

const USignature& HtnInstance::getBlankActionSig() {
    return _blank_action_sig;
}

HtnOp& HtnInstance::getOp(const USignature& opSig) {
    auto it = _operators.find(opSig._name_id);
    if (it != _operators.end()) return static_cast<HtnOp&>(it->second);
    return static_cast<HtnOp&>(_methods.at(opSig._name_id));
}

const Action& HtnInstance::getActionTemplate(int nameId) const {
    return _operators.at(nameId);
}

const Reduction& HtnInstance::getReductionTemplate(int nameId) const {
    return _methods.at(nameId);
}

bool HtnInstance::hasReductions(int taskId) const {
    return _task_id_to_reduction_ids.count(taskId);
}

const std::vector<int>& HtnInstance::getReductionIdsOfTaskId(int taskId) const {
    return _task_id_to_reduction_ids.at(taskId);
}

bool HtnInstance::isReductionPrimitivizable(int reductionId) const {
    return _reduction_to_primitivization.count(reductionId);
}

const Action& HtnInstance::getReductionPrimitivization(int reductionId) const {
    return _operators.at(_reduction_to_primitivization.at(reductionId));
}

bool HtnInstance::isActionRepetition(int actionId) const {
    return _repeated_to_actual_action.count(actionId);
}

int HtnInstance::getRepetitionNameOfAction(int actionId) {
    return nameId("__REPEATED_" + _name_back_table[actionId]);
}

USignature HtnInstance::getRepetitionOfAction(const USignature& action) {

    int repOpNameId = getRepetitionNameOfAction(action._name_id);
    USignature sig(repOpNameId, action._args);

    if (!_op_table.hasAction(sig)) {

        // Define the operator
        if (!_operators.count(repOpNameId)) {
            const Action& op = _operators[action._name_id];
            Action a(repOpNameId, op.getArguments());
            a.setPreconditions(op.getPreconditions());
            a.setExtraPreconditions(op.getExtraPreconditions());
            a.setEffects(op.getEffects());
            _operators[repOpNameId] = std::move(a);
            _repeated_to_actual_action[repOpNameId] = action._name_id;
            const auto& sorts = _signature_sorts_table[action._name_id];
            _signature_sorts_table[repOpNameId] = sorts;
        }

        // Define the action
        Action a = _operators[repOpNameId];
        _op_table.addAction(a.substitute(Substitution(a.getArguments(), sig._args)));
    }

    return sig;
}

const Action& HtnInstance::getActionFromRepetition(int vChildId) const {
    return _operators.at(_repeated_to_actual_action.at(vChildId));
}

int HtnInstance::getActionNameFromRepetition(int vChildId) const {
    auto it = _repeated_to_actual_action.find(vChildId);
    return it == _repeated_to_actual_action.end() ? -1 : it->second;
}

std::optional<Action> HtnInstance::instantiateWithQConstants(const Action& action, const std::vector<FlatHashSet<int>>& argumentDomains, size_t originPositionId) {
    auto instantiatedArgs = instantiateArgumentsWithQConstants(action, argumentDomains, originPositionId);
    if (!instantiatedArgs) return std::nullopt;
    return toAction(action.getNameId(), instantiatedArgs.value());
}

std::optional<Reduction> HtnInstance::instantiateWithQConstants(const Reduction& reduction, const std::vector<FlatHashSet<int>>& argumentDomains, size_t originPositionId) {
    auto instantiatedArgs = instantiateArgumentsWithQConstants(reduction, argumentDomains, originPositionId);
    if (!instantiatedArgs) return std::nullopt;
    return reduction.substituteRed(Substitution(reduction.getArguments(), instantiatedArgs.value()));
}

std::optional<std::vector<int>> HtnInstance::instantiateArgumentsWithQConstants(const HtnOp& operation, const std::vector<FlatHashSet<int>>& argumentDomains, size_t originPositionId) {
    if (operation.getArguments().empty()) return std::vector<int>();
    if (argumentDomains.size() != operation.getArguments().size()) return std::nullopt;

    std::vector<int> args = operation.getArguments();
    std::vector<size_t> variableArgumentIndices;
    for (size_t i = 0; i < args.size(); i++) {
        if (isVariable(args[i])) variableArgumentIndices.push_back(i);
    }

    for (size_t argumentIndex : variableArgumentIndices) {
        if (!argumentDomains[argumentIndex].empty()) continue;
        Log::d("Empty domain for arg %s of %s\n", TOSTR(args[argumentIndex]), TOSTR(operation.getSignature()));
        return std::nullopt;
    }

    // Assemble new operator arguments
    FlatHashMap<int, int> numIntroducedQConstsPerType;
    NodeHashMap<int, std::vector<int>> domainsPerQConst;
    for (size_t argumentIndex : variableArgumentIndices) {
        const auto& domain = argumentDomains[argumentIndex];
        if (domain.size() == 1) {
            // Only one valid constant here: Replace directly
            args[argumentIndex] = *domain.begin();
        } else {
            // Several valid constants here: Introduce q-constant

            // Assemble name
            int sortCounter = 0;
            int primarySort = _signature_sorts_table[operation.getSignature()._name_id][argumentIndex];
            auto it = numIntroducedQConstsPerType.find(primarySort);
            if (it == numIntroducedQConstsPerType.end()) {
                numIntroducedQConstsPerType[primarySort] = 1;
            } else {
                sortCounter = it->second;
                it->second++;
            }
            std::vector<int> domainVec(domain.begin(), domain.end());
            std::stringstream domainHash;
            domainHash << std::hex << USignatureHasher()(USignature(primarySort, domainVec));
            std::string qConstName = "Q_" + std::to_string(originPositionId)
                + "_" + _name_back_table[primarySort]
                + ":" + std::to_string(sortCounter) 
                + "_" + domainHash.str()
                + (_share_q_constants ? std::string() : "_#"+std::to_string(_q_constants.size()));
            
            // Initialize q-constant
            args[argumentIndex] = createQConstant(qConstName, domain, originPositionId);
            domainsPerQConst[args[argumentIndex]] = std::move(domainVec);
        }
    }

    // Remember exact domain of each q constant for this operation
    USignature newSig(operation.getSignature()._name_id, args);
    for (auto& [qconst, domain] : domainsPerQConst) {
        _q_constants.setOperationDomain(qconst, newSig, std::move(domain));
    }

    return args;
}

int HtnInstance::createQConstant(const std::string& name, const FlatHashSet<int>& domain, size_t originPositionId) {
    assert(originPositionId > 0);
    auto existing = _name_table.find(name);
    if (existing != _name_table.end()) {
        const int id = existing->second;
        assert(_q_constants.getOriginPositionId(id) == originPositionId);
        assert(getDomainOfQConstant(id) == domain);
        return id;
    }

    const int id = _q_constants.nextId();
    _name_table[name] = id;
    _name_back_table[id] = name;

    std::string qSortName = "qsort_" + _name_back_table[id];
    int newSortId = nameId(qSortName);
    _constants_by_sort[newSortId].insert(domain.begin(), domain.end());

    // A guaranteed sort contains every possible value of the pseudo-constant.
    FlatHashSet<int> qConstSorts;
    qConstSorts.insert(_declared_sort_ids.begin(), _declared_sort_ids.end());
    for (int c : _constants_by_sort[newSortId]) {
        std::vector<int> sortsToRemove;
        for (int qsort : qConstSorts) {
            if (std::find(_constants_by_sort[qsort].begin(), _constants_by_sort[qsort].end(), c) 
                    == _constants_by_sort[qsort].end()) {
                sortsToRemove.push_back(qsort);
            }
        }
        for (int remSort : sortsToRemove) qConstSorts.erase(remSort);
    }
    _q_constants.add(id, originPositionId, newSortId, std::move(qConstSorts));
    return id;
}

std::vector<std::vector<int>> HtnInstance::getCandidateArgumentDomains(const USignature& qSig, const std::vector<int>& restrictiveSorts) {

    std::vector<std::vector<int>> eligibleArgs;

    if (!hasQConstants(qSig) && isFullyGround(qSig)) 
        return eligibleArgs;

    eligibleArgs.resize(qSig._args.size());
    for (size_t argPos = 0; argPos < qSig._args.size(); argPos++) {
        int arg = qSig._args[argPos];
        if (isVariable(arg) || isQConstant(arg)) {
            // Q-constant sort or variable
            const auto& domain = _constants_by_sort.at(isQConstant(arg) ? _q_constants.getPrimarySort(arg)
                        : getSorts(qSig._name_id).at(argPos));
            if (restrictiveSorts.empty()) {
                eligibleArgs[argPos].insert(eligibleArgs[argPos].end(), domain.begin(), domain.end());
            } else {
                const auto& restrictiveDomain = _constants_by_sort.at(restrictiveSorts.at(argPos));
                for (int c : domain) {
                    if (restrictiveDomain.count(c)) eligibleArgs[argPos].push_back(c);
                }
            }
        } else {
            // normal constant
            eligibleArgs[argPos].push_back(arg);
        }
        //assert(eligibleArgs[argPos].size() > 0);
        if (eligibleArgs[argPos].empty()) {
            return std::vector<std::vector<int>>();
        }
    }
    return eligibleArgs;
}

ArgIterator HtnInstance::enumerateCandidateDecodings(const USignature& signature, const std::vector<int>& restrictiveSorts) {
    return enumerateCandidateDecodings(signature, getCandidateArgumentDomains(signature, restrictiveSorts));
}

ArgIterator HtnInstance::enumerateCandidateDecodings(const USignature& signature, std::vector<std::vector<int>> candidateDomains) {
    return ArgIterator(signature._name_id, std::move(candidateDomains));
}

SampleArgIterator HtnInstance::sampleCandidateDecodings(const USignature& signature, const std::vector<int>& restrictiveSorts, size_t numSamples) {
    return sampleCandidateDecodings(signature, getCandidateArgumentDomains(signature, restrictiveSorts), numSamples);
}

SampleArgIterator HtnInstance::sampleCandidateDecodings(const USignature& signature, std::vector<std::vector<int>> candidateDomains, size_t numSamples) {
    return SampleArgIterator(signature._name_id, std::move(candidateDomains), numSamples);
}

const std::vector<int>& HtnInstance::getSorts(int nameId) const {
    return _signature_sorts_table.at(nameId);
}

std::vector<int> HtnInstance::getArgumentSorts(const USignature& signature) const {
    std::vector<int> argumentSorts = getSorts(signature._name_id);
    assert(argumentSorts.size() == signature._args.size());
    for (size_t argumentIndex = 0; argumentIndex < signature._args.size(); ++argumentIndex) {
        const int argument = signature._args[argumentIndex];
        if (!_var_ids.count(argument)) continue;
        const auto declaredSort = _sort_by_variable_id.find(argument);
        if (declaredSort == _sort_by_variable_id.end()) {
            Log::e("No sort metadata for variable %s in %s.\n", toString(argument).c_str(), TOSTR(signature));
            abort();
        }
        argumentSorts[argumentIndex] = declaredSort->second;
    }
    return argumentSorts;
}

const FlatHashSet<int>& HtnInstance::getConstantsOfSort(int sort) const {
    return _constants_by_sort.at(sort);
}

int HtnInstance::getPrimarySortOfQConstant(int qconst) const {
    return _q_constants.getPrimarySort(qconst);
}

const FlatHashSet<int>& HtnInstance::getSortsOfQConstant(int qconst) const {
    return _q_constants.getGuaranteedSorts(qconst);
}

std::vector<int> HtnInstance::getConditionSortsFromOperation(const USignature& condition, const USignature& operation) {
    std::vector<int> conditionSorts = getSorts(condition._name_id);
    const std::vector<int>& operationSorts = getSorts(operation._name_id);
    for (size_t conditionIndex = 0; conditionIndex < conditionSorts.size(); conditionIndex++) {
        for (size_t operationIndex = 0; operationIndex < operation._args.size(); operationIndex++) {
            if (condition._args[conditionIndex] == operation._args[operationIndex]) {
                conditionSorts[conditionIndex] = operationSorts[operationIndex];
                break;
            }
        }
    }
    return conditionSorts;
}

const FlatHashSet<int>& HtnInstance::getDomainOfQConstant(int qconst) const {
    return _constants_by_sort.at(_q_constants.getPrimarySort(qconst));
}

size_t HtnInstance::getOriginPositionIdOfQConstant(int qconst) const {
    return _q_constants.getOriginPositionId(qconst);
}

std::optional<std::vector<int>> HtnInstance::takeQConstantDomainForOperation(int qconst, const USignature& op) {
    return _q_constants.takeOperationDomain(qconst, op);
}

const NodeHashMap<int, Action>& HtnInstance::getActionTemplates() const {
    return _operators;
}
NodeHashMap<int, Reduction>& HtnInstance::getReductionTemplates() {
    return _methods;
}

Action HtnInstance::toAction(int actionName, const std::vector<int>& args) const {
    const auto& op = _operators.at(actionName);
    return op.substitute(Substitution(op.getArguments(), args));
}

Reduction HtnInstance::toReduction(int reductionName, const std::vector<int>& args) const {
    const auto& op = _methods.at(reductionName);
    return op.substituteRed(Substitution(op.getArguments(), args));
}

USignature HtnInstance::restoreOriginalTaskArity(const USignature& signature) const {
    USignature restored(signature);
    restored._args.resize(_original_n_taskvars.at(signature._name_id));
    return restored;
}

bool HtnInstance::isPrimitivizedAction(int actionNameId) const {
    return _primitivization_to_parent_and_child.count(actionNameId);
}

const std::pair<int, int>& HtnInstance::getReductionAndActionFromPrimitivization(int primitivizationName) const {
    return _primitivization_to_parent_and_child.at(primitivizationName);
}

bool HtnInstance::isSecondSplitAction(int actionNameId) const {
    return toString(actionNameId).starts_with("__LLT_SECOND");
}

bool HtnInstance::sortHasConstants(int sortId) const {
    return _constants_by_sort.count(sortId) && !_constants_by_sort.at(sortId).empty();
}

std::string HtnInstance::getPredicateInCorrectCase(std::string pred) const {
    std::transform(pred.begin(), pred.end(), pred.begin(), ::tolower);
    const auto match = _predicate_names_by_lowercase.find(pred);
    if (match != _predicate_names_by_lowercase.end()) return match->second;
    Log::e("Predicate %s does not exist in the domain file.\n", pred.c_str());
    exit(1);
}


int HtnInstance::numActionsInMacro(int nameId) const {
    return _macro_action_compiler->getExpansion(toString(nameId)).primitiveSteps.size();
}

std::vector<USignature> HtnInstance::getActionsFromMacro(const USignature& macroAction) const {
    std::vector<USignature> actions;
    if (!isMacroTask(macroAction._name_id)) return actions;

    const MacroActionExpansion& expansion = _macro_action_compiler->getExpansion(toString(macroAction._name_id));
    actions.reserve(expansion.primitiveSteps.size());
    for (const MacroPrimitiveStep& step : expansion.primitiveSteps) {
        std::vector<int> arguments;
        arguments.reserve(step.macroArgumentIndices.size());
        for (size_t argumentIndex : step.macroArgumentIndices) arguments.push_back(macroAction._args.at(argumentIndex));
        actions.emplace_back(_name_table.at(step.actionName), std::move(arguments));
    }
    return actions;
}

bool HtnInstance::isMacroTask(int nameId) const {
    return _macro_action_compiler && _macro_action_compiler->isMacroAction(toString(nameId));
}

HtnInstance::~HtnInstance() = default;
