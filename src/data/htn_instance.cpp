
#include <algorithm>
#include "data/htn_instance.h"

#include "util/log.h"

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


HtnInstance::~HtnInstance() = default;
