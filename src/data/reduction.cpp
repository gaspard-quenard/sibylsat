
#include "reduction.h"

Reduction::Reduction() : HtnOp() {}
Reduction::Reduction(HtnOp& op) : HtnOp(op) {}
Reduction::Reduction(const Reduction& r)
        : HtnOp(r._id, r._args),
          _task_name_id(r._task_name_id),
          _task_args(r._task_args),
          _subtasks(r._subtasks),
          _possible_effect_summary(r._possible_effect_summary),
          _argument_dependent_possible_effects(r._argument_dependent_possible_effects) {
    for (auto pre : r.getPreconditions()) addPrecondition(pre);
    for (auto pre : r.getExtraPreconditions()) addExtraPrecondition(pre);
    for (auto eff : r.getEffects()) addEffect(eff);
}
Reduction::Reduction(int nameId, const std::vector<int>& args, const USignature& task) : 
        HtnOp(nameId, args), _task_name_id(task._name_id), _task_args(task._args) {}
Reduction::Reduction(int nameId, const std::vector<int>& args, USignature&& task) : 
        HtnOp(nameId, args), _task_name_id(task._name_id), _task_args(std::move(task._args)) {}

Reduction Reduction::substituteRed(const Substitution& s) const {
    HtnOp op = HtnOp::substitute(s);
    Reduction r(op);
    
    r._task_name_id = _task_name_id;
    
    r._task_args.resize(_task_args.size());
    for (size_t i = 0; i < _task_args.size(); i++) {
        auto it = s.find(_task_args[i]);
        if (it != s.end()) r._task_args[i] = it->second;
        else r._task_args[i] = _task_args[i];
    }
    
    r._subtasks.resize(_subtasks.size());
    for (size_t i = 0; i < _subtasks.size(); i++) {
        r._subtasks[i] = _subtasks[i].substitute(s);
    }
    r._possible_effect_summary = _possible_effect_summary;
    for (const Signature& effect : _argument_dependent_possible_effects) {
        r._argument_dependent_possible_effects.insert(effect.substitute(s));
    }

    return r;
}

void Reduction::addSubtask(const USignature& subtask) {
    _subtasks.push_back(subtask);
}
void Reduction::addSubtask(USignature&& subtask) {
    _subtasks.push_back(std::move(subtask));
}
void Reduction::setSubtasks(std::vector<USignature>&& subtasks) {
    _subtasks = std::move(subtasks);
}

USignature Reduction::getTaskSignature() const {
    return USignature(_task_name_id, _task_args);
}
const std::vector<int>& Reduction::getTaskArguments() const {
    return _task_args;
}
const std::vector<USignature>& Reduction::getSubtasks() const {
    return _subtasks;
}

void Reduction::setPossibleEffectSummary(PossibleMethodEffects effects) {
    _possible_effect_summary = std::make_shared<const PossibleMethodEffects>(std::move(effects));
}

const PossibleMethodEffects& Reduction::getPossibleEffectSummary() const {
    assert(_possible_effect_summary != nullptr);
    return *_possible_effect_summary;
}

const BitVec& Reduction::getArgumentIndependentPossibleEffects(bool negated) const {
    const PossibleMethodEffects& summary = getPossibleEffectSummary();
    return negated ? summary.argumentIndependentNegative : summary.argumentIndependentPositive;
}

const SigSet& Reduction::getArgumentDependentPossibleEffects() const {
    return _argument_dependent_possible_effects;
}

void Reduction::specializeArgumentDependentPossibleEffects() {
    const SigSet& liftedEffects = getPossibleEffectSummary().argumentDependentLiftedEffects;
    std::vector<int> placeholders(_args.size());
    for (size_t index = 0; index < placeholders.size(); ++index) placeholders[index] = -static_cast<int>(index) - 1;

    const Substitution substitution(placeholders, _args);
    _argument_dependent_possible_effects.clear();
    _argument_dependent_possible_effects.reserve(liftedEffects.size());
    for (const Signature& effect : liftedEffects) _argument_dependent_possible_effects.insert(effect.substitute(substitution));
}

SigSet Reduction::getPossibleEffectsForArguments(const std::vector<int>& occurrenceArguments) const {
    std::vector<int> placeholders(occurrenceArguments.size());
    for (size_t index = 0; index < placeholders.size(); ++index) {
        placeholders[index] = -static_cast<int>(index) - 1;
    }

    const Substitution substitution(placeholders, occurrenceArguments);
    SigSet effects;
    const PossibleMethodEffects& summary = getPossibleEffectSummary();
    effects.reserve(summary.argumentIndependentLiftedEffectsForInference.size() + summary.argumentDependentLiftedEffects.size());
    effects.insert(summary.argumentIndependentLiftedEffectsForInference.begin(), summary.argumentIndependentLiftedEffectsForInference.end());
    for (const Signature& effect : summary.argumentDependentLiftedEffects) effects.insert(effect.substitute(substitution));
    return effects;
}

Reduction& Reduction::operator=(const Reduction& other) {
    _id = other._id;
    _args = other._args;
    _preconditions = other._preconditions;
    _extra_preconditions = other._extra_preconditions;
    _effects = other._effects;
    _task_name_id = other._task_name_id;
    _task_args = other._task_args;
    _subtasks = other._subtasks;
    _possible_effect_summary = other._possible_effect_summary;
    _argument_dependent_possible_effects = other._argument_dependent_possible_effects;
    return *this;
}
