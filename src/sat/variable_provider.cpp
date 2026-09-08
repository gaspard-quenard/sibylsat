#include "sat/variable_provider.h"

#include <algorithm>
#include <cassert>

#include "util/names.h"

VariableProvider::VariableProvider(HtnInstance& htn, VariableAllocator& allocator)
    : _htn(htn),
      _allocator(allocator),
      _primitive_signature(_htn.nameId("__PRIMITIVE___"), std::vector<int>()),
      _substitution_name_id(_htn.nameId("__SUBSTITUTE___")) {}

IntPair VariableProvider::canonicalEqualityKey(int firstQConstant, int secondQConstant) {
    return std::minmax(firstQConstant, secondQConstant);
}

std::string VariableProvider::positionVariableName(const Position& position, const USignature& signature) const {
    return Names::to_string(signature) + "@(" + std::to_string(position.getCreationIteration())
            + "," + std::to_string(position.getPositionId()) + ")";
}

std::string VariableProvider::substitutionVariableName(int qConstant, int groundObject) const {
    return Names::to_string(USignature(_substitution_name_id, {qConstant, groundObject}));
}

bool VariableProvider::hasVariable(VarType type, const Position& position, const USignature& signature) const {
    return position.hasVariable(type, signature);
}

int VariableProvider::getVariable(VarType type, const Position& position, const USignature& signature) const {
    return position.getVariable(type, signature);
}

int VariableProvider::getOrCreateVariable(VarType type, Position& position, const USignature& signature) {
    const int existingVariable = position.getVariableOrZero(type, signature);
    if (existingVariable != 0) return existingVariable;

    const int variable = _allocator.allocateVariable(positionVariableName(position, signature));
    position.setVariable(type, signature, variable);
    return variable;
}

int VariableProvider::getOrCreateSubstitutionVariable(int qConstant, int groundObject) {
    assert(_htn.isQConstant(qConstant));
    assert(!_htn.isQConstant(groundObject));

    const IntPair key(qConstant, groundObject);
    const auto existing = _substitution_variables.find(key);
    if (existing != _substitution_variables.end()) return existing->second;

    const int variable = _allocator.allocateVariable(substitutionVariableName(qConstant, groundObject));
    _substitution_variables[key] = variable;
    return variable;
}

int VariableProvider::getSubstitutionVariableOrZero(int qConstant, int groundObject) const {
    const auto variable = _substitution_variables.find(IntPair(qConstant, groundObject));
    return variable == _substitution_variables.end() ? 0 : variable->second;
}

int VariableProvider::getOrCreatePrimitiveVariable(Position& position) {
    return getOrCreateVariable(VarType::OP, position, _primitive_signature);
}

int VariableProvider::getPrimitiveVariableOrZero(const Position& position) const {
    return position.getVariableOrZero(VarType::OP, _primitive_signature);
}

bool VariableProvider::hasQConstantEqualityVariable(int firstQConstant, int secondQConstant) const {
    return _q_constant_equality_variables.count(canonicalEqualityKey(firstQConstant, secondQConstant));
}

int VariableProvider::createQConstantEqualityVariable(int firstQConstant, int secondQConstant) {
    const IntPair key = canonicalEqualityKey(firstQConstant, secondQConstant);
    assert(!_q_constant_equality_variables.count(key));

    const std::string name = "(__Q_EQUAL " + std::to_string(key.first) + " " + std::to_string(key.second) + ")";
    const int variable = _allocator.allocateVariable(name);
    _q_constant_equality_variables[key] = variable;
    return variable;
}

int VariableProvider::getQConstantEqualityVariable(int firstQConstant, int secondQConstant) const {
    const IntPair key = canonicalEqualityKey(firstQConstant, secondQConstant);
    const auto variable = _q_constant_equality_variables.find(key);
    assert(variable != _q_constant_equality_variables.end());
    return variable->second;
}
