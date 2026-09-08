#ifndef SIBYLSAT_VARIABLE_PROVIDER_H
#define SIBYLSAT_VARIABLE_PROVIDER_H

#include "data/htn_instance.h"
#include "data/position.h"
#include "sat/variable_allocator.h"

/**
 * Maps planning concepts to their SAT variables.
 *
 * VariableAllocator owns the numeric ID sequence; this class owns the semantic
 * lookup tables that make repeated requests return the same variable.
 */
class VariableProvider {
private:
    HtnInstance& _htn;
    VariableAllocator& _allocator;
    const USignature _primitive_signature;
    const int _substitution_name_id;

    FlatHashMap<IntPair, int, IntPairHasher> _substitution_variables;
    FlatHashMap<IntPair, int, IntPairHasher> _q_constant_equality_variables;

    static IntPair canonicalEqualityKey(int firstQConstant, int secondQConstant);
    std::string positionVariableName(const Position& position, const USignature& signature) const;
    std::string substitutionVariableName(int qConstant, int groundObject) const;

public:
    VariableProvider(HtnInstance& htn, VariableAllocator& allocator);

    bool hasVariable(VarType type, const Position& position, const USignature& signature) const;
    int getVariable(VarType type, const Position& position, const USignature& signature) const;
    int getOrCreateVariable(VarType type, Position& position, const USignature& signature);

    int getOrCreateSubstitutionVariable(int qConstant, int groundObject);
    /** Return zero when this substitution has not been encoded. */
    int getSubstitutionVariableOrZero(int qConstant, int groundObject) const;

    int getOrCreatePrimitiveVariable(Position& position);
    int getPrimitiveVariableOrZero(const Position& position) const;

    bool hasQConstantEqualityVariable(int firstQConstant, int secondQConstant) const;
    int createQConstantEqualityVariable(int firstQConstant, int secondQConstant);
    /** Return an existing equality variable; both argument orders are equivalent. */
    int getQConstantEqualityVariable(int firstQConstant, int secondQConstant) const;
};

#endif
