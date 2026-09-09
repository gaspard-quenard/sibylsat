
#ifndef DOMPASCH_TREE_REXX_REDUCTION_H
#define DOMPASCH_TREE_REXX_REDUCTION_H

#include <memory>
#include <vector>

#include "data/htn_op.h"
#include "data/signature.h"
#include "util/bitvec.h"

/**
 * Immutable over-approximation of the effects that a method may produce.
 *
 * Lifted effects may contain negative argument-index placeholders and internal
 * lifted variables. They are deliberately separate from HtnOp::getEffects(),
 * which is reserved for effects guaranteed after executing an operation.
 */
struct PossibleMethodEffects {
    // Retained in lifted form so preprocessing can propagate effects through methods.
    SigSet argumentIndependentLiftedEffectsForInference;
    // Effects that must be specialized with the arguments of a method occurrence.
    SigSet argumentDependentLiftedEffects;
    BitVec argumentIndependentPositive;
    BitVec argumentIndependentNegative;
};

class Reduction : public HtnOp {

private:

    // Coding of the methods' AT's name.
    int _task_name_id = -1;
    // The method's AT's arguments.
    std::vector<int> _task_args;

    // The ordered list of subtasks.
    std::vector<USignature> _subtasks;

    // Shared by the template and its instantiated copies without duplicating bit vectors.
    std::shared_ptr<const PossibleMethodEffects> _possible_effect_summary;

    // Lifted possible effects specialized with this occurrence's method arguments.
    SigSet _argument_dependent_possible_effects;

    const PossibleMethodEffects& getPossibleEffectSummary() const;

public:
    Reduction();
    Reduction(HtnOp& op);
    Reduction(const Reduction& r);
    Reduction(int nameId, const std::vector<int>& args, const USignature& task);
    Reduction(int nameId, const std::vector<int>& args, USignature&& task);

    Reduction substituteRed(const Substitution& s) const;

    void addSubtask(const USignature& subtask);
    void addSubtask(USignature&& subtask);
    void setSubtasks(std::vector<USignature>&& subtasks);

    USignature getTaskSignature() const;
    const std::vector<int>& getTaskArguments() const;
    const std::vector<USignature>& getSubtasks() const;

    /** Attach the possible-effect summary computed during preprocessing. */
    void setPossibleEffectSummary(PossibleMethodEffects effects);
    /** Return argument-independent ground effects shared by every occurrence. */
    const BitVec& getArgumentIndependentPossibleEffects(bool negated) const;
    /** Return possible effects whose method arguments were specialized for this occurrence. */
    const SigSet& getArgumentDependentPossibleEffects() const;
    /** Specialize the template's argument-dependent effects with this occurrence's arguments. */
    void specializeArgumentDependentPossibleEffects();
    /** Return all possible effects specialized with the supplied method arguments. */
    SigSet getPossibleEffectsForArguments(const std::vector<int>& occurrenceArguments) const;

    Reduction& operator=(const Reduction& other);
};

#endif
