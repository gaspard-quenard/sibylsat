
#ifndef DOMPASCH_TREE_REXX_HTN_INSTANCE_H
#define DOMPASCH_TREE_REXX_HTN_INSTANCE_H

#include <assert.h>
#include <memory>
#include <optional>

#include "data/action.h"
#include "data/reduction.h"
#include "data/signature.h"
#include "util/names.h"
#include "util/params.h"
#include "util/hashmap.h"
#include "util/bitvec.h"
#include "util/statistics.h"
#include "data/op_table.h"
#include "data/q_constant_registry.h"

#include "algo/arg_iterator.h"
#include "algo/sample_arg_iterator.h"
#include "data/mutex_groups.h"

class MacroActionCompiler;
class HtnInstanceBuilder;
class HtnStatistics;

class HtnInstance {

private:
    Parameters& _params;

    std::unique_ptr<MacroActionCompiler> _macro_action_compiler;

    // Maps a string to its name ID within the problem.
    FlatHashMap<std::string, int> _name_table;
    // Maps a name ID to its string within the problem.
    NodeHashMap<int, std::string> _name_back_table;
    // Running number to assign new IDs to strings.
    int _name_table_running_id = 1;

    // Set of all name IDs that are variables (start with '?').
    FlatHashSet<int> _var_ids;
    // Set of all predicate name IDs.
    FlatHashSet<int> _predicate_ids;
    // Set of equality predicate name IDs.
    FlatHashSet<int> _equality_predicates;
    QConstantRegistry _q_constants;

    // Maps a {predicate,task,method} name ID to a list of sorts IDs.
    NodeHashMap<int, std::vector<int>> _signature_sorts_table;
    // Sort metadata for variables whose IDs include their declaring operation.
    FlatHashMap<int, int> _sort_by_variable_id;

    // Maps a sort name ID to a set of constants of that sort.
    NodeHashMap<int, FlatHashSet<int>> _constants_by_sort;
    FlatHashSet<int> _declared_sort_ids;
    std::unordered_map<std::string, std::string> _predicate_names_by_lowercase;

    // Maps each {action,reduction} name ID to the number of task variables it originally had.
    FlatHashMap<int, int> _original_n_taskvars;

    // Maps an action name ID to its action object.
    NodeHashMap<int, Action> _operators;
    // Maps a reduction name ID to its reduction object.
    NodeHashMap<int, Reduction> _methods;

    // Name IDs of static predicates (predicate that cannot change during the problem).
    NodeHashSet<int> _static_predicates;

    // Lookup for all actions and reductions instantiated so far.
    OpTable _op_table;

    // Maps a task name ID to the name IDs of possible reductions for the task.
    NodeHashMap<int, std::vector<int>> _task_id_to_reduction_ids;

    // Maps a reduction name ID to the primitivization (action name ID) that replaces it.
    FlatHashMap<int, int> _reduction_to_primitivization;
    // Maps a primitivization (action name ID) to its original reduction name ID
    // and the replaced child name ID.
    FlatHashMap<int, std::pair<int, int>> _primitivization_to_parent_and_child;

    FlatHashMap<int, int> _repeated_to_actual_action;

    USigSet _init_state;
    SigSet _goals;
    // Name ID of the initial reduction in _methods.
    int _init_reduction_id = -1;
    Action _blank_action;
    Action _goal_action;
    USignature _blank_action_sig;
    
    const bool _share_q_constants;

    FlatHashSet<int> _name_id_recursive_methods;

public:
    ~HtnInstance();

    // Get the params 
    Parameters& getParams() const {
        return _params;
    }

    bool isEqualityPredicate(int nameId) const {
        return _equality_predicates.count(nameId);
    }
    const FlatHashSet<int>& getEqualityPredicateIds() const { return _equality_predicates; }
    bool isStaticPredicate(int nameId) const {
        return _static_predicates.count(nameId);
    }

    bool isMacroTask(int nameId) const;
    int numActionsInMacro(int nameId) const;
    std::vector<USignature> getActionsFromMacro(const USignature& macroAction) const;

    /** Return whether mutex groups were requested and loaded. */
    bool hasMutexGroups() const { return _mutex_groups != nullptr; }
    /** Return the loaded mutex-group representation. */
    MutexGroups& getMutexGroups() { assert(_mutex_groups); return *_mutex_groups; }
    const MutexGroups& getMutexGroups() const { assert(_mutex_groups); return *_mutex_groups; }
    /** Install mutex groups computed after the core HTN model has been built. */
    void setMutexGroups(std::unique_ptr<MutexGroups> mutexGroups) { _mutex_groups = std::move(mutexGroups); }

    const USigSet& getInitState() const { return _init_state; }
    const Reduction& getInitReduction() const;
    const USignature& getBlankActionSig();
    const Action& getGoalAction() const { return _goal_action; }
    const NodeHashMap<int, Action>& getActionTemplates() const;
    NodeHashMap<int, Reduction>& getReductionTemplates();

    Action toAction(int actionName, const std::vector<int>& args) const;
    Reduction toReduction(int reductionName, const std::vector<int>& args) const;
    HtnOp& getOp(const USignature& opSig);
    const Action& getActionTemplate(int nameId) const;
    const Reduction& getReductionTemplate(int nameId) const;
    OpTable& getOpTable() {return _op_table;}

    bool hasReductions(int taskId) const;
    const std::vector<int>& getReductionIdsOfTaskId(int taskId) const;

    bool isReductionPrimitivizable(int reductionId) const;
    const Action& getReductionPrimitivization(int reductionId) const;

    bool isActionRepetition(int actionId) const;
    int getRepetitionNameOfAction(int actionId);
    USignature getRepetitionOfAction(const USignature& action);
    int getActionNameFromRepetition(int vChildId) const;
    const Action& getActionFromRepetition(int vChildId) const;

    const std::vector<int>& getSorts(int nameId) const;
    /** Return the declared sort of each argument without parsing generated variable names. */
    std::vector<int> getArgumentSorts(const USignature& signature) const;
    const FlatHashSet<int>& getConstantsOfSort(int sort) const;
    int getPrimarySortOfQConstant(int qconst) const;
    const FlatHashSet<int>& getSortsOfQConstant(int qconst) const;
    size_t getOriginPositionIdOfQConstant(int qconst) const;
    const FlatHashSet<int>& getDomainOfQConstant(int qconst) const;
    std::optional<std::vector<int>> takeQConstantDomainForOperation(int qconst, const USignature& op);

    /**
     * Returns one sort per condition argument, derived from the corresponding
     * argument in the operation.
     *
     * Example: operation (?x:A, ?y:B), condition p(?y, ?x) -> {B, A}.
     * Fixed constants retain the corresponding predicate argument sort.
     */
    std::vector<int> getConditionSortsFromOperation(const USignature& condition, const USignature& operation);

    /** Returns the candidate constants for every argument of a signature. */
    std::vector<std::vector<int>> getCandidateArgumentDomains(const USignature& signature, const std::vector<int>& restrictiveSorts = {});
    /** Enumerates every candidate decoding, including signatures absent from the ground-fact table. */
    ArgIterator enumerateCandidateDecodings(const USignature& signature, const std::vector<int>& restrictiveSorts = {});
    /** Enumerates candidates from domains already computed by the caller. */
    ArgIterator enumerateCandidateDecodings(const USignature& signature, std::vector<std::vector<int>> candidateDomains);
    /** Samples candidate decodings derived from the supplied argument sorts. */
    SampleArgIterator sampleCandidateDecodings(const USignature& signature, const std::vector<int>& restrictiveSorts, size_t numSamples);
    /** Samples candidates from domains already computed by the caller. */
    SampleArgIterator sampleCandidateDecodings(const USignature& signature, std::vector<std::vector<int>> candidateDomains, size_t numSamples);

    std::optional<Action> instantiateWithQConstants(const Action& action, const std::vector<FlatHashSet<int>>& argumentDomains, size_t originPositionId);
    std::optional<Reduction> instantiateWithQConstants(const Reduction& reduction, const std::vector<FlatHashSet<int>>& argumentDomains, size_t originPositionId);

    /** Remove parser-introduced auxiliary arguments before printing the original task. */
    USignature restoreOriginalTaskArity(const USignature& signature) const;
    /** Return whether an action is the compiled replacement of a single-subtask reduction. */
    bool isPrimitivizedAction(int actionNameId) const;
    /** Return the original reduction and child action represented by a primitivized action. */
    const std::pair<int, int>& getReductionAndActionFromPrimitivization(int primitivizationName) const;
    /** Return whether an action is the removable second half of a parser-split action. */
    bool isSecondSplitAction(int actionNameId) const;

    int nameId(const std::string& name);
    std::string toString(int id) const;

    /** Create a traversal-local argument name and preserve variable sort metadata. */
    int createRenamedArgument(int argumentId, const std::string& suffix);

    bool isVariable(int argument) const;

    inline bool isQConstant(int c) const {
        return _q_constants.contains(c);
    }

    bool hasQConstants(const USignature& signature) const;
    bool isUnifiable(const Signature& from, const Signature& to, FlatHashMap<int, int>* substitution = nullptr) const;
    bool isUnifiable(const USignature& from, const USignature& to, FlatHashMap<int, int>* substitution = nullptr) const;
    bool isFullyGround(const USignature& signature) const;
    bool hasSomeInstantiation(const USignature& signature) const;
    bool hasConsistentlyTypedArgs(const USignature& signature) const;

    inline bool isPredicate(int nameId) const {
        return _predicate_ids.count(nameId);
    }

    inline bool isAction(const USignature& sig) const {
        return _operators.count(sig._name_id);
    }

    inline bool isReduction(const USignature& sig) const {
        return _methods.count(sig._name_id);
    }

    inline size_t getNumberOfQConstants() const {
        return _q_constants.size();
    }

    std::vector<TypeConstraint> getQConstantTypeConstraints(const USignature& signature) const;

    inline void addRecursiveMethod(int nameId) {
        _name_id_recursive_methods.insert(nameId);
    }

    inline bool isRecursiveMethod(int nameId) {
        return _name_id_recursive_methods.count(nameId);
    }


    bool sortHasConstants(int sortId) const;
    NodeHashMap<int, FlatHashSet<int>>& getConstantsBySort() {return _constants_by_sort;}
    std::string getPredicateInCorrectCase(std::string pred) const;

private:
    friend class HtnInstanceBuilder;
    friend class HtnStatistics;

    /** Construct an empty internal model; HtnInstanceBuilder populates it. */
    explicit HtnInstance(Parameters& params);

    std::optional<std::vector<int>> instantiateArgumentsWithQConstants(const HtnOp& operation, const std::vector<FlatHashSet<int>>& argumentDomains, size_t originPositionId);
    int createQConstant(const std::string& name, const FlatHashSet<int>& domain, size_t originPositionId);

    std::unique_ptr<MutexGroups> _mutex_groups;
};

#endif
