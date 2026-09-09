#include "sat/decoder.h"

#include <algorithm>

#include "util/log.h"

Decoder::Decoder(HtnInstance& htn, const QConstantManager& qConstants, Position*& rootPosition, std::vector<Position*>& leafPositions, SatInterface& sat, VariableProvider& vars)
    : _htn(htn), _q_constants(qConstants), _root_position(rootPosition), _leaf_positions(leafPositions), _sat(sat), _vars(vars) {}

std::vector<PlanItem> Decoder::extractFrontierPlan(FrontierPlanMode mode) const {
    std::vector<PlanItem> plan(_leaf_positions.size());
    for (size_t positionIndex = 0; positionIndex < _leaf_positions.size(); positionIndex++) {
        const Position& leaf = *_leaf_positions[positionIndex];
        const USignature& selectedOperation = getSelectedOperation(leaf);
        if (selectedOperation == Sig::NONE_SIG) continue;
        if (mode == FrontierPlanMode::PrimitiveActionsOnly && !_htn.isAction(selectedOperation)) continue;

        USignature operation = selectedOperation;
        if (_htn.isActionRepetition(operation._name_id)) {
            operation._name_id = _htn.getActionNameFromRepetition(selectedOperation._name_id);
        }

        Log::d("PLANDBG %zu,%zu OP %s\n", leaf.getCreationIteration(), positionIndex, TOSTR(operation));

        const USignature decodedOperation = decodeQConstants(leaf, operation);
        if (decodedOperation == Sig::NONE_SIG) continue;

        const int operationVar = leaf.getVariableOrZero(VarType::OP, selectedOperation);
        assert(operationVar != 0);
        plan[positionIndex] = {operationVar, decodedOperation, decodedOperation, {}};
    }

    return plan;
}

Plan Decoder::extractPlan() const {
    Plan result;
    auto& [classicalPlan, hierarchy] = result;
    classicalPlan = extractFrontierPlan();

    const Position* hierarchyRoot = findSelectedInitialReduction();
    if (hierarchyRoot != nullptr) {
        appendSelectedHierarchy(classicalPlan, hierarchy, *hierarchyRoot);
    }
    return result;
}

const USignature& Decoder::getSelectedOperation(const Position& position) const {
    const int primitiveNameId = _htn.nameId("__PRIMITIVE___");
    const USignature* selectedOperation = nullptr;

    for (const auto& [signature, operationVar] : position.getVariableTable(VarType::OP)) {
        if (!_sat.holds(operationVar) || signature._name_id == primitiveNameId) continue;

        if (selectedOperation != nullptr) {
            Log::e("Plan error: Multiple operations selected at position (%zu,%zu): %s and %s\n",
                    position.getCreationIteration(), position.getPositionId(),
                    TOSTR(*selectedOperation), TOSTR(signature));
            assert(false);
            continue;
        }
        selectedOperation = &signature;
    }

    return selectedOperation == nullptr ? Sig::NONE_SIG : *selectedOperation;
}

USignature Decoder::getSelectedDecodedOperation(const Position& position) const {
    return decodeQConstants(position, getSelectedOperation(position));
}

std::optional<int> Decoder::getSelectedQConstantValue(int qConstant) const {
    std::optional<int> selectedValue;
    for (int groundArgument : _q_constants.getDomain(qConstant)) {
        const int substitutionVariable = _vars.getSubstitutionVariableOrZero(qConstant, groundArgument);
        if (substitutionVariable == 0 || !_sat.holds(substitutionVariable)) continue;

        if (selectedValue.has_value()) {
            Log::e("Plan error: Multiple substitutions selected for q-constant %s\n", TOSTR(qConstant));
            assert(false);
            continue;
        }
        selectedValue = groundArgument;
    }
    return selectedValue;
}

/**
 * Replace every q-constant with the unique ground object selected by its SAT
 * substitution variables. For example, move(?q1,b) becomes move(a,b) when
 * substitute(?q1,a) is true. NONE_SIG indicates a missing substitution.
 */
USignature Decoder::decodeQConstants(const Position& position, const USignature& signature) const {
    Substitution substitution;
    for (int argument : signature._args) {
        if (!_q_constants.contains(argument) || substitution.count(argument)) continue;

        const std::optional<int> selectedValue = getSelectedQConstantValue(argument);
        if (!selectedValue.has_value()) {
            Log::v("(%zu,%zu) No substitution for q-constant %s in %s\n",
                    position.getCreationIteration(), position.getPositionId(), TOSTR(argument), TOSTR(signature));
            return Sig::NONE_SIG;
        }
        substitution[argument] = selectedValue.value();
    }

    const USignature decodedSignature = signature.substitute(substitution);
    if (!substitution.empty()) Log::d("Decoded %s as %s\n", TOSTR(signature), TOSTR(decodedSignature));
    return decodedSignature;
}

NodeHashSet<int> Decoder::collectTrueVariablesBeforeFrontierIndex(size_t frontierEnd) const {
    NodeHashSet<int> trueVariables;

    const size_t end = std::min(frontierEnd, _leaf_positions.size());
    for (size_t positionIndex = 0; positionIndex < end; positionIndex++) {
        for (Position* position = _leaf_positions[positionIndex]; position != nullptr && position != _root_position; position = position->getParentPosition()) {
            for (VarType variableType : {VarType::FACT, VarType::OP}) {
                for (const auto& [signature, variable] : position->getVariableTable(variableType)) {
                    (void) signature;
                    if (_sat.holds(variable)) trueVariables.insert(variable);
                }
            }
        }
    }

    return trueVariables;
}

int Decoder::findFrontierIndex(const Position& position) const {
    for (size_t index = 0; index < _leaf_positions.size(); index++) {
        if (_leaf_positions[index] == &position) return static_cast<int>(index);
    }
    return -1;
}

int Decoder::findDescendantFrontierIndex(const Position& position) const {
    const Position* current = &position;
    while (current != nullptr) {
        const int frontierIndex = findFrontierIndex(*current);
        if (frontierIndex >= 0) return frontierIndex;

        const auto& children = current->getChildrenPositions();
        if (children.empty()) return -1;

        // Expanded actions continue through the first child. Any later child
        // is padding for reductions that have more subtasks.
        current = children.front();
    }
    return -1;
}

const Position* Decoder::findSelectedInitialReduction() const {
    if (_root_position == nullptr) return nullptr;

    const auto& rootChildren = _root_position->getChildrenPositions();
    if (rootChildren.empty()) return nullptr;

    const Position* initialReductionPosition = rootChildren.front();
    const USigSet& reductions = initialReductionPosition->getReductions();
    if (reductions.size() != 1) {
        Log::e("Plan error: The root's first child contains %zu reductions instead of the single initial reduction\n",
                reductions.size());
        assert(false);
        return nullptr;
    }

    const USignature& initialReduction = *reductions.begin();
    const int expectedNameId = _htn.getInitReduction().getNameId();
    if (initialReduction._name_id != expectedNameId) {
        Log::e("Plan error: The root's first child contains %s instead of the initial reduction %s\n",
                TOSTR(initialReduction), TOSTR(_htn.getInitReduction().getSignature()));
        assert(false);
        return nullptr;
    }

    const USignature& selectedOperation = getSelectedOperation(*initialReductionPosition);
    if (selectedOperation != initialReduction) {
        Log::e("Plan error: Initial reduction %s is not selected at the root's first child\n",
                TOSTR(initialReduction));
        assert(false);
        return nullptr;
    }

    return initialReductionPosition;
}

void Decoder::appendSelectedHierarchy(const std::vector<PlanItem>& frontierPlan, std::vector<PlanItem>& hierarchy, const Position& position) const {
    const USignature& selectedOperation = getSelectedOperation(position);
    if (_htn.isAction(selectedOperation)) return;

    if (!_htn.isReduction(selectedOperation)) {
        Log::e("Plan error: Invalid action/reduction id=%i at (%zu,%zu)\n",
                selectedOperation._name_id, position.getCreationIteration(), position.getPositionId());
        assert(false);
        return;
    }

    const Reduction& reduction = _htn.getOpTable().getReduction(selectedOperation);
    int operationVar = _vars.getVariable(VarType::OP, position, selectedOperation);

    const USignature decodedReductionSignature = decodeQConstants(position, selectedOperation);
    if (decodedReductionSignature == Sig::NONE_SIG) {
        Log::e("Plan error: Could not decode reduction %s at (%zu,%zu)\n",
                TOSTR(selectedOperation), position.getCreationIteration(), position.getPositionId());
        assert(false);
        return;
    }
    const Reduction decodedReduction = reduction.substituteRed(Substitution(reduction.getArguments(), decodedReductionSignature._args));

    if (position.getParentPosition() == _root_position || position.getParentPosition() == nullptr) {
        operationVar = 0;
    }

    Log::d("[%i] %s:%s @ (%zu,%zu)\n", operationVar, TOSTR(decodedReduction.getTaskSignature()),
            TOSTR(decodedReductionSignature), position.getCreationIteration(), position.getPositionId());

    hierarchy.emplace_back(operationVar, decodedReduction.getTaskSignature(), decodedReductionSignature, std::vector<int>());
    const size_t hierarchyItemIndex = hierarchy.size() - 1;

    const auto& children = position.getChildrenPositions();
    const size_t numSubtasks = reduction.getSubtasks().size();
    if (children.size() < numSubtasks) {
        Log::e("Plan error: Missing child positions for %s at (%zu,%zu)\n",
                TOSTR(decodedReductionSignature), position.getCreationIteration(), position.getPositionId());
        assert(false);
        return;
    }

    for (size_t childIndex = 0; childIndex < numSubtasks; childIndex++) {
        const Position* childPosition = children[childIndex];
        const USignature& childOperation = getSelectedOperation(*childPosition);
        if (_htn.isAction(childOperation)) {
            const int frontierIndex = findDescendantFrontierIndex(*childPosition);
            if (frontierIndex >= 0) {
                const int actionId = frontierPlan[static_cast<size_t>(frontierIndex)].id;
                hierarchy[hierarchyItemIndex].subtaskIds.push_back(actionId);
                Log::d("    -> [%i] %s\n", actionId, TOSTR(childOperation));
            }
        } else if (_htn.isReduction(childOperation)) {
            const int childId = _vars.getVariable(VarType::OP, *childPosition, childOperation);
            hierarchy[hierarchyItemIndex].subtaskIds.push_back(childId);
            Log::d("    -> [%i] %s\n", childId, TOSTR(childOperation));
            appendSelectedHierarchy(frontierPlan, hierarchy, *childPosition);
        } else {
            Log::e("Plan error: Invalid action/reduction %s at (%zu,%zu)\n",
                    TOSTR(childOperation), childPosition->getCreationIteration(), childPosition->getPositionId());
            assert(false);
        }
    }
}
