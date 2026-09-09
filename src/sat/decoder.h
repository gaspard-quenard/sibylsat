#ifndef DOMPASCH_LILOTANE_DECODER_H
#define DOMPASCH_LILOTANE_DECODER_H

#include <optional>

#include "data/htn_instance.h"
#include "algo/q_constant_manager.h"
#include "data/plan.h"
#include "data/position.h"
#include "sat/sat_interface.h"
#include "sat/variable_provider.h"

class Decoder {
private:
    HtnInstance& _htn;
    const QConstantManager& _q_constants;
    Position*& _root_position;
    std::vector<Position*>& _leaf_positions;
    SatInterface& _sat;
    VariableProvider& _vars;

    const USignature& getSelectedOperation(const Position& position) const;
    std::optional<int> getSelectedQConstantValue(int qConstant) const;
    USignature decodeQConstants(const Position& position, const USignature& signature) const;

    int findFrontierIndex(const Position& position) const;
    int findDescendantFrontierIndex(const Position& position) const;
    const Position* findSelectedInitialReduction() const;

    /**
     * Recursively reconstruct the selected decomposition tree
     * solution rooted in the initial reduction position. Each selected reduction is appended to the hierarchy with the
     * IDs of its subtasks. Reduction subtasks are decoded recursively, while
     * action subtasks are linked to their corresponding items in frontierPlan.
     */
    void appendSelectedHierarchy(const std::vector<PlanItem>& frontierPlan, std::vector<PlanItem>& hierarchy, const Position& position) const;

public:
    enum class FrontierPlanMode {
        PrimitiveActionsOnly,
        AllSelectedOperations
    };

    Decoder(HtnInstance& htn, const QConstantManager& qConstants, Position*& rootPosition, std::vector<Position*>& leafPositions, SatInterface& sat, VariableProvider& vars);

    std::vector<PlanItem> extractFrontierPlan(FrontierPlanMode mode = FrontierPlanMode::PrimitiveActionsOnly) const;
    Plan extractPlan() const;

    USignature getSelectedDecodedOperation(const Position& position) const;

    /**
     * Collect true operation and fact variables before the given frontier
     * index. Ancestor variables are included because carried positions may
     * reuse variables created in earlier tree nodes.
     */
    NodeHashSet<int> collectTrueVariablesBeforeFrontierIndex(size_t frontierEnd) const;
};

#endif
