
#ifndef DOMPASCH_LILOTANE_DECODER_H
#define DOMPASCH_LILOTANE_DECODER_H

#include "data/htn_instance.h"
#include "data/position.h"
#include "sat/sat_interface.h"
#include "sat/variable_provider.h"
#include "data/plan.h"

class Decoder {

private:
    HtnInstance& _htn;
    Position*& _root_position;
    std::vector<Position*>& _leaf_positions;
    SatInterface& _sat;
    VariableProvider& _vars;

public:
    Decoder(HtnInstance& htn, Position*& rootPosition, std::vector<Position*>& leafPositions, SatInterface& sat, VariableProvider& vars) :
        _htn(htn), _root_position(rootPosition), _leaf_positions(leafPositions), _sat(sat), _vars(vars) {}

    enum PlanExtraction {ALL, PRIMITIVE_ONLY};
    std::vector<PlanItem> extractClassicalPlan(PlanExtraction mode = PRIMITIVE_ONLY) {

        //VariableDomain::lock();
        int primitiveNameId = _htn.nameId("__PRIMITIVE___");

        std::vector<PlanItem> plan(_leaf_positions.size());
        for (size_t pos = 0; pos < _leaf_positions.size(); pos++) {
            Position& leaf = *_leaf_positions[pos];

            int chosenActions = 0;
            for (const auto& [sig, aVar] : leaf.getVariableTable(VarType::OP)) {
                if (!_sat.holds(aVar)) continue;

                if (sig._name_id == primitiveNameId) continue;

                USignature aSig = sig;
                if (mode == PRIMITIVE_ONLY && !_htn.isAction(aSig)) continue;

                if (_htn.isActionRepetition(aSig._name_id)) {
                    aSig._name_id = _htn.getActionNameFromRepetition(sig._name_id);
                }

                //log("  %s ?\n", TOSTR(aSig));

                chosenActions++;
                
                Log::d("PLANDBG %i,%i A %s\n", (int) leaf.getLayerIndex(), (int) pos, TOSTR(aSig));

                // Decode q constants
                USignature aDec = getDecodedQOp(leaf, aSig);
                if (aDec == Sig::NONE_SIG) continue;
                plan[pos] = {aVar, aDec, aDec, std::vector<int>()};
            }

            assert(chosenActions <= 1 || Log::e("Plan error: Added %i actions at step %i!\n", chosenActions, pos));
            if (chosenActions == 0) {
                plan[pos] = {-1, USignature(), USignature(), std::vector<int>()};
            }
        }

        return plan;
    }

    Plan extractPlan() {

        auto result = Plan();
        auto& [classicalPlan, plan] = result;
        classicalPlan = extractClassicalPlan();
        Position* hierarchyRoot = getHierarchyRoot();
        if (hierarchyRoot != nullptr) {
            recursiveCreateHierarchy(classicalPlan, plan, *hierarchyRoot);
        }

        return result;
    }

    bool value(VarType type, const Position& pos, const USignature& sig) {
        int v = _vars.getVariable(type, pos, sig);
        Log::d("VAL %s@(%i,%i)=%i %i\n", TOSTR(sig), (int) pos.getLayerIndex(), (int) pos.getPositionIndex(), v, _sat.holds(v));
        return _sat.holds(v);
    }


    USignature getDecodedQOp(const Position& position, const USignature& origSig) const {
        USignature sig = origSig;
        while (true) {
            bool containsQConstants = false;
            for (int arg : sig._args) if (_htn.isQConstant(arg)) {
                // q constant found
                containsQConstants = true;

                int numSubstitutions = 0;
                for (int argSubst : _htn.getDomainOfQConstant(arg)) {
                    const USignature& sigSubst = _vars.sigSubstitute(arg, argSubst);
                    if (_vars.isEncodedSubstitution(sigSubst) && _sat.holds(_vars.varSubstitution(arg, argSubst))) {
                        Log::d("SUBSTVAR [%s/%s] TRUE => %s ~~> ", TOSTR(arg), TOSTR(argSubst), TOSTR(sig));
                        numSubstitutions++;
                        Substitution sub;
                        sub[arg] = argSubst;
                        sig.apply(sub);
                        Log::d("%s\n", TOSTR(sig));
                    } else {
                        //Log::d("%i FALSE\n", varSubstitution(sigSubst));
                    }
                }

                if (numSubstitutions == 0) {
                    Log::v("(%i,%i) No substitutions for arg %s of %s\n", (int) position.getLayerIndex(), (int) position.getPositionIndex(), TOSTR(arg), TOSTR(origSig));
                    return Sig::NONE_SIG;
                }
                assert(numSubstitutions == 1 || Log::e("%i substitutions for arg %s of %s\n", numSubstitutions, TOSTR(arg), TOSTR(origSig)));
            }

            if (!containsQConstants) break; // done
        }

        //if (origSig != sig) Log::d("%s ~~> %s\n", TOSTR(origSig), TOSTR(sig));
        
        return sig;
    }

    const USignature& getOpTrue(const Position& position) const {
        for (const auto& [s, v] : position.getVariableTable(VarType::OP)) {
            if (_sat.holds(v) &&  !(s._name_id == _htn.nameId("__PRIMITIVE___"))) {
                return s;
            }
        }
        return Sig::NONE_SIG;
    }

    int findLeafIndex(const Position& node) const {
        for (size_t idx = 0; idx < _leaf_positions.size(); idx++) {
            if (_leaf_positions[idx] == &node) {
                return idx;
            }
        }
        return -1;
    }

    Position* getHierarchyRoot() const {
        if (_root_position == nullptr) {
            return nullptr;
        }
        for (Position* child : _root_position->getChildrenPositions()) {
            const USignature& op = getOpTrue(*child);
            if (_htn.isReduction(op)) {
                return child;
            }
        }
        if (_root_position->getChildrenPositions().empty()) {
            return nullptr;
        }
        return _root_position->getChildrenPositions().front();
    }

    int findFinalLeafIndex(const Position& node) const {
        const Position* current = &node;
        while (current != nullptr) {
            int leafIndex = findLeafIndex(*current);
            if (leafIndex >= 0) {
                return leafIndex;
            }
            const auto& children = current->getChildrenPositions();
            if (children.empty()) {
                return -1;
            }
            current = children.front();
        }
        return -1;
    }

    void recursiveCreateHierarchy(std::vector<PlanItem>& classicalPlan, std::vector<PlanItem>& hierarchy, Position& position) {

        const USignature& actionOrReductionTrue = getOpTrue(position);

        // If this is a method, add it into the hirerarchy + add id of all its subtasks and launch the recursion for each subtask
        if (_htn.isAction(actionOrReductionTrue)) {
            return;
        } else if (_htn.isReduction(actionOrReductionTrue)) {
            const Reduction& r = _htn.getOpTable().getReduction(actionOrReductionTrue);

            int v = _vars.getVariable(VarType::OP, position, actionOrReductionTrue);

            USignature decRSig = getDecodedQOp(position, actionOrReductionTrue);
            if (decRSig == Sig::NONE_SIG)  {
                assert(false);
            }

            Reduction rDecoded = r.substituteRed(Substitution(r.getArguments(), decRSig._args));

            if (position.getParentPosition() == _root_position || position.getParentPosition() == nullptr) {
                v = 0; // Set the id to 0 for the root
            }

            Log::d("[%i] %s:%s @ (%i,%i)\n", v, TOSTR(rDecoded.getTaskSignature()), TOSTR(decRSig), (int) position.getLayerIndex(), (int) position.getPositionIndex());

            hierarchy.push_back(PlanItem(v, rDecoded.getTaskSignature(), decRSig, std::vector<int>()));
            size_t itemIndex = hierarchy.size() - 1;

            const auto& children = position.getChildrenPositions();
            size_t numSubtasks = r.getSubtasks().size();
            assert(children.size() >= numSubtasks || Log::e("Plan error: Missing child positions for %s at %i,%i!\n",
                    TOSTR(decRSig), (int) position.getLayerIndex(), (int) position.getPositionIndex()));

            for (size_t childIdx = 0; childIdx < numSubtasks && childIdx < children.size(); childIdx++) {
                Position* childPosition = children[childIdx];
                const USignature& nextActionOrReductionTrue = getOpTrue(*childPosition);
                if (_htn.isAction(nextActionOrReductionTrue)) {
                    int leafIndex = findFinalLeafIndex(*childPosition);
                    if (leafIndex >= 0) {
                        int actionId = classicalPlan[leafIndex].id;
                        hierarchy[itemIndex].subtaskIds.push_back(actionId);
                        Log::d("    -> [%i] %s\n", actionId, TOSTR(nextActionOrReductionTrue));
                    }
                } else if (_htn.isReduction(nextActionOrReductionTrue)) {
                    int childId = _vars.getVariable(VarType::OP, *childPosition, nextActionOrReductionTrue);
                    hierarchy[itemIndex].subtaskIds.push_back(childId);
                    Log::d("    -> [%i] %s\n", childId, TOSTR(nextActionOrReductionTrue));
                    recursiveCreateHierarchy(classicalPlan, hierarchy, *childPosition);
                } else {
                    assert(false || Log::e("Plan error: Invalid action/reduction %s at %i,%i!\n", TOSTR(nextActionOrReductionTrue), (int) childPosition->getLayerIndex(), (int) childPosition->getPositionIndex()));
                }
            }

        } else {
            Log::e("Plan error: Invalid action/reduction id=%i at %i,%i!\n", actionOrReductionTrue._name_id, (int) position.getLayerIndex(), (int) position.getPositionIndex());
            assert(actionOrReductionTrue._name_id != -1);
        }
    }
};

#endif
