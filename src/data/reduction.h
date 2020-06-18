
#ifndef DOMPASCH_TREE_REXX_REDUCTION_H
#define DOMPASCH_TREE_REXX_REDUCTION_H

#include <vector>
#include <map>

#include "data/htn_op.h"
#include "data/signature.h"

class Reduction : public HtnOp {

private:

    // Coding of the methods' AT's name.
    int _task_name_id;
    // The method's AT's arguments.
    std::vector<int> _task_args;

    // The ordered list of subtasks.
    std::vector<USignature> _subtasks;

public:
    Reduction();
    Reduction(HtnOp& op);
    Reduction(const Reduction& r);
    Reduction(int nameId, const std::vector<int>& args, const USignature& task);

    void orderSubtasks(const std::map<int, std::vector<int>>& orderingNodelist);

    Reduction substituteRed(const FlatHashMap<int, int>& s) const;

    void addSubtask(USignature subtask);
    void setSubtasks(const std::vector<USignature>& subtasks);

    USignature getTaskSignature() const;
    const std::vector<int>& getTaskArguments() const;
    const std::vector<USignature>& getSubtasks() const;

    Reduction& operator=(const Reduction& other);
};

#endif