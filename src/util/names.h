
#ifndef DOMPASCH_TREE_REXX_NAMES_H
#define DOMPASCH_TREE_REXX_NAMES_H

#include <string>

#include "data/signature.h"
#include "data/action.h"

#define TOSTR(x) Names::to_string(x).c_str()

namespace Names {
    void init(NodeHashMap<int, std::string>& nameBackTable);
    std::string to_string(int nameId);
    std::string to_string(const std::vector<int>& nameIds);
    std::string to_string(const USignature& sig);
    std::string to_string(const Signature& sig);
    std::string to_string_nobrackets(const USignature& sig);
    std::string to_string(const FlatHashMap<int, int>& s);
    std::string to_string(const Action& a);
}

#endif