#include <cassert>
#include <utility>
#include <vector>

#include "sat/literal_tree.h"

int main() {
    LiteralTree<int> tree;

    tree.insert({2, 4});
    tree.insert({1, 2, 3, 4});
    assert(tree.contains({2, 4}));
    assert(!tree.contains({1, 2, 3, 4}));

    tree.insert({1, 3});
    tree.insert({4});
    assert(tree.contains({4}));
    assert(tree.contains({1, 3}));
    assert(!tree.contains({2, 4}));

    tree.insert({1});
    assert(tree.contains({1}));
    assert(!tree.contains({1, 3}));

    tree.insert({});
    assert(tree.containsEmpty());
    assert(!tree.contains({1}));

    LiteralTree<int> reverseInsertion;
    reverseInsertion.insert({1, 2, 3});
    reverseInsertion.insert({2});
    assert(reverseInsertion.contains({2}));
    assert(!reverseInsertion.contains({1, 2, 3}));

    LiteralTree<int> merged;
    merged.insert({2, 4});
    LiteralTree<int> moreGeneral;
    moreGeneral.insert({4});
    merged.merge(std::move(moreGeneral));
    assert(merged.contains({4}));
    assert(!merged.contains({2, 4}));

    LiteralTree<int> reverseMerged;
    reverseMerged.insert({4});
    LiteralTree<int> moreSpecific;
    moreSpecific.insert({2, 4});
    reverseMerged.merge(std::move(moreSpecific));
    assert(reverseMerged.contains({4}));
    assert(!reverseMerged.contains({2, 4}));

    return 0;
}
