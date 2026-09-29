#include <algorithm>
#include <random>
#include <set>
#include <stdexcept>
#include <utility>
#include <vector>

#include "sat/literal_tree.h"

static void check(bool condition) {
    if (!condition) throw std::runtime_error("Literal-tree regression failed");
}

static void sameEncoding(const LiteralTree<int>& left, const LiteralTree<int>& right) {
    check(left.encode() == right.encode());
    check(left.encodeNegation() == right.encodeNegation());
    check(left.getEncodingLiteralCount() == right.getEncodingLiteralCount());
    check(left.getNegationEncodingLiteralCount() == right.getNegationEncodingLiteralCount());
}

static bool isSubsequence(const std::vector<int>& shorter, const std::vector<int>& longer) {
    size_t matched = 0;
    for (int literal : longer) {
        if (matched < shorter.size() && shorter[matched] == literal) ++matched;
    }
    return matched == shorter.size();
}

int main() {
    LiteralTree<int> tree;

    tree.insert({2, 4});
    tree.insert({1, 2, 3, 4});
    check(tree.contains({2, 4}));
    check(!tree.contains({1, 2, 3, 4}));

    tree.insert({1, 3});
    tree.insert({4});
    check(tree.contains({4}));
    check(tree.contains({1, 3}));
    check(!tree.contains({2, 4}));

    tree.insert({1});
    check(tree.contains({1}));
    check(!tree.contains({1, 3}));

    tree.insert({});
    check(tree.containsEmpty());
    check(!tree.contains({1}));

    LiteralTree<int> reverseInsertion;
    reverseInsertion.insert({1, 2, 3});
    reverseInsertion.insert({2});
    check(reverseInsertion.contains({2}));
    check(!reverseInsertion.contains({1, 2, 3}));

    LiteralTree<int> merged;
    merged.insert({2, 4});
    LiteralTree<int> moreGeneral;
    moreGeneral.insert({4});
    merged.merge(std::move(moreGeneral));
    check(merged.contains({4}));
    check(!merged.contains({2, 4}));

    LiteralTree<int> reverseMerged;
    reverseMerged.insert({4});
    LiteralTree<int> moreSpecific;
    moreSpecific.insert({2, 4});
    reverseMerged.merge(std::move(moreSpecific));
    check(reverseMerged.contains({4}));
    check(!reverseMerged.contains({2, 4}));

    // A duplicate must preserve the exact trie and both encodings.
    LiteralTree<int> uniform;
    uniform.insert({1, 2, 3});
    uniform.insert({1, 2, 4});
    const auto beforeDuplicate = uniform;
    uniform.insert({1, 2, 3});
    sameEncoding(uniform, beforeDuplicate);

    // Copy/move assignment overwrites metadata as well as the owned nodes.
    LiteralTree<int> copy(uniform), assigned;
    assigned.insert({9});
    assigned = uniform;
    LiteralTree<int> moved(std::move(copy)), moveAssigned;
    moveAssigned.insert({8});
    moveAssigned = std::move(assigned);
    sameEncoding(uniform, moved);
    sameEncoding(uniform, moveAssigned);
    for (auto* tree : {&moved, &moveAssigned}) {
        tree->insert({2});
        check(tree->contains({2}));
        check(!tree->contains({1, 2, 3}));
        check(!tree->contains({1, 2, 4}));
    }
    // Moved-from trees can be reused at a different length.
    copy.insert({5});
    assigned.insert({6, 7});
    check(copy.contains({5}) && assigned.contains({6, 7}));
    uniform = uniform;
    uniform = std::move(uniform);
    sameEncoding(uniform, beforeDuplicate);

    // Empty-target merge must transfer the length information too.
    LiteralTree<int> emptyTarget, source(beforeDuplicate);
    emptyTarget.merge(std::move(source));
    emptyTarget.insert({3});
    check(!emptyTarget.contains({1, 2, 3}));
    check(emptyTarget.contains({1, 2, 4}));
    source.insert({9, 10});
    check(source.contains({9, 10}));
    emptyTarget.merge(std::move(emptyTarget));
    check(emptyTarget.contains({3}));

    LiteralTree<int> emptyPath;
    emptyPath.insert({});
    emptyPath.insert({});
    emptyPath.insert({1, 2});
    check(emptyPath.containsEmpty() && !emptyPath.contains({1, 2}));

    // Intersection leaves an unfinished {1} branch. The next general insert
    // removes it; a fast insert here would incorrectly retain its CNF clauses.
    LiteralTree<int> intersection, other;
    intersection.insert({1, 2});
    other.insert({1, 3});
    intersection.intersect(std::move(other));
    auto intersectionCopy = intersection;
    auto intersectionMoved = std::move(intersectionCopy);
    for (auto* tree : {&intersection, &intersectionMoved}) {
        tree->insert({4, 5});
        LiteralTree<int> expected;
        expected.insert({4, 5});
        sameEncoding(*tree, expected);
    }
    other.insert({8});
    check(other.contains({8}));

    // An independent antichain oracle checks same-length insertions and the
    // transition to general subsequence minimization, including repeated items.
    std::mt19937 random(62);
    for (int trial = 0; trial < 100; ++trial) {
        LiteralTree<int> actual;
        std::set<std::vector<int>> minimal;
        std::vector<std::vector<int>> inserted;
        for (int step = 0; step < 100; ++step) {
            const size_t length = step < 75 ? 3 : random() % 6;
            std::vector<int> path(length);
            for (int& literal : path) literal = 1 + random() % 6;
            inserted.push_back(path);
            const bool redundant = std::any_of(minimal.begin(), minimal.end(),
                [&](const auto& stored) { return isSubsequence(stored, path); });
            if (!redundant) {
                for (auto it = minimal.begin(); it != minimal.end();) {
                    if (isSubsequence(path, *it)) it = minimal.erase(it);
                    else ++it;
                }
                minimal.insert(path);
            }
            actual.insert(path);
            for (const auto& query : inserted) {
                check(actual.contains(query) == minimal.count(query));
                check(actual.hasPathSubsumedBy(query) == std::any_of(minimal.begin(), minimal.end(),
                    [&](const auto& stored) { return isSubsequence(stored, query); }));
                check(actual.subsumes(query) == std::any_of(minimal.begin(), minimal.end(),
                    [&](const auto& stored) { return isSubsequence(query, stored); }));
            }
        }
    }

    return 0;
}
