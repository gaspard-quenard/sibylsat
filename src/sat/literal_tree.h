
#ifndef DOMPASCH_LILOTANE_LITERAL_TREE_H
#define DOMPASCH_LILOTANE_LITERAL_TREE_H

#include <type_traits>
#include <utility>
#include <vector>

#include "util/hashmap.h"

/** Store a set of ordered literal sequences as paths in a prefix tree. */
template <typename T, typename THash = robin_hood::hash<T>>
class LiteralTree {
    struct Node {

        FlatHashMap<T, Node*, THash> children;
        bool validLeaf = false;

        Node() = default;
        Node(const Node& other) : validLeaf(other.validLeaf) {
            for (const auto& [key, child] : other.children) {
                children[key] = new Node(*child);
            }
        }
        Node(Node&& other) : children(std::move(other.children)), validLeaf(other.validLeaf) {
            other.children.clear();
            other.validLeaf = false;
        }

        Node& operator=(const Node& other) {
            if (this == &other) return *this;
            Node copy(other);
            children.swap(copy.children);
            std::swap(validLeaf, copy.validLeaf);
            return *this;
        }

        Node& operator=(Node&& other) noexcept {
            if (this == &other) return *this;
            clear();
            children = std::move(other.children);
            validLeaf = other.validLeaf;
            other.children.clear();
            other.validLeaf = false;
            return *this;
        }

        void clear() {
            for (const auto& [lit, child] : children) {
                (void) lit;
                delete child;
            }
            children.clear();
            validLeaf = false;
        }

        ~Node() { clear(); }
        
        void insertUnchecked(const std::vector<T>& lits, size_t idx) {
            if (idx == lits.size()) {
                validLeaf = true;
                return;
            }
            auto it = children.find(lits[idx]);
            Node* child;
            if (it == children.end()) {
                child = new Node(); // insert child
                children[lits[idx]] = child;
            } else child = it->second;
            // recursion
            child->insertUnchecked(lits, idx+1);
        }

        bool contains(const std::vector<T>& lits, size_t idx) const {
            if (idx == lits.size()) return validLeaf;
            auto it = children.find(lits[idx]);
            if (it == children.end()) return false;
            return it->second->contains(lits, idx+1);
        }

        /*
        Returns true if the tree has a path of which <lits> is a subpath.
        */
        bool subsumes(const std::vector<T>& lits, size_t idx) const {

            // No literals left in the given path?
            if (idx == lits.size()) {
                if (validLeaf) return true;
                // If any (transitive) child is a valid leaf, return true
                for (auto& [key, child] : children) {
                    (void) key;
                    if (child->subsumes(lits, idx)) return true;
                }
                return false;
            }

            // Valid child node according to next literal present?
            auto it = children.find(lits[idx]);
            if (it != children.end()) {
                // Yes: check if it subsumes the remaining path
                if (it->second->subsumes(lits, idx+1)) return true;
            }

            // No valid child node:
            // Any (transitive) child must subsume the same path
            for (auto& [key, child] : children) {
                (void) key;
                if (child->subsumes(lits, idx)) return true;
            }
            return false;
        }

        /*
        Returns true if the tree has a path which is a sub-path of <lits>.
        */
        bool hasPathSubsumedBy(const std::vector<T>& lits, size_t idx) const {
            // Reaching a stored leaf means that all of its literals were found,
            // even if the queried path contains additional literals.
            if (validLeaf) return true;

            for (size_t i = idx; i < lits.size(); i++) {
                auto child = children.find(lits[i]);
                if (child != children.end() && child->second->hasPathSubsumedBy(lits, i + 1)) {
                    return true;
                }
            }
            return false;
        }

        bool removePathsSubsumedBy(const std::vector<T>& lits, size_t idx) {
            if (idx == lits.size()) {
                clear();
                return true;
            }

            std::vector<T> keysToRemove;
            for (auto& [key, child] : children) {
                const size_t nextIdx = key == lits[idx] ? idx + 1 : idx;
                if (child->removePathsSubsumedBy(lits, nextIdx)) {
                    delete child;
                    keysToRemove.push_back(key);
                }
            }
            for (const T& key : keysToRemove) children.erase(key);
            return !validLeaf && children.empty();
        }

        template<typename Visitor>
        void visitPaths(std::vector<T>& path, Visitor& visitor) const {
            if (validLeaf) visitor(path);
            for (const auto& [literal, child] : children) {
                path.push_back(literal);
                child->visitPaths(path, visitor);
                path.pop_back();
            }
        }

        std::pair<size_t, size_t> getEncodingDimensions() const {
            std::pair<size_t, size_t> result;
            if (validLeaf) return result;
            auto& [cls, lits] = result;
            cls = 1;
            lits = children.size();
            for (const auto& [lit, child] : children) {
                auto [cCls, cLits] = child->getEncodingDimensions();
                cls += cCls;
                lits += cLits + cCls;
            }
            return result;
        }
        void encode(std::vector<std::vector<T>>& cls, std::vector<T>& path) const {
            if (validLeaf) return;

            // orClause: IF the current path, THEN either of the children.
            int pathSize = path.size();
            std::vector<T> orClause(pathSize + children.size());
            size_t i = 0;
            for (; i < path.size(); i++) {
                if constexpr (std::is_arithmetic<T>()) orClause[i] = -path[i];
                else if constexpr (std::is_same<T, std::pair<int, int>>::value) {
                    orClause[i] = std::pair<int, int>{-path[i].first, path[i].second};
                } else orClause[i] = path[i];
            }
            for (const auto& [lit, child] : children) {
                orClause[i++] = lit;
                path.resize(pathSize+1);
                path.back() = lit;
                child->encode(cls, path);
            }
            cls.push_back(std::move(orClause));
        }

        std::pair<size_t, size_t> getNegationEncodingDimensions() const {
            std::pair<size_t, size_t> result;
            if (validLeaf) return result;
            auto& [cls, lits] = result;
            cls = 0;
            lits = 0;
            for (const auto& [lit, child] : children) {
                if (child->validLeaf) { 
                    cls++;
                    lits++;
                } else {
                    auto [cCls, cLits] = child->getNegationEncodingDimensions();
                    cls += cCls;
                    lits += cLits + cCls;
                }
            }
            return result;
        }
        void encodeNegation(std::vector<std::vector<T>>& cls, std::vector<T>& path) const {
            if (validLeaf) return;

            size_t pathSize = path.size();
            std::vector<T> clause(pathSize + 1);
            for (size_t i = 0; i < pathSize; i++) {
                if constexpr (std::is_arithmetic<T>()) clause[i] = -path[i];
                else clause[i] = path[i];
            }
            // For each child that is a valid leaf, encode the negated path to it
            for (const auto& [lit, child] : children) if (child->validLeaf) {
                if constexpr (std::is_arithmetic<T>()) clause[pathSize] = -lit;
                else clause[pathSize] = lit;
                cls.push_back(clause);
            }

            // For all other children, encode recursively
            for (const auto& [lit, child] : children) if (!child->validLeaf) {
                path.resize(pathSize+1);
                path.back() = lit;
                child->encodeNegation(cls, path);
            }
        }

    };

    Node _root;

public:

    LiteralTree() = default;
    LiteralTree(const LiteralTree& other) : _root(other._root) {}
    LiteralTree(LiteralTree&& other) : _root(std::move(other._root)) {}

    LiteralTree& operator=(LiteralTree<T, THash>&& other) noexcept {
        _root = std::move(other._root);
        return *this;
    }

    LiteralTree& operator=(const LiteralTree<T, THash>& other) {
        _root = other._root;
        return *this;
    }

    /**
     * Insert a path while retaining only subset-minimal paths.
     *
     * These paths can represent alternative conjunctions. If an existing path
     * is a subset of the new one, the new alternative is redundant. Conversely,
     * the new path replaces every existing superset because A OR (A AND B) is A.
     * Maintaining that invariant here also keeps the tree's structural CNF
     * encoding from imposing constraints belonging only to a redundant branch.
     */
    void insert(const std::vector<T>& lits) {
        if (_root.hasPathSubsumedBy(lits, 0)) return;
        _root.removePathsSubsumedBy(lits, 0);
        _root.insertUnchecked(lits, 0);
    }

    void merge(LiteralTree<T, THash>&& other) {
        if (this == &other) return;
        if (!_root.validLeaf && _root.children.empty()) {
            _root = std::move(other._root);
            return;
        }

        std::vector<T> path;
        auto insertPath = [this](const std::vector<T>& otherPath) { insert(otherPath); };
        other._root.visitPaths(path, insertPath);
    }

    void intersect(LiteralTree<T, THash>&& other) {
        std::vector<std::pair<Node*, Node*>> nodeStack;
        nodeStack.emplace_back(&_root, &other._root);
        while (!nodeStack.empty()) {
            auto [node, otherNode] = nodeStack.back();
            nodeStack.pop_back();
            node->validLeaf = node->validLeaf && otherNode->validLeaf;
            std::vector<T> keysToRemove;
            for (auto& [key, val] : node->children) {
                if (!otherNode->children.count(key)) {
                    // Not contained in both: remove!
                    delete val;
                    keysToRemove.push_back(key);
                } else {
                    // Contained in both: Check children
                    nodeStack.emplace_back(val, otherNode->children.at(key));
                }
            }
            for (auto& key : keysToRemove) node->children.erase(key);
            for (auto& [key, child] : otherNode->children) {
                if (!node->children.count(key)) delete child;
            }
            otherNode->children.clear();
            if (node != &_root) delete otherNode;
        }
    }

    size_t getEncodingLiteralCount() const {
        return _root.getEncodingDimensions().second;
    }
    size_t getNegationEncodingLiteralCount() const {
        return _root.getNegationEncodingDimensions().second;
    }

    bool contains(const std::vector<T>& lits) const {
        return _root.contains(lits, 0);
    }

    bool subsumes(const std::vector<T>& lits) const {
        return _root.subsumes(lits, 0);
    }

    bool hasPathSubsumedBy(const std::vector<T>& lits) const {
        return _root.hasPathSubsumedBy(lits, 0);
    }

    bool containsEmpty() const {
        return _root.validLeaf;
    }

    std::vector<std::vector<T>> encode(std::vector<T> headLits = std::vector<T>()) const {
        std::vector<std::vector<T>> cls;
        _root.encode(cls, headLits);
        return cls;
    }

    std::vector<std::vector<T>> encodeNegation(std::vector<T> headLits = std::vector<T>()) const {
        std::vector<std::vector<T>> cls;
        _root.encodeNegation(cls, headLits);
        return cls;
    }

};


#endif
