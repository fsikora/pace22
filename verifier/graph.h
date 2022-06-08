#pragma once

#include <vector>

namespace fvs {

template<typename IteratorT>
class IteratorRange {
 public:
  IteratorRange(const IteratorT& first, const IteratorT& firstInvalid) :
    __begin(first),
    __end(firstInvalid) { }

  using Iterator = IteratorT; // make publicly visible

  IteratorT begin() {
    return __begin;
  }

  IteratorT end() {
    return __end;
  }

  bool empty() {
    return __begin == __end;
  }

 private:
  IteratorT __begin, __end;
};

class Graph
{

  using NeighborIterator = typename std::vector<int>::const_iterator;
  using NeighborRange = IteratorRange<NeighborIterator>;

 public:
  explicit Graph(int n) :
    _num_nodes(n),
    _num_edges(0),
    _adj_list(n) { }

  int numNodes() const {
    return _num_nodes;
  }

  int numEdges() const {
    return _num_edges;
  }

  NeighborRange neighbors(const int u) const {
    return NeighborRange(
      _adj_list[u].cbegin(), _adj_list[u].cend());
  }

  void addEdge(const int u, const int v) {
    _adj_list[u].push_back(v);
    ++_num_edges;
  }

 private:
  int _num_nodes;
  int _num_edges;
  std::vector<std::vector<int>> _adj_list;
};

} // namespace fvs
