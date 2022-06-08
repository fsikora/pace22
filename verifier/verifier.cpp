#include <fstream>
#include <iostream>
#include <sstream>
#include <vector>
#include <queue>
#include "graph.h"

namespace {
	using fvs::Graph;
}

Graph readGraph(const std::string& filename) {
  std::string line;

  // open file for reading
  std::ifstream in(filename.c_str());
  if (!in) {
    std::cerr << "Error opening " << filename << std::endl;
    std::exit(-1);
  }

  std::getline(in,line);
  //skip comments
  while( line[0] == '%' ) {
    std::getline(in, line);
  }

  int N, M, ew;
  std::stringstream ss(line);
  ss >> N >> M >> ew;
  Graph graph(N);

  bool node_weights = false;
  bool edge_weights = false;
  if( ew == 11 ) {
    node_weights = true;
    edge_weights = true;
  } else if ( ew == 10) {
    node_weights = true;
  } else if ( ew == 1 ) {
    edge_weights = true;
  }

  long source = 0;
  long node_weight = 0;
  while( std::getline(in, line) ) {

    if (line[0] == '%') { // a comment in the file
      continue;
    }

    std::stringstream ss(line);
    if( node_weights ) {
      ss >> node_weight;
    } else {
      node_weight = 0;
    }

    long target;
    while( ss >> target ) {
      long edge_weight = 1;
      if( edge_weights ) {
        ss >> edge_weight;
      }
      --target;
      graph.addEdge(source, target);
      ++M;
    }
    if(in.eof()) {
      break;
    }
    source++;
  }
  return graph;
}

bool isAcyclic(const Graph& graph, const std::vector<bool>& fvs) {
  int fvs_size = 0;
  for ( size_t i = 0; i < fvs.size(); ++i ) {
    fvs_size += fvs[i];
  }

  std::vector<int> in_degree(graph.numNodes(), 0);
  for ( int u = 0; u < graph.numNodes(); ++u ) {
    if ( !fvs[u] ) {
      for ( const int v : graph.neighbors(u) ) {
        ++in_degree[v];
      }
    }
  }

  std::queue<int> q;
  for ( int u = 0; u < graph.numNodes(); ++u ) {
    if ( !fvs[u] && in_degree[u] == 0 ) {
      q.push(u);
    }
  }

  int visited_nodes = 0;
  while ( !q.empty() ) {
    int u = q.front();
    q.pop();
    ++visited_nodes;

    for ( const int v : graph.neighbors(u) ) {
      --in_degree[v];
      if ( !fvs[v] && in_degree[v] == 0 ) {
        q.push(v);
      }
    }
  }

  return visited_nodes == (graph.numNodes() - fvs_size);
}

std::vector<bool> readSolution(const int num_nodes,
                               const std::string& filename) {
  std::vector<bool> fvs(num_nodes, false);

  std::string line;

  // open file for reading
  std::ifstream in(filename.c_str());
  if (!in) {
    std::cerr << "Error opening " << filename << std::endl;
    std::exit(-1);
  }

  while( std::getline(in, line) ) {

    std::stringstream ss(line);
    long u;
    ss >> u;

    if ( u > num_nodes ) {
      std::cerr << "Invalid node in solution ( Node = " << u << " )" << std::endl;
      std::exit(-1);
    }

    if ( !ss.eof() ) {
      std::cerr << "Line contains more than one node ( Line = '" << line << "'" << std::endl;
      std::exit(-1);
    }

    if ( fvs[u - 1] ) {
      std::cerr << "Node " << u << " is contained multiple times in solution" << std::endl;
      std::exit(-1);
    }

    fvs[--u] = true;

    if(in.eof()) {
      break;
    }
  }

  return fvs;
}

int main(int argc, char** argv)
{
	if (argc < 2) {
		std::cerr << "usage: verifer [graph file] [solution file]" << std::endl;
		return -1;
	}

  const std::string graph_filename(argv[1]);
  const std::string sol_filename(argv[2]);
  const Graph graph = readGraph(graph_filename);
  const std::vector<bool> fvs = readSolution(graph.numNodes(), sol_filename);

  if ( isAcyclic(graph, fvs) ) {
    std::cout << "OK" << std::endl;
  } else {
    std::cerr << "Feedback vertex set does not induce an acyclic subgraph" << std::endl;
    std::exit(-1);
  }

	return 0;
}
