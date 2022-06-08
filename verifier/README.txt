To compile this verifier for Feedback Vertex Set execute "make all" in the command line.
Afterwards, there is an executable "verifier". The verifier expects
as first argument a path to graph file in the following format:

https://pacechallenge.org/2022/tracks/#input-format

The second argument is expected to be a path to a solution file
containing a list of nodes in the following format:

https://pacechallenge.org/2022/tracks/#output-format

The verifier checks whether the subgraph induced by removing all nodes in the feedback vertex set is acyclic. The verifier does not check for optimality.
