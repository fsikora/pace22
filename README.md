# PACE22
[PACE 2022](https://pacechallenge.org/2022/) Heuristic solver for DFVS 

To compile :
```make```

To run :
```./pace < instancename```
   
Uses [SNAP](snap.stanford.edu/) for graph management.

Author : Florian Sikora (LAMSADE, U Dauphine, 2022)

It uses extensive Reduction Rules to reduce the input graph and then use some local search with a simulated annealing strategy. See [description solver](description.pdf).