This is a repository collecting some basic algorithms I implemented in scheme, mostly for self-learning.

The implementations in this repository are not supposed to be efficient.


## List of algorithms implemented so far


### Prim's algorithm
This is a classical algorithm for computing minimum spanning trees in a weighted graph.
My implementation is in `weighted-graph.rkt` (the function `minimum-tree-prim`).

The code could be simpler to read if I used a less general priority queue implementation.
Now the queue stores a weight-element pair as a list of `(cons weight element)`, but it could be rewritten using the fact that in Prim's algorithm the priority of each edge is just its weight.
This would replace a few `caar` and `cadr` calls with `(edge-w (car queue))` and `car` respectively.

### Kruskal's algorithm
The implementation is in `weighted-graph.rkt` (the function `minimum-tree-kruskal`).
I think this implementation is quite simple, easier to understand than `minimum-tree-prim`.

