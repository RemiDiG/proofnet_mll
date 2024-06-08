# MLL Proof nets for Yalla - Some implementation choices

We describe here some non-trivial implementation choices made in this library.
We would like to thank **Damien Pous** for advices about how to use his graph library as well as discussions about implementation.

## About *base_graph*
The current implementation is a graph with:
- rules on vertices (given by *vlabel*)
- formulas on edges (given by *flabel*)
- booleans saying for each edge if it is a left one (given by *llabel*)
A propriety then asks that that non parr/tens vertices have their in-edges to be left one, for canonicity.

Previous choices were:
- a *direction: bool -> parr/tens vertices -> edge* on the graph, giving for each parr/tens-vertex its left and right edges
&rarr; the dependant types made everything arkward, starting from the definition
- a *direction: bool -> vertices -> edge* on the graph, giving for each vertex its left and right edges, and with bogus values for axiom, cut and conclusion vertices
&rarr; giving a valid bogus value was sometimes non-trivial when modifying a proof net, which complexified artificially some proofs
- a *left: vertices -> edge* on the graph, giving for each parr/tens-vertex its left edge, as the right ones can be deduced from there
&rarr the above problems still hold
-  a *left: vertices -> option edge* on the graph, giving for each parr/tens-vertex its left edge, and for other vertices None
&rarr this solves the previous problems, however manipulating option type here became heavy quickly

## About the properties *proper*
These local properties are used to check if a *base_graph* is a proof structure.
They allow to define *left*, *right*, ...
We chose not to use *left* to define these properties instead, as this would need to define some pseudo-left first, and prove this fonction has good properties, which would complexify the code.

## About the correctness criterion
We define it with a special notion of paths, giving colors to edges. This allows to consider only one graph, the one of the proof net, and not the so-called correctness graphs. This way we do not need to prove, for instance, that the correctness graphe of a graph where we remove a vertex is the correctness graph of the original graph, without the corresponding vertex.

## About *uconnected*
We define connectivity by *forall (x y : G), exists (_ : Supath f x y), true* and not *forall (x y : G), Supath f x y*, so as to be in Prop instead of Type.
This has two advantages:
- we can define properties such as tree <-> uacyclic /\ uconnected
- this allows case analysis when proving connectivity (this point being a weak argument, as it is easy to define a lemma to prove the Type version from the Prop one)

## About *order*
The current implementation is a list of nodes, that is asked to contain exactly each conclusion vertex once.

Previous choices were:
- an injective function associating to each conclusion vertex an ordinal (we tried *conclusion -> I_#|conclusions|* , *I_#|conclusions| -> conclusion* and *conclusion -> int*)
&rarr  the dependant types were hard to manipulate, and it was even worse for the ordinals; furthermore checking injectivity to define a new graph was heavy
- a permutation of the conclusion vertices
&rarr  still hard to manipulate, and we need to do it often

## About *add_node*
The current implementation is a general definition, with some useless cases to take into account, generalising adding a tens, parr or cut.
This was simplier that transporting proofs everywhere.
