# MLL Proof nets for Yalla

Formalization of linear logic proof-nets for multiplicative linear logic in the spirit of the [Yalla library](https://perso.ens-lyon.fr/olivier.laurent/yalla/).

Requires:
- [OLlibs](https://github.com/olaure01/ollibs) (add-ons for the standard library): [see installation instructions](https://github.com/olaure01/ollibs/blob/master/README.md).
- [Graph Theory](https://github.com/coq-community/graph-theory) (library for graphs): [see installation instructions](https://github.com/coq-community/graph-theory/blob/master/README.md).
- [Mczify](https://github.com/math-comp/mczify) (lia for MathComp): [see installation instructions](https://github.com/math-comp/mczify/blob/master/README.md).

Tested with Coq 8.20.0, MathComp 2.2.0, Ollibs 2.0.7, Graph Theory 0.9.5, Mczify 1.5.0+2.0+8.16.

Organization of the code (by dependency):
- **mll_prelim.v** general results, with no relation to linear logic;
- **graph_more.v** some general lemmas about GraphTheory;
- **upath.v** development of part of GraphTheory, with undirected paths in a multigraph;
- **supath.v** development of part of GraphTheory, with undirected edge-simple paths in a multigraph;
- **simple_upath.v** development of part of GraphTheory, with undirected vertex-simple paths in a multigraph;
- **graph_uconnected_nb.v** proof that an acyclic graph has for number of connected components its number of vertices minus its number of edges, generalized to our notion of f-paths;
- **mgraph_dag.v** development of part of GraphTheory, about directed acyclic multigraph;
- **mgraph_tree.v** proof that in an acyclic graph, there is at most one simple path between two vertices;
- **yeo.v** proof of one of our generalizations of Yeo theorem;
- **mll_def.v** definition of proof-nets, with its intermediate definitions, along basic results and reformulations;
- **mll_basic.v** general results following from the definition of a proof-net;
- **mll_correct.v** defines some basic graph operations and proves they respect the correctness criterion;
- **mll_seq_to_pn.v** definition of the desequentialization function, proof it produces proof-nets, and that each step respects isomorphisms (for instance, taking two isomorphic graphs and adding a ⅋-vertex between isomorphic edges yield isomorphic graphs) - the latter being used for sequentialization;
- **mll_pn_to_seq_def.v** definition of a sequentializing vertex as the inverse of desequentializing;
- **mll_pn_to_seq.v** proof that a proof-net contains a terminal splitting vertex, using Yeo theorem;
- **mll_pn_to_seq_ax.v** a terminal ax-vertex is sequentializing;
- **mll_pn_to_seq_cut.v** a splitting cut-vertex is sequentializing;
- **mll_pn_to_seq_parr.v** a terminal ⅋-vertex is sequentializing;
- **mll_pn_to_seq_tens.v** a terminal splitting ⊗-vertex is sequentializing;
- **mll_pn_to_seq_th.v** proof of the sequentialization theorem from the previous results;
- **mll_cut.v** definition of cut-elimination, proof it respects correction, and that it terminates;
- **mll_ax_exp.v** work in progress about axiom-expansion in proof-nets;
- **unused.v** general results that became useless during the development;
- **bug_report_x.v** files with examples where Coq compiles for a very long time.
