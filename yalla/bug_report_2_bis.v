From mathcomp Require Import all_ssreflect.

Set Default Timeout 10.

Record graph : Type :=
  Graph {
      vertex : countType; (* replacing countType by choiceType or eqType makes it quicker; finType is also long *)
      edge : Type;
      endpoint : bool -> edge -> vertex; (* source and target functions *) }.
Notation source := (endpoint _ false).
Notation target := (endpoint _ true).

Definition add_vertex (G : graph) : graph :=
  {| vertex := option (vertex G);
     edge := edge G;
     endpoint b e := Some (endpoint G b e); |}.
Notation "G ∔ 1" := (add_vertex G) (at level 20, left associativity).

Definition add_edge (G : graph) (x y : vertex G) : graph :=
  {| vertex := vertex G;
     edge := option (edge G);
     endpoint b e := match e with Some e => endpoint G b e | None => if b then y else x end; |}.
Notation "G ∔ [ x , y ]" := (@add_edge G x y) (at level 20, left associativity).

Fixpoint walk {G : graph} (x y : vertex G) (w : seq (edge G)) :=
  if w is e :: w' then (source e == x) && walk (target e) y w' else x == y.

Section LongComputation.

Variables (G : graph) (v : vertex G) (e : edge G).

Definition sigma_graph :=
  {| vertex := {x : vertex G | true};
     edge := edge G;
     endpoint b e := Sub (endpoint G b e) is_true_true; |}.

Definition complex_graph : graph :=
  sigma_graph ∔ 1 ∔ 1 (* We add two vertices, *)
    ∔ [Some (Some (Sub (source e) is_true_true)) , Some None] (* one edge from source e to the first one *)
    ∔ [Some None , Some (Some (Sub (source e) is_true_true))]. (* and another edge from the first one to source e. *)

Lemma long_walk (u : vertex sigma_graph) :
  walk (Some (Some u) : vertex complex_graph) (Some (Some u)) [:: Some None; None] ->
  ((Some (Some (Sub (source e) is_true_true : vertex sigma_graph)) : vertex complex_graph) == (Some (Some u) : vertex complex_graph)) &&
  ((Some (Some (Sub (source e) is_true_true : vertex sigma_graph)) : vertex complex_graph) == (Some (Some u) : vertex complex_graph)).
Proof.
  by simpl.
Fail Time Qed. (* Timeout! *) (* Finished transaction in 87.985 secs (87.222u,0.194s) (successful) *)
Restart.
  Fail Time done. (* Timeout! *) (* Takes more than 200 secs *)
  by unfold walk.
Time Qed. (* Finished transaction in 0.008 secs (0.008u,0.s) (successful)*)
(* TODO time if add more +1? *)
End LongComputation.
