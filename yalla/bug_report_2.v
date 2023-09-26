From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import mgraph.

Set Default Timeout 10.

Section Report.

Variables (G : graph unit unit) (v : G) (e : edge G) (E : source e \in [set: G]).

Definition sigma_graph : graph unit unit :=
  induced [set: G].
(* Graph whose vertices are almost { v : vertex G | true }. *)

Definition complex_graph : graph unit unit :=
  sigma_graph ∔ tt ∔ tt
    ∔ [inl (inl (Sub (source e) E)) , tt , inl (inr tt)]
    ∔ [inl (inr tt) , tt , inl (inl (Sub (source e) E))].
(* We add two vertices, one edge from source e to the first one, and
  another edge from the first one to source e. *)

(*
Fixpoint walk {Lv Le : Type} {G : graph Lv Le} (x y : G) (w : path) :=
  if w is e :: w' then (source e == x) && walk (target e) y w' else x == y.
*)

Lemma walk_1 (u : complex_graph) :
  walk u u [:: Some None; None] ->
  ((inl (inl (Sub (source e) E : sigma_graph)) : vertex complex_graph) == u) &&
  ((inl (inl (Sub (source e) E : sigma_graph)) : vertex complex_graph) == u).
Proof.
  by simpl.
Fail Time Qed. (* Timeout! *)
(* Coq 8.17.1: Finished transaction in 1.165 secs (1.161u,0.s) (successful)
   Coq 8.18.0: Finished transaction in 11.396 secs (3.899u,0.059s) (successful) *)
Restart.
  Fail done. (* Timeout! *)
  by unfold walk.
Time Qed. (* Finished transaction in 0.743 secs (0.237u,0.004s) (successful) *)

Lemma walk_2 (u : sigma_graph) :
  walk (inl (inl u) : complex_graph) (inl (inl u)) [:: Some None; None] ->
  ((inl (inl (Sub (source e) E : sigma_graph)) : vertex complex_graph) == (inl (inl u) : vertex complex_graph)) &&
  ((inl (inl (Sub (source e) E : sigma_graph)) : vertex complex_graph) == (inl (inl u) : vertex complex_graph)).
Proof.
  by simpl.
Fail Time Qed. (* Timeout! *)
Restart.
  Fail done. (* Timeout! *)
  by unfold walk.
Time Qed. (* Finished transaction in 0.006 secs (0.006u,0.s) (successful) *)

End Report.
