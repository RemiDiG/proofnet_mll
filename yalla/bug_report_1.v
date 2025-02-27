(*
Compilation time too long to manipulate the graph.
*)
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From GraphTheory Require Import mgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Timeout 10. (* Stop running after 10 secondes *)

Section Test.

Variables (Lv Le : Type) (cut : Lv).

Definition extend_edge_graph (G : graph Lv Le) (e : edge G) (R : Lv) (As At : Le) : graph Lv Le :=
  remove_edges [set e : edge G] ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)].

Definition op_1 (G : graph Lv Le) (e f g : edge G) : graph Lv Le :=
  G ∔ [source f , elabel e , target g].

Definition op_2 (G : graph Lv Le) (e f g : edge G) : graph Lv Le :=
  induced ([set: op_1 e f g] :\ (source e) :\ (target e)).

Definition new_graph (G : graph Lv Le) (e f g : edge G)
  (N : None \in (edge_set ([set: op_1 e f g] :\ source e :\ target e))) :=
  (@extend_edge_graph
    (@extend_edge_graph (op_2 e f g) (Sub None N) cut (elabel e) (elabel e))
    None cut (elabel e) (elabel e)).

Section Typing.

Variables (G : graph Lv Le) (e f g a : edge G)
  (N : None \in (edge_set ([set: op_1 e f g] :\ source e :\ target e))).

Variable p0 : Some a \in edge_set ([set: op_1 e f g] :\ source e :\ target e).
Variable p1 : Sub (Some a) p0 \notin [set (Sub None N : edge (op_2 e f g))].

Time Check (Some (Some (inl (Sub (Sub (Some a) p0) p1))) :
edge (@extend_edge_graph (op_2 e f g) (Sub None N) cut (elabel e) (elabel e))).
(* ~100 secs *) (* TODO now ~5 secs! *)
(*
Goal edge (new_graph N).
exact (Some (Some (inl (Sub (Some (Some (inl (Sub (Sub (Some a) p0) p1)))) p2)))). *)
(* COQ compiles for a very long time, if it finishs *)

End Typing.
Fail Time Definition new_graph_iso_e_bij_bwd (G : graph Lv Le) (e f g : edge G)
  (N : None \in (edge_set ([set: op_1 e f g] :\ source e :\ target e))) :
  edge G -> edge (new_graph N) :=
  fun a =>
  if @boolP (Some a \in edge_set ([set: op_1 e f g] :\ source e :\ target e)) is
    AltTrue p0 then
    if @boolP (Sub (Some a) p0 \notin [set (Sub None N : edge (op_2 e f g))]) is AltTrue p1 then
      if @boolP (Some (Some (inl (Sub (Sub (Some a) p0) p1))) \notin [set None]) is AltTrue p2 then
        Some (Some (inl (Sub (Some (Some (inl (Sub (Sub (Some a) p0) p1)))) p2)))
  else None else None else None.
(* COQ compiles for a very long time, if it finishs *)

End Test.