(* Basic operations respecting correctness *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
From mathcomp Require Import all_ssreflect zify.
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export graph_more mll_prelim mll_def.

Import EqNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Section Atoms.

Context { atom : DecType }.
Notation formula := (@formula atom).
Notation base_graph := (graph (flat rule) (flat formula)).
Notation graph_left := (@graph_left atom).
Notation graph_data := (@graph_data atom).
Notation geos := (@geos atom).

Definition red_ax_graph_1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : base_graph :=
  G ∔ [source (other_cut Hcut) , dual (elabel e) , target (other_ax Hax)].

Definition red_ax_graph (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : base_graph :=
  induced ([set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)).

Definition extend_edge_graph {Lv Le : Type} (G : graph Lv Le) (e : edge G) (R : Lv) (As At : Le) : graph Lv Le :=
  remove_edges [set e : edge G] ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)].

Definition red_ax_G (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut) (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :=
  (@extend_edge_graph _ _
    (@extend_edge_graph _ _ (red_ax_graph Hcut Hax) (Sub None N) cut (dual (elabel e)) (elabel e))
    None ax (elabel e) (dual (elabel e))).

Definition red_ax_iso_v_bij_fwd (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  red_ax_G N -> G :=
  fun v => match v with
  | inl (inl (exist u _)) => u
  | inl (inr tt)          => target e
  | inr tt                => source e
  end.

Definition red_ax_iso_e_bij_fwd (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  edge (red_ax_G N) -> edge G :=
  fun a => match a with
  | Some (Some (inl (exist (Some (Some (inl (exist (exist (Some a) _) _)))) _))) => a
  | None => other_ax Hax
  | Some None => e
  | _ => other_cut Hcut
  end.

(*
Definition red_ax_iso_e_bij_bwd (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  edge G -> edge (red_ax_G N) :=
  fun a =>
  if @boolP (Some a \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)) is
    AltTrue p0 then
    if @boolP (Sub (Some a) p0 \notin [set (Sub None N : edge (red_ax_graph Hcut Hax))]) is AltTrue p1 then
      if @boolP (Some (Some (inl (Sub (Sub (Some a) p0) p1))) \notin [set None]) is AltTrue p2 then
        Some (Some (inl (Sub (Some (Some (inl (Sub (Sub (Some a) p0) p1)))) p2)))
      else None else None
  else
    if a == e then Some None
    else if a == other_ax Hax then None
    else if @boolP _ is AltTrue p2 then Some (Some (inl (Sub (Some None) p2))) else None.
*)
(* COQ compiles for a very long time > 2h *)

End Atoms.
