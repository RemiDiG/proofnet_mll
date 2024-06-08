(*
Compilation time too long to manipulate the graph.
*)
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden".
From GraphTheory Require Import mgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Timeout 60. (* Stop running after 1 minute *)

Section Test.

Variables (Lv Le : Type) (cut : Lv).

Definition extend_edge_graph (G : graph Lv Le) (e : edge G) (R : Lv) (As At : Le) : graph Lv Le :=
  remove_edges [set e : edge G] ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)].

Definition new_graph (G : graph Lv Le) (e : edge G) :=
  (@extend_edge_graph
    (@extend_edge_graph G e cut (elabel e) (elabel e))
    None cut (elabel e) (elabel e)).

Fail Time Definition transport_to_new (G : graph Lv Le) (e : edge G) :
  edge G -> edge (new_graph e) :=
  fun a =>
    if @boolP (a \notin [set e]) is AltTrue p1 then
      if @boolP (Some (Some (inl (Sub a p1))) \notin [set None]) is AltTrue p2 then
        Some (Some (inl (Sub (Some (Some (inl (Sub a p1)))) p2)))
  else None else None.
(* COQ compiles for a very long time, if it finishs; at least 10 minutes *)

Time Definition transport_to_new (G : graph Lv Le) (e : edge G) :
  edge G -> edge (new_graph e) :=
  fun a =>
    if @boolP (a \notin [set e]) is AltTrue p1 then
      if @boolP
        ((Some (Some (inl (Sub a p1 : edge (remove_edges [set e : edge G])))) :
          edge (@extend_edge_graph G e cut (elabel e) (elabel e)))
          \notin [set None]) is AltTrue p2 then
            Some (Some (inl (Sub (Some (Some (inl (Sub a p1 : edge (remove_edges [set e : edge G])))) :
              edge (@extend_edge_graph G e cut (elabel e) (elabel e))) p2 :
                edge (remove_edges [set None : edge (@extend_edge_graph G e cut (elabel e) (elabel e))]))))
  else None else None.
(* Adding types makes it quasi immediate *)

End Test.
