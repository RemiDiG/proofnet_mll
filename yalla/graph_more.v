(* Extension for [mgraph] of the library GraphTheory *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From GraphTheory Require Import preliminaries mgraph structures bij setoid_bigop.
From Yalla Require Import mll_prelim.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



(** * Notations from the library *)
Open Scope graph_scope.
(* G0 ⊎ G1 = disjoint union
   G ∔ v = add a vertex labelled v
   G ∔ [ x , u , y ] = add an arrow from x to y labelled u *)

(** ** Dual of a graph, with all edges flipped **)
Definition dual {Lv Le : Type} (G : graph Lv Le) : graph Lv Le :=
  {| vertex := G;
     edge := edge G;
     endpoint b := @endpoint _ _ G (~~ b);
     vlabel := @vlabel _ _ G;
     elabel := @elabel _ _ G;
  |}.


(** ** Out & In edges of a vertex *)
Definition edges_at_outin (b : bool) {Lv Le : Type} {G : graph Lv Le} (v : G) : {set edge G} :=
  [set e | endpoint b e == v].
Notation edges_at_out := (edges_at_outin false).
Notation edges_at_in := (edges_at_outin true).

Lemma endpoint_in_edges_at_outin (b : bool) {Lv Le : Type} {G : graph Lv Le} (e : edge G) :
  e \in edges_at_outin b (endpoint b e).
Proof. by rewrite in_set. Qed.
Notation source_in_edges_at_out := (endpoint_in_edges_at_outin false).
Notation target_in_edges_at_in := (endpoint_in_edges_at_outin true).


(** ** Rewriting of edges_at *)
Lemma edges_at_eq {Lv Le : Type} (G : graph Lv Le) (v : G) (e : edge G) :
  (e \in edges_at v) = (source e == v) || (target e == v).
Proof.
  rewrite !in_set /incident. symmetry.
  destruct [exists b, endpoint b e == v] eqn:E.
  - revert E => /existsP[[] ->]; caseb.
  - revert E => /existsPn-?. splitb.
Qed.

Lemma edges_at_at_outin (Lv Le : Type) (G : graph Lv Le) (v : G) :
  edges_at v = (edges_at_in v) :|: (edges_at_out v).
Proof. apply /setP => e. by rewrite edges_at_eq !in_set orbC. Qed.

Lemma in_edges_at_endpoint {Lv Le : Type} {G : graph Lv Le} (e : edge G) (b : bool) :
  e \in edges_at (endpoint b e).
Proof. rewrite edges_at_eq. by destruct b; rewrite eq_refl // orb_true_r. Qed.


(** ** The set of edges of the whole set of vertices, is the whole set of edges *)
Lemma edge_set_setT {Lv Le : Type} (G : graph Lv Le) :
  edge_set [set: G] = setT.
Proof. apply /setP => ?. by rewrite !in_set. Qed. 


(** ** Isomorphisms preserve cardinality *)
Lemma card_iso {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) :
  F ≃ G -> #|F| = #|G|.
Proof. intros [? _ _ _]. by apply card_bij. Qed.

(** ** Some specific isomorphisms *)
(* Definition edge_graph_iso {Lv: comMonoid} {Le : elabelType} (u v : Lv) (e e' : Le) :
  e = e' -> edge_graph u e v = edge_graph u e' v.
Proof.
  intros. by subst e'.
Defined. *) (* TODO see where it is used! *)

(** ** Some specific isomorphisms *)
Definition edge_graph_iso {Lv: comMonoid} {Le : elabelType} (u v : Lv) (e e' : Le) :
  e = e' -> edge_graph u e v ≃ edge_graph u e' v.
Proof.
  intros.
  apply (@add_edge_iso'' _ _ _ _ iso_id); trivial.
  by replace e with e'.
Defined. (* TODO see where it is used! *)

Definition induced_func_v {Lv Le : Type} (F G : graph Lv Le) (f : bij F G) (S : {set F}) (R : {set G}) :
  R = [set f v | v in S]  -> induced S -> induced R.
Proof.
  intros E [v V].
  exists (f v).
  by rewrite E bij_imset_f.
Defined.

Lemma edge_set_iso {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (f : F ≃ G) (S : {set F}) :
  edge_set [set f v | v in S] = [set f.e e | e in edge_set S].
Proof.
  apply /setP => e.
  rewrite !in_set -(bijK' f (source e)) -(bijK' f (target e)) -[in RHS](bijK' f.e e)
    !bij_imset_f !in_set !endpoint_iso'.
  destruct (f.d _); trivial.
  apply andbC.
Qed.

Definition induced_func_e {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (f : F ≃ G)
  (S : {set F}) (R : {set G}) : R = [set f v | v in S]  -> edge (induced S) -> edge (induced R).
Proof.
  intros E [a A].
  exists (f.e a).
  by rewrite E edge_set_iso bij_imset_f.
Defined.

Definition induced_iso {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (h : F ≃ G)
  (S : {set F}) (R : {set G}) : R = [set h v | v in S] -> induced S ≃ induced R.
Proof.
  intro E.
  assert (E' : S = [set h^-1 v | v in R]) by by apply bij_imset_invert.
  set f := induced_func_v E.
  set f' := @induced_func_v _ _ _ _ (iso_sym _) _ _ E'.
  assert (fK : cancel f f').
  { intros [? ?]. cbnb. apply bijK. }
  assert (fK' : cancel f' f).
  { intros [? ?]. cbnb. apply bijK'. }
  set iso_v := {| bij_fwd := _ ; bij_bwd := _ ; bijK := fK ; bijK' := fK' |}.
  set g := induced_func_e E.
  set g' := @induced_func_e _ _ _ _ (iso_sym _) _ _ E'.
  assert (gK : cancel g g').
  { intros [? ?]. cbnb. apply bijK. }
  assert (gK' : cancel g' g).
  { intros [? ?]. cbnb. apply bijK'. }
  set iso_e := {| bij_fwd := _ ; bij_bwd := _ ; bijK := gK ; bijK' := gK' |}.
  exists iso_v iso_e (fun v => h.d (val v)). splitb.
  - intros [? ?] ?. cbnb. apply endpoint_iso.
  - intros [? ?]. cbnb. apply vlabel_iso.
  - intros [? ?]. cbnb. apply elabel_iso.
Defined.

(** * The induced subgraph with all vertices is (isomorphic to) the whole graph *)
Lemma induced_all {Lv: comMonoid} {Le : elabelType} (G : graph Lv Le) :
  induced [set : G] ≃ G.
Proof.
  set f : induced [set : G] -> G := fun v => val v.
  set f' : G -> induced [set : G] := fun v => Sub v (in_setT v).
  assert (fK : cancel f f') by (intros [? ?]; cbnb).
  assert (fK' : cancel f' f) by cbnb.
  set iso_v := {| bij_fwd := _ ; bij_bwd := _ ; bijK := fK ; bijK' := fK' |}.
  set g : edge (induced [set : G]) -> edge G := fun e => val e.
  assert (Hg : forall e, e \in edge_set [set: G]).
  { intros. by rewrite !in_set. }
  set g' : edge G -> edge (induced [set : G]) := fun e => Sub e (Hg e).
  assert (gK : cancel g g') by (intros [? ?]; cbnb).
  assert (gK' : cancel g' g) by cbnb.
  set iso_e := {| bij_fwd := _ ; bij_bwd := _ ; bijK := gK ; bijK' := gK' |}.
  exists iso_v iso_e pred0.
  splitb.
Defined.

Definition induced_all_iso {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (h : F ≃ G) :
  induced [set: F] ≃ induced [set: G].
Proof.
  etransitivity. apply induced_all.
  etransitivity. apply h.
  symmetry. apply induced_all.
Defined.

(** * Basic results about cardinality *)
Lemma card_edge_add_vertex (Lv Le : Type) (G : graph Lv Le) (v : Lv) :
  #|edge (G ∔ v)| = #|edge G|.
Proof. rewrite card_sum card_void. lia. Qed.

Lemma card_edge_add_edge (Lv Le : Type) (G : graph Lv Le) (u v : G) (e : Le) :
  #|edge (G ∔ [u, e, v])| = #|edge G| + 1.
Proof. rewrite card_option. lia. Qed.

Lemma card_add_vertex (Lv Le : Type) (G : graph Lv Le) (v : Lv) :
  #|G ∔ v| = #|G| + 1.
Proof. by rewrite card_sum card_unit. Qed.

Lemma card_induced_all {Lv: comMonoid} {Le : elabelType} (G : graph Lv Le) :
 #|induced [set : G]| = #|G|.
Proof. apply card_iso, induced_all. Qed.

Lemma card_inducedD1 (Lv Le : Type) (G : graph Lv Le) (S : {set G}) (v : G) :
  #|induced S| = (v \in S) + #|induced (S :\ v)|.
Proof. rewrite /= !card_set_subset 2!cardsE. apply cardsD1. Qed.

Lemma cards_subgraph_pred (Lv Le : Type) (G : graph Lv Le) V E (C : consistent V E) (P : pred G) :
  #|[set x : subgraph_for C | P (val x)]| = #|[set x | P x] :&: V|.
Proof.
  rewrite -!card_set_subset.
  assert (Hf : forall (u : {u : subgraph_for C | P (val u)}),
    (val (val u) \in [set x | P x]) && (val (val u) \in V)).
  { move => [[u In]/= U]. by rewrite in_set U In. }
  set f : {u : subgraph_for C | P (val u)} ->
    {u : G | (u \in [set x | P x]) && (u \in V)} :=
    fun u => Sub (val (val u)) (Hf u).
  assert (Hg0 : forall (u : {u : G | (u \in [set x | P x]) && (u \in V)}),
    val u \in V) by by move => [? /= /andP[_ ?]].
  assert (Hg1 : forall (u : {u : G | (u \in [set x | P x]) && (u \in V)}),
    P (val (Sub (val u) (Hg0 u) : subgraph_for C))).
  { move => [? /= /andP[U _]]. revert U. by rewrite in_set. }
  set g : {u : G | (u \in [set x | P x]) && (u \in V)} ->
    {u : subgraph_for C | P (val u)} :=
    fun u => Sub _ (Hg1 u).
  apply (@bij_card_eq _ _ f), (@Bijective _ _ _ g) => ?; cbnb.
Qed.

Lemma remove_vertex_card {Lv Le : Type} {G : graph Lv Le} (v : G) :
  #|remove_vertex v| + 1 = #|G|.
Proof.
  rewrite card_set_subset cardsE cardsC1.
  enough (#|G| <> 0) by lia.
  intro N. apply card0_eq in N. by specialize (N v).
Qed.
