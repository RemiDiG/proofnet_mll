(* Extension for [mgraph] of the library GraphTheory
   About Directed Acyclic Multigraphs, in which the relation being linked by a walk is well-founded
 *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph.
From Yalla Require Import mll_prelim graph_more.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


(** ** Directed paths in a multigraph *)
Definition path {Lv Le : Type} {G : graph Lv Le} := seq (edge G).

Definition path_endpoint {Lv Le : Type} {G : graph Lv Le} (b : bool) (s : G) (p : path) :=
  match b with
  | false => head s [seq source e | e <- p]
  | true => last s [seq target e | e <- p]
  end.
Notation path_source := (path_endpoint false).
Notation path_target := (path_endpoint true).


(** ** Directed walks in a multigraph *)
(*
Fixpoint walk {Lv Le : Type} {G : graph Lv Le} (x y : G) (w : path) :=
  if w is e :: w' then (source e == x) && walk (target e) y w' else x == y.
*)
(* TODO beaucoup de doublon avec uwalk : généraliser ? demander à DP *)

(* Any path can be seen as an unoriented path *)
Coercion upath_of_path {Lv Le : Type} {G : graph Lv Le} (p : @path _ _ G) : upath :=
  [seq forward e | e <- p].

Lemma uwalk_walk {Lv Le : Type} {G : graph Lv Le} (p : @path _ _ G) {s t : G} :
  uwalk s t p = walk s t p.
Proof. revert s t. induction p as [ | ? ? IH] => s t //=. by rewrite IH. Qed.

Lemma endpoint_upath_path {Lv Le : Type} {G : graph Lv Le} (b : bool) (s : G) (p : path) :
  upath_endpoint b s p = path_endpoint b s p.
Proof. destruct b; by rewrite /= -map_comp. Qed.

Lemma walk_endpoint {Lv Le : Type} {G : graph Lv Le} (p : path) (x y : G) :
  walk x y p -> path_source x p = x /\ path_target x p = y.
Proof. rewrite -uwalk_walk -!endpoint_upath_path. apply uwalk_endpoint. Qed.

Lemma walk_sub_middle {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q : path) :
  walk s t (p ++ q) -> path_target s p = path_source t q.
Proof. rewrite -!uwalk_walk -!endpoint_upath_path /upath_of_path map_cat. apply uwalk_sub_middle. Qed.

Lemma walk_subK {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q : path) :
  walk s t (p ++ q) -> walk s (path_target s p) p /\ walk (path_source t q) t q.
Proof. rewrite -!uwalk_walk -!endpoint_upath_path /upath_of_path map_cat. apply uwalk_subK. Qed.

Lemma walk_sub {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q r : path) :
  walk s t (p ++ q ++ r) -> walk (path_target s p) (path_source t r) q.
Proof. rewrite -!uwalk_walk -!endpoint_upath_path /upath_of_path !map_cat. apply uwalk_sub. Qed.

Lemma walk_cat {Lv Le : Type} {G : graph Lv Le} (s i t : G) (p q : path) :
  walk s i p -> walk i t q -> walk s t (p ++ q).
Proof. rewrite -!uwalk_walk /upath_of_path map_cat. apply uwalk_cat. Qed.

Lemma walk_rcons {Lv Le : Type} {G : graph Lv Le} (s t : G) (p : path) (e : edge G) :
  walk s t (rcons p e) = (walk s (source e) p) && (target e == t).
Proof. rewrite -!uwalk_walk /upath_of_path map_rcons. apply uwalk_rcons. Qed.

Lemma walk_subgraph {Lv Le : Type} (G : graph Lv Le) V E C (s t : @subgraph_for _ _ G V E C) p :
  walk s t p -> walk (val s) (val t) [seq val e | e <- p].
Proof.
  revert s t. induction p as [ | [a A] p IH] => s t //=.
  cbnb. move => /andP[-> W]. splitb.
  change (target a) with (val (Sub (target a) (C _ _ (valP (exist _ a A))) : subgraph_for C)).
  by apply IH.
Qed.

Lemma walk_dual {Lv Le : Type} (G : graph Lv Le) p u v :
  @walk _ _ (dual G) u v p = @walk _ _ G v u (rev p).
Proof.
  revert u v. induction p as [ | e p IH] => u v //=.
  by rewrite rev_cons walk_rcons IH andb_comm.
Qed.

Lemma walk_edge {Lv Le : Type} (G : graph Lv Le) (e : edge G) :
  walk (source e) (target e) [:: e].
Proof. splitb. Qed.

Definition acyclic {Lv Le : Type} (G : graph Lv Le) :=
  forall (x : G) (p : path), walk x x p -> p = [::].

(** ** Directed Acyclic Multigraph *)
Record dam (Lv Le : Type) : Type := Dam {
    mgraph_of :> graph Lv Le;
    acy : acyclic mgraph_of;
  }.

(** ** Acyclicity is preserved by taking subgraphs *)
Lemma acy_subdam {Lv Le : Type} (G : dam Lv Le) V E C :
  acyclic (@subgraph_for _ _ G V E C).
Proof.
  intros ? ? P.
  assert (A := acy (walk_subgraph P)).
  by revert A => /eqP; rewrite map_nil => /eqP-->.
Qed.

Definition subdam_for {Lv Le : Type} {G : dam Lv Le} {V : {set G}} E C :=
  Dam (@acy_subdam _ _ _ V E C).

Definition remove_vertex_dam {Lv Le : Type} {G : dam Lv Le} (z : G) :=
  subdam_for (@consistent_del1 _ _ _ z).

(** ** Acyclicity is preserved by duality *)
Lemma dual_acy {Lv Le : Type} (G : graph Lv Le) :
  acyclic G -> acyclic (dual G).
Proof.
  intros C v p W.
  rewrite walk_dual in W.
  specialize (C _ _ W).
  by apply /eqP; rewrite -rev_nil; apply /eqP.
Qed.

Definition dual_dam {Lv Le : Type} (G : dam Lv Le) := Dam (dual_acy (@acy _ _ G)).


(** ** The relation being linked by a walk is well-founded in dam *)
Definition is_connected_strict {Lv Le : Type} {G : graph Lv Le} (t s : G) :=
  exists p, (p != [::]) && walk s t p.

Definition is_connected_strict_rev {Lv Le : Type} {G : graph Lv Le} (s t : G) :=
  is_connected_strict t s.

Lemma acc_is_connected_strict_edges {Lv Le : Type} (G : graph Lv Le) (u : G) :
  (forall e, source e = u -> Acc is_connected_strict (target e)) ->
  Acc is_connected_strict u.
Proof.
  intro H.
  constructor => v [p /andP[/eqP-P W]].
  destruct p as [ | e p]; first by []. clear P.
  revert W => /= /andP[/eqP-E W]. subst u.
  specialize (H _ erefl).
  destruct p as [ | f p].
  { by revert W => /= /eqP-<-. }
  apply (Acc_inv H).
  exists (f :: p). rewrite W. splitb.
Qed.

Lemma well_founded_dam_empty {Lv Le : Type} (G : graph Lv Le) :
  #|G| = 0 -> well_founded (@is_connected_strict _ _ G).
Proof. intros N x. apply card0_eq in N. by specialize (N x). Qed.

Lemma well_founded_dam_below {Lv Le : Type} (G : dam Lv Le) (v : G) :
  well_founded (@is_connected_strict _ _ (remove_vertex_dam v)) ->
  forall (u : remove_vertex v) p, walk v (val u) p ->
  Acc is_connected_strict (val u).
Proof.
  intros Rwf u. induction u as [[u U] IH] using (well_founded_ind Rwf).
  move => p /= VU.
  apply acc_is_connected_strict_edges. intros e ?. subst u.
  assert (E : e \in ~: edges_at v).
  { rewrite in_set edges_at_eq. splitb.
    all: apply /eqP => ?; subst v.
    - clear IH. contradict U; apply /negP. by rewrite !in_set negb_involutive.
    - assert (F := acy (walk_cat VU (walk_edge e))).
      by revert F => /eqP; rewrite cat_nil => /andP[_ /eqP-?]. }
  set UT := walk_edge e.
  change (target e) with (val (target (Sub e E : edge (remove_vertex v)))) in UT.
  refine (IH _ _ _ (walk_cat VU UT)).
  exists [:: Sub e E]. splitb. cbnb.
Qed.

Lemma well_founded_dam_removed {Lv Le : Type} (G : dam Lv Le) (v : G) :
  well_founded (@is_connected_strict _ _ (remove_vertex_dam v)) ->
  Acc is_connected_strict v.
Proof.
  intro. constructor => u [p /andP[/eqP-P W]].
  assert (U : u \in [set~ v]).
  { rewrite !in_set. apply /eqP => ?. subst u.
    contradict P. apply (acy W). }
  now refine (@well_founded_dam_below _ _ _ _ _ (Sub u U) _ W).
Qed.

Lemma well_founded_dam {Lv Le : Type} (G : dam Lv Le) :
  well_founded (@is_connected_strict _ _ G).
Proof.
  revert G.
  enough (H : forall n (G : dam Lv Le), #|G| = n -> well_founded (@is_connected_strict _ _ G))
    by (intro G; by apply (H #|G|)).
  intro n; induction n as [ | n IH]; intros G N.
  { by apply well_founded_dam_empty. }
  intro v.
  apply well_founded_dam_removed, IH.
  rewrite -(remove_vertex_card v) in N. simpl in *. lia.
Qed.

Lemma dual_rev {Lv Le : Type} (G : dam Lv Le) u v :
  @is_connected_strict _ _ (dual_dam G) u v <-> @is_connected_strict_rev _ _ G u v.
Proof. split; move => [p ?]; exists (rev p); by rewrite -walk_dual rev_nil. Qed.

Lemma well_founded_dam_rev {Lv Le : Type} (G : dam Lv Le) :
  well_founded (@is_connected_strict_rev _ _ G).
Proof. apply (Morphisms_Prop.well_founded_morphism _ _ (@dual_rev _ _ G)), well_founded_dam. Qed.

(** ** Basic lemmas in a directed acyclic multigraph ** **)
Lemma disjoint_edges_at_outin (Lv Le : Type) (G : dam Lv Le) (v : G) :
  [disjoint (edges_at_in v) & (edges_at_out v)].
Proof.
  apply /disjointP => e.
  rewrite !in_set => /eqP-?. subst v => /eqP-ST.
  destruct G as [G A]; simpl in e, ST.
  assert (W : walk (target e) (target e) [:: e]) by by rewrite /= ST eq_refl.
  by specialize (A _ _ W).
Qed.

Lemma card_edges_at_at_outin (Lv Le : Type) (G : dam Lv Le) (v : G) :
  #|edges_at v| = #|edges_at_in v| + #|edges_at_out v|.
Proof.
  rewrite edges_at_at_outin.
  destruct (leq_card_setU (edges_at_in v) (edges_at_out v)) as [_ C].
  rewrite disjoint_edges_at_outin in C.
  by revert C => /eqP-->.
Qed.
