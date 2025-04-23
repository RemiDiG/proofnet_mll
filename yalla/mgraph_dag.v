(* Extension for [mgraph] of the library GraphTheory
   About Directed Acyclic Multigraphs, in which the relation being linked by a walk is well-founded
 *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From HB Require Import structures.
From GraphTheory Require Import preliminaries mgraph.
From Yalla Require Import mll_prelim graph_more upath simple_upath.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Section Walk.

Context {Lv Le : Type} {G : graph Lv Le}.

(** ** Directed paths in a multigraph *)
Definition path := seq (edge G).

Definition path_endpoint (b : bool) (s : G) (p : path) :=
  match b with
  | false => head s [seq source e | e <- p]
  | true  => last s [seq target e | e <- p]
  end.
Notation path_source := (path_endpoint false).
Notation path_target := (path_endpoint true).

(* Any path can be seen as an unoriented path *)
Coercion upath_of_path (p : path) : upath :=
  [seq forward e | e <- p].

Lemma in_upath_of_path (p : path) (e : edge G) (b : bool) :
  (e, b) \in upath_of_path p = (e \in p) && b.
Proof.
  destruct b; [destruct (e \in p) eqn:E | ]; rewrite /= ?andb_false_r; apply /mapP.
  - by exists e.
  - move=> [a A AE]. inversion AE. subst a. by rewrite A in E.
  - by move=> [? _ ?].
Qed.

Lemma endpoint_upath_path (b : bool) (s : G) (p : path) :
  upath_endpoint b s p = path_endpoint b s p.
Proof. destruct b; by rewrite /= -map_comp. Qed.
(* TODO homogeneize names *)


(** ** Directed walks in a multigraph *)
(*
Fixpoint walk {Lv Le : Type} {G : graph Lv Le} (x y : G) (w : path) :=
  if w is e :: w' then (source e == x) && walk (target e) y w' else x == y.
*)
(* TODO beaucoup de doublon avec uwalk : généraliser ? demander à DP *)
Lemma uwalk_walk (p : path) {s t : G} :
  uwalk s t p = walk s t p.
Proof. move: s t. induction p as [ | ? ? IH] => s t //=. by rewrite IH. Qed.

(** Some results on walk, obtained from uwalk *) (* TODO most are useless for me... *)
Lemma walk_endpoint (p : path) (x y : G) :
  walk x y p -> path_source x p = x /\ path_target x p = y.
Proof. rewrite -uwalk_walk -!endpoint_upath_path. apply uwalk_endpoint. Qed.

Lemma walk_edge (e : edge G) :
  walk (source e) (target e) [:: e].
Proof. by rewrite /= !eq_refl. Qed.

Lemma walk_rcons (s t : G) (p : path) (e : edge G) :
  walk s t (rcons p e) = (walk s (source e) p) && (target e == t).
Proof. rewrite -!uwalk_walk /upath_of_path map_rcons. apply uwalk_rcons. Qed.

Lemma walk_cat (s t : G) (p q : path) :
  walk s t (p ++ q) = walk s (path_target s p) p && (walk (path_target s p) t q).
Proof. by rewrite -!uwalk_walk /upath_of_path map_cat uwalk_cat endpoint_upath_path. Qed.

Lemma walk_sub_middle (s t : G) (p q : path) :
  walk s t (p ++ q) -> path_target s p = path_source t q.
Proof. rewrite -!uwalk_walk -!endpoint_upath_path /upath_of_path map_cat. apply uwalk_sub_middle. Qed.

Lemma walk_dual p u v :
  @walk _ _ (dual G) u v p = @walk _ _ G v u (rev p).
Proof.
  move: u. induction p as [ | e p IH] => u //=.
  by rewrite rev_cons walk_rcons IH andb_comm.
Qed.

Lemma walk_subgraph V E C (s t : @subgraph_for _ _ G V E C) p :
  walk s t p -> walk (val s) (val t) [seq val e | e <- p].
Proof.
  move: s. induction p as [ | [a A] p IH] => s //=.
  cbnb => /andP[-> W] /=.
  rewrite -[target a]/(val (Sub (target a) (C _ _ (valP (exist _ a A))) : subgraph_for C)).
  by apply IH.
Qed.

End Walk.

Definition acyclic {Lv Le : Type} (G : graph Lv Le) :=
  forall (x : G) (p : path), walk x x p -> p = [::].

(** ** Directed Acyclic Multigraph *)
Record dam (Lv Le : Type) : Type := Dam {
    mgraph_of :> graph Lv Le;
    acy : acyclic mgraph_of;
  }.


(** ** The relation being linked by a walk is well-founded in dam *)
Lemma forward_upath_is_path {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) :
  [forall e, (e \in p) ==> e.2] -> p = upath_of_path [seq e.1 | e <- p].
Proof.
  induction p as [ | [e b] p IH] => //= forward_p.
  f_equal.
  - move: forward_p => /forallP/(_ (e, b)) /=.
    by rewrite in_cons eq_refl /= => ->.
  - apply IH. clear IH.
    apply/forallP => f. apply/implyP => f_in_p.
    move: forward_p => /forallP/(_ f).
    by rewrite in_cons f_in_p orb_true_r /= => ->.
Qed.

Lemma exists_walk_boolP {Lv Le : Type} {G : graph Lv Le} (s t : G) :
  reflect (exists p, walk s t p)
  [exists p : Simple_upath G, (upath_source s (val p) == s) && (upath_target s (val p) == t)
    && [forall e, (e \in val p) ==> e.2]].
Proof.
  apply iff_reflect. split.
  - move=> [p walk_p].
    rewrite -uwalk_walk in walk_p.
    apply uwalk_to_simple_upath in walk_p as [q [source_q [target_q sub_q]]].
    apply/existsP. exists q.
    rewrite source_q target_q !eq_refl /=.
    apply/forallP => e. apply/implyP => e_in_q.
    move: sub_q => /(_ e e_in_q)/mapP[f _ ?]. by subst e.
  - move=> /existsP/sigW[[q Q] /andP[/andP[/eqP-source_q /eqP-target_q] path_q]].
    apply forward_upath_is_path in path_q. simpl in path_q.
    assert (H := uwalk_of_simple_upath Q s).
    rewrite source_q target_q path_q uwalk_walk in H.
    by exists [seq e.1 | e <- q].
Qed.

Definition is_connected {Lv Le : Type} {G : graph Lv Le} (t s : G) :=
  [exists p : Simple_upath G, (upath_source s (val p) == s) && (upath_target s (val p) == t)
    && [forall e, (e \in val p) ==> e.2]].
  (* We use this to be in bool (see exists_walk_boolP). *)

Lemma is_connected_reflexive {Lv Le : Type} {G : graph Lv Le} :
  reflexive (@is_connected _ _ G).
Proof. move=> u. apply/exists_walk_boolP. by exists [::] => /=. Qed.

Lemma is_connected_antisymmetric {Lv Le : Type} {G : dam Lv Le} :
  antisymmetric (@is_connected _ _ G).
Proof.
  move=> u v /andP[/exists_walk_boolP[p walk_v_u] /exists_walk_boolP[q walk_u_v]].
  assert (walk_v_v : walk v v (p ++ q)).
  { rewrite walk_cat.
    destruct (walk_endpoint walk_v_u) as [_ ->].
    by rewrite walk_v_u walk_u_v. }
  have/eqP := acy walk_v_v.
  rewrite cat_nil => /andP[/eqP-? /eqP-?]. subst p q.
  by move: walk_v_u => /= /eqP-->.
Qed.

Lemma is_connected_transitive {Lv Le : Type} {G : graph Lv Le} :
  transitive (@is_connected _ _ G).
Proof.
  move=> u v w /exists_walk_boolP[p walk_u_v] /exists_walk_boolP[q walk_w_u].
  apply/exists_walk_boolP.
  exists (q ++ p).
  rewrite walk_cat.
  destruct (walk_endpoint walk_w_u) as [_ ->].
  by rewrite walk_w_u walk_u_v.
Qed.

Definition vertex_finPOrder {Lv Le : Type} {G : graph Lv Le} : Type := vertex G.
(* TODO
We need vertex G : Type and not finType to consider it as a finPOrderType.
Discuss it with DP, try to modify GraphTheory and pull request.
*)
HB.instance Definition _ {Lv Le : Type} {G : graph Lv Le} := Finite.on (@vertex_finPOrder _ _ G). (* To prevent delta-expansion *)
Set Warnings "-redundant-canonical-projection". (* to ignore warnings of already canonical *)
HB.instance Definition _ {Lv Le : Type} {G : dam Lv Le} := @Order.Le_isPOrder.Build
  tt (@vertex_finPOrder _ _ G) _ is_connected_reflexive
  is_connected_antisymmetric is_connected_transitive.
Set Warnings "redundant-canonical-projection".
(* TODO need changing the graph library -> then make a pull request! *)

Definition is_connected_strict {Lv Le : Type} {G : graph Lv Le} (t s : G) :=
  exists p, (p != [::]) && walk s t p.

Lemma is_connected_strict_lt_of_is_connectedP {Lv Le : Type} {G : dam Lv Le} (u v : G) :
  reflect (is_connected_strict u v) ((v != u) && is_connected u v).
Proof.
  apply iff_reflect. split.
  - move=> [p /andP[/eqP-p_nil walk_p]].
    assert (v != u) as ->.
    { case/boolP: (v == u) => //= /eqP-?. subst v.
      contradict p_nil. exact: acy walk_p. }
    simpl. apply/exists_walk_boolP. by exists p.
  - move=> /andP[/eqP-v_neq_u /exists_walk_boolP[p walk_v_u]].
    exists p. rewrite walk_v_u andb_true_r.
    move: walk_v_u. destruct p; last by [].
    by move=> /eqP.
Qed.

Lemma well_founded_dam {Lv Le : Type} (G : dam Lv Le) :
  well_founded (@is_connected_strict _ _ G).
Proof.
  apply (Morphisms_Prop.well_founded_morphism _ _
    (fun u v => rwP (is_connected_strict_lt_of_is_connectedP u v))),
    (@lt_wf _ vertex_finPOrder).
Qed.

Definition is_connected_strict_rev {Lv Le : Type} {G : graph Lv Le} (s t : G) :=
  is_connected_strict t s.

Lemma well_founded_dam_rev {Lv Le : Type} (G : dam Lv Le) :
  well_founded (@is_connected_strict_rev _ _ G).
Proof.
  apply (Morphisms_Prop.well_founded_morphism _ _
    (fun u v => rwP (is_connected_strict_lt_of_is_connectedP v u))),
    (@gt_wf _ vertex_finPOrder).
Qed.

(** ** Basic lemmas in a directed acyclic multigraph ** **) (* TODO most are useless for me... *)
(* Acyclicity is preserved by duality *)
Lemma dual_acy {Lv Le : Type} (G : graph Lv Le) :
  acyclic G -> acyclic (graph_more.dual G).
Proof.
  move=> C v p W.
  rewrite walk_dual in W.
  move: C => /(_ _ _ W)/eqP.
  by rewrite rev_nil => /eqP-->.
Qed.

Definition dual_dam {Lv Le : Type} (G : dam Lv Le) := Dam (dual_acy (@acy _ _ G)).

(* Acyclicity is preserved by taking subgraphs *)
Lemma acy_subdam {Lv Le : Type} (G : dam Lv Le) V E C :
  acyclic (@subgraph_for _ _ G V E C).
Proof.
  move=> ? ? P.
  assert (A := acy (walk_subgraph P)).
  move: A => /eqP. by rewrite map_nil => /eqP-->.
Qed.

Definition subdam_for {Lv Le : Type} {G : dam Lv Le} {V : {set G}} E C :=
  Dam (@acy_subdam _ _ _ V E C).

Lemma dual_rev {Lv Le : Type} (G : dam Lv Le) u v :
  @is_connected_strict _ _ (dual_dam G) u v <-> @is_connected_strict_rev _ _ G u v.
Proof. split; move=> [p ?]; exists (rev p); by rewrite -walk_dual rev_nil. Qed.

Lemma disjoint_edges_at_outin (Lv Le : Type) (G : dam Lv Le) (v : G) :
  [disjoint (edges_at_in v) & (edges_at_out v)].
Proof.
  apply/disjointP => e.
  rewrite !in_set => /eqP-? /eqP-ST. subst v.
  assert (W : walk (target e) (target e) [:: e]) by by rewrite /= ST eq_refl.
  by assert (A := acy W).
Qed.

Lemma card_edges_at_at_outin (Lv Le : Type) (G : dam Lv Le) (v : G) :
  #|edges_at v| = #|edges_at_in v| + #|edges_at_out v|.
Proof.
  rewrite edges_at_at_outin.
  have [_ C] := leq_card_setU (edges_at_in v) (edges_at_out v).
  rewrite disjoint_edges_at_outin in C.
  by move: C => /eqP-->.
Qed.
