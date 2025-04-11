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


(** ** Directed walks in a multigraph *)

Fixpoint walk  (p : path) :=
  if p is e :: p' then (target e == path_source (target e) p') && walk p' else true.
(* TODO beaucoup de doublon avec uwalk : généraliser ? demander à DP *)

Lemma uwalk_walk (p : path) :
  uwalk p = walk p.
Proof. induction p as [ | ? p IH] => //=. rewrite IH. by destruct p. Qed.

(** Some results on walk, obtained from uwalk *) (* TODO most are useless for me... *)
(* Lemma walk_endpoint (p : path) (x y : G) :
  walk x y p -> path_source x p = x /\ path_target x p = y.
Proof. rewrite -uwalk_walk -!endpoint_upath_path. apply uwalk_endpoint. Qed. *)

Lemma walk_edge (e : edge G) :
  walk [:: e].
Proof. by rewrite /= !eq_refl. Qed.

Lemma walk_rcons (p : path) (e : edge G) :
  walk (rcons p e) = (walk p) && (source e == (path_target (source e) p)).
Proof. by rewrite -!uwalk_walk /upath_of_path map_rcons uwalk_rcons /= -map_comp. Qed.

Lemma walk_cat (p q : path) :
  walk (p ++ q) = (walk p) && (walk q) &&
                   ((p == [::]) || (q == [::]) ||
                   [forall v, path_target v p == path_source v q]).
Proof. by rewrite -!uwalk_walk /upath_of_path map_cat uwalk_cat !map_nil //= -!map_comp. Qed.

(* Lemma walk_sub_middle (s t : G) (p q : path) :
  walk s t (p ++ q) -> path_target s p = path_source t q.
Proof. rewrite -!uwalk_walk -!endpoint_upath_path /upath_of_path map_cat. apply uwalk_sub_middle. Qed. *)

Lemma walk_subK (p q : path) :
  walk (p ++ q) -> walk p /\ walk q.
Proof. rewrite -!uwalk_walk /upath_of_path map_cat. apply uwalk_subK. Qed.

Lemma walk_sub (p q r : path) :
  walk (p ++ q ++ r) -> walk q.
Proof. rewrite -!uwalk_walk /upath_of_path !map_cat. apply uwalk_sub. Qed.

End Walk.

Notation path_source := (path_endpoint false).
Notation path_target := (path_endpoint true).

Lemma walk_dual {Lv Le : Type} {G : graph Lv Le} p :
  @walk _ _ (dual G) p = @walk _ _ G (rev p).
Proof.
  induction p as [ | e p IH] => //=.
  by rewrite rev_cons walk_rcons IH andb_comm /= map_rev last_rev.
Qed.

Lemma walk_subgraph {Lv Le : Type} {G : graph Lv Le} V E C (p : @path _ _  (@subgraph_for _ _ G V E C)) :
  walk p -> walk [seq val e | e <- p].
Proof.
  induction p as [ | [a A] p IH] => //=.
  rewrite eq_sym sub_val_eq.
  move=> /andP[/eqP-<- W].
  rewrite (IH W) andb_true_r.
  by destruct p.
Qed.

Definition acyclic {Lv Le : Type} (G : graph Lv Le) :=
  forall (p : path), walk p -> forall (x : G), path_source x p = path_target x p -> p = [::].

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
  reflect (exists p, walk p && (path_source s p == s) && (path_target s p == t))
  [exists p : Simple_upath G, (upath_source s (val p) == s) && (upath_target s (val p) == t)
    && [forall e, (e \in val p) ==> e.2]].
Proof.
  apply iff_reflect. split.
  - move=> [p ].
    rewrite -uwalk_walk -!endpoint_upath_path => /andP[/andP[walk_p source_p] target_p].
    apply uwalk_to_simple_upath in walk_p as [q [endpoints_q sub_q]].
    apply/existsP.
    destruct p.
    { exists (Sub [::] (simple_upath_nil G)).
      move: target_p. rewrite /= !eq_refl => -> /=. by apply/forallP. }
    exists q.
    move: endpoints_q source_p target_p => /= [<- <-] /eqP-<- /eqP-<-.
    splitb.
    + by destruct q as [[ | ? ?] ?].
    + apply/forallP => e. apply/implyP => e_in_q.
      move: sub_q => /(_ e e_in_q)/mapP[f _ ?]. by subst e.
  - move=> /existsP/sigW[[q Q] /= /andP[/andP[/eqP-source_q /eqP-target_q] path_q]].
    apply forward_upath_is_path in path_q. simpl in path_q.
    exists [seq e.1 | e <- q].
    rewrite -{2}source_q -target_q -uwalk_walk uwalk_of_simple_upath -?path_q //=.
    apply/andP. split.
    + destruct q as [ | [? ?] ?] => //=.
      by inversion path_q.
    + destruct q as [ | ? [? ?] _] using last_ind => //=.
      rewrite !map_rcons !last_rcons.
      rewrite /upath_of_path !map_rcons in path_q.
      apply rcons_inj in path_q. by inversion path_q.
Qed.

Definition is_connected {Lv Le : Type} {G : graph Lv Le} (t s : G) :=
  [exists p : Simple_upath G, (upath_source s (val p) == s) && (upath_target s (val p) == t)
    && [forall e, (e \in val p) ==> e.2]].
  (* We use this to be in bool (see exists_walk_boolP). *)

Lemma is_connected_reflexive {Lv Le : Type} {G : graph Lv Le} :
  reflexive (@is_connected _ _ G).
Proof. move=> u. apply/exists_walk_boolP. exists [::]. by rewrite !eq_refl. Qed.

Lemma is_connected_antisymmetric {Lv Le : Type} {G : dam Lv Le} :
  antisymmetric (@is_connected _ _ G).
Proof.
  move=> u v /andP[/exists_walk_boolP[p /andP[/andP[walk_p s_p] t_p]]
    /exists_walk_boolP[q /andP[/andP[walk_q s_q] t_q]]].
  assert (walk_v_v : walk (p ++ q)).
  { rewrite walk_cat walk_p walk_q.
    destruct p, q => //=.
    apply/forallP => _.
    by move: t_p s_q => /= /eqP--> /eqP-->. }
  have := @acy _ _ _ _ walk_v_v v.
  move: s_p t_q t_p. rewrite /= !map_cat head_cat last_cat.
  destruct p, q => //=.
  - by move=> _ /eqP--> _ _.
  - by move=> _ _ /eqP--> _.
  - by move=> _ /eqP--> _ _.
  - by move=> /eqP--> /eqP--> _ /(_ Logic.eq_refl).
Qed.

Lemma is_connected_transitive {Lv Le : Type} {G : graph Lv Le} :
  transitive (@is_connected _ _ G).
Proof.
  move=> u v w /exists_walk_boolP[p /andP[/andP[walk_p /eqP-s_p] /eqP-t_p]]
    /exists_walk_boolP[q /andP[/andP[walk_q /eqP-s_q] /eqP-t_q]].
  apply/exists_walk_boolP.
  exists (q ++ p).
  rewrite walk_cat {}walk_p {}walk_q.
  move: s_p t_p s_q t_q.
  rewrite /= !map_cat head_cat last_cat.
  destruct p, q => //=.
  - move=> _ -> _ ->. by rewrite !eq_refl.
  - move=> _ -> -> ->. by rewrite !eq_refl.
  - move=> -> -> _ ->. by rewrite !eq_refl.
  - move=> -> -> -> ->. rewrite !eq_refl !andb_true_r. by apply/forallP.
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
  exists p, (p != [::]) && walk p && (path_source s p == s) && (path_target s p == t).

Lemma is_connected_strict_lt_of_is_connectedP {Lv Le : Type} {G : dam Lv Le} (u v : G) :
  reflect (is_connected_strict u v) ((v != u) && is_connected u v).
Proof.
  apply iff_reflect. split.
  - move=> [p /andP[/andP[/andP[/eqP-p_nil walk_p] /eqP-source_p] /eqP-target_p]].
    assert (v != u) as ->.
    { case/boolP: (v == u) => //= /eqP-?. subst v.
      rewrite -{2}target_p in source_p.
      contradict p_nil. exact: acy walk_p _ source_p. }
    simpl. apply/exists_walk_boolP. exists p.
    by rewrite walk_p source_p target_p !eq_refl.
  - move=> /andP[/eqP-v_neq_u /exists_walk_boolP[p /andP[/andP[walk_p] source_p] target_p]].
    exists p. rewrite walk_p source_p target_p !andb_true_r.
    destruct p; last by [].
    move: target_p => /eqP-?. by subst u.
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
  move=> C p W v.
  rewrite walk_dual in W.
  move: C => /(_ _ W v).
  rewrite /= !map_rev head_rev last_rev => C cyclic.
  symmetry in cyclic. move: C => /(_ cyclic)/eqP.
  by rewrite rev_nil => /eqP-->.
Qed.

Definition dual_dam {Lv Le : Type} (G : dam Lv Le) := Dam (dual_acy (@acy _ _ G)).

(* Acyclicity is preserved by taking subgraphs *)
Lemma acy_subdam {Lv Le : Type} (G : dam Lv Le) V E C :
  acyclic (@subgraph_for _ _ G V E C).
Proof.
  move=> p P [u U].
  have := @acy _ _ _ _ (walk_subgraph P) u.
  destruct p as [ | ? p] => //=.
  destruct p as [ | ? ? _] using last_ind => //= H /eqP.
  - rewrite sub_val_eq /= => /eqP-H2. by specialize (H H2).
  - move: H. rewrite !map_rcons !last_rcons sub_val_eq /= => H /eqP-H2. by specialize (H H2).
Qed.

Definition subdam_for {Lv Le : Type} {G : dam Lv Le} {V : {set G}} E C :=
  Dam (@acy_subdam _ _ _ V E C).

Lemma dual_rev {Lv Le : Type} (G : dam Lv Le) u v :
  @is_connected_strict _ _ (dual_dam G) u v <-> @is_connected_strict_rev _ _ G u v.
Proof.
  split; move=> [p P]; exists (rev p); rewrite -walk_dual rev_nil; move: P.
  - rewrite /= !map_rev head_rev last_rev.
    by destruct p => //= /andP[/andP[/andP[-> ->] ->] ->].
  - rewrite /= !map_rev head_rev last_rev.
    destruct p => //= /andP[/andP[/andP[-> ?] ->] ->]. by rewrite !walk_dual revK /= !andb_true_r.
Qed.

Lemma disjoint_edges_at_outin (Lv Le : Type) (G : dam Lv Le) (v : G) :
  [disjoint (edges_at_in v) & (edges_at_out v)].
Proof.
  apply/disjointP => e.
  rewrite !in_set => /eqP-? /eqP-ST. subst v.
  assert (W : walk [:: e]) by by rewrite /= eq_refl.
  by have := acy W => /= /(_ (source e) ST).
Qed.

Lemma card_edges_at_at_outin (Lv Le : Type) (G : dam Lv Le) (v : G) :
  #|edges_at v| = #|edges_at_in v| + #|edges_at_out v|.
Proof.
  rewrite edges_at_at_outin.
  have [_ C] := leq_card_setU (edges_at_in v) (edges_at_out v).
  rewrite disjoint_edges_at_outin in C.
  by move: C => /eqP-->.
Qed.
