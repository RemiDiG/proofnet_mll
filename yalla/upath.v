(* Extension for [mgraph] of the library GraphTheory *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From GraphTheory Require Import preliminaries mgraph structures bij setoid_bigop.
From Yalla Require Import mll_prelim graph_more.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


(** ** Undirected paths in an oriented multigraph *)
Notation forward e := (e, true). (* An edge taken from source to target *)
Notation backward e := (e, false). (* An edge taken from target to source *)
Notation reversed e := (e.1, ~~e.2).
Notation usource e := (endpoint (~~e.2) e.1).
Notation utarget e := (endpoint e.2 e.1).
(* TODO with
Definition uendpoint {Lv Le : Type} {G : graph Lv Le} b (e : (edge G) * bool) :=
  endpoint (if b then ~~e.2 else e.2) e.1.
Notation usource := (uendpoint false).
Notation utarget := (uendpoint true).
???
 *)
(* TODO with more standard vocabulary: path = open simple walk, trail = no repetition of edges, cycle = close simple walk *)

Section Graph.

Context {Lv Le : Type} {G : graph Lv Le}.

Lemma usource_reversed (e : edge G * bool) :
  usource (reversed e) = utarget e.
Proof. destruct e. by rewrite negb_involutive. Qed.

Lemma utarget_reversed (e : edge G * bool) :
  utarget (reversed e) = usource e.
Proof. by destruct e. Qed.

Definition upath := seq ((edge G) * bool).
(* Undirected path = a vertex and a sequence of directed edges.
   We cannot take a sequence of vertices as we can have multiple edges between two vertices.
   Having an alternating sequence of vertices and edges is tedious.
   We could have taken a vertex and a sequence of directed edges, because there are difficulties
   for the endpoints of a path due to the empty path. *)
(* Definition upath := ((vertex G) * seq ((edge G) * bool))%type. TODO? *)

(* Endpoints of an undirected path.
   We need a vertex s for the empty path *)
Definition upath_endpoint (b : bool) (s : G) (p : upath) :=
  match b with
  | false => head s [seq usource e | e <- p]
  | true  => last s [seq utarget e | e <- p]
  end.
Notation upath_source := (upath_endpoint false).
Notation upath_target := (upath_endpoint true).

Lemma upath_source_cat (s : G) (p q : upath) :
  upath_source s (p ++ q) = upath_source (upath_source s q) p.
Proof. by case: p. Qed.

Lemma upath_target_cat (s : G) (p q : upath) :
  upath_target s (p ++ q) = upath_target (upath_target s p) q.
Proof.
  move: p. induction q as [ | e q IH] => p.
  - by rewrite cats0.
  - by rewrite -cat_rcons IH /= map_rcons last_rcons.
Qed.

Fixpoint upath_rev (p : upath) : upath :=
  match p with
  | [::] => [::]
  | e :: q => rcons (upath_rev q) (reversed e)
  end.

Lemma upath_rev_fst (p : upath) :
  [seq e.1 | e <- upath_rev p] = rev [seq e.1 | e <- p].
Proof.
  induction p as [ | e p IH]; first by [].
  by rewrite /= rev_cons map_rcons IH.
Qed.

Lemma upath_rev_size (p : upath) :
  size (upath_rev p) = size p.
Proof. induction p as [ | e p IH]; by rewrite //= size_rcons IH. Qed.

Lemma upath_rev_rcons (p : upath) e :
  upath_rev (rcons p e) = reversed e :: upath_rev p.
Proof.
  move: e. induction p as [ | ? ? IH] => e //=.
  by rewrite IH rcons_cons.
Qed.

Lemma upath_rev_cat (p q : upath) :
  upath_rev (p ++ q) = upath_rev q ++ upath_rev p.
Proof.
  move: q. induction p as [ | ? ? IH] => q /=.
  - by rewrite cats0.
  - by rewrite IH rcons_cat.
Qed.

Lemma upath_rev_nil (p : upath) :
  (upath_rev p == [::]) = (p == [::]).
Proof.
  destruct p; first by [].
  apply/eqP. simpl. apply rcons_nil.
Qed.

Lemma upath_rev_inv : involutive upath_rev.
Proof.
  elim => //= ? ? IH.
  by rewrite upath_rev_rcons {}IH negb_involutive /= -surjective_pairing.
Qed.

Lemma upath_rev_in (p : upath) (e : edge G * bool) :
  (e \in upath_rev p) = (reversed e \in p).
Proof.
  move: p e. elim => //= a ? IH e.
  rewrite in_rcons in_cons {}IH.
  by destruct a as [? []], e as [? []].
Qed.

Lemma map_usource_upath_rev (p : upath) :
  [seq usource e | e <- upath_rev p] = rev [seq utarget e | e <- p].
Proof. induction p as [ | e p IH]; by rewrite // map_rcons {}IH rev_cons negb_involutive. Qed.

Lemma map_utarget_upath_rev (p : upath) :
  [seq utarget e | e <- upath_rev p] = rev [seq usource e | e <- p].
Proof. induction p as [ | e p IH]; by rewrite // map_rcons {}IH rev_cons. Qed.

Lemma head_upath_rev (e : edge G * bool) (p : upath) :
  head e (upath_rev p) = reversed (last (reversed e) p).
Proof.
  move: e. induction p as [ | ? ? IH] => e /=.
  - by rewrite negb_involutive -surjective_pairing.
  - by rewrite head_rcons IH /= negb_involutive -surjective_pairing.
Qed.

Lemma last_upath_rev (e : edge G * bool) (p : upath) :
  last e (upath_rev p) = reversed (head (reversed e) p).
Proof.
  destruct p => /=.
  - by rewrite negb_involutive -surjective_pairing.
  - by rewrite last_rcons.
Qed.

Lemma upath_endpoint_rev (b : bool) (v : G) (p : upath) :
  upath_endpoint b v (upath_rev p) = upath_endpoint (~~ b) v p.
Proof.
  destruct b => /=.
  - by rewrite map_utarget_upath_rev last_rev.
  - by rewrite map_usource_upath_rev head_rev.
Qed.

Definition upath_turn (p : upath) : upath :=
  match p with
  | [::] => [::]
  | e :: p => rcons p e
  end.

Lemma cyclic_source_eq_target (o : upath) (v : G)
  (e1 e2 : edge G * bool) :
  o <> [::] -> upath_source v o = upath_target v o ->
  utarget (last e1 o) = usource (head e2 o).
Proof. destruct o => //= _ ->. by rewrite -(last_map (fun e => utarget e)). Qed.


(** ** Undirected walk in an oriented multigraph *)
(* Fixpoint uwalk (x y : G) (p : upath) :=
  if p is e :: p' then (usource e == x) && uwalk (utarget e) y p' else x == y. *)
Fixpoint uwalk (p : upath) :=
  if p is e :: p' then (utarget e == upath_source (utarget e) p') && uwalk p' else true.

(* TODO ?
Definition close (p : upath) : bool :=
  match p with
  | [::] => true (* false? *)
  | e :: _ => upath_source (usource e) p == upath_target (usource e) p
  end.
*)

Lemma uwalk_rcons (p : upath) (e : edge G * bool) :
  uwalk (rcons p e) = uwalk p && (usource e == upath_target (usource e) p).
Proof.
  move: e. induction p as [ | ep p IH] => e.
  - by rewrite /= !eq_refl.
  - rewrite /= IH andbA map_rcons head_rcons.
    destruct p; last by [].
    by rewrite !eq_refl /= !andb_true_r eq_sym.
Qed.

Lemma uwalk_cat (p q : upath) :
  uwalk (p ++ q) = (uwalk p) && (uwalk q) &&
                   ((p == [::]) || (q == [::]) ||
                   [forall v, upath_target v p == upath_source v q]).
Proof.
  induction p as [ | e p IH] => /=; first by rewrite andb_true_r.
  rewrite {}IH.
  destruct p, q as [ | f q]; rewrite ?eq_refl ?andb_true_r //=; try lia.
  case: (utarget e == usource f) => //=.
  - replace [forall v, true] with true; first by lia.
    symmetry. by apply/forallP.
  - replace [forall v, false] with false; first by rewrite andb_false_r.
    symmetry. apply/forallPn. by exists (usource e).
Qed.

(* Lemma uwalk_cat (p q : upath) : G ->
  uwalk (p ++ q) = (uwalk p) && (uwalk q) && [exists v, upath_target v p == upath_source v q].
Proof.
  move=> v. induction p as [ | e p IH] => /=.
  - enough ([exists v, v == upath_source v q]) as -> by by rewrite andb_true_r.
    apply/existsP. exists (upath_source v q). by destruct q.
  - rewrite {}IH /=.
    transitivity ((utarget e == head (utarget e) [seq usource _e | _e <- p ++ q]) &&
      [exists v, last v [seq utarget e | e <- p] == head v [seq usource e | e <- q]] &&
      (uwalk p) && (uwalk q)); first by lia.
    transitivity ((utarget e == head (utarget e) [seq usource _e | _e <- p]) &&
      [exists v, last (utarget e) [seq utarget e | e <- p] == head v [seq usource e | e <- q]] &&
      (uwalk p) && (uwalk q)); last by lia.
    f_equal. f_equal.
    destruct p, q as [ | f q]; rewrite ?eq_refl //=.
    + transitivity true; [ | symmetry]; apply/existsP; by exists (utarget e).
    + case: (utarget e == usource f); simpl.
      * transitivity true; [ | symmetry]; apply/existsP; by exists (usource f).
      * symmetry. by apply/existsPn.
Qed. *)

Lemma uwalk_subK (p q : upath) :
  uwalk (p ++ q) -> uwalk p /\ uwalk q.
Proof. rewrite uwalk_cat. destruct p, q; introb. Qed.

Lemma uwalk_sub (p q r : upath) :
  uwalk (p ++ q ++ r) -> uwalk q.
Proof. move=> W. apply uwalk_subK in W as [_ W]. by apply uwalk_subK in W as [-> _]. Qed.

Lemma uwalk_rev (p : upath) :
  uwalk (upath_rev p) = uwalk p.
Proof.
  induction p as [ | e p IH];
  by rewrite // uwalk_rcons upath_endpoint_rev IH negb_involutive /= andbC.
Qed.

Lemma uwalk_turn (v : G) (p : upath) :
  upath_source v p = upath_target v p ->
  uwalk p -> uwalk (upath_turn p).
Proof.
  destruct p as [ | e p] => //=.
  rewrite uwalk_rcons => -> /andP[_ ->].
  destruct p => //=.
Qed.

Lemma uwalk_turns (v : G) (p q : upath) :
  upath_source v (p ++ q) = upath_target v (p ++ q) ->
  uwalk (p ++ q) -> uwalk (q ++ p).
Proof.
  move: q. induction p as [ | e p IH] => q.
  { by rewrite cats0. }
  replace (q ++ e :: p) with ((q ++ [:: e]) ++ p) by by rewrite -catA.
  move=> cyclic W.
  apply IH.
  - move: cyclic W.
    rewrite /= !map_cat !head_cat !last_cat /=.
    destruct p, q; introb.
  - have := uwalk_turn cyclic W.
    by rewrite /= rcons_cat cats1.
Qed.

Lemma mem_usource_utarget_uwalk (v : G) (p: upath) :
  uwalk p -> rcons [seq usource e | e <- p] (upath_target v p) =
    (upath_source v p) :: [seq utarget e | e <- p].
Proof.
  move: v. induction p as [ | e p IH] => v //=.
  move=> /andP[/eqP-source_p W].
  by rewrite (IH (utarget e) W) /= -source_p.
Qed.

Lemma mem_usource_utarget_cycle (v : G) (p: upath) :
  upath_source v p = upath_target v p -> uwalk p ->
  [seq usource e | e <- p] =i [seq utarget e | e <- p].
Proof.
  destruct p => //= cyclic_p /andP[/eqP--> W].
  rewrite -(mem_usource_utarget_uwalk _ W) cyclic_p.
  apply eq_mem_sym, mem_rcons.
Qed.

Lemma endpoint_of_edge_in_cycle (o : upath) :
  [seq utarget a | a <- o] =i [seq usource a | a <- o] ->
  forall e, e \in [seq a.1 | a <- o] ->
  forall b, endpoint b e \in [seq usource a | a <- o].
Proof.
  move=> Omem e E b'.
  apply in_map_fst in E as [b E].
  destruct (eq_or_eq_negb b b'); subst b'.
  - by rewrite -Omem (map_f (fun e => utarget e) E).
  - by apply (map_f (fun e => usource e) E).
Qed.

Lemma uwalk_nth (p : upath) (i : nat) :
  uwalk p -> i.+1 < size p ->
  forall e f,
  usource (nth e p i.+1) = utarget (nth f p i).
Proof.
  move: p. induction i as [ | i IH] => p W i1_lt e f.
  - destruct p as [ | ? [ | ? p]] => //=.
    by move: W => /= /andP[/eqP--> _].
  - destruct p as [ | a p] => //=.
    apply IH.
    + by move: W => /= /andP[_ ->].
    + simpl in i1_lt. lia.
Qed.


Definition upath_disjoint {I : finType} (f : edge G -> option I)
  (p q : upath) := [disjoint [seq f x.1 | x <- p] & [seq f x.1 | x <- q]].

(* TODO c'est le vrai disjoint, l'autre est plutôt un f-disjoint *)
(* TODO Utiliser plutôt disjoint avec f = id ? pour en déduire des lemmes *)
(* TODO renommer ; et mettre ailleurs ? *)
(* Definition upath_disjoint2 (p q : upath) :=
  [disjoint [seq x.1 | x <- p] & [seq x.1 | x <- q]].

Lemma upath_disjoint2_sym (p q : upath) :
  upath_disjoint2 p q = upath_disjoint2 q p.
Proof. by rewrite /upath_disjoint2 disjoint_sym. Qed.

Lemma upath_disjoint2_rev (p q : upath) :
  upath_disjoint2 p q -> upath_disjoint2 (upath_rev p) q.
Proof. by rewrite /upath_disjoint2 upath_rev_fst disjoint_rev. Qed. *)

End Graph.
Notation upath_source := (upath_endpoint false).
Notation upath_target := (upath_endpoint true).

Lemma uwalk_in_subgraph {Lv Le : Type} {G : graph Lv Le} {V : {set G}} {E : {set edge G}}
  (con : consistent V E) (p : @upath _ _ (subgraph_for con)) :
  uwalk p = uwalk [seq (val e.1, e.2) | e <- p].
Proof.
  induction p as [ | e p IH] => //=.
  rewrite {}IH eq_sym sub_val_eq eq_sym /=.
  by destruct p.
Qed.

(** ** Some lemmae when considering standard isomorphisms (those which do not flip edges) *)
(** Isomorphisms preserve out/in-edges *)
Lemma edges_at_outin_iso {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (h : F ≃ G) :
  h.d =1 xpred0 ->
  forall b v, edges_at_outin b (h v) = [set h.e e | e in edges_at_outin b v].
Proof.
  move=> H b v. apply/setP => e.
  by rewrite -[e](bijK' h.e) bij_imset_f !inE endpoint_iso H bij_eqLR bijK.
Qed.

Definition iso_path {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (h : F ≃ G)
  (p : upath) : upath :=
  [seq (h.e e.1, e.2) | e <- p].

Lemma iso_walk {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (h : F ≃ G) :
  h.d =1 xpred0 ->
  forall p, uwalk p -> uwalk (iso_path h p).
Proof.
  move=> H p. induction p as [ | u p HP] => //= /andP[/eqP-usource_p W].
  rewrite !endpoint_iso !H {1}usource_p (HP W) andb_true_r /=.
  clear -H.
  destruct p as [ | e p] => //=.
  by rewrite endpoint_iso H.
Qed.
