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
(* We consider edges in both directions. *)
Notation forward e := (e, true). (* An edge taken from source to target *)
Notation backward e := (e, false). (* An edge taken from target to source *)
Notation reversed e := (e.1, ~~ e.2).
(* Notation usource e := (endpoint (~~ e.2) e.1).
Notation utarget e := (endpoint e.2 e.1). *)

(* TODO with more standard vocabulary: path = open simple walk, trail = no repetition of edges, cycle = close simple walk *)
Section Graph.

Context {Lv Le : Type} {G : graph Lv Le}.

Definition uendpoint (b : bool) (e : (edge G) * bool) :=
  endpoint (if b then e.2 else ~~ e.2) e.1.
(* As a Notation and not a Definition as otherwise we need to unfold it way too often? *)
(* Notation uendpoint b e :=
  (endpoint (if b then e.2 else ~~ e.2) e.1). *)
(* Arguments uendpoint b e /. *)
Notation usource e := (uendpoint false e).
Notation utarget e := (uendpoint true e).

Lemma uendpoint_reversed (b : bool) (e : edge G * bool) :
  uendpoint b (reversed e) = uendpoint (~~ b) e.
Proof.  by destruct b, e as [? []]. Qed.
(*
Lemma usource_reversed (e : edge G * bool) :
  usource (reversed e) = utarget e.
Proof. by rewrite uendpoint_reversed. Qed.
Lemma utarget_reversed (e : edge G * bool) :
  utarget (reversed e) = usource e.
Proof. by destruct e. Qed.
*)

(* An undirected path is a sequence of unoriented edges, ie of couples (e, b) *)
Definition upath := seq ((edge G) * bool).

Definition upath_endpoint (b : bool) (s : G) (p : upath) :=
  match b with
  | false => head s [seq usource e | e <- p]
  | true  => last s [seq utarget e | e <- p]
  end.
Notation upath_source := (upath_endpoint false).
Notation upath_target := (upath_endpoint true).

Lemma upath_target_cat (s : G) (p q : upath) :
  upath_target s (p ++ q) = upath_target (upath_target s p) q.
Proof.
  move: p. induction q as [ | e q IH] => p.
  - by rewrite cats0.
  - by rewrite -cat_rcons IH /= map_rcons last_rcons.
Qed.

(* Reverse of an undirected path *)
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

Lemma map_uendpoint_upath_rev (b : bool) (p : upath) :
  [seq uendpoint b e | e <- upath_rev p] = rev [seq uendpoint (~~ b) e | e <- p].
Proof. induction p as [ | [? []] ? IH], b; by rewrite // map_rcons {}IH rev_cons. Qed.
Notation map_usource_upath_rev := (map_uendpoint_upath_rev false).
Notation map_utarget_upath_rev := (map_uendpoint_upath_rev true).
(* Lemma map_usource_upath_rev (p : upath) :
  [seq usource e | e <- upath_rev p] = rev [seq utarget e | e <- p].
Proof. induction p as [ | e p IH]; by rewrite // map_rcons {}IH rev_cons negb_involutive. Qed.
Lemma map_utarget_upath_rev (p : upath) :
  [seq utarget e | e <- upath_rev p] = rev [seq usource e | e <- p].
Proof. induction p as [ | e p IH]; by rewrite // map_rcons {}IH rev_cons. Qed. *)

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
Proof. by destruct b; rewrite /= map_uendpoint_upath_rev ?last_rev ?head_rev. Qed.

(* Rotating a cycle *)
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
(* We explicitely put endpoints x and y so as to always use uwalk and never
  upath_endpoint, that needs a vertex as a base value. *)
Fixpoint uwalk (x y : G) (p : upath) :=
  if p is e :: p' then (usource e == x) && uwalk (utarget e) y p' else x == y.

Lemma uwalk_endpoint (p : upath) (x y : G) :
  uwalk x y p -> upath_source x p = x /\ upath_target x p = y.
Proof.
  move: x. induction p as [ | e p IH] => x /=.
  - by move=> /eqP-->.
  - move=> /andP[/eqP--> W].
    by destruct (IH _ W) as [_ <-].
Qed.
(* TODO with bool instead of source and target? *)

Lemma uwalk_eq (p : upath) (x y s t : G) :
  p <> [::] -> uwalk x y p -> uwalk s t p -> x = s /\ y = t.
Proof.
  move: x s. induction p as [ | e p IH] => //= x s _ /andP[/eqP-? W] /andP[/eqP-? W'].
  subst x s. split; first by [].
  destruct p as [ | f p].
  - by move: W W' => /eqP-<- /eqP-<-.
  - assert (H : f :: p <> nil) by by [].
    apply (IH _ _ H W W').
Qed.
(* TODO would be good not to use it *)

Lemma uwalk_rcons (s t : G) (p : upath) (e : edge G * bool) :
  uwalk s t (rcons p e) = (uwalk s (usource e) p) && (utarget e == t).
Proof.
  move: s. induction p as [ | ? ? IH] => s /=.
  - by rewrite eq_sym.
  - by rewrite IH andbA.
Qed.

(* Lemma uwalk_cat (s i t : G) (p q : upath) :
  uwalk s i p -> uwalk i t q -> uwalk s t (p ++ q).
Proof.
  move: s. induction p as [ | e p IH] => s /= Wp Wq; move: Wp.
  - by move=> /eqP-->.
  - move=> /andP[/eqP-<- ?]. by rewrite eq_refl /= IH.
Qed. *)
(* Lemma uwalk_cat_bis (s t : G) (p q : upath) :
  uwalk s t (p ++ q) = [exists i, uwalk s i p && (uwalk i t q)].
Proof.
  move: s. induction p as [ | e p IH] => s /=.
  - case/boolP: (uwalk s t q) => uwalk_q; symmetry.
    + apply/existsP. exists s.
      by rewrite eq_refl uwalk_q.
    + apply/existsPn => i.
      by case/boolP: (s == i) => // /eqP-<-.
  - rewrite {}IH.
    case/boolP: (usource e == s) => _ //=.
    symmetry. by apply/existsPn.
Qed. *)
Lemma uwalk_cat (s t : G) (p q : upath) :
  uwalk s t (p ++ q) = uwalk s (upath_target s p) p && (uwalk (upath_target s p) t q).
Proof.
  move: s. induction p as [ | ? ? IH] => s /=.
  - by rewrite eq_refl.
  - rewrite {}IH /=. lia.
Qed. (* TODO use only the bis or ter and then remove the old ones *)

Lemma uwalk_sub_middle (s t : G) (p q : upath) :
  uwalk s t (p ++ q) -> upath_target s p = upath_source t q.
Proof. rewrite uwalk_cat => /andP[_ /uwalk_endpoint[? ?]]. by destruct q. Qed.

(* Lemma uwalk_subK (s t : G) (p q : upath) :
  uwalk s t (p ++ q) -> uwalk s (upath_target s p) p /\ uwalk (upath_source t q) t q.
Proof.
  move: s t q; induction p as [ | e p Hp] => s t q W /=.
  - split; trivial.
    assert (H := uwalk_sub_middle W). cbn in H. by rewrite -H.
  - cbn in *. move: W => /andP[/eqP--> W].
    rewrite eq_refl /=. apply (Hp _ _ _ W).
Qed. *)

(* Lemma uwalk_sub (s t : G) (p q r : upath) :
  uwalk s t (p ++ q ++ r) -> uwalk (upath_target s p) (upath_source t r) q.
Proof.
  move=> W.
  assert (W' : uwalk (upath_target s p) t (q ++ r)).
  { rewrite (uwalk_sub_middle W). by destruct (uwalk_subK W) as [_ ->]. }
  rewrite -(uwalk_sub_middle W'). by destruct (uwalk_subK W') as [-> _].
Qed. *)

Lemma uwalk_rev (s t : G) (p : upath) :
  uwalk s t (upath_rev p) = uwalk t s p.
Proof.
  move: t. induction p as [ | ? ? IH] => t //=.
  by rewrite uwalk_rcons {}IH 2!uendpoint_reversed andbC.
Qed.

Lemma uwalk_turn (s : G) (e : edge G * bool) (p : upath) :
  uwalk s s (e :: p) -> uwalk (utarget e) (utarget e) (upath_turn (e :: p)).
Proof. by rewrite uwalk_rcons eq_refl andb_true_r => /= /andP[/eqP-<- W]. Qed.

Lemma uwalk_turns (s : G) (p q : upath) :
  uwalk s s (p ++ q) -> uwalk (upath_source s q) (upath_source s q) (q ++ p).
Proof.
  move: p. induction q as [ | e q IH] => p /=.
  { by rewrite cats0. }
  replace (p ++ e :: q) with ((p ++ [:: e]) ++ q) by by rewrite -catA.
  move=> W. rewrite eq_refl /=.
  move: IH => /(_ _ W).
  rewrite catA cats1 uwalk_rcons.
  by move=> /andP[? /eqP-->].
Qed.

Lemma mem_usource_utarget_uwalk (s t : G) (p: upath) :
  uwalk s t p -> t :: [seq usource e | e <- p] =i s :: [seq utarget e | e <- p].
Proof.
  move: s. induction p as [ | e p IH] => s /=.
  { by move=> /eqP-->. }
  move=> /andP[/eqP-? W] x. subst s.
  move: IH => /(_ _ W x) {W}.
  rewrite !in_cons. lia.
Qed.

Lemma mem_usource_utarget_cycle (s : G) (p: upath) :
  uwalk s s p -> [seq usource e | e <- p] =i [seq utarget e | e <- p].
Proof. destruct p => //= /andP[/eqP--> W]. exact (mem_usource_utarget_uwalk W). Qed.

Lemma endpoint_of_edge_in_cycle (o : upath) :
  [seq utarget a | a <- o] =i [seq usource a | a <- o] ->
  forall e, e \in [seq a.1 | a <- o] ->
  forall b, endpoint b e \in [seq usource a | a <- o].
Proof.
  move=> Omem e E b'.
  apply in_map_fst in E as [b E].
  destruct (eq_or_eq_negb b b'); subst b'.
  - by rewrite -Omem (map_f _ E).
  - by rewrite (map_f _ E).
Qed.

Lemma uwalk_nth (p : upath) (s t : G) (i : nat) :
  uwalk s t p -> i.+1 < size p ->
  forall e f,
  usource (nth e p i.+1) = utarget (nth f p i).
Proof.
  move: p s. induction i as [ | i IH] => p s uwalk_p i1_lt e f.
  - destruct p as [ | ? [ | ? p]] => //=.
    by move: uwalk_p => /= /andP[_ /andP[/eqP--> _]].
  - destruct p as [ | a p] => //=.
    apply (IH _ (utarget a)).
    + by move: uwalk_p => /= /andP[_ ->].
    + simpl in i1_lt. lia.
Qed.

Definition upath_disjoint {I : finType} (f : edge G -> option I) (p q : upath) :=
  [disjoint [seq f x.1 | x <- p] & [seq f x.1 | x <- q]].

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
Notation usource := (uendpoint false).
Notation utarget := (uendpoint true).
Notation upath_source := (upath_endpoint false).
Notation upath_target := (upath_endpoint true).

Lemma uwalk_in_subgraph {Lv Le : Type} {G : graph Lv Le} {V : {set G}} {E : {set edge G}}
  (con : consistent V E) (p : @upath _ _ (subgraph_for con)) s t :
  uwalk s t p = uwalk (val s) (val t) [seq (val e.1, e.2) | e <- p].
Proof.
  move: s. induction p as [ | ? ? IH] => s //=.
  by rewrite {}IH eq_sym sub_val_eq eq_sym.
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
  forall p s t, uwalk s t p -> uwalk (h s) (h t) (iso_path h p).
Proof.
  move=> H p. induction p as [ | e p IH] => s t /=.
  - by move=> /eqP-->.
  - move=> /andP[/eqP-<- ?].
    rewrite /uendpoint !endpoint_iso !H eq_refl /=.
    by apply IH.
Qed.
