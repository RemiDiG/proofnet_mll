(* Extension for [mgraph] of the library GraphTheory *)

From Coq Require Import Bool.
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import mgraph.

Import EqNotations.

Set Mangle Names.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(** ** Out & In edges of a vertex *)
Definition edges_at_subset (b : bool) {Lv Le : Type} {G : graph Lv Le} (v : G) : {set edge G} :=
  [set e | endpoint b e == v].
Notation edges_out_at_subset := (edges_at_subset false).
Notation edges_in_at_subset := (edges_at_subset true).

Lemma endpoint_in_edges_at_subset (b : bool) {Lv Le : Type} {G : graph Lv Le} (e : edge G) :
  e \in edges_at_subset b (endpoint b e).
Proof. by rewrite in_set. Qed.
Notation source_in_edges_out := (endpoint_in_edges_at_subset false).
Notation target_in_edges_in := (endpoint_in_edges_at_subset true).


(** ** Undirected path in an oriented multigraph *)
Notation forward e := (e, true).
Notation backward e := (e, false).

Definition upath {Lv Le : Type} {G : graph Lv Le} := seq ((edge G) * bool).
Notation usource e := (endpoint (~~e.2) e.1).
Notation utarget e := (endpoint e.2 e.1).

Definition endpoint_upath {Lv Le : Type} {G : graph Lv Le} (b : bool) (s : G) (p : upath) :=
  match b with
  | false => head s [seq usource e | e <- p]
  | true => last s [seq utarget e | e <- p]
  end.
Notation source_upath := (endpoint_upath false).
Notation target_upath := (endpoint_upath true). 

Definition disjoint_upaths {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I)
  (p q : @upath _ _ G) := [disjoint [seq f x.1 | x <- p] & [seq f x.1 | x <- q]].

Fixpoint uwalk {Lv Le : Type} {G : graph Lv Le} (x y : G) (w : upath) :=
  if w is e :: w' then (usource e == x) && uwalk (utarget e) y w' else x == y.

Lemma uwalk_endpoint {Lv Le : Type} {G : graph Lv Le} (p : upath) :
  forall (x y : G), uwalk x y p -> source_upath x p = x /\ target_upath x p = y.
Proof.
  induction p as [ | (e, b) p IH]; move => x y; cbn.
  { by move => /eqP ->. }
  move => /andP[/eqP -> W]. split; trivial.
  specialize (IH _ _ W). by destruct IH as [_ <-].
Qed.

Lemma uwalk_eq {Lv Le : Type} {G : graph Lv Le} (p : upath) :
  forall (x y s t : G), p <> nil -> uwalk x y p -> uwalk s t p -> x = s /\ y = t.
Proof.
  induction p as [ | (e, b) p IH]; try by [].
  move => x y s t _ /andP[/eqP w W] /andP[/eqP w' W']; subst x s. split; trivial.
  destruct p as [ | p0 p].
  - revert W W'; by move => /eqP <- /eqP <-.
  - assert (H : p0 :: p <> nil) by by [].
    apply (IH _ _ _ _ H W W').
Qed.

Lemma uwalk_cat {Lv Le : Type} {G : graph Lv Le} (s i t : G) (p q : upath) :
  uwalk s i p -> uwalk i t q -> uwalk s t (p ++ q).
Proof.
  revert s i t q; induction p as [ | e p Hp]; intros s i t q Wp Wq.
  - revert Wp; by move => /eqP ->.
  - revert Wp; cbn; move => /andP[/eqP <- Wp]. apply /andP; split; trivial.
    by apply (Hp _ i).
Qed.

Lemma uwalk_sub_middle {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q : upath) :
  uwalk s t (p ++ q) -> target_upath s p = source_upath t q.
Proof.
  revert s t q; induction p as [ | e p Hp]; intros s t q; cbn in *.
  - destruct q; cbn.
    + by move => /eqP ->.
    + by move => /andP[/eqP -> _].
  - move =>/andP[_ W]. apply (Hp _ _ _ W).
Qed.

Lemma uwalk_sub_1 {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q : upath) :
  uwalk s t (p ++ q) -> uwalk s (target_upath s p) p /\ uwalk (source_upath t q) t q.
Proof.
  revert s t q; induction p as [ | e p Hp]; intros s t q W.
  - cbn. split; trivial.
    assert (H := uwalk_sub_middle W). cbn in H. by rewrite -H.
  - cbn in *. revert W; move => /andP[/eqP -> W].
    split; [apply /andP; split; trivial | ]; apply (Hp _ _ _ W).
Qed.

Lemma uwalk_sub {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q r : upath) :
  uwalk s t (p ++ q ++ r) -> uwalk (target_upath s p) (source_upath t r) q.
Proof.
  intro W.
  assert (W' : uwalk (target_upath s p) t (q ++ r)).
  { rewrite (uwalk_sub_middle W). by destruct (uwalk_sub_1 W) as [_ ->]. }
  rewrite -(uwalk_sub_middle W'). by destruct (uwalk_sub_1 W') as [-> _].
Qed.

Fixpoint upath_rev {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) :=
  match p with
  | [::] => [::]
  | (e, b) :: q => rcons (upath_rev q) (e, ~~b)
  end.

Lemma upath_rev_size {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) :
  size (upath_rev p) = size p.
Proof.
  induction p as [ | (e, b) p H]; trivial; cbn.
  by rewrite size_rcons H.
Qed.

Lemma upath_rev_cat {Lv Le : Type} {G : graph Lv Le} (p q : @upath _ _ G) :
  upath_rev (p ++ q) = upath_rev q ++ upath_rev p.
Proof.
  revert q; induction p as [ | (e, b) p H]; intro q; cbn.
  { by rewrite cats0. }
  by rewrite H rcons_cat.
Qed.

Lemma upath_rev_inv {Lv Le : Type} {G : graph Lv Le} : involutive (@upath_rev _ _ G).
Proof.
  intro p. induction p as [ | (e, b) p H]; trivial; cbn.
  by rewrite -cats1 upath_rev_cat H /= negb_involutive.
Qed.

Lemma upath_rev_fst {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) :
  [seq e.1 | e <- upath_rev p] = rev [seq e.1 | e <- p].
Proof.
  rewrite -map_rev.
  induction p as [ | (e, b) p IH]; trivial; cbn.
  by rewrite rev_cons !map_rcons IH.
Qed.

Lemma upath_rev_in {Lv Le : Type} {G : graph Lv Le} (p : upath) :
  forall (e : edge G) (b : bool), ((e, b) \in upath_rev p) = ((e, ~~b) \in p).
Proof.
  induction p as [ | (e, b) p H]; intros a c; trivial; cbn.
  rewrite -has_pred1 has_rcons has_pred1 in_cons H; cbn; rewrite eq_sym.
  by replace (eqb (~~ b) c) with (~~ c == b) by by rewrite eqb_negLR eq_sym.
Qed.

Lemma uwalk_rcons {Lv Le : Type} {G : graph Lv Le} (s t : G) (p : upath) (e : edge G * bool) :
  uwalk s t (rcons p e) = (uwalk s (usource e) p) && (utarget e == t).
Proof.
  revert s t e; induction p as [ | ep p IH]; intros s t e; cbn.
  all: apply /eqP; cbn; apply /eqP; case: ifP => /eqP ?; subst.
  - by rewrite eq_refl.
  - symmetry; apply andb_false_intro1. apply /eqP. by apply nesym.
  - rewrite eq_refl. apply IH.
  - symmetry; apply andb_false_intro1, andb_false_intro1. by apply /eqP.
Qed.

Lemma uwalk_rev {Lv Le : Type} {G : graph Lv Le} (s t : G) (p : upath) :
  uwalk s t p -> uwalk t s (upath_rev p).
Proof.
  revert s t; induction p as [ | (e, b) p H]; intros s t; cbn.
  { by move => /eqP ->. }
  move => /andP[/eqP <- W].
  rewrite uwalk_rcons negb_involutive. apply /andP; split; trivial.
  by apply H.
Qed.


(** ** Simpl undirected paths : paths whose edges have different id and are not forbidden *)
(** The function f : edge G -> option I is used to identify some edges. *)
(** Taking f := fun e => Some e gives the standard simple paths, which do not use the
same edge twice *)
Definition simpl_upath {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : upath) :=
  (uwalk s t p) && uniq ([seq f e.1 | e <- p]) && (None \notin [seq f e.1 | e <- p]).

Record Simpl_upath {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :
  predArgType := {upval :> upath;  upvalK : simpl_upath f s t upval}.
Canonical Simpl_upath_subType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  [subType for (@upval _ _ _ _ f s t)].
Definition Simpl_upath_eqMixin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in [eqMixin of Simpl_upath f s t by <:].
Canonical Simpl_upath_eqType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in EqType (Simpl_upath f s t) (Simpl_upath_eqMixin f s t).
Definition Simpl_upath_choiceMixin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in [choiceMixin of (Simpl_upath f s t) by <:].
Canonical Simpl_upath_choiceType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in ChoiceType (Simpl_upath f s t) (Simpl_upath_choiceMixin f s t).
Definition Simpl_upath_countMixin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in [countMixin of (Simpl_upath f s t) by <:].
Canonical Simpl_upath_countType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in CountType (Simpl_upath f s t) (Simpl_upath_countMixin f s t).

Lemma upath_catK {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s i t : G)
  (p : Simpl_upath f s i) (q : Simpl_upath f i t) :
  disjoint_upaths f p q -> simpl_upath f s t (val p ++ val q).
Proof.
  revert p q; move => [p P] [q Q] /=; revert P Q;
  move => /andP[/andP[Wp Up] Np] /andP[/andP[Wq Uq] Nq] D.
  repeat (apply /andP; split).
  - apply (uwalk_cat Wp Wq).
  - rewrite map_cat cat_uniq. repeat (apply /andP; split); trivial.
    by rewrite /disjoint_upaths disjoint_sym disjoint_has in D.
  - rewrite map_cat mem_cat. apply /norP; split; trivial.
Qed.

Definition upath_cat {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s i t : G)
  (p : Simpl_upath f s i) (q : Simpl_upath f i t) (D : disjoint_upaths f p q) :=
   {| upval := val p ++ val q ; upvalK := upath_catK D |}.

Lemma upath_subK_1 {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p q : upath) :
  simpl_upath f s t (p ++ q) -> simpl_upath f s (target_upath s p) p /\ simpl_upath f (source_upath t q) t q.
Proof.
  move => /andP[/andP[W U] N].
  revert U N. rewrite !map_cat cat_uniq mem_cat. move =>/andP[Up /andP[_ ?]] /norP[? ?].
  split; repeat (apply /andP; split); trivial; apply (uwalk_sub_1 W).
Qed.

Lemma upath_subK {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p q r : upath) :
  simpl_upath f s t (p ++ q ++ r) -> simpl_upath f (target_upath s p) (source_upath t r) q.
Proof.
  intro H.
  assert (H' : simpl_upath f (target_upath s p) t (q ++ r)).
  { assert (W : uwalk s t (p ++ q ++ r)).
    { revert H. by move => /andP[/andP[-> _] _]. }
    rewrite (uwalk_sub_middle W).
    by destruct (upath_subK_1 H) as [_ ->]. }
  assert (W' : uwalk (target_upath s p) t (q ++ r)).
  { revert H'. by move => /andP[/andP[-> _] _]. }
  rewrite -(uwalk_sub_middle W').
  by destruct (upath_subK_1 H') as [-> _].
Qed.

Definition upath_sub {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p q r : upath) (H : simpl_upath f s t (p ++ q ++ r)) :=
  {| upval := q ; upvalK := upath_subK H |}.

Lemma upath_revK {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : upath) :
  simpl_upath f s t p -> simpl_upath f t s (upath_rev p).
Proof.
  move =>/andP[/andP[W U] N]. repeat (apply /andP; split).
  - by apply uwalk_rev.
  - by rewrite map_comp upath_rev_fst map_rev rev_uniq -map_comp.
  - by rewrite map_comp upath_rev_fst map_rev -has_pred1 has_rev has_pred1 -map_comp.
Qed.

Definition upath_revS {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : Simpl_upath f s t) :=
  {| upval := upath_rev p ; upvalK := upath_revK (upvalK p) |}. (* TODO homogeneiser noms *)

Lemma upath_nilK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G) :
  simpl_upath f s s [::].
Proof. unfold simpl_upath; cbn. repeat (apply /andP; split); trivial. Qed.

Definition upath_nil {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G) :=
  {| upval := [::] ; upvalK := upath_nilK f s |}.


Definition uacyclic {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :=
  forall (x : G) (p : Simpl_upath f x x), p = upath_nil f x.

Definition uconnected {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :=
  forall (x y : G), exists (_ : Simpl_upath f x y), true.
