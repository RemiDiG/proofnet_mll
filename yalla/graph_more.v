(* Extension for [mgraph] of the library GraphTheory *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph structures bij.
From Yalla Require Import mll_prelim.

Import EqNotations.

Set Mangle Names.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

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
  destruct ([exists b, endpoint b e == v]) eqn:E.
  - revert E => /existsP[[] ->]; caseb.
  - revert E => /existsPn-E. splitb.
Qed.


(** ** Isomorphisms preserve cardinality *)
Lemma card_iso {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) :
  F ≃ G -> #|F| = #|G|.
Proof. intros [? _ _ _]. by apply card_bij. Qed.


(** ** The induced subgraph with all vertices is (isomorphic to) the whole graph *)
Lemma induced_all {Lv: comMonoid} {Le : elabelType} (G : graph Lv Le) :
  induced [set : G] ≃ G.
Proof.
  set f : induced [set : G] -> G := fun v => val v.
  set f' : G -> induced [set : G] := fun v => Sub v (in_setT v).
  assert (fK : cancel f f') by (intros [? ?]; cbnb).
  assert (fK' : cancel f' f) by (intros ?; cbnb).
  set iso_v := {| bij_fwd := _ ; bij_bwd := _ ; bijK := fK ; bijK' := fK' |}.
  set g : edge (induced [set : G]) -> edge G := fun e => val e.
  assert (Hg : forall e, e \in edge_set [set: G]).
  { intros. by rewrite !in_set. }
  set g' : edge G -> edge (induced [set : G]) := fun e => Sub e (Hg e).
  assert (gK : cancel g g') by (intros [? ?]; cbnb).
  assert (gK' : cancel g' g) by cbnb.
  set iso_e := {| bij_fwd := _ ; bij_bwd := _ ; bijK := gK ; bijK' := gK' |}.
  exists iso_v iso_e pred0.
  splitb; reflexivity.
Qed.


(** ** Undirected paths in an oriented multigraph *)
Notation forward e := (e, true).
Notation backward e := (e, false).

Definition upath {Lv Le : Type} {G : graph Lv Le} := seq ((edge G) * bool).
Notation usource e := (endpoint (~~e.2) e.1).
Notation utarget e := (endpoint e.2 e.1).

Definition upath_endpoint {Lv Le : Type} {G : graph Lv Le} (b : bool) (s : G) (p : upath) :=
  match b with
  | false => head s [seq usource e | e <- p]
  | true => last s [seq utarget e | e <- p]
  end.
Notation upath_source := (upath_endpoint false).
Notation upath_target := (upath_endpoint true).

Lemma upath_target_cat {Lv Le : Type} {G : graph Lv Le} (s : G) (p q : upath) :
  upath_target s (p ++ q) = upath_target (upath_target s p) q.
Proof.
  revert p; induction q as [ | e q IH] => p.
  { by rewrite cats0. }
  replace (p ++ e :: q) with ((rcons p e) ++ q) by by rewrite -cats1 -catA.
  rewrite IH.
  destruct q; trivial.
  by rewrite /= map_rcons last_rcons.
Qed.

Definition upath_disjoint {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I)
  (p q : @upath _ _ G) := [disjoint [seq f x.1 | x <- p] & [seq f x.1 | x <- q]].

Fixpoint upath_rev {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) : @upath _ _ G :=
  match p with
  | [::] => [::]
  | (e, b) :: q => rcons (upath_rev q) (e, ~~b)
  end.

Lemma upath_rev_size {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) :
  size (upath_rev p) = size p.
Proof. induction p as [ | (e, b) p H]; by rewrite // size_rcons H. Qed.

Lemma upath_rev_cat {Lv Le : Type} {G : graph Lv Le} (p q : @upath _ _ G) :
  upath_rev (p ++ q) = upath_rev q ++ upath_rev p.
Proof.
  revert q; induction p as [ | (e, b) p H] => q /=.
  - by rewrite cats0.
  - by rewrite H rcons_cat.
Qed.

Lemma upath_rev_inv {Lv Le : Type} {G : graph Lv Le} : involutive (@upath_rev _ _ G).
Proof.
  intro p. induction p as [ | (?, ?) ? H]; trivial; cbn.
  by rewrite -cats1 upath_rev_cat H /= negb_involutive.
Qed.

Lemma upath_rev_fst {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) :
  [seq e.1 | e <- upath_rev p] = rev [seq e.1 | e <- p].
Proof.
  rewrite -map_rev.
  induction p as [ | (e, b) p H]; trivial.
  by rewrite rev_cons !map_rcons H.
Qed.

Lemma upath_rev_in {Lv Le : Type} {G : graph Lv Le} (p : upath) :
  forall (e : edge G) (b : bool), ((e, b) \in upath_rev p) = ((e, ~~b) \in p).
Proof.
  induction p as [ | (e, b) p H] => a c //=.
  rewrite in_rcons in_cons H.
  by destruct b, c.
Qed.

Definition upath_turn {Lv Le : Type} {G : graph Lv Le} : @upath _ _ G -> @upath _ _ G :=
  fun p => match p with
  | [::] => [::]
  | e :: p => rcons p e
  end.


(** ** Undirected walks in an oriented multigraph *)
Fixpoint uwalk {Lv Le : Type} {G : graph Lv Le} (x y : G) (w : upath) :=
  if w is e :: w' then (usource e == x) && uwalk (utarget e) y w' else x == y.

Lemma uwalk_endpoint {Lv Le : Type} {G : graph Lv Le} (p : upath) :
  forall (x y : G), uwalk x y p -> upath_source x p = x /\ upath_target x p = y.
Proof.
  induction p as [ | (e, b) p IH] => x y /=.
  { by move => /eqP ->. }
  move => /andP[/eqP -> W]. split; trivial.
  by destruct (IH _ _ W) as [_ <-].
Qed.

Lemma uwalk_eq {Lv Le : Type} {G : graph Lv Le} (p : upath) :
  forall (x y s t : G), p <> nil -> uwalk x y p -> uwalk s t p -> x = s /\ y = t.
Proof.
  induction p as [ | (e, b) p IH]; try by [].
  move => x y s t _ /andP[/eqP ? W] /andP[/eqP ? W']; subst x s. split; trivial.
  destruct p as [ | f p].
  - by revert W W' => /eqP <- /eqP <-.
  - assert (H : f :: p <> nil) by by [].
    apply (IH _ _ _ _ H W W').
Qed.

Lemma uwalk_rcons {Lv Le : Type} {G : graph Lv Le} (s t : G) (p : upath) (e : edge G * bool) :
  uwalk s t (rcons p e) = (uwalk s (usource e) p) && (utarget e == t).
Proof.
  revert s t e; induction p as [ | ep p IH] => s t e /=.
  all: apply /eqP; cbn; apply /eqP; case: ifP => /eqP ?; subst.
  - by rewrite eq_refl.
  - symmetry; apply andb_false_intro1. apply /eqP. by apply nesym.
  - rewrite eq_refl. apply IH.
  - symmetry; apply andb_false_intro1, andb_false_intro1. by apply /eqP.
Qed.

Lemma uwalk_cat {Lv Le : Type} {G : graph Lv Le} (s i t : G) (p q : upath) :
  uwalk s i p -> uwalk i t q -> uwalk s t (p ++ q).
Proof.
  revert s i t q; induction p as [ | e p Hp] => s i t q Wp Wq; revert Wp; cbn.
  - by move => /eqP ->.
  - move => /andP[/eqP <- ?]. apply /andP; split; trivial. by apply (Hp _ i).
Qed.

Lemma uwalk_sub_middle {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q : upath) :
  uwalk s t (p ++ q) -> upath_target s p = upath_source t q.
Proof.
  revert s t q; induction p as [ | e p Hp] => s t q; cbn in *.
  - destruct q; cbn; [by move => /eqP -> | by move => /andP[/eqP -> _]].
  - move =>/andP[_ W]. apply (Hp _ _ _ W).
Qed.

Lemma uwalk_subK {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q : upath) :
  uwalk s t (p ++ q) -> uwalk s (upath_target s p) p /\ uwalk (upath_source t q) t q.
Proof.
  revert s t q; induction p as [ | e p Hp] => s t q W.
  - cbn. split; trivial.
    assert (H := uwalk_sub_middle W). cbn in H. by rewrite -H.
  - cbn in *. revert W => /andP[/eqP -> W].
    splitb; apply (Hp _ _ _ W).
Qed.

Lemma uwalk_sub {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q r : upath) :
  uwalk s t (p ++ q ++ r) -> uwalk (upath_target s p) (upath_source t r) q.
Proof.
  intro W.
  assert (W' : uwalk (upath_target s p) t (q ++ r)).
  { rewrite (uwalk_sub_middle W). by destruct (uwalk_subK W) as [_ ->]. }
  rewrite -(uwalk_sub_middle W'). by destruct (uwalk_subK W') as [-> _].
Qed.

Lemma uwalk_rev {Lv Le : Type} {G : graph Lv Le} (s t : G) (p : upath) :
  uwalk t s (upath_rev p) = uwalk s t p.
Proof.
  revert s t; induction p as [ | (e, b) p H] => s t /=.
  { apply eq_sym. }
  rewrite uwalk_rcons negb_involutive H.
  apply andb_comm.
Qed.

Lemma uwalk_turn {Lv Le : Type} {G : graph Lv Le} (s : G) (e : edge G * bool) (p : upath) :
  uwalk s s (e :: p) -> uwalk (utarget e) (utarget e) (upath_turn (e :: p)).
Proof. by rewrite uwalk_rcons eq_refl andb_true_r => /= /andP[/eqP <- W]. Qed.

Lemma uwalk_turns {Lv Le : Type} {G : graph Lv Le} (s : G) (p q : upath) :
  uwalk s s (p ++ q) -> uwalk (upath_source s q) (upath_source s q) (q ++ p).
Proof.
  revert p; induction q as [ | e q IH] => p /=.
  { by rewrite cats0. }
  replace (p ++ e :: q) with ((p ++ [:: e]) ++ q) by by rewrite -catA.
  intro W. splitb.
  specialize (IH _ W).
  rewrite catA cats1 uwalk_rcons in IH.
  by revert IH => /andP[? /eqP ->].
Qed.


(** ** Simple undirected paths : paths whose edges have different non-forbidden id *)
(** The function f : edge G -> option I is used to identify some edges. *)
(** Taking f := fun e => Some e gives the standard simple paths, which do not use the same edge twice *)
Definition supath {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : upath) :=
  (uwalk s t p) && uniq [seq f e.1 | e <- p] && (None \notin [seq f e.1 | e <- p]).

Record Supath {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :
  predArgType := {upval :> upath; upvalK : supath f s t upval}.
Canonical Ssupath_subType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  [subType for (@upval _ _ _ _ f s t)].
Definition Supath_eqMixin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in [eqMixin of Supath f s t by <:].
Canonical Supath_eqType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in EqType (Supath f s t) (Supath_eqMixin f s t).
Definition Supath_choiceMixin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in [choiceMixin of (Supath f s t) by <:].
Canonical Supath_choiceType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in ChoiceType (Supath f s t) (Supath_choiceMixin f s t).
Definition Supath_countMixin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in [countMixin of (Supath f s t) by <:].
Canonical Supath_countType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in CountType (Supath f s t) (Supath_countMixin f s t).

Lemma upath_size {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) p :
  supath f s t p -> size p < S #|edge G|.
Proof.
  move => /andP[/andP[_ U] _].
  rewrite map_comp in U.
  apply map_uniq in U.
  revert U => /card_uniqP U.
  rewrite size_map in U.
  rewrite -U.
  exact: max_card.
Qed.

Definition Supath_tuple {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : Supath f s t) : {n : 'I_(S #|edge G|) & n.-tuple (edge G * bool)} :=
  let (p, Up) := p in existT _ (Ordinal (upath_size Up)) (in_tuple p).

Definition tuple_Supath {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (m : {n : 'I_(S #|edge G|) & n.-tuple (edge G * bool)}) : option (Supath f s t) :=
  let (_, p) := m in match boolP (supath f s t p) with
  | AltTrue P => Some (Sub (val p) P)
  | AltFalse _ => None
  end.

Lemma Supath_tupleK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :
  pcancel (@Supath_tuple _ _ _ _ f s t) (tuple_Supath f s t).
Proof.
  move => [/= p P].
  case: {-}_ / boolP; last by rewrite P.
  by move => P'; rewrite (bool_irrelevance P' P).
Qed.

Definition Supath_finMixin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in PcanFinMixin (@Supath_tupleK _ _ _ _ f s t).
Canonical Supath_finType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in FinType (Supath f s t) (Supath_finMixin f s t).


Lemma supath_nin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p q : upath) :
  forall e b, supath f s t (p ++ e :: q) -> (e.1, b) \notin p ++ q.
Proof.
  move => e b.
  rewrite /supath !map_cat !cat_uniq /=.
  move => /andP[/andP[_ /andP[_ /andP[/norP[P _] /andP[Q _]]]] _].
  rewrite mem_cat; apply /negP => /orP[? | ?];
  [contradict P | contradict Q]; apply /negP/negPn/mapP; by exists (e.1, b).
Qed.

Lemma supath_catK {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s i t : G)
  (p : Supath f s i) (q : Supath f i t) :
  upath_disjoint f p q -> supath f s t (val p ++ val q).
Proof.
  revert p q; move => [p /andP[/andP[Wp Up] Np]] [q /andP[/andP[Wq Uq] Nq]] /= D.
  splitb.
  - apply (uwalk_cat Wp Wq).
  - rewrite map_cat cat_uniq. splitb.
    by rewrite /upath_disjoint disjoint_sym disjoint_has in D.
  - rewrite map_cat mem_cat. splitb.
Qed.

Definition supath_cat {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s i t : G)
  (p : Supath f s i) (q : Supath f i t) (D : upath_disjoint f p q) :=
  {| upval := val p ++ val q ; upvalK := supath_catK D |}.

Lemma supath_subKK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p q : upath) :
  supath f s t (p ++ q) -> supath f s (upath_target s p) p /\ supath f (upath_source t q) t q.
Proof.
  move => /andP[/andP[W U] N].
  revert U N. rewrite !map_cat cat_uniq mem_cat =>/andP[Up /andP[_ ?]] /norP[? ?].
  splitb; apply (uwalk_subK W).
Qed.

Lemma supath_subK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p q r : upath) :
  supath f s t (p ++ q ++ r) -> supath f (upath_target s p) (upath_source t r) q.
Proof.
  intro H.
  assert (W : uwalk s t (p ++ q ++ r)) by by revert H => /andP[/andP[-> _] _].
  assert (H' : supath f (upath_target s p) t (q ++ r)).
  { rewrite (uwalk_sub_middle W).
    by destruct (supath_subKK H) as [_ ->]. }
  assert (W' : uwalk (upath_target s p) t (q ++ r)) by by revert H' => /andP[/andP[-> _] _].
  rewrite -(uwalk_sub_middle W').
  by destruct (supath_subKK H') as [-> _].
Qed.

Definition supath_sub {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p q r : upath) (H : supath f s t (p ++ q ++ r)) :=
  {| upval := q ; upvalK := supath_subK H |}.

Lemma supath_revK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : upath) :
  supath f s t p -> supath f t s (upath_rev p).
Proof.
  move =>/andP[/andP[W U] N]. splitb.
  - by rewrite uwalk_rev.
  - by rewrite map_comp upath_rev_fst map_rev rev_uniq -map_comp.
  - by rewrite map_comp upath_rev_fst map_rev in_rev -map_comp.
Qed.

Definition supath_rev {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : Supath f s t) :=
  {| upval := _ ; upvalK := supath_revK (upvalK p) |}.

Lemma supath_turnK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G)
  (e : edge G * bool) (p : upath) :
  supath f s s (e :: p) -> supath f (utarget e) (utarget e) (upath_turn (e :: p)).
Proof.
  move =>/andP[/andP[W U] N]. splitb.
  - apply (uwalk_turn W).
  - rewrite map_rcons rcons_uniq.
    by revert U => /= /andP [-> ->].
  - rewrite map_rcons in_rcons.
    revert N; rewrite /= in_cons => /norP [n N].
    splitb.
Qed.
(*
Definition supath_turn {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G)
  (e : edge G * bool) ((e :: p) : Supath f s s) : ???. *)

Lemma supath_turnsK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G)
  (p q : upath) :
  supath f s s (p ++ q) -> supath f (upath_source s q) (upath_source s q) (q ++ p).
Proof.
  move =>/andP[/andP[W U] N]. splitb.
  - apply (uwalk_turns W).
  - by rewrite map_cat uniq_catC -map_cat.
  - by rewrite map_cat mem_cat orbC -mem_cat -map_cat.
Qed.
(* 
Definition supath_turns {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G)
  (p ++ q : Supath f s t) := ???. *)

Lemma supath_nilK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G) :
  supath f s s [::].
Proof. unfold supath; cbn. splitb. Qed.

Definition supath_nil {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G) :=
  {| upval := [::] ; upvalK := supath_nilK f s |}.


Definition uacyclic {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :=
  forall (x : G) (p : Supath f x x), p = supath_nil f x.

Definition uconnected {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :=
  forall (x y : G), exists (_ : Supath f x y), true.


(** ** Connectivity for functions injective except on None *)
Definition is_uconnected {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (x y : G) :=
  [exists p : Supath f x y, true].

Definition is_uconnected_id {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (x : G) :
  is_uconnected f x x.
Proof. apply /existsP. by exists (supath_nil _ _). Defined.

Definition is_uconnected_sym {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (x y : G) :
  is_uconnected f x y -> is_uconnected f y x.
Proof. move => /existsP[P _]. apply /existsP. by exists (supath_rev P). Defined.


Lemma uconnected_simpl {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) p :
  {in ~: f @^-1 None &, injective f} -> uwalk s t p -> None \notin [seq f e.1 | e <- p] -> Supath f s t.
Proof.
  move => F W N; revert s t W N; induction p as [ | e p IH] => s t.
  { move => /eqP <- _. exact (supath_nil f s). }
  rewrite /supath /= in_cons => /andP[/eqP <- W] {s} /norP[n N].
  revert IH => /(_ _ _ W N) {W N p} q.
  assert (P : supath f (usource e) (utarget e) (e :: nil)).
  { rewrite /supath !in_cons /= orb_false_r. splitb. }
  set p := {| upval := _ ; upvalK := P |}.
  destruct (upath_disjoint f p q) eqn:D.
  { exact (supath_cat D). }
  destruct q as [q Q].
  revert D; rewrite /upath_disjoint disjoint_sym disjoint_has /p has_sym /= orb_false_r => /negPn/mapP-E.
  assert (E' : exists2 a, a \in q & f e.1 == f a.1).
  { destruct E as [a]. exists a; trivial. by apply /eqP. }
  revert E' => {E} /sig2W[[a b] In /eqP-Hea].
  assert (a = e.1).
  { assert (a \in ~: f @^-1 None /\ e.1 \in ~: f @^-1 None) as [A E].
    { rewrite !in_set -Hea.
      by revert n => /eqP n; apply nesym in n; revert n => /eqP ->. }
    by apply (F _ _ A E). }
  subst a; clear Hea.
  apply in_elt_sub in In.
  assert (In' : exists n : nat, q == take n q ++ (e.1, b) :: drop n.+1 q).
  { destruct In as [k ?]. exists k. by apply /eqP. }
  revert In'. move => {In} /sigW[k /eqP-Qeq].
  rewrite Qeq in Q.
  destruct (supath_subKK Q) as [_ R], e as [e c]; cbn in *.
  destruct (eq_comparable b c); [subst b | ].
  * exact {| upval := _ ; upvalK := R |}.
  * assert (b = ~~c) by by destruct b, c. subst b.
    revert R. rewrite /supath map_cons in_cons /=.
    move => /andP[/andP[/andP[_ W] /andP[_ U]] /norP[_ N]].
    assert (R : supath f (endpoint (~~ c) e) t (drop k.+1 q)) by splitb.
    exact {| upval := _ ; upvalK := R |}.
Qed.

Definition is_uconnected_comp {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} ->
  forall (x y z : G), is_uconnected f x y -> is_uconnected f y z -> is_uconnected f x z.
Proof.
  move => F x y z /existsP[[pxy /andP[/andP[Wxy _] Nxy]] _] /existsP[[pyz /andP[/andP[Wyz _] Nyz]] _].
  enough (P : Supath f x z).
  { apply /existsP. by exists P. }
  apply (uconnected_simpl (p := pxy ++ pyz)); trivial.
  - by apply (uwalk_cat Wxy).
  - rewrite map_cat mem_cat. splitb.
Defined.

Global Instance is_uconnected_Equivalence {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) : CEquivalence (is_uconnected f).
Proof. constructor. exact (is_uconnected_id _). exact (is_uconnected_sym (f := _)). exact (is_uconnected_comp F). Defined.

Lemma is_uconnected_eq {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> forall u v w, is_uconnected f u v ->
  is_uconnected f u w = is_uconnected f v w.
Proof.
  move => F u v w UV.
  destruct (is_uconnected f v w) eqn:VW.
  - apply (is_uconnected_comp F UV VW).
  - destruct (is_uconnected f u w) eqn:UW; trivial.
    contradict VW; apply not_false_iff_true.
    apply (is_uconnected_comp F (is_uconnected_sym UV) UW).
Qed.

Lemma is_uconnected_equivalence {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} ->
  equivalence_rel (is_uconnected f).
Proof.
  intros F x y z. split.
  - apply is_uconnected_id.
  - by apply is_uconnected_eq.
Qed.

(** Equivalence classes of uconnected, so to speak about connected components *)
Definition uconnected_nb {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :=
  #|equivalence_partition (is_uconnected f) [set: G]|.

Lemma uconnected_to_nb1 {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> #|G| <> 0 -> uconnected f -> uconnected_nb f = 1.
Proof.
  move => F N C.
  destruct (set_0Vmem [set: G]) as [Hc | [v _]]; trivial.
  { contradict N. by rewrite -cardsT Hc cards0. }
  unfold uconnected_nb, equivalence_partition.
  apply /eqP/cards1P.
  exists [set u in [set: G] | is_uconnected f v u].
  apply /eqP/eq_set1P. split.
  { apply /imsetP. by exists v. }
  move => ? /imsetP [u _ ?]; subst.
  apply eq_finset => w.
  rewrite in_set /=.
  transitivity true; [ | symmetry]; apply /existsP; apply C.
Qed.

Lemma uconnected_from_nb1 {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> uconnected_nb f = 1 -> uconnected f.
Proof.
  move => F /eqP/cards1P[S /eqP/eq_set1P[Sin Seq]] u v.
  assert (Suin : [set w in [set: G] | is_uconnected f u w] \in
    equivalence_partition (is_uconnected f) [set: G]).
  { apply /imsetP. by exists u. }
  assert (UW := Seq _ Suin). cbn in UW. subst S.
  assert (Svin : [set w in [set: G] | is_uconnected f v w] \in
    equivalence_partition (is_uconnected f) [set: G]).
  { apply /imsetP. by exists v. }
  assert (Heq := Seq _ Svin). cbn in Heq. clear - F Heq.
  assert (V : v \in [set w in [set: G] | is_uconnected f v w]).
  { rewrite in_set. splitb. apply is_uconnected_id. }
  rewrite Heq in_set in V.
  by revert V => /andP[_ /existsP ?].
Qed.

Lemma nb1_not_empty {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  uconnected_nb f = 1 -> #|G| <> 0.
Proof.
  move => /eqP/cards1P[? /eqP/eq_set1P[Sin _]] N.
  rewrite -cardsT in N. apply cards0_eq in N.
  contradict Sin; apply /negP.
  rewrite N /equivalence_partition. apply /imsetP. move => [? In].
  contradict In; apply /negP.
  by rewrite !in_set.
Qed.

Definition neighbours {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G) :=
  [set utarget e | e : edge G * bool & (f e.1 != None) && (usource e == v)].

Lemma uacyclic_loop {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  uacyclic f -> forall e, f e <> None -> source e <> target e.
Proof.
  move => A e En E.
  enough (P : supath f (source e) (source e) [:: forward e]).
  { specialize (A _ {| upval := _ ; upvalK := P |}).
    contradict A; cbnb. }
  rewrite /supath in_cons orb_false_r. splitb; apply /eqP.
  - by rewrite E.
  - by apply nesym.
Qed.

Lemma uacyclip_2loop {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  {in [set e | f e.1 != None & usource e == v] &, injective (fun e : edge G * bool => utarget e)}.
Proof.
  move => F A [e eb] [j jb]; rewrite !in_set /= =>
    /andP[/eqP-En /eqP-Es] /andP[/eqP-Jn /eqP-Js] T.
  apply /eqP/negPn/negP => /eqP-Hejb.
  assert (Hej : e <> j).
  { move => ?; subst j.
    destruct (eq_comparable eb jb) as [ | Hb]; [by subst jb | ].
    assert (Hf := uacyclic_loop A En). contradict Hf.
    by destruct eb, jb. }
  enough (P : supath f v v [:: (e, eb); (j, ~~ jb)]).
  { specialize (A _ {| upval := _ ; upvalK := P |}).
    contradict A. cbnb. }
  rewrite /supath /= !in_cons !orb_false_r.
  splitb; apply /eqP; rewrite ?negb_involutive //; try by apply nesym.
  intro Fej. contradict Hej.
  apply F; rewrite // !in_set; by apply /eqP.
Qed.

Lemma neighbours_nb {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  #|neighbours f v| = #|~: f @^-1 None :&: edges_at v|.
Proof.
  move => F A.
  rewrite /neighbours card_in_imset -?card_set_subset; last by by apply uacyclip_2loop.
  assert (Hg : forall (e : [finType of {a | (f a.1 != None) && (usource a == v)}]),
    ((val e).1 \in ~: f @^-1 None) && ((val e).1 \in edges_at v)).
  { move => [[e b] E].
    rewrite !in_set /=.
    revert E => /andP[? ?]. splitb.
    apply /existsP. by exists (~~b). }
  set g : [finType of {a | (f a.1 != None) && (usource a == v)}] ->
    [finType of {e | (e \in ~: f @^-1 None) && (e \in edges_at v)}] :=
    fun e => Sub (val e).1 (Hg e).
  assert (Hh : forall e : [finType of {e | (e \in ~: f @^-1 None) && (e \in edges_at v)}],
    exists b, (f (val e, b).1 != None) && (usource (val e, b) == v)).
  { move => [e E] /=.
    revert E; rewrite !in_set => /andP[? /existsP[b ?]].
    exists (~~b). splitb. by rewrite negb_involutive. }
  set h : [finType of {e | (e \in ~: f @^-1 None) && (e \in edges_at v)}] ->
    [finType of {a | (f a.1 != None) && (usource a == v)}] :=
    fun e => let (b, H) := sigW (Hh e) in Sub (val e, b) H.
  apply (bij_card_eq (f := g)), (Bijective (g := h)).
  - move => [e E].
    rewrite /h /g /=.
    destruct (sigW _) as [b H].
    apply /eqP; cbn; simpl; splitb; apply /eqP.
    destruct (eq_comparable b e.2) as [-> | Hbe]; trivial.
    revert E H => /andP[/eqP-En /eqP-V] /andP[_ /eqP-V'].
    assert (Hf := uacyclic_loop A En). contradict Hf.
    destruct b, e as [? []]; by rewrite // V V'.
  - move => ?. rewrite /h /g /=. destruct (sigW _). cbnb.
Qed.

Lemma in_elt_sub_fst {Lv Le : Type} {G : graph Lv Le} :
  forall (p : @upath _ _ G) e, e \in p ->
  exists n, exists a, p = take n p ++ a :: drop n.+1 p /\ utarget a = utarget e /\
    forall f, f \in take n p -> utarget f <> utarget e.
Proof.
  move => p; induction p as [ | a p IH] => // e.
  rewrite in_cons.
  destruct (eq_comparable (utarget a) (utarget e)) as [Heq | Hneq].
  - move => _. exists 0, a. split.
    + by rewrite /= drop0.
    + splitb. by move => *.
  - assert (e == a = false) as -> by by apply /eqP; move => *; subst.
    move => /= In.
    specialize (IH _ In). destruct IH as [n [f [Eq [F IH]]]].
    exists n.+1, f.
    rewrite /= -Eq. splitb.
    move => x. rewrite in_cons => /orP[/eqP -> // | ?].
    by apply IH.
Qed.

Lemma remove_vertex_card {Lv Le : Type} {G : graph Lv Le} (v : G) :
  #|remove_vertex v| + 1 = #|G|.
Proof.
  rewrite card_set_subset cardsE cardsC1.
  enough (#|G| <> 0) by lia.
  intro N. apply card0_eq in N. by specialize (N v).
Qed.

Definition remove_vertex_f {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) : edge (remove_vertex v) -> option I :=
  fun e => f (val e).

Lemma remove_vertex_f_sinj {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) : {in ~: f @^-1 None &, injective f} ->
  {in ~: (remove_vertex_f f (v := v)) @^-1 None &, injective (remove_vertex_f f (v := v))}.
Proof.
  move => F [u U] [w W]; rewrite !in_set /remove_vertex_f /= => /eqP Fu /eqP Fw Eq. cbnb.
  by apply F; rewrite // !in_set; apply /eqP.
Qed.

(*
Lemma supath_induced {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (S : {set G}) :
  forall s t (p : Supath (fun (e : edge (induced S)) => f (val e)) s t),
  {q : Supath f (val s) (val t) & upval q = [seq (val a.1, a.2) | a <- upval p]}.
Proof.
  intros s t [p P]. revert s t P.
  induction p as [ | ([a A], b) p IH]; simpl => s t; rewrite /supath /=.
  { introb. subst t. by exists (supath_nil _ _). }
  rewrite in_cons => /andP[/andP[/andP[/eqP-? W] /andP[u U]] /norP[n N]]. subst s. simpl.
  assert (P : supath (fun (e : edge (induced S)) => f (val e)) (Sub (endpoint b a) (induced_proof b (valP (exist _ a A))) : induced S)
    t p) by splitb.
  specialize (IH _ _ P). destruct IH as [[q Q] HQ].
  revert HQ; cbnb => ?; subst q. simpl in Q.
  enough (QS : supath f (endpoint (~~ b) a) (val t) ((a, b) :: _))
    by by exists {| upval := _ ; upvalK := QS|}.
  revert Q. rewrite /supath /= in_cons. introb. splitb.
  revert u. clear. induction p as [ | c p IH]; trivial.
  rewrite /= !in_cons. move => /norP[l L]. splitb.
  by apply IH.
Qed.
*)

Lemma remove_vertex_uacyclic {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) :
  uacyclic f -> uacyclic (remove_vertex_f f (v := v)).
Proof.
  move => A [x X] [p' P']. cbnb.
  enough (P : supath f x x [seq (val e.1, e.2) | e <- p']).
  { revert A => /(_ _ {| upval := _ ; upvalK := P |}) /eqP; cbn => /eqP A.
    by destruct p'. }
  revert P' => /andP[/andP[W ?] ?].
  splitb; rewrite -?map_comp //.
  enough (H : forall x y X Y, uwalk (Sub x X : remove_vertex v) (Sub y Y) p' ->
    uwalk x y [seq (val _0.1, _0.2) | _0 <- p']) by by apply (H _ _ _ _ W).
  clear; induction p' as [ | [[? ?] ?] ? IH] => // ? ? ? ?; cbnb => /andP[? W].
  splitb. apply (IH _ _ _ _ W).
Qed.

Lemma remove_vertex_None_nb {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) :
  #|~: (remove_vertex_f f (v := v)) @^-1 None| = #|~: f @^-1 None :\: edges_at v|.
Proof.
  rewrite -!card_set_subset.
  assert (Sube : forall e, e \notin edges_at v = (e \in edge_set [set~ v])).
  { move => e.
    rewrite !in_set /incident.
    apply (sameP existsPn), iff_reflect; split.
    - move => *; splitb.
    - by move => /andP[? ?] []. }
  assert (Ine : forall (e : edge (remove_vertex v)),
    val e \in ~: f @^-1 None = (e \notin (remove_vertex_f f (v := v)) @^-1 None)).
  { move => *. by rewrite !in_set /remove_vertex_f /remove_vertex_f. }
  assert (Hg : forall (e : {E | E \notin (remove_vertex_f f (v := v)) @^-1 None}),
    (val (val e) \notin edges_at v) && (val (val e) \in ~: f @^-1 None)).
  { move => [[? In] E].
    rewrite Sube Ine /=. splitb.
    clear E; rewrite !in_set /incident in In.
    rewrite !in_set.
    splitb; revert In => /existsPn; by [move => /(_ false) | move => /(_ true)]. }
  set g : {e | e \notin (remove_vertex_f f (v := v)) @^-1 None} ->
    {e : edge G | (e \notin edges_at v) && (e \in ~: f @^-1 None)} :=
    fun e => Sub (val (val e)) (Hg e).
  assert (Hh : forall (e : {e : edge G | (e \notin edges_at v) && (e \in ~: f @^-1 None)}),
    val e \in ~: edges_at v).
  { move => [e E] /=. rewrite in_set. by revert E => /andP[? _]. }
  assert (Hh' : forall (e : {e : edge G | (e \notin edges_at v) && (e \in ~: f @^-1 None)}),
    (Sub (val e) (Hh e) \notin (remove_vertex_f f (v := v)) @^-1 None)).
  { move => [e E]. rewrite -Ine /=. by revert E => /andP[_ ?]. }
  set h : {e : edge G | (e \notin edges_at v) && (e \in ~: f @^-1 None)} ->
    {e | e \notin (remove_vertex_f f (v := v)) @^-1 None} :=
    fun e => Sub (Sub (val e) (Hh e)) (Hh' e).
  apply (bij_card_eq (f := g)), (Bijective (g := h)); move => *; cbnb.
Qed.

Lemma remove_vertex_uconnected_to {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) :
  forall u w, is_uconnected (remove_vertex_f f (v := v)) u w -> is_uconnected f (val u) (val w).
Proof.
  move => [u U] [w W] /existsP[[q /andP[/andP[Wq Uq]] Nq] _] /=. apply /existsP.
  enough (Q' : supath f u w [seq (val e.1, e.2) | e <- q])
    by by exists {| upval := _ ; upvalK := Q' |}.
  revert u U Wq Uq Nq; induction q as [ | [[e E] b] q IHq] => u U.
  { move => *. splitb. }
  cbnb; rewrite /remove_vertex_f /= !in_cons => /andP[? Wq] /andP[? Uq] /norP[? Nq].
  revert IHq => /(_ _ _ Wq Uq Nq) /andP[/andP[? ?] ?].
  rewrite /supath /= in_cons -map_comp. splitb.
Qed.

Lemma remove_vertex_uconnected_to_NS {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) :
  {in ~: f @^-1 None &, injective f} ->
  forall u w, ~~ is_uconnected f v (val u) ->
  is_uconnected (remove_vertex_f f (v := v)) u w = is_uconnected f (val u) (val w).
Proof.
  move => F [u U] [w W] /= /existsPn /= Hu.
  destruct (is_uconnected f u w) eqn:UW.
  2:{ destruct (is_uconnected (remove_vertex_f f (v := v)) (Sub u U) (Sub w W)) eqn:UW'; trivial.
    by rewrite (remove_vertex_uconnected_to UW') in UW. }
  revert UW => /existsP[[p P] _].
  revert u U Hu P; induction p as [ | e p IHp] => u U Hu P.
  { revert P => /andP[/andP[/eqP-? _] _]; subst w.
    rewrite (eq_irrelevance U W).
    apply /existsP. by exists (supath_nil _ _). }
  revert P => /andP[/andP[/= /andP[/eqP-? Wp] /andP[up Up]]];
  rewrite in_cons => /norP[/eqP-np Np]; subst u.
  assert (P' : supath f (utarget e) w p) by splitb.
  assert (U' : utarget e \in [set~ v]).
  { rewrite !in_set.
    apply /eqP => Hc.
    enough (Pc : supath f v (usource e) [:: (e.1, ~~e.2)]) by by specialize (Hu {| upval := _ ; upvalK := Pc |}).
    rewrite /supath in_cons /= negb_involutive Hc orb_false_r. splitb. by apply /eqP. }
  assert (Hu' : Supath f v (utarget e) -> false).
  { move => [q /andP[/andP[Wq _ ] Nq]].
    enough (Supath f v (usource e)) by by apply Hu.
    apply (uconnected_simpl (p := rcons q (e.1, ~~e.2))); trivial.
    - rewrite uwalk_rcons /= negb_involutive. splitb.
    - rewrite map_rcons mem_rcons. splitb. by apply /eqP. }
  specialize (IHp _ U' Hu' P').
  revert IHp => /existsP[[q /andP[/andP[Wq _ ] Nq]] _] {Hu' P'}.
  enough (P : Supath (remove_vertex_f f (v:=v)) (Sub (usource e) U) (Sub w W)).
  { apply /existsP. by exists P. }
  assert (E : e.1 \in ~: edges_at v).
  { clear - U U'. revert U U'; rewrite !in_set => ? ?.
    apply /existsPn; move => []; by destruct e as [e []]. }
  apply (uconnected_simpl (p := (Sub e.1 E, e.2) :: q : @upath _ _ (remove_vertex v))).
  - by apply remove_vertex_f_sinj.
  - assert (Hr : (Sub (endpoint e.2 (sval (Sub e.1 E))) (consistent_del1 _ (valP _))) =
      (Sub (utarget e) U' : remove_vertex v)) by cbnb.
    cbn. rewrite Hr {Hr}. splitb.
  - splitb. by apply /eqP.
Qed.

Lemma remove_vertex_uconnected_NS {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) :
  {in ~: f @^-1 None &, injective f} ->
  #|[set [set w : remove_vertex v | is_uconnected f (val u) (val w)] |
    u : remove_vertex v & ~~ is_uconnected f v (val u)]| =
  #|[set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u]|.
Proof.
  move => F.
  set G' := remove_vertex v.
  rewrite -card_sig -[in RHS]card_sig.
  assert (Hg : forall (E : sig_finType (pred_of_set
    [set [set w : G' | is_uconnected f (val u) (val w)] | u : G' & ~~ is_uconnected f v (val u)])),
    [set val u | u in val E] \in [set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u]).
  { move => [E HE].
    assert (HE' := HE). revert HE' => /imsetP/sig2_eqW[u Hu ?]; subst E.
    rewrite in_set in Hu. rewrite SubK.
    assert ([set val u0 | u0 in [set w : G' | is_uconnected f (val u) (val w)]]
      = [set w | is_uconnected f (val u) w]) as ->.
    { transitivity [set val w | w : G' & is_uconnected f (val u) (val w)]; [by apply eq_imset | ].
      apply /setP => w.
      rewrite in_set.
      destruct (is_uconnected f (val u) w) eqn:UW; apply /imsetP.
      - assert (W : w \in [set~ v]).
        { rewrite !in_set. apply /eqP => ?; subst w.
          contradict Hu; apply /negP/negPn.
          by apply is_uconnected_sym. }
        exists (Sub w W); rewrite ?in_set; cbnb.
      - move => [[w' ?]]. rewrite in_set /= => Hc ?; subst w'.
        by rewrite Hc in UW. }
    apply /imsetP. exists (val u); by rewrite // in_set. }
  set g : sig_finType (pred_of_set
    [set [set w | is_uconnected f (val u) (val w)] | u : G' & ~~ is_uconnected f v (val u)]) ->
    sig_finType (pred_of_set [set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u]) :=
    fun E => Sub [set val u | u in val E] (Hg E).
  assert (Hh : forall u : G, ~~ is_uconnected f v u -> [set w | is_uconnected f u (val w)] \in
    [set [set w : G' | is_uconnected f (val u) (val w)] | u : G' & ~~ is_uconnected f v (val u)]).
  { move => u Hu.
    apply /imsetP.
    assert (U : u \in [set~ v]).
    { rewrite !in_set. apply /eqP => ?; subst u.
      contradict Hu; apply /negP/negPn.
      apply is_uconnected_id. }
    exists (Sub u U); by rewrite // in_set. }
  assert (Hh' : forall E : sig_finType (pred_of_set [set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u]),
    {u : G | ~~ is_uconnected f v u & val E = [set w | is_uconnected f u w]}).
  { move => [E HE].
    assert (HE' := HE).
    revert HE' => /imsetP/sig2_eqW[u Hu ?].
    rewrite in_set in Hu.
    by exists u. }
  set h : sig_finType (pred_of_set [set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u])
    -> sig_finType (pred_of_set [set [set w | is_uconnected f (val u) (val w)] |
    u : G' & ~~ is_uconnected f v (val u)]) :=
    fun E => let (u, Hu, _) := Hh' E in Sub [set w | is_uconnected f u (val w)] (Hh u Hu).
  apply (bij_card_eq (f := g)), (Bijective (g := h)).
  - move => E.
    unfold h. destruct (Hh' (g E)) as [u U Hu].
    destruct E as [E HE]; cbnb.
    revert Hu. rewrite /g /=.
    revert HE => /imsetP[[w W] Hw ?]; subst E; simpl.
    move => /setP/(_ u).
    rewrite !in_set is_uconnected_id.
    move => /imsetP[[x X]]; rewrite in_set /= => WU ?; subst x.
    f_equal; apply /setP; move => {X} [x X].
    rewrite !in_set /=.
    by apply is_uconnected_eq, is_uconnected_sym.
  - move => E.
    unfold h. destruct (Hh' E) as [u U Hu].
    destruct E as [E HE]; cbnb.
    simpl in Hu; subst E.
    f_equal; apply /setP => w.
    rewrite in_set.
    destruct (is_uconnected f u w) eqn:UW.
    + apply /imsetP.
      assert (W : w \in [set~ v]).
      { rewrite !in_set. apply /eqP => ?; subst w.
        contradict U; apply /negP/negPn.
        by apply is_uconnected_sym. }
      exists (Sub w W); [ | cbnb].
      by rewrite in_set.
    + apply /imsetP. move => [[x X]]. rewrite in_set /= => UX ?; subst x.
      by rewrite UX in UW.
Qed.

Lemma uconnected_cc {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) :
  {in ~: f @^-1 None &, injective f} ->
  [set [set w | is_uconnected f u w] | u : G & is_uconnected f v u] =
  [set [set w | is_uconnected f v w]].
Proof.
  move => F.
  apply /setP => E.
  rewrite !in_set.
  destruct (E == [set w | is_uconnected f v w]) eqn:B; revert B => /eqP B.
  - subst E.
    apply /imsetP.
    exists v; trivial.
    rewrite !in_set.
    apply is_uconnected_id.
  - apply /imsetP. move => [u]; rewrite !in_set => VU ?; subst E.
    contradict B.
    apply /setP => w.
    rewrite !in_set.
    by apply is_uconnected_eq, is_uconnected_sym.
Qed.

Lemma remove_vertex_uconnected_S {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  #|[set [set w | is_uconnected (remove_vertex_f f (v := v)) u w] | u : _ & is_uconnected f v (val u)]| =
  #|neighbours f v|.
Proof.
  move => F A.
  set G' := remove_vertex v.
  set f' := remove_vertex_f f (v := v).
  rewrite -card_sig -[in RHS]card_sig.
  assert (Hg : forall E : sig_finType (pred_of_set [set [set w | is_uconnected f' u w] | u : G' & is_uconnected f v (val u)]),
    { u : G' | val u \in neighbours f v & val E = [set w : G' | is_uconnected f' u w]}).
  { move => [E HE] /=.
    revert HE => /imsetP/sig2_eqW[[u U] VU ?]; subst E.
    rewrite !in_set /= in VU. apply is_uconnected_sym in VU.
    revert VU => /existsP/sigW[[p P] _].
    revert P; case/lastP: p => [ | p e].
    { move => /andP[/andP[/eqP ? _] _]; subst u.
      contradict U; apply /negP.
      by rewrite !in_set negb_involutive. }
    rewrite /supath uwalk_rcons map_rcons rcons_uniq in_rcons
      => /andP[/andP[/andP[Wp /eqP Et] /andP[Ep Up]]] /norP[/eqP En Np].
    wlog : e p Wp Up Np Et Ep En / forall a, a \in p -> utarget a <> v.
    { move => Hw.
      destruct [forall a, (a \in p) ==> (utarget a != v)] eqn:HHw.
      { apply (Hw _ _ Wp); trivial.
        move => a Ain. by revert HHw => /forallP /(_ a) /implyP /(_ Ain) /eqP ?. }
      revert HHw => /forallPn/sigW[x].
      rewrite negb_imply negb_involutive => /andP[Xin /eqP Xv].
      apply in_elt_sub_fst in Xin.
      assert (Xin' : exists n, [exists a, (p == take n p ++ a :: drop n.+1 p) &&
        (utarget a == utarget x) && [forall f, (f \in take n p) ==> (utarget f != utarget x)]]).
      { destruct Xin as [m [a [Hp [Ha Xin]]]].
        exists m; apply /existsP; exists a.
        rewrite {1}Hp Ha. splitb.
        apply /forallP => ?; apply /implyP => ?; apply /eqP.
        by apply Xin. }
      revert Xin' => {Xin} /sigW[nx /existsP/sigW[t /andP[/andP[/eqP Hp /eqP Tt] /forallP Inpx]]].
      rewrite Xv in Inpx. rewrite Xv in Tt. clear x Xv.
      assert (P' : supath f u (usource t) (take nx p)).
      { assert (P : supath f u (usource e) p) by splitb.
        rewrite Hp in P. rewrite Hp in Wp.
        destruct (supath_subKK P) as [P' _].
        by rewrite (uwalk_sub_middle Wp) in P'. }
      revert P' => /andP[/andP[Wp' Up'] Np'].
      apply (Hw _ _ Wp' Up' Np'); trivial.
      - revert Up. rewrite {1}Hp map_cat cat_uniq /=. by introb.
      - revert Np. rewrite {1}Hp map_cat mem_cat /= in_cons. introb.
      - move => a Ain ?. by revert Inpx => /(_ a) /implyP /(_ Ain) /eqP ?. }
    move => Hpv.
    set w := usource e.
    assert (P : supath f u w p) by splitb.
    clear Wp Up Np.
    assert (W : w \in [set~ v]).
    { rewrite /w !in_set. apply /eqP => Hc.
      assert (Pe : supath f v v [:: e]).
      { rewrite /supath /= Et -Hc in_cons orb_false_r. splitb. by apply /eqP. }
      specialize (A _ {| upval := _ ; upvalK := Pe |}).
      contradict A. cbnb. }
    exists (Sub w W).
    + rewrite /= /neighbours.
      apply /imsetP. exists (e.1, ~~e.2); trivial.
      rewrite in_set negb_involutive Et. splitb. by apply /eqP; apply nesym.
    + apply /setP => x.
      rewrite !in_set.
      apply (is_uconnected_eq (remove_vertex_f_sinj F)). clear x.
      apply /existsP.
      revert u U P; induction p as [ | a p IHp] => u U P.
      { revert P => /andP[/andP[/eqP ? _] _]; subst u.
        rewrite (eq_irrelevance U W).
        by exists (supath_nil _ _). }
      revert P => /andP[/andP[/= /andP[/eqP Ha Wp] /andP[up Up]]];
      rewrite in_cons => /norP[/eqP np Np]; subst w.
      assert (P' : supath f (utarget a) (usource e) p) by splitb.
      revert Ep; rewrite /= in_cons => /norP[/eqP ? Ep].
      assert (U' : utarget a \in [set~ v]).
      { rewrite !in_set. apply /eqP.
        apply Hpv. rewrite in_cons. caseb. }
      assert (Hpv' : forall a, a \in p -> utarget a <> v).
      { move => *. apply Hpv. rewrite in_cons. caseb. }
      specialize (IHp Ep Hpv' _ U' P'). destruct IHp as [[pf Pf] _].
      enough (P : Supath (remove_vertex_f f (v:=v)) (Sub u U) (Sub (usource e) W)).
        by by exists P.
      assert (U'' : usource a != v).
      { by revert U; rewrite !in_set Ha. }
      assert (Ain : a.1 \in ~: edges_at v).
      { clear - U U' U''. revert U U'; rewrite !in_set /incident => ? ?.
        by apply /existsPn; move => []; destruct a as [a []]. }
      revert Pf => /andP[/andP[Wpf _ ] Npf].
      apply (uconnected_simpl (p := (Sub a.1 Ain, a.2) :: pf : @upath _ _ (remove_vertex v))); simpl.
      - by apply remove_vertex_f_sinj.
      - assert ((Sub (utarget a) _) = Sub (utarget a) U') as -> by cbnb.
        splitb. by cbn; apply /eqP.
      - rewrite /= in_cons. splitb. by apply /eqP. }
  set g : sig_finType (pred_of_set [set [set w | is_uconnected f' u w] | u : G' & is_uconnected f v (val u)]) ->
    sig_finType (pred_of_set (neighbours f v)) := fun E => let (u, U, _) := Hg E in Sub (val u) U.
  assert (Hh : forall u : sig_finType (pred_of_set (neighbours f v)), val u \in [set~ v]).
  { move => [u U].
    rewrite /= !in_set. apply /eqP => Huv.
    enough (exists (e : edge G), source e = target e /\ None <> f e) as [e [Ce Ne]].
    { assert (Pe : supath f (source e) (target e) [:: forward e]).
      { rewrite /supath /= in_cons orb_false_r. splitb. by apply /eqP. }
      rewrite Ce in Pe.
      specialize (A _ {| upval := _ ; upvalK := Pe |}).
      contradict A; cbnb. }
    assert (Hu : u \in neighbours f v) by by []. clear U.
    revert Hu => /imsetP[[e b]]; rewrite in_set => /andP[/eqP Ne /eqP E] E'; apply nesym in Ne.
    exists e. split; trivial.
    by destruct b; rewrite E -E' Huv. }
  assert (Hh' : forall u : sig_finType (pred_of_set (neighbours f v)),
    [set w | is_uconnected f' (Sub (val u) (Hh u)) w] \in [set [set w | is_uconnected f' u0 w]
    | u0 : G' & is_uconnected f v (val u0)]).
  { move => u.
    apply /imsetP.
    exists (Sub (val u) (Hh u)); trivial.
    destruct u as [u U].
    rewrite !in_set /=.
    assert (Hu : u \in neighbours f v) by by []. clear U.
    apply /existsP.
    revert Hu => /imsetP[e]; rewrite in_set => /andP[/eqP Ne /eqP E] E'; apply nesym in Ne.
    assert (Pe : supath f v u [:: e]).
    { rewrite /supath /= in_cons orb_false_r E E'. splitb. by apply /eqP. }
    by exists {| upval := _ ; upvalK := Pe |}. }
  set h : sig_finType (pred_of_set (neighbours f v)) ->
    sig_finType (pred_of_set [set [set w | is_uconnected f' u w] | u : G' & is_uconnected f v (val u)]) :=
    fun u => Sub [set w | is_uconnected f' (Sub (val u) (Hh u)) w] (Hh' u).
  apply (bij_card_eq (f := g)), (Bijective (g := h)).
  - move => E.
    unfold g. destruct (Hg E) as [[u Uin] U Hu].
    unfold h.
    destruct E as [E HE]; cbnb; f_equal.
    simpl in Hu. subst E.
    by assert (Sub u (Hh (Sub u U)) = Sub u Uin) as -> by cbnb.
  - move => u.
    unfold g. destruct (Hg (h u)) as [[w Win] W Hw], u as [u U].
    cbnb. simpl in W. rewrite /h /= in Hw.
    revert Hw => /setP /(_ (Sub w Win)). rewrite !in_set is_uconnected_id => /existsP[[p P] _].
    assert (exists ew, usource ew = w /\ utarget ew = v /\ None <> f ew.1) as [ew [Sew [Tew New]]].
    { revert W => /imsetP[e]; rewrite in_set => /andP[/eqP Ne /eqP E] E'; apply nesym in Ne; symmetry in E'.
      exists (e.1, ~~e.2). splitb. by rewrite negb_involutive. }
    assert (exists eu, usource eu = v /\ utarget eu = u /\ None <> f eu.1) as [eu [Seu [Teu Neu]]].
    { assert (U' : u \in neighbours f v) by by [].
      revert U' => /imsetP[e]; rewrite in_set => /andP[/eqP Ne /eqP E] E'; apply nesym in Ne; symmetry in E'.
      exists e. splitb. }
    destruct (eq_comparable w u) as [ | Hneq]; trivial.
    assert (Heuw : eu.1 <> ew.1).
    { intro Hc. contradict Hneq.
      destruct eu as [eu []], ew as [ew []]; by rewrite -Sew -Teu Hc // -[in LHS]Hc Seu Tew. }
    enough (Pc : supath f v v (eu :: rcons [seq (val a.1, a.2) | a <- p] ew)).
    { specialize (A _ {| upval := _ ; upvalK := Pc |}).
      contradict A; cbnb. }
    assert (Pm : supath f u w [seq (val a.1, a.2) | a <- p]).
    { revert P => /andP[/andP[Wp Up] Np].
      assert (Hr : [seq f e.1 | e <- [seq (val a.1, a.2) | a <- p]] = [seq f' e.1 | e <- p]).
      { rewrite -map_comp. by apply eq_map. }
      rewrite -Hr in Up; rewrite -Hr in Np.
      splitb.
      enough (He : forall (p : @upath _ _ G') u U w W, uwalk (Sub u U : G') (Sub w W) p ->
        uwalk u w [seq (val a.1, a.2) | a <- p]) by apply (He _ _ _ _ _ Wp).
      clear => p; induction p as [ | ? ? IHp] => // ? ? ? ?; cbnb => /andP[? W].
      splitb. apply (IHp _ _ _ _ W). }
    revert Pm => /andP[/andP[? ?] ?].
    rewrite /supath /= !map_rcons !mem_rcons !in_cons !mem_rcons !rcons_uniq.
    splitb; try by apply /eqP.
    + rewrite uwalk_rcons Tew Teu Sew. splitb.
    + apply /eqP => Hc.
      contradict Heuw.
      apply F; rewrite // !in_set; apply /eqP; by apply nesym.
    + apply /mapP. move => [[e b] Ein Eeq].
      assert (e = eu.1).
      { apply F; rewrite // !in_set; apply /eqP; [ | by apply nesym].
        move => Ne. contradict Eeq.
        rewrite Ne. by apply nesym. }
      subst e.
      revert Ein => /mapP[[[a Av] c] _ /eqP]; cbn => /andP[/eqP ? /eqP ?]. subst a c.
      contradict Av; apply /negP.
      rewrite !in_set negb_involutive /incident -Seu. apply /existsP.
      destruct eu as [? []]; by [exists false | exists true].
    + apply /mapP. move => [[e b] Ein Eeq].
      assert (e = ew.1).
      { apply F; rewrite // !in_set; apply /eqP; [ | by apply nesym].
        move => Ne. contradict Eeq.
        rewrite Ne. by apply nesym. }
      subst e.
      revert Ein => /mapP[[[a Av] c] _ /eqP]; cbn => /andP[/eqP ? /eqP ?]. subst a c.
      contradict Av; apply /negP.
      rewrite !in_set negb_involutive /incident -Tew. apply /existsP.
      destruct ew as [? []]; by [exists true | exists false].
Qed.

Lemma remove_vertex_uconnected_nb {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  uconnected_nb (remove_vertex_f f (v := v)) + 1 = uconnected_nb f + #|~: f @^-1 None :&: edges_at v|.
Proof.
  move => F A.
  set G' := remove_vertex v.
  set f' := remove_vertex_f f (v := v).
  assert (equivalence_partition (is_uconnected f) setT =
    [set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u] :|:
    [set [set w | is_uconnected f u w] | u : G & is_uconnected f v u] /\
    equivalence_partition (is_uconnected (remove_vertex_f f (v := v))) setT =
    [set [set w | is_uconnected f' u w] | u : G' & ~~ is_uconnected f v (val u)] :|:
    [set [set w | is_uconnected f' u w] | u : G' & is_uconnected f v (val u)]) as [Hr Hr'].
  { split; rewrite /equivalence_partition imsetUCr; apply eq_imset => ?; by rewrite setT_in_pred. }
  rewrite /uconnected_nb Hr Hr' {Hr Hr'}.
  assert (Hr : [set [set w | is_uconnected f' u w] | u : G' & ~~ is_uconnected f v (val u)] =
    [set [set w | is_uconnected f (val u) (val w)] | u : G' & ~~ is_uconnected f v (val u)]).
  { apply eq_in_imset => u. rewrite in_set => Hu. apply eq_finset => w.
    by apply remove_vertex_uconnected_to_NS. }
  rewrite Hr {Hr} !cardsU.
  assert (Hr : [set [set w | is_uconnected f (val u) (val w)] | u : G' & ~~ is_uconnected f v (val u)]
    :&: [set [set w | is_uconnected f' u w] | u : G' & is_uconnected f v (val u)] = set0).
  { apply disjoint_setI0. apply /disjointP => ? /imsetP [u U] ? /imsetP [w W]; subst.
    revert U W; rewrite !in_set => U W.
    move => /setP /(_ u). rewrite !in_set is_uconnected_id => Hc. symmetry in Hc.
    apply is_uconnected_sym in Hc.
    rewrite remove_vertex_uconnected_to_NS // in Hc.
    apply is_uconnected_sym in Hc.
    contradict U; apply /negP/negPn.
    apply (is_uconnected_comp F W Hc). }
  rewrite Hr {Hr} cards0.
  assert (Hr : [set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u]
    :&: [set [set w | is_uconnected f u w] | u : G & is_uconnected f v u] = set0).
  { apply disjoint_setI0. apply /disjointP => ? /imsetP [u U] ? /imsetP [w W]; subst.
    revert U W; rewrite !in_set => U W.
    move => /setP /(_ u). rewrite !in_set is_uconnected_id => Hc. symmetry in Hc.
    contradict U; apply /negP/negPn.
    apply (is_uconnected_comp F W Hc). }
  rewrite Hr {Hr} cards0 remove_vertex_uconnected_NS // uconnected_cc // -/S cards1 remove_vertex_uconnected_S //
    neighbours_nb //; lia.
Qed.

Lemma uacyclic_uconnected_nb {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  uconnected_nb f + #|~: f @^-1 None| = #|G|.
Proof.
  remember #|G| as n eqn:N; symmetry in N.
  revert G N f; induction n as [ | n IH] => G N f F A.
  { rewrite -cardsT in N. apply cards0_eq in N.
    rewrite /uconnected_nb N /equivalence_partition imset0 cards0.
    enough (#|~: f @^-1 None| <= 0) by lia.
    enough (#|edge G| = 0) as <- by apply max_card.
    apply eq_card0 => e.
    assert (H : source e \in set0) by by rewrite -N.
    by rewrite in_set in H. }
  destruct (set_0Vmem [set: G]) as [Hc | [v _]].
  { contradict N. by rewrite -cardsT Hc cards0. }
  set f' := remove_vertex_f f (v := v).
  assert (N' : #|remove_vertex v| = n) by (rewrite -(remove_vertex_card v) in N; lia).
  assert (F' : {in ~: f' @^-1 None &, injective f'}) by by apply remove_vertex_f_sinj.
  specialize (IH _ N' _ F' (remove_vertex_uacyclic A)).
  assert (#|~: f' @^-1 None| = #|~: f @^-1 None :\: edges_at v|) by by apply remove_vertex_None_nb.
  assert (uconnected_nb f' + 1 = uconnected_nb f + #|~: f @^-1 None :&: edges_at v|)
    by by apply remove_vertex_uconnected_nb.
  assert (#|~: f @^-1 None| = #|~: f @^-1 None :\: edges_at v| + #|~: f @^-1 None :&: edges_at v|) as ->.
  { rewrite cardsD.
    enough (#|~: f @^-1 None| >= #|~: f @^-1 None :&: edges_at v|) by lia.
    rewrite -(cardsID (edges_at v) (~: f @^-1 None)).
    lia. }
  lia.
Qed.
(* TODO simplify this last proof with all its parts *)

(** ** Some lemmae when considering a standard isomorphisms (those which do not flip edges) *)
(** Isomorphisms preserve out/in-edges *)
Lemma edges_at_outin_iso {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) :
  forall (h : F ≃ G), h.d =1 xpred0 ->
  forall b v, edges_at_outin b (h v) = [set h.e e | e in edges_at_outin b v].
Proof.
  move => h H b v. apply /setP => e.
  by rewrite -[e](bijK' h.e) bij_imset_f !inE endpoint_iso H bij_eqLR bijK.
Qed.

Definition iso_path {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (h : F ≃ G) :
  upath -> upath :=
  fun p => [seq (h.e e.1, e.2) | e <- p].

Lemma iso_walk {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (h : F ≃ G) :
  h.d =1 xpred0 ->
  forall p s t, uwalk s t p -> uwalk (h s) (h t) (iso_path h p).
Proof.
  intros H p; induction p as [ | u p HP]; intros s t; cbn.
  + by move => /eqP ->.
  + move => /andP[/eqP w W].
    rewrite !endpoint_iso !H w.
    splitb. by apply HP.
Qed.

(* TODO Supath pour turn et turns ? *) (* TODO mettre un fichier upath *)