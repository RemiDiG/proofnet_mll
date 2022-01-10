(* Extension for [mgraph] of the library GraphTheory
   About Directed Acyclic Multigraphs, in which the relation being linked by a walk is well-founded
 *)

Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import mgraph.
From Yalla Require Import mll_prelim.

Import EqNotations.

Set Mangle Names.
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
(* TODO beaucoup de doublon avec uwalk : généraliser ? *)
Lemma walk_endpoint {Lv Le : Type} {G : graph Lv Le} (p : path) :
  forall (x y : G), walk x y p -> path_source x p = x /\ path_target x p = y.
Proof.
  induction p as [ | e p IH] => x y /=.
  { by move => /eqP ->. }
  move => /andP[/eqP -> W]. split; trivial.
  by destruct (IH _ _ W) as [_ <-].
Qed.

Lemma walk_cat {Lv Le : Type} {G : graph Lv Le} (s i t : G) (p q : path) :
  walk s i p -> walk i t q -> walk s t (p ++ q).
Proof.
  revert s i t q; induction p as [ | e p Hp] => s i t q Wp Wq; revert Wp; cbn.
  - by move => /eqP ->.
  - move => /andP[/eqP <- ?]. apply /andP; split; trivial. by apply (Hp _ i).
Qed.

Lemma walk_sub_middle {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q : path) :
  walk s t (p ++ q) -> path_target s p = path_source t q.
Proof.
  revert s t q; induction p as [ | e p Hp] => s t q; cbn in *.
  - destruct q; cbn; [by move => /eqP -> | by move => /andP[/eqP -> _]].
  - move =>/andP[_ W]. apply (Hp _ _ _ W).
Qed.

Lemma walk_subK {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q : path) :
  walk s t (p ++ q) -> walk s (path_target s p) p /\ walk (path_source t q) t q.
Proof.
  revert s t q; induction p as [ | e p Hp] => s t q W.
  - cbn. split; trivial.
    assert (H := walk_sub_middle W). cbn in H. by rewrite -H.
  - cbn in *. revert W => /andP[/eqP -> W].
    splitb; apply (Hp _ _ _ W).
Qed.

Lemma walk_sub {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q r : path) :
  walk s t (p ++ q ++ r) -> walk (path_target s p) (path_source t r) q.
Proof.
  intro W.
  assert (W' : walk (path_target s p) t (q ++ r)).
  { rewrite (walk_sub_middle W). by destruct (walk_subK W) as [_ ->]. }
  rewrite -(walk_sub_middle W'). by destruct (walk_subK W') as [-> _].
Qed.

Lemma walk_rcons {Lv Le : Type} {G : graph Lv Le} (s t : G) (p : path) (e : edge G) :
  walk s t (rcons p e) = (walk s (source e) p) && (target e == t).
Proof.
  revert s t e; induction p as [ | ep p IH] => s t e /=.
  all: apply /eqP; cbn; apply /eqP; case: ifP => /eqP-H; subst.
  all: rewrite ?eq_refl //.
  - apply nesym in H. revert H => /eqP-H. symmetry. caseb.
  - apply IH.
  - revert H => /eqP-H. symmetry. caseb.
Qed.

Definition acyclic {Lv Le : Type} {G : graph Lv Le} :=
  forall (x : G) (p : path), walk x x p -> p = [::].

Definition is_connected_strict {Lv Le : Type} {G : graph Lv Le} (t s : G) :=
  exists p, (p != [::]) && walk s t p.

Definition is_connected_strict_rev {Lv Le : Type} {G : graph Lv Le} (s t : G) :=
  is_connected_strict t s.

(** ** Directed Acyclic Multigraph *)
Record dam (Lv Le : Type) : Type := Dam {
    mgraph_of :> graph Lv Le;
    acy : @acyclic _ _ mgraph_of;
  }.


(** ** Walks from a node in a dam form a finite type *)
Record Walk {Lv Le : Type} {G : graph Lv Le} (s : G) :
  predArgType := {wval :> path; wvalK : [exists t, walk s t wval]}.
Canonical Walk_subType {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  [subType for (@wval _ _ _ s)].
Definition Walk_eqMixin {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  Eval hnf in [eqMixin of Walk s by <:].
Canonical Walk_eqType {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  Eval hnf in EqType (Walk s) (Walk_eqMixin s).
Definition Walk_choiceMixin {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  Eval hnf in [choiceMixin of (Walk s) by <:].
Canonical Walk_choiceType {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  Eval hnf in ChoiceType (Walk s) (Walk_choiceMixin s).
Definition Walk_countMixin {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  Eval hnf in [countMixin of (Walk s) by <:].
Canonical Walk_countType {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  Eval hnf in CountType (Walk s) (Walk_countMixin s).

Lemma walk_uniq {Lv Le : Type} {G : dam Lv Le} p :
  forall (s t : G), walk s t p -> uniq [seq source e | e <- p].
Proof.
  induction p as [ | e p IH]; trivial.
  move => s t /= /andP[/eqP-? W]. subst s.
  splitb; first last.
  { exact (IH _ _ W). }
  apply /mapP. intros [f F S].
  apply in_elt_sub in F.
  destruct F as [n P].
  assert (C := @acy _ _ G (source e) (e :: take n p)).
  enough (W' : walk (source e) (source e) (e :: take n p)) by by apply C in W'.
  simpl. splitb.
  rewrite P in W. apply (@walk_sub _ _ _ _ _ [::]) in W.
  by rewrite /= -S in W.
Qed.

Lemma walk_size {Lv Le : Type} {G : dam Lv Le} (s t : G) p :
  walk s t p -> size p < S #|G|.
Proof.
  move => W.
  assert (U := walk_uniq W).
  revert U => /card_uniqP-U.
  rewrite size_map in U.
  rewrite -U.
  exact: max_card.
Qed.

Definition Walk_tuple {Lv Le : Type} {G : dam Lv Le} (s : G) (p : Walk s) :
  {n : 'I_(S #|G|) & n.-tuple (edge G)} :=
  let (w, W) := p in let (t, W') := sigW (existsP W) in existT _ (Ordinal (walk_size W')) (in_tuple w).

Definition tuple_Walk {Lv Le : Type} {G : graph Lv Le} (s : G)
  (m : {n : 'I_(S #|G|) & n.-tuple (edge G)}) : option (Walk s) :=
  let (_, p) := m in match boolP [exists t, walk s t p] with
  | AltTrue W => Some (Sub (val p) W)
  | AltFalse _ => None
  end.

Lemma Walk_tupleK {Lv Le : Type} {G : dam Lv Le} (s : G) :
  pcancel (@Walk_tuple _ _ _ s) (tuple_Walk s).
Proof.
  move => [w W] /=. destruct (sigW (existsP W)) as [t ?]. simpl.
  case: {-}_ / boolP; last by rewrite W.
  move => W'. by rewrite (bool_irrelevance W' W).
Qed.

Definition Walk_finMixin {Lv Le : Type} {G : dam Lv Le} (s : G) :=
  Eval hnf in PcanFinMixin (@Walk_tupleK _ _ _ s).
Canonical Walk_finType {Lv Le : Type} {G : dam Lv Le} (s : G) :=
  Eval hnf in FinType (Walk s) (Walk_finMixin s).

(** ** Well-founded *)
Lemma Walk_nilK {Lv Le : Type} {G : graph Lv Le} (s : G) :
  [exists t, walk s t [::]].
Proof. apply /existsP. exists s. by unfold walk. Qed.

Definition Walk_nil {Lv Le : Type} (G : graph Lv Le) (x : G) : Walk x :=
  {| wval := _ ; wvalK := Walk_nilK x |}.

Definition size_walk {Lv Le : Type} {G : dam Lv Le} {x : G} : Walk x -> nat :=
  fun w => size (wval w).

(* Order of a node : size of the bigger walk starting from it *)
Definition dam_order {Lv Le : Type} (G : dam Lv Le) : G -> nat :=
  fun x => size_walk [arg max_(w > Walk_nil x) (size_walk w)].

Lemma dam_order_monotone {Lv Le : Type} (G : dam Lv Le) :
  forall (x y : G), is_connected_strict x y -> (dam_order x < dam_order y)%coq_nat.
Proof.
  move => x y /sigW-[p /andP[/eqP-P W]]. unfold dam_order.
  enough (E : size_walk [arg max_(w0 > Walk_nil y)(size_walk w0)] >=
          size_walk [arg max_(w0 > Walk_nil x)(size_walk w0)] + size p).
  { destruct p as [ | ? p]; try by [].
    simpl in E.
    assert (Hr : (size p).+1 = size p +1) by lia.
    rewrite Hr {Hr} in E.
    enough (size_walk [arg max_(w0 > Walk_nil x)size_walk w0] + 1 <=
      size_walk [arg max_(w0 > Walk_nil y)size_walk w0]) by lia.
    assert (E' : size_walk [arg max_(w0 > Walk_nil x)size_walk w0] + 1 <=
      size_walk [arg max_(w0 > Walk_nil x)size_walk w0] + (size p + 1)) by lia.
    apply (leq_trans E' E). }
  destruct [arg max_(w0 > Walk_nil x)size_walk w0] as [v V].
  rewrite {1}/size_walk /=.
  revert V => /existsP/sigW[t V].
  assert (WV : [exists t, walk y t (p ++ v)]).
  { apply /existsP. exists t. exact (walk_cat W V). }
  assert (Hr : size_walk {| wval := _ ; wvalK := WV |} = size v + size p).
  { rewrite /size_walk /= size_cat. lia. }
  rewrite -Hr {Hr}.
  case: arg_maxnP; trivial.
  intros ? _ H. by apply H.
Qed.

Lemma well_founded_dam {Lv Le : Type} (G : dam Lv Le) :
  well_founded (@is_connected_strict _ _ G).
Proof. exact (Wf_nat.well_founded_lt_compat _ _ _ (@dam_order_monotone _ _ G)). Qed.

Lemma dam_order_max {Lv Le : Type} (G : dam Lv Le) :
  forall (x : G), dam_order x <= #|G|.
Proof.
  intro x. unfold dam_order.
  destruct [arg max_(_ > _)_ _] as [p P].
  rewrite /size_walk /=.
  revert P => /existsP/sigW[? P].
  by apply (walk_size P).
Qed.

Definition dam_order_rev {Lv Le : Type} (G : dam Lv Le) : G -> nat :=
  fun x => #|G| - dam_order x.

Lemma dam_order_to_rev {Lv Le : Type} (G : dam Lv Le) :
  forall (x y : G), (dam_order x > dam_order y)%coq_nat ->
  (dam_order_rev x < dam_order_rev y)%coq_nat.
Proof.
  intros x y. unfold dam_order_rev, dam_order.
  enough (size_walk [arg max_(w > Walk_nil x)size_walk w] <= #|G|
    /\ size_walk [arg max_(w > Walk_nil y)size_walk w] <= #|G|) by lia.
  split; apply dam_order_max.
Qed.

Lemma dam_order_monotone_rev {Lv Le : Type} (G : dam Lv Le) :
  forall (x y : G), is_connected_strict_rev x y -> (dam_order_rev x < dam_order_rev y)%coq_nat.
Proof. intros. by apply dam_order_to_rev, dam_order_monotone. Qed.

Lemma well_founded_dam_rev {Lv Le : Type} (G : dam Lv Le) :
  well_founded (@is_connected_strict_rev _ _ G).
Proof. exact (Wf_nat.well_founded_lt_compat _ _ _ (@dam_order_monotone_rev _ _ G)). Qed.
