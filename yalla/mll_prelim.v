(* Preliminaries for proof nets in MLL *)

From Coq Require Import Bool.
From OLlibs Require Import dectype Permutation_Type_more.
From mathcomp Require Import all_ssreflect zify.
From GraphTheory Require Import preliminaries.

Import EqNotations.

Set Mangle Names.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


(** * Useful tactics *)
(** Break hypothesys *)
Ltac introb := repeat (let H := fresh "Hif" in let H' := fresh "Hif" in
  match goal with
  | |- is_true (?x && ?y) -> _      => move => /andP[H H']; revert H H'
  | |- is_true (~~ (?x && ?y)) -> _ => move => /nandP[H | H]; revert H
  | |- (?x && ?y) = false -> _      => move => /nandP[H | H]; revert H
  | |- is_true (?x || ?y) -> _      => move => /orP[H | H]; revert H
  | |- is_true (~~ (?x || ?y)) -> _ => move => /norP[H H']; revert H H'
  | |- (?x || ?y) = false -> _      => move => /norP[H H']; revert H H'
  | |- is_true ?x -> _              => move => /eqP H; rewrite // 1?H //
  | |- ?x = false -> _              => move => /eqP H; rewrite // 1?H //
  | |- ?x = ?y -> _                 => move => H; rewrite // 1?H //
  | |- _ -> _                       => move => H
  end).

(** Make cases on if *)
(* Make all cases, try to rewrite the equality condition and conserve the conditions
  under the form _ = _ or _ <> _, folding trivial cases *)
Ltac case_if := repeat (case: ifP); cbn; introb.

(** Split both /\ and && and ~~||, folding trivial cases *)
Ltac splitb := repeat (split || apply /andP || apply /norP); trivial.

(** Solve trivial \/ and || and ~~&& *)
Ltac caseb :=
  try done;
  try ((by left; caseb) || (by right; caseb));
  try (apply /orP; (by left; caseb) || (by right; caseb));
  try (apply /nandP; (by left; rewrite ?negb_involutive //; caseb)
                  || (by right; rewrite ?negb_involutive //; caseb)).

(** Try to simplify the goal *)
Ltac cbnb := repeat (cbn; try (apply /eqP; cbn; apply /eqP); rewrite ?SubK //).




(** * About set *)
Lemma enum_subset {T : finType} P : enum [set x | P x] = filter P (enum T).
Proof.
  rewrite enumT.
  apply eq_filter. hnf.
  apply in_set.
Qed.


Lemma set2D1 {T : finType} (a b : T) : b != a -> [set a; b] :\ a = [set b].
Proof.
  intro H. apply /setP => e.
  rewrite !in_set andb_orb_distrib_r andNb; cbn.
  elim: (eq_comparable e b).
  - move => ->. by rewrite H.
  - move => /eqP /negPf ->. by rewrite andb_false_r.
Qed.


Lemma cardsUmax [T : finType] (A B : {set T}) : #|A| <= #|A :|: B| /\ #|B|  <= #|A :|: B|.
Proof. split; apply subset_leq_card; [apply subsetUl | apply subsetUr]. Qed.


Lemma imset_set2 : forall (aT rT : finType) (f : aT -> rT) (x y : aT),
  [set f x | x in [set x; y]] = [set f x; f y].
Proof.
  intros ? ? f x y.
  apply /setP => ?.
  rewrite Imset.imsetE !in_set.
  apply /imageP. case: ifP.
  - move => /orP[/eqP -> | /eqP ->];
    [exists x | exists y]; trivial;
    rewrite !in_set; caseb.
  - move => /norP [/eqP H' /eqP H''] [z Hz].
    revert Hz; rewrite !in_set; by move => /orP [/eqP -> | /eqP ->].
Qed.


Lemma pick1 {T : finType} (t : T) : [pick x in [set t]] = Some t.
Proof.
  case: pickP.
  - intros ?.
    rewrite in_set.
    by move => /eqP ->.
  - move => /(_ t).
    by rewrite in_set1 eq_refl.
Qed.


(** Function picking the only element of a singleton *)
Definition pick_unique := fun {T : finType} {S : {set T}}
  (H : #|S| = 1) => sval (mem_card1 H).

Lemma pick_unique_in {T : finType} {S : {set T}} (H : #|S| = 1) :
  pick_unique H \in S.
Proof.
  rewrite -subset_pred1.
  apply eq_subxx.
  unfold pick_unique.
  by destruct (mem_card1 H).
Qed.

Lemma pick_unique_set {T : finType} {S : {set T}} (Hs : #|S| = 1) :
  S = [set pick_unique Hs].
Proof.
  symmetry; apply /setP /subset_cardP.
  - by rewrite cards1 Hs.
  - by rewrite sub1set pick_unique_in.
Qed.


(** Function picking the 2nd element of a 2-elements set *)
Definition unique_other {T : finType} (S : {set T}) (x : T) :
  #|S| = 2 -> x \in S -> #|S :\ x| = 1.
Proof. replace (#|S :\ x|) with (#|S| - (x \in S)) by (rewrite (cardsD1 x S); lia). lia. Qed.

Definition other {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :=
  pick_unique (unique_other Hs Hin).

Lemma other_in_neq {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :
  other Hs Hin \in S /\ other Hs Hin != x.
Proof. unfold other. by destruct (setD1P (pick_unique_in (unique_other Hs Hin))). Qed.

Lemma other_set {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :
  S = [set x; other Hs Hin].
Proof.
  symmetry; apply /setP /subset_cardP.
  - rewrite cards2 Hs eq_sym.
    by destruct (other_in_neq Hs Hin) as [_ ->].
  - replace (pred_of_set S) with (pred_of_set (S :|: S)) by (f_equal; apply setUid).
    apply setUSS;
    rewrite sub1set //.
    apply other_in_neq.
Qed.

Lemma other_setD {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :
  S :\ x = [set other Hs Hin].
Proof.
  apply setP; hnf => *.
  by rewrite (proj2_sig (mem_card1 (unique_other _ _))) in_set.
Qed.

Lemma other_eq {T : finType} {S : {set T}} {x y : T} (Hs : #|S| = 2) (Hx : x \in S)
  (Hy : y \in S) (Hneq : y <> x) : y = other Hs Hx.
Proof. apply /set1P. rewrite -other_setD. apply /setD1P. splitb. by apply /eqP. Qed.


(** Results on 'I_n *)
(* Tactic to distinguish cases in 'I_2 *)
Lemma case_I2 : forall (n : 'I_2), n = ord0 \/ n = ord1.
Proof.
  enough (H : forall (n : 'I_2), (n == ord0) || (n == ord1)).
  { intro n. revert H => /(_ n) /orP[/eqP H | /eqP H]; caseb. }
  by intros [[ | [ | n]] ?].
Qed.

Ltac destruct_I2 n := destruct (case_I2 n) as [? | ?]; subst n.

(* Tactic to distinguish cases in 'I_3 *)
Lemma case_I3 : forall (n : 'I_3), n = ord0 \/ n = ord1 \/ n = ord2.
Proof.
  enough (H : forall (n : 'I_3), (n == ord0) || (n == ord1) || (n == ord2) : bool).
  { intro n. revert H => /(_ n) /orP[/orP[/eqP H | /eqP H] | /eqP H]; caseb. }
  by intros [[ | [ | [ | n]]] ?].
Qed.

Ltac destruct_I3 n := destruct (case_I3 n) as [? | [? | ?]]; subst n.


(* Tactic computing cardinals of subsets of 'I_n, with n fixed to a known nat *)
Lemma enum_I0 : enum 'I_0 = [::].
Proof. rewrite -enum0. apply eq_enum, card0_eq, card_ord. Qed.

Ltac compute_card_subIn := rewrite cardE enum_subset; cbn;
                           repeat (rewrite enum_ordS; cbn);
                           now rewrite enum_I0.


(** Symmetric property on set with 2 elements *)
Definition true_on2 {T : finType} {S : {set T}} (P : rel T) (HS : #|S| = 2) :=
  forall (t : T) (Ht : t \in S), P t (other HS Ht).

(* Proving a symmetric property on one suffices to prove it on all *)
Lemma simpl_sym {T : finType} {S : {set T}} (HS : #|S| = 2) (P : rel T)
  (HP : symmetric P) (t : T) (Ht : t \in S) : P t (other HS Ht) -> true_on2 P HS.
Proof.
  intros H s.
  destruct (eq_comparable t s) as [<- | Hneq] => Hs.
  - by replace Hs with Ht by apply eq_irrelevance.
  - by rewrite -(other_eq HS Hs Ht Hneq) HP (other_eq HS Ht Hs (nesym Hneq)).
Qed.



(** * About seq *)
Lemma in_notin {T : eqType} (l : seq T) (x y : T) :
  x \in l -> y \notin l -> x != y.
Proof.
  intros Hx Hy.
  destruct (eq_comparable x y) as [-> | ].
  - by contradict Hx; apply /negP.
  - by apply /eqP.
Qed.

Lemma inr_seq_inl_filter {L R : eqType} (l: seq L) (P : pred L) :
  forall (b : R), (inr b : L + R) \notin [seq (inl a : L + R) | a <- l & P a].
Proof. intros. induction l as [ | a ? ?]; cbn; trivial. by case: (P a). Qed.

Lemma in_seq_sig {T : eqType} {P : pred T} : forall (a : {x : T | P x}) (l : seq ({x : T | P x})),
  (a \in l) = (sval a \in [seq sval v | v <- l]).
Proof. intros ? l. induction l as [ | ? ? H]; trivial. by rewrite !in_cons H. Qed.

Lemma uniq_seq_sig {T : eqType} {P : pred T} : forall (l : seq ({x : T | P x})),
  (uniq l) = (uniq [seq sval v | v <- l]).
Proof.
  intro l; induction l as [ | ? ? H]; trivial.
  by rewrite map_cons !cons_uniq -H in_seq_sig.
Qed.

Lemma not_uniq_map {T U : eqType} (f : T -> U) (s : seq T) :
  forall x y, x \in s -> y \in s -> x <> y -> f x = f y -> ~~ uniq (map f s).
Proof.
  intros x y X Y N E.
  apply /(uniqPn (f x)).
  enough (O : index x s < index y s \/ index y s < index x s).
  { destruct O; [exists (index x s), (index y s) | exists (index y s), (index x s)].
    all: by rewrite size_map !(nth_map x) ?nth_index ?index_mem. }
  destruct (index x s < index y s) eqn:H; [caseb | ].
  enough (index y s <> index x s) by lia.
  intro Hc; contradict N.
  by rewrite -(nth_index x X) -(nth_index x Y) Hc.
Qed.

Lemma in_elt_sub {T : eqType} (s : seq T) (x : T) :
  (x \in s) -> exists l r, s = l ++ x :: r.
Proof.
  move => /(nthP x) [n N E].
  exists (take n s), (drop n.+1 s).
  by rewrite -{1}(cat_take_drop n s) -E -drop_nth.
Qed.



(** * About permutations *)
(** Function taking two lists l1 l2 permutations of one another, and returning a
polymorphic permutation sending l1 to l2 *)
Fixpoint perm_of {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) {struct sigma} :
  forall {B : Type}, seq B -> seq B :=
  match sigma with
  | Permutation_Type_nil_nil => fun _ => id
  | Permutation_Type_skip _ _ _ tau => fun _ b => match b with
    | d :: e => d :: (perm_of tau e)
    | [::] => [::]
    end
  | Permutation_Type_swap _ _ _ => fun _ b => match b with
    | f :: d :: e => d :: f :: e
    | _ => b
    end
  | Permutation_Type_trans _ _ _ tau1 tau2 => fun _ b => perm_of tau2 (perm_of tau1 b)
  end.

Lemma perm_of_consistent {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) :
  perm_of sigma l1 = l2.
Proof. unfold perm_of. by induction sigma as [ | ? ? ? ? -> | | ? ? ? ? -> ? ->]. Qed.

Lemma perm_of_map {A B S : Type}  {l1 l2 : seq S} (sigma : Permutation_Type l1 l2)
  (l : seq A) (f : A -> B) :
  perm_of sigma [seq f i | i <- l] = [seq f i | i <- perm_of sigma l].
Proof.
  revert A B l f.
  induction sigma as [ | ? ? ? ? H | | ? ? ? ? H ? H'] => A B l0 f; trivial; cbn.
  - destruct l0; trivial; cbn; by rewrite H.
  - by destruct l0 as [ | ? [ | ? ?]].
  - by rewrite H H'.
Qed.

Lemma perm_of_in {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) :
  forall {B : finType} (l : seq B) (b : B), (b \in perm_of sigma l) = (b \in l).
Proof.
  induction sigma as [ | ? ? ? ? H | | ? ? ? ? H ? H'] => B l0 b; trivial; cbn.
  - destruct l0; trivial; by rewrite !in_cons H.
  - destruct l0 as [ | a [ | a' l0]]; trivial.
    rewrite !in_cons !orb_assoc.
    by replace ((b == a') || (b == a)) with ((b == a) || (b == a')) by by rewrite orb_comm.
  - by rewrite H' H.
Qed.

Lemma perm_of_uniq {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) {B : finType}
  (l : seq B) : uniq (perm_of sigma l) = uniq l.
Proof.
  revert B l.
  induction sigma as [ | ? ? ? ? H | | ? ? ? ? H ? H'] => B l0; trivial; cbn.
  - destruct l0; trivial; cbn; by rewrite perm_of_in H.
  - destruct l0 as [ | ? [ | ? ?]]; trivial; cbn.
    rewrite !in_cons !negb_or !andb_assoc; apply andb_id2r => _.
    rewrite andb_comm andb_assoc; apply andb_id2r => _.
    rewrite andb_comm; apply andb_id2r => _.
    apply /eqP; case_if. by apply nesym.
  - by rewrite H' H.
Qed.



(** * A DecType is an eqType *)
Definition decType_eqMixin (X : DecType) := EqMixin (eq_dt_reflect (X := X)).
