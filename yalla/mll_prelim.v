(* Preliminaries for proof nets in MLL *)

From Coq Require Import Bool.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries bij.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


(** * For simplification *)
Lemma SubK' (T : Type) (P : pred T) (u : T) (U : P u) : valP (exist _ u U) = U.
Proof. apply eq_irrelevance. Qed. (* TODO to use *)

Lemma subn_0 (n : nat) : n - 0 = n.
Proof. lia. Qed. (* TODO extrêment bizarre qu'il n'y soit pas déjà ... *)

(** * Useful tactics *)
(** Break hypothesys, try to rewrite them, and simplify *)
Ltac introb := repeat (let H := fresh "Hif" in let H' := fresh "Hif" in
  match goal with
  | |- is_true (~~ ~~ ?x)      -> _ => move => /negPn //
  | |- (~~ ?x) = false         -> _ => move => /negPn //
  | |- ~~ (?x = false)         -> _ => move => /negPn //
  | |- is_true (?x && ?y)      -> _ => move => /andP[H H'] //; revert H H'
  | |- is_true (~~ (?x && ?y)) -> _ => move => /nandP[H | H] //; revert H
  | |- (?x && ?y) = false      -> _ => move => /nandP[H | H] //; revert H
  | |- is_true (?x || ?y)      -> _ => move => /orP[H | H] //; revert H
  | |- is_true (~~ (?x || ?y)) -> _ => move => /norP[H H'] //; revert H H'
  | |- (?x || ?y) = false      -> _ => move => /norP[H H'] //; revert H H'
  | |- is_true ?x              -> _ => move => /eqP-H //; rewrite 1?H //
  | |- ?x = false              -> _ => move => /eqP-H //; rewrite 1?H //
  | |- ?x = ?y                 -> _ => move => H //; rewrite 1?H //
  | |- _                       -> _ => move => H //
  end);
  rewrite_all eqbF_neg; rewrite_all eqb_id; rewrite_all eq_refl;
  rewrite_all negb_involutive; try subst; try done.

(** Make cases on if *)
(* Make all cases, try to rewrite the equality condition and conserve the conditions
  under the form _ = _ or _ <> _, folding trivial cases *)
Ltac case_if1 := repeat (case: ifP); cbn; introb.
Ltac case_if := repeat case_if1.

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
Ltac cbnb := repeat (cbn; try (apply /eqP; cbn; apply /eqP); rewrite //=).




(** * About set *)
Lemma enum_subset {T : finType} P : enum [set x | P x] = filter P (enum T).
Proof.
  rewrite enumT.
  apply eq_filter. hnf.
  apply in_set.
Qed.


Lemma finset_of_pred_of_set (T : finType) (S : {set T}) : finset (pred_of_set S) = S.
Proof. apply /setP. intros ?. by rewrite !in_set. Qed.


(** Both visions of a set as set or subset have the same cardinal *)
Lemma card_set_subset {T : finType} (P : pred T) :
  #|[finType of {e : T | P e}]| = #|[set e | P e]|.
Proof. by rewrite card_sig cardsE. Qed.


Lemma setC2 {T : finType} (a b : T) :
  ~: [set a; b] = setT :\ a :\ b.
Proof. apply /setP => ?. by rewrite !in_set negb_orb andb_true_r andb_comm. Qed.


Lemma setCn {T : finType} (P : pred T) :
  [set x | ~~ P x] = ~: [set x | P x].
Proof. by apply /setP => ?; rewrite !in_set. Qed.


Lemma setT_in_pred {T : finType} (P : pred T) :
  [set x in setT | P x] = [set x | P x].
Proof. apply /setP => ?. by rewrite !in_set. Qed.


Lemma imsetUCr {aT rT : finType} (f : aT -> rT) (P : pred aT) :
  [set f a | a : aT & ~~ P a] :|: [set f a | a : aT & P a] = [set f a | a in setT].
Proof. by rewrite -imsetU setUC setCn setUCr. Qed.


Lemma sum_pred {A B : finType} (P : pred (A + B)) :
  [set x : A + B | P x] = inl @: [set x | P (inl x)] :|: inr @: [set x | P (inr x)].
Proof.
  apply /setP => x.
  rewrite !in_set.
  symmetry. destruct (P x) eqn:H, x.
  - rewrite mem_imset; last by apply inl_inj.
    by rewrite in_set H.
  - rewrite mem_imset; last by apply inr_inj.
    by rewrite in_set H orb_true_r.
  - apply /norP. split.
    + rewrite mem_imset; last by apply inl_inj.
      by rewrite in_set H.
    + apply /imsetP. by intros [? ? ?].
  - apply /norP. split.
    + apply /imsetP. by intros [? ? ?].
    + rewrite mem_imset; last by apply inr_inj.
      by rewrite in_set H.
Qed.


Lemma inlr_pred_I {R S : finType} (P : pred R) (Q : pred S) :
  [set inl x | x : R & P x] :&: [set inr x | x : S & Q x] = set0.
Proof.
  apply /setP => x.
  rewrite !in_set.
  apply /nandP.
  destruct x; [right | left];
  apply /imsetP; by intros [? ? ?].
Qed.


Lemma cards_sum_pred {A B : finType} P :
  #|[set x : A + B | P x]| = #|[set x | P (inl x)]| + #|[set x | P (inr x)]|.
Proof. rewrite sum_pred cardsU inlr_pred_I cards0 subn_0 !card_imset //; apply inr_inj || apply inl_inj. Qed.


Lemma set1C {T : finType} (x : T) : [set~ x] = setT :\ x.
Proof. apply /setP => ?. by rewrite !in_set andb_true_r. Qed.


Lemma set1CI {T : finType} (S : {set T}) (x : T) : S :&: [set~ x] = S :\ x.
Proof. by rewrite set1C setIDA setIT. Qed.


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
  - move => /norP[/eqP H' /eqP H''] [z Hz].
    revert Hz; rewrite !in_set; by move => /orP[/eqP -> | /eqP ->].
Qed.


Lemma finset0 {T : finType} {S : {set T}} (t : T) :
  t \in S -> #|S| <> 0.
Proof.
  intros I C. contradict I; apply /negP.
  by rewrite (cards0_eq C) in_set.
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

Lemma pick_unique_set {T : finType} {S : {set T}} (H : #|S| = 1) :
  S = [set pick_unique H].
Proof.
  symmetry; apply /setP/subset_cardP.
  - by rewrite cards1 H.
  - by rewrite sub1set pick_unique_in.
Qed.

Lemma pick_unique_eq {T : finType} {S : {set T}} (H : #|S| = 1) :
  forall s, s \in S -> s = pick_unique H.
Proof.
  intros s Sin.
  apply /set1P.
  by rewrite -(pick_unique_set H).
Qed.


(** Function picking the 2nd element of a 2-elements set *)
Definition unique_other {T : finType} (S : {set T}) (x : T) :
  #|S| = 2 -> x \in S -> #|S :\ x| = 1.
Proof. replace (#|S :\ x|) with (#|S| - (x \in S)) by (rewrite (cardsD1 x S); lia). lia. Qed.

Definition other {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :=
  pick_unique (unique_other Hs Hin).

Lemma other_in_neq {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :
  other Hs Hin \in S /\ other Hs Hin != x.
Proof. by destruct (setD1P (pick_unique_in (unique_other Hs Hin))). Qed.

Lemma other_set {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :
  S = [set x; other Hs Hin].
Proof.
  symmetry; apply /setP/subset_cardP.
  - rewrite cards2 Hs eq_sym.
    by destruct (other_in_neq Hs Hin) as [_ ->].
  - replace (pred_of_set S) with (pred_of_set (S :|: S)) by (f_equal; apply setUid).
    apply setUSS; rewrite sub1set //.
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
Proof. apply pick_unique_eq. rewrite !in_set. splitb. by apply /eqP. Qed.


(** Results on 'I_n *)
(* Tactic to distinguish cases in 'I_n for n <= 10, n arbitrary *)
Ltac destruct_I i := let I := fresh "I" in
  destruct i as [i I]; do 10 (try (destruct i as [ | i])); try by [].
(* Ltac nsplit n i :=
  match n with
  | 0 => idtac
  | S ?m => destruct i as [ | i]; [ | nsplit m]
  end. TODO possible to do better with something like this ? *)

(* Tactic computing cardinals of subsets of 'I_n, with n fixed to a constant *)
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

Lemma inr_seq_inl_filter {L R : eqType} (l : seq L) (P : pred L) :
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
  (x \in s) -> exists n, s = (take n s) ++ x :: (drop n.+1 s).
Proof.
  move => /(nthP x) [n N E].
  exists n.
  by rewrite -{1}(cat_take_drop n s) -E -drop_nth.
Qed.

Lemma rcons_nil {T : Type} (s : seq T) (x : T) :
  rcons s x <> [::].
Proof.
  intro H.
  assert (Hs : size (rcons s x) = 0) by by rewrite H.
  contradict Hs.
  by rewrite size_rcons.
Qed.

Lemma in_rcons {T : eqType} (y : T) (s : seq T) (x : T) :
  x \in rcons s y = (x == y) || (x \in s).
Proof. by rewrite -has_pred1 has_rcons has_pred1 pred1E. Qed.

Lemma in_rev {T : eqType} (s : seq T) (x : T) :
  x \in rev s = (x \in s).
Proof. by rewrite -has_pred1 has_rev has_pred1. Qed.

Lemma map_nil {T U : eqType} (s : seq T) (f : T -> U) :
  ([seq f x | x <- s] == [::]) = (s == [::]).
Proof. by destruct s. Qed.

Lemma cat_nil {T : eqType} (s r : seq T) :
  (s ++ r == [::]) = (s == [::]) && (r == [::]).
Proof. by destruct s, r. Qed.

Lemma rev_nil {A : finType} (l : list A) :
  (rev l == [::]) = (l == [::]).
Proof. destruct l; trivial. rewrite rev_cons. apply /eqP. apply rcons_nil. Qed.

Lemma last_rev {T : Type} (s : seq T) (x : T) :
  last x (rev s) = head x s. (* TODO unused ? *)
Proof. destruct s; by rewrite // rev_cons last_rcons. Qed.

Lemma eq_seq_sig {T : eqType} {P : pred T} (l r : seq ({x : T | P x})) :
  [seq sval v | v <- l] = [seq sval v | v <- r] -> l = r.
Proof.
  revert l; induction r as [ | ? ? IH] => l /=.
  { move => /eqP. by rewrite map_nil => /eqP-->. }
  destruct l; simpl; first by by [].
  intro H. inversion H as [[H0 H1]].
  rewrite (IH _ H1). apply /eqP. cbn. rewrite H0. splitb. by apply /eqP.
Qed.

Lemma forall_notincons {A : eqType} {B : finType} (P : B -> A) (f : A) p :
  [forall b, P b \notin f :: p] = [forall b, P b != f] && [forall b, P b \notin p].
Proof.
  symmetry; destruct [forall b, P b \notin f :: p] eqn:H; revert H.
  - move => /forallP-H.
    splitb; apply /forallP => a; revert H => /(_ a); rewrite in_cons; introb.
  - move => /forallPn[a /negPn].
    rewrite in_cons => /orP[/eqP-H | H];  apply /nandP; [left | right]; apply /forallPn; exists a;
    rewrite H; by apply /negPn.
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

Lemma perm_of_rew_r {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) :
  forall (l3 : seq A) (Heq : l2 = l3) (B : Type),
  @perm_of A l1 l3 (rew Heq in sigma) B =1 perm_of sigma.
Proof. intros. by subst. Qed.


(** Permutation for maps, defined (as opposed as in OLlibs) ... *)
Fixpoint Permutation_Type_map_def {A B : Type} (f : A -> B) (l l' : seq A)
  (sigma : Permutation_Type l l') : Permutation_Type (map f l) (map f l') :=
  match sigma with
  | Permutation_Type_nil_nil => Permutation_Type_nil_nil _
  | Permutation_Type_skip x _ _ tau => Permutation_Type_skip (f x) (Permutation_Type_map_def f tau)
  | Permutation_Type_swap x y l0 => Permutation_Type_swap (f x) (f y) (map f l0)
  | Permutation_Type_trans _ _ _ tau1 tau2 =>
      Permutation_Type_trans (Permutation_Type_map_def f tau1) (Permutation_Type_map_def f tau2)
  end.

(* ... in order to prove the following lemma *)
Lemma perm_of_Permutation_Type_map {S : Type}  {l1 l2 : seq S} (sigma : Permutation_Type l1 l2) :
  forall {A B : Type} (l : seq A) (f : S -> B),
  perm_of (Permutation_Type_map_def f sigma) l = perm_of sigma l.
Proof.
  induction sigma as [ | ? ? ? ? H | | ? ? ? ? H ? H'] => A B l0 f; trivial; simpl.
  - destruct l0; trivial. by rewrite H.
  - by rewrite H H'.
Qed.


(** Permutation between two lists without duplicate and linked by a bijection *)
Definition Permutation_Type_bij_uniq {A B : eqType} (h : bij A B) (l : seq A) (l' : seq B) :
  uniq l -> uniq l' -> (forall x, x \in l <-> h x \in l') ->
  Permutation_Type l' [seq h x | x <- l].
Proof.
  revert l'. induction l as [ | e l IH] => /= l' U U' In.
  - enough (l' = [::]) as -> by exact (Permutation_Type_nil_nil _).
    destruct l' as [ | e' l']; trivial.
    specialize (In (h^-1 e')).
    rewrite in_nil in_cons bijK' eq_refl /= in In.
    by assert false by by apply In.
  - revert U => /= /andP[Nin U].
    assert (Ine : h e \in l').
    { apply In. rewrite in_cons. caseb. }
    assert (N : exists n : nat, l' == take n l' ++ h e :: drop n.+1 l').
    { destruct (in_elt_sub Ine) as [n ?]. exists n. by apply /eqP. }
    revert N => /sigW[n /eqP-N].
    set l1' := take n l'.
    set l2' := drop n.+1 l'.
    fold l1' l2' in N.
    assert (In2 : forall a, a \in l <-> h a \in l1' ++ l2').
    { intro a.
      destruct (eq_comparable a e) as [? | Hneq]; [subst a | ].
      - split => H.
        + by contradict H; apply /negP.
        + contradict U'; apply /negP.
          rewrite N.
          change (h e :: l2') with ([:: h e] ++ l2').
          rewrite uniq_catCA cat_uniq has_sym /=. caseb.
      - specialize (In a).
        revert In.
        rewrite N !mem_cat !in_cons bij_eq //.
        by replace (a == e) with false by by symmetry; apply /eqP. }
    assert (U'2 : uniq (l1' ++ l2')).
    { revert U'. rewrite N !cat_uniq /=. introb. splitb. }
    specialize (IH _ U U'2 In2).
    rewrite N.
    by symmetry; apply Permutation_Type_cons_app; symmetry.
Defined.



(** * A DecType is an eqType *)
Definition decType_eqMixin (X : DecType) := EqMixin (eq_dt_reflect (X := X)).



(** * About image of a set through a bijection *)
Lemma bij_imset_invert (aT rT : finType) (f : bij aT rT) (A : {set aT}) (B : {set rT}) :
  B = [set f x | x in A] -> A = [set f^-1 x | x in B].
Proof.
  intros ->. rewrite -imset_comp -{1}(imset_id A).
  apply eq_imset => ?. by rewrite /= bijK.
Qed.
