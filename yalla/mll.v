(* Unit-free MLL following Yalla schemas *)


From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
From mathcomp Require Import all_ssreflect zify.
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.
From HB Require Import structures.

Import EqNotations.

Set Mangle Names.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(** * MLL formulas *)

Section Atoms.

(** A set of atoms for building formulas *)
Context { atom : DecType }.

(** Formulas *)
Inductive formula :=
| var : atom -> formula
| covar : atom -> formula
| tens : formula -> formula -> formula
| parr : formula -> formula -> formula.
Notation "'ν' X" := (var X) (at level 12).
Notation "'κ' X" := (covar X) (at level 12).
Infix "⊗" := tens (left associativity, at level 25). (* TODO other way to overload notations ? *)(* zulip *)
Infix "⅋" := parr (at level 40).

(** ** Equality of [formula] in [bool] *)
Fixpoint eqb_form A B :=
match A, B with
| var X, var Y => dectype.eqb X Y
| covar X, covar Y => dectype.eqb X Y
| tens A1 A2, tens B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| parr A1 A2, parr B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| _, _ => false
end.

Lemma eqb_eq_form : forall A B, eqb_form A B = true <-> A = B.
Proof.
intro A; induction A as [ | | ? IHA1 ? IHA2 | ? IHA1 ? IHA2];
intro B; destruct B; (split; intros Heq); inversion Heq as [H0]; auto.
- now apply eqb_eq in H0; subst.
- now subst; cbn; apply eqb_eq.
- now apply eqb_eq in H0; subst.
- now subst; cbn; apply eqb_eq.
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  now apply IHA1 in H1; apply IHA2 in H2; subst.
- now subst; cbn; apply andb_true_iff; split; [ apply IHA1 | apply IHA2 ].
- apply andb_true_iff in H0 as [H1 H2].
  now apply IHA1 in H1; apply IHA2 in H2; subst.
- now subst; cbn; apply andb_true_iff; split; [ apply IHA1 | apply IHA2 ].
Qed.

Definition formulas_dectype := {|
  car := formula;
  dectype.eqb := eqb_form;
  eqb_eq := eqb_eq_form |}.

(** ** Dual of a [formula] *)
Fixpoint dual A :=
match A with
| var x     => covar x
| covar x   => var x
| tens A B  => parr (dual B) (dual A)
| parr A B  => tens (dual B) (dual A)
end.
Notation "A ^" := (dual A) (at level 12, format "A ^").

Lemma bidual A : dual (dual A) = A.
Proof. now induction A as [ | | ? IHA1 ? IHA2 | ? IHA1 ? IHA2]; cbn; rewrite ?IHA1 ?IHA2. Qed.

Lemma codual A B : dual A = B <-> A = dual B.
Proof. now split; intro H; rewrite <- (bidual A), <- (bidual B), H, ? bidual. Qed.

Lemma dual_inj : injective dual.
Proof. now intros A B H; rewrite <- (bidual A), <- (bidual B), H. Qed.

(** ** Size of a [formula] as its number of symbols *)
Fixpoint fsize A :=
match A with
| var X    => 1
| covar X  => 1
| tens A B => S (fsize A + fsize B)
| parr A B => S (fsize A + fsize B)
end.

Lemma fsize_pos A : 0 < fsize A.
Proof. by induction A. Qed.

Lemma fsize_dual A : fsize (dual A) = fsize A.
Proof. induction A as [ | | ? IHA1 ? IHA2 | ? IHA1 ? IHA2]; cbn; rewrite ?IHA1 ?IHA2; lia. Qed.


(** * MLL Proofs *)
Inductive ll : list formula -> Type :=
| ax_r : forall X, ll (covar X :: var X :: nil)
| ex_r : forall l1 l2, ll l1 -> Permutation_Type l1 l2 -> ll l2
| tens_r : forall A B l1 l2, ll (A :: l1) -> ll (B :: l2) -> ll (tens A B :: l2 ++ l1)
| parr_r : forall A B l, ll (A :: B :: l) -> ll (parr A B :: l)
| cut_r : forall A l1 l2, ll (A :: l1) -> ll (dual A :: l2) -> ll (l2 ++ l1).
Notation "⊢ l" := (ll l) (at level 70).



(** ** Size of proofs *)
Fixpoint psize l (pi : ll l) :=
match pi with
| ax_r _ => 1
| ex_r _ _ pi0 _ => S (psize pi0)
| tens_r _ _ _ _ pi0 pi1 => S (psize pi0 + psize pi1)
| parr_r _ _ _ pi0 => S (psize pi0)
| cut_r _ _ _ pi0 pi1 => S (psize pi0 + psize pi1)
end.

Lemma psize_pos l (pi : ll l) : 0 < psize pi.
Proof. by destruct pi. Qed.

Lemma psize_rew l l' (pi : ll l) (Heq : l = l') : psize (rew Heq in pi) = psize pi.
Proof. now subst. Qed.

(* TODO cleaning above -> psize useless ? *)
(*********************************************************************************************)
(** ** Preliminaries *) (* TODO organize preliminaries (break it ? add formulas + proofs in it ? ... *)
(** * Some useful tactics *)
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


(** * Some results on 'I_n *)
(** 'I_0 has the empty enumeration *)
Lemma enum_I0 : enum 'I_0 = [::].
Proof. rewrite -enum0. apply eq_enum, card0_eq, card_ord. Qed.

(** Tactic to distinguish cases in 'I_2 *)
Lemma case_I2 : forall (n : 'I_2), n = ord0 \/ n = ord1.
Proof.
  enough (H : forall (n : 'I_2), (n == ord0) || (n == ord1)).
  { intro n.
    revert H; move =>  /(_ n) /orP[/eqP H | /eqP H]; caseb. }
  by intros [[ | [ | n]] ?].
Qed.

Ltac destruct_I2 n := destruct (case_I2 n) as [? | ?]; subst n.

(** Tactic to distinguish cases in 'I_3 *)
Lemma case_I3 : forall (n : 'I_3), n = ord0 \/ n = ord1 \/ n = ord2.
Proof.
  enough (H : forall (n : 'I_3), (n == ord0) || (n == ord1) || (n == ord2) : bool).
  { intro n.
    revert H; move =>  /(_ n) /orP[/orP[/eqP H | /eqP H] | /eqP H]; caseb. }
  by intros [[ | [ | [ | n]]] ?].
Qed.

Ltac destruct_I3 n := destruct (case_I3 n) as [? | [? | ?]]; subst n.


(** * Type [rule] for the rule of a node *)
Inductive rule : Type :=
  | ax_l
  | tens_l
  | parr_l
  | cut_l
  | concl_l.
Notation ax := (ax_l).
Notation "⊗" := (tens_l) (at level 12).
Notation "⅋" := (parr_l) (at level 12).
Notation cut := (cut_l).
Notation c := (concl_l).

(** Equality of [rule] *)
Definition eqb_rule (A B : rule): bool :=
  match A, B with
  | ax, ax    => true
  | ⊗, ⊗      => true
  | ⅋, ⅋      => true
  | cut, cut  => true
  | c, c      => true
  | _, _      => false
  end.

Lemma eqb_eq_rule : forall A B, eqb_rule A B = true <-> A = B.
Proof. by intros [] []. Qed.

Definition rules_dectype := {|
  car := rule;
  dectype.eqb := eqb_rule;
  eqb_eq := eqb_eq_rule |}.

(** Function rule_op such that (rule, ax, rule_op) is a commutative monoid *)
(* Necessary to use iso from Graph Theory, but fondamentaly useless for us *)
Definition rule_op : rule -> rule -> rule := fun r s => match r, s with
  | ax, s => s
  | r, ax => r
  | _, _  => c
  end.

Lemma rule_cm_laws : comMonoidLaws (ax : flat rule) rule_op.
Proof.
  splitb.
  - by intros ? ? -> ? ? ->.
  - by intros [] [] [].
  - by intros [].
  - by intros [] [].
Qed.

HB.instance Definition rule_commMonoid :=
  ComMonoid_of_Setoid.Build (flat rule) rule_cm_laws. (* TODO warning equalite avec instance de unit ? typage *)

(** * Graph that we will consider *)
Notation base_graph := (graph (flat rule) (flat formula)). (* [flat] is used for isomorphisms *)

(* In our case, isometries are standard isometries; i.e. they do not flip edges *)
Lemma iso_noflip (F G : base_graph) (h : F ≃ G) : h.d =1 xpred0.
Proof.
  hnf. intro e.
  destruct h as [? ? iso_d [? ? E]]; cbn; clear - E.
  specialize (E e).
  by destruct (iso_d e).
Qed.


(** * A DecType is an eqType *)
Definition decType_eqMixin (X : DecType) := EqMixin (eq_dt_reflect (X := X)).

(* [formula] as an eqType *)
Canonical formula_eqType := EqType formula (decType_eqMixin (formulas_dectype)).

(* [rule] as an eqType *)
Canonical rule_eqType := EqType rule (decType_eqMixin (rules_dectype)).


(** * Removing an element of a 2-elements set yields the set with the other element *)
Lemma set2D1 {T : finType} (a b : T) : b != a -> [set a; b] :\ a = [set b].
Proof.
  intro H. apply /setP => e.
  rewrite !in_set andb_orb_distrib_r andNb; cbn.
  elim: (eq_comparable e b).
  - move => ->. by rewrite H.
  - move => /eqP /negPf ->. by rewrite andb_false_r.
Qed.


(** * Lemma helping computing the cardinal of a subset *)
Lemma enum_subset {T : finType} P : enum [set x | P x] = filter P (enum T).
Proof.
  rewrite enumT.
  apply eq_filter. hnf.
  apply in_set.
Qed.

Lemma cardsUmax [T : finType] (A B : {set T}) : #|A| <= #|A :|: B| /\ #|B|  <= #|A :|: B|.
Proof. split; apply subset_leq_card; [apply subsetUl | apply subsetUr]. Qed.


(** * Tactic computing cardinals of subsets of 'I_n, with n fixed to a known nat *)
Ltac compute_card_subIn := rewrite cardE enum_subset; cbn;
                           repeat (rewrite enum_ordS; cbn);
                           now rewrite enum_I0.


(** * Function picking the only element of a singleton *)
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


(** * Function taking the 2nd element of a 2-elements set *)
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
  apply setP; hnf; intros.
  by rewrite (proj2_sig (mem_card1 (unique_other _ _))) in_set.
Qed.

Lemma other_eq {T : finType} {S : {set T}} {x y : T} (Hs : #|S| = 2) (Hx : x \in S)
  (Hy : y \in S) (Hneq : y <> x) : y = other Hs Hx.
Proof. apply /set1P. rewrite -other_setD. apply /setD1P. splitb. by apply /eqP. Qed.


(** * Symmetric property on set with 2 elements *)
Definition true_on2 {T : finType} {S : {set T}} (P : rel T) (HS : #|S| = 2) :=
  forall (t : T) (Ht : t \in S), P t (other HS Ht).

(** Proving a symmetric property on one suffices to prove it on all *)
Lemma simpl_sym {T : finType} {S : {set T}} (HS : #|S| = 2) (P : rel T)
  (HP : symmetric P) (t : T) (Ht : t \in S) : P t (other HS Ht) -> true_on2 P HS.
Proof.
  intros H s.
  destruct (eq_comparable t s) as [Heq | Hneq].
  - rewrite -Heq.
    intro Hs.
    by replace Hs with Ht by apply eq_irrelevance.
  - intro Hs.
    by rewrite -(other_eq HS Hs Ht Hneq) HP (other_eq HS Ht Hs (nesym Hneq)).
Qed.

(** Equality with dual is a symmetric property *)
Definition is_dual := fun A B => dual A == B.

Lemma dual_sym : symmetric is_dual.
Proof.
  unfold symmetric, is_dual.
  intros A B.
  apply /eqP; case_if;
  rewrite codual //.
  by apply nesym.
Qed.

Definition is_dual_f {T : Type} (f : T -> formula) :=
  fun (a b : T) => is_dual (f a) (f b).

Lemma dual_sym_f {T : Type} (f : T -> formula) : symmetric (is_dual_f f).
Proof. unfold symmetric, is_dual_f. intros. apply dual_sym. Qed.


(** * Self properties on formula *)
Lemma no_selfdual : forall (A : formula), dual A <> A.
Proof. by move => []. Qed.

Lemma no_selftens_l : forall A B, tens A B <> A.
Proof. intro A; induction A as [ | | ? H A ? | ]; intros ? Hc; inversion Hc. by apply (H A). Qed.

Lemma no_selftens_r : forall A B, tens B A <> A.
Proof. intro A; induction A as [ | | A ? ? H | ]; intros ? Hc; inversion Hc. by apply (H A). Qed.

Lemma no_selfparr_l : forall A B, parr A B <> A.
Proof. intro A; induction A as [ | | | ? H A ? ]; intros ? Hc; inversion Hc. by apply (H A). Qed.

Lemma no_selfparr_r : forall A B, parr B A <> A.
Proof. intro A; induction A as [ | | | A ? ? H ]; intros ? Hc; inversion Hc. by apply (H A). Qed.

Ltac no_selfform := try apply no_selfdual;
                    try apply no_selftens_l;
                    try apply no_selftens_r;
                    try apply no_selfparr_l;
                    try apply no_selfparr_r.


(** * Some specific lemmas about seq *)
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


(** * Image of a set of cardinal 2 *)
Lemma imset_set2 : forall (aT rT : finType) (f : aT -> rT) (x y : aT),
  [set f x | x in [set x; y]] = [set f x; f y].
Proof.
  intros ? ? f x y.
  apply /setP => ?.
  rewrite Imset.imsetE !in_set.
  apply /imageP. case: ifP.
  - move => /orP[/eqP H' | /eqP H'];
    [exists x | exists y]; trivial;
    rewrite !in_set;
    caseb.
  - move => /norP [/eqP H' /eqP H''] [z Hz] Hc;
    revert Hz; rewrite !in_set; move => /orP [/eqP Hz | /eqP Hz];
    by rewrite Hz in Hc.
Qed.


(** * Lemma about pick *)
Lemma pick1 {T : finType} (t : T) : [pick x in [set t]] = Some t.
Proof.
  case: pickP.
  - intros ?.
    rewrite in_set.
    by move => /eqP ->.
  - move => /(_ t).
    by rewrite in_set1 eq_refl.
Qed.


(** * Set with 3 elements for case tens, parr and cut *)
Inductive trilean :=
  | tens_t
  | parr_t
  | cut_t.


(** * Some results on permutations *)
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
  induction sigma as [ | ? ? ? ? H | | ? ? ? ? H ? H']; cbn;
  intros A B l0 f; trivial.
  - destruct l0; trivial; cbn; by rewrite H.
  - by destruct l0 as [ | ? [ | ? ?]].
  - by rewrite H H'.
Qed.

Lemma perm_of_in {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) :
  forall {B : finType} (l : seq B) (b : B), (b \in perm_of sigma l) = (b \in l).
Proof.
  induction sigma as [ | ? ? ? ? H | | ? ? ? ? H ? H']; cbn;
  intros B l0 b; trivial.
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
  induction sigma as [ | ? ? ? ? H | | ? ? ? ? H ? H']; cbn;
  intros B l0; trivial.
  - destruct l0; trivial; cbn; by rewrite perm_of_in H.
  - destruct l0 as [ | ? [ | ? ?]]; trivial; cbn.
    rewrite !in_cons !negb_or !andb_assoc; apply andb_id2r => _.
    rewrite andb_comm andb_assoc; apply andb_id2r => _.
    rewrite andb_comm; apply andb_id2r => _.
    apply /eqP; case_if.
    by apply nesym.
  - by rewrite H' H.
Qed.



(** ** Stratum 0: Multigraphs from the library GraphTheory *)
(** * Notations from the library *)
Open Scope graph_scope.
(* G0 ⊎ G1 = disjoint union
   G ∔ v = add a vertex labelled v
   G ∔ [ x , u , y ] = add an arrow from x to y labelled u *)

(** * Out & In edges of a vertex *)
Definition edges_at_subset (b : bool) {Lv Le : Type} {G : graph Lv Le} (v : G) : {set edge G} :=
  [set e | endpoint b e == v].
Notation edges_out_at_subset := (edges_at_subset false).
Notation edges_in_at_subset := (edges_at_subset true).

Lemma endpoint_in_edges_at_subset (b : bool) {Lv Le : Type} {G : graph Lv Le} (e : edge G) :
  e \in edges_at_subset b (endpoint b e).
Proof. by rewrite in_set. Qed.
Notation source_in_edges_out := (endpoint_in_edges_at_subset false).
Notation target_in_edges_in := (endpoint_in_edges_at_subset true).



(** ** Stratum 1: Multigraphs with a left function *)
(* Multigraph with vertex label = rule and arrow label = formula
   [left] giving for a node its left in-edge (if relevant) *)
Set Primitive Projections.
Record graph_left : Type :=
  Graph_left {
    graph_of :> base_graph;
    left : vertex graph_of -> edge graph_of;
  }.
Unset Primitive Projections.


(** * Derivated functions, useful at the level geometric structure *)
(** Nonsensical values for total functions on vertices but where only some vertices matters *)
Definition bogus {G : graph_left} : G -> edge G := fun v => left v.
Opaque bogus.

(** Function [right] returning another in-edge than left *)
Definition right {G : graph_left} : G -> edge G :=
  fun v => match [pick x in edges_in_at_subset v :\ left v] with
  | Some e => e
  | None => bogus v
  end.

(** Function [ccl] returning an out-edge *)
Definition ccl {G : graph_left} : G -> edge G :=
  fun v => match [pick x in edges_out_at_subset v] with
  | Some e => e
  | None => bogus v
  end.

(** Function [edge_of_concl] returning an in-edge *)
Definition edge_of_concl {G : graph_left} : G -> edge G :=
  fun v => match [pick x in edges_in_at_subset v] with
  | Some e => e
  | None => bogus v
  end.


(* Picking an out or in edge if it exists *)
Definition pick_edge_at {G : graph_left} : G -> edge G :=
  fun (v : G) =>
  match [pick x in edges_out_at_subset v :|: edges_in_at_subset v] with
  | Some e => e
  | None => bogus v
  end.



(** ** Stratum 2: Multigraphs with some more data *)
(* [order] giving an ordering of its conclusion nodes *)
Set Primitive Projections.
Record graph_data : Type :=
  Graph_data {
    graph_left_of :> graph_left;
    order : seq graph_left_of;
  }.
Unset Primitive Projections.


(** Sequent of the graph *)
Definition sequent (G : graph_data) : list formula :=
  [seq elabel (edge_of_concl i) | i <- order G].



(** ** Stratum 3: Geometric Structure *)
(** * Conditions on the neighborhood of a node according to its rule *)
(** Out/In-degree of a node according to its rule *)
Definition deg (b : bool) := match b with
  | false => fun (r : rule) => match r with
    | ax  => 2
    | ⊗   => 1
    | ⅋   => 1
    | cut => 0
    | c   => 0
    end
  | true => fun (r : rule) => match r with
    | ax  => 0
    | ⊗   => 2
    | ⅋   => 2
    | cut => 2
    | c   => 1
    end
  end.
Notation deg_out := (deg false).
Notation deg_in := (deg true).

(** Property of a geometric structure *)
Definition proper_degree (G : graph_data) :=
  forall (b : bool) (v : G), #|edges_at_subset b v| = deg b (vlabel v).

Definition proper_left (G : graph_data) :=
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  left v \in edges_in_at_subset v.

Definition proper_order (G : graph_data) :=
  (forall (v : G), vlabel v = concl_l <-> v \in order G) /\ uniq (order G).

Set Primitive Projections.
Record geos : Type :=
  Geos {
    graph_data_of :> graph_data;
    p_deg : proper_degree graph_data_of;
    p_left : proper_left graph_data_of;
    p_order : proper_order graph_data_of;
  }.
Unset Primitive Projections.
Notation p_deg_out := (p_deg false).
Notation p_deg_in := (p_deg true).


(** * Derivated results on a geometric structure *)
Lemma left_e (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  target (left v) = v.
Proof.
  intros v Hv.
  assert (H := p_left Hv).
  rewrite in_set in H; by apply /eqP.
Qed.

(** Function right for the right premisse of a tens / parr *)
Lemma unique_right (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ -> #|edges_in_at_subset v| = 2.
Proof. intros v [Hl | Hl]; by rewrite p_deg Hl. Qed.

Lemma right_o (G : geos) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  right v = other (unique_right H) (p_left H).
Proof.
  intros v H; unfold right.
  replace (edges_in_at_subset v :\ left v) with
    ([set left v; other (unique_right H) (p_left H)] :\ left v)
    by by rewrite -(other_set (unique_right H) (p_left H)).
  rewrite set2D1 ?pick1 //. by apply other_in_neq.
Qed.

Lemma p_right (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  right v \in edges_in_at_subset v /\ right v != left v.
Proof. intros. rewrite right_o. apply other_in_neq. Qed.

Lemma right_e (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  target (right v) = v.
Proof.
  intros v Hv.
  assert (H := p_right Hv).
  revert H; rewrite in_set; by move => [/eqP H _].
Qed.

Lemma right_set (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  edges_in_at_subset v = [set left v; right v].
Proof. intros. rewrite right_o. apply other_set. Qed.

Lemma right_eq (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  forall (e : edge G), target e = v /\ e <> left v -> e = right v.
Proof.
  intros ? ? ? [? ?].
  rewrite right_o. apply other_eq; try by [].
  rewrite in_set; by subst.
Qed.


(** Function ccl for the conclusion of a tens / parr *)
Lemma unique_ccl (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  #|edges_out_at_subset v| = 1.
Proof. intros v [Hl | Hl]; by rewrite p_deg Hl. Qed.

Lemma ccl_o (G : geos) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  ccl v = pick_unique (unique_ccl H).
Proof.
  intros v H; unfold ccl.
  assert ([pick x in edges_out_at_subset v] = [pick x in [set pick_unique (unique_ccl H)]])
    as -> by by rewrite -(pick_unique_set (unique_ccl H)).
  by rewrite pick1.
Qed.

Lemma p_ccl (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  ccl v \in edges_out_at_subset v.
Proof. intros. rewrite ccl_o. apply pick_unique_in. Qed.

Lemma ccl_e (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  source (ccl v) = v.
Proof.
  intros v Hv.
  assert (H := p_ccl Hv).
  rewrite in_set in H; by apply /eqP.
Qed.

Lemma ccl_set (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  edges_out_at_subset v = [set ccl v].
Proof. intros. rewrite ccl_o. apply pick_unique_set. Qed.

Lemma ccl_eq (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  forall (e : edge G), source e = v -> e = ccl v.
Proof.
  intros v Hv e He.
  assert (H : e \in edges_out_at_subset v) by by rewrite in_set He.
  revert H. rewrite ccl_set // in_set. by move => /eqP H.
Qed.


(** Function returning the unique (input) edge of a conclusion *)
Lemma unique_concl (G : geos) :
  forall (v : G), vlabel v = concl_l ->
  #|edges_in_at_subset v| = 1.
Proof. intros v Hl; by rewrite p_deg Hl. Qed.

Lemma edge_of_concl_o (G : geos) :
  forall (v : G) (H : vlabel v = concl_l),
  edge_of_concl v = pick_unique (unique_concl H).
Proof.
  intros v H; unfold edge_of_concl.
  assert ([pick x in edges_in_at_subset v] = [pick x in [set pick_unique (unique_concl H)]])
    as -> by by rewrite -(pick_unique_set (unique_concl H)).
  by rewrite pick1.
Qed.

Lemma p_concl (G : geos) :
  forall (v : G), vlabel v = concl_l -> edge_of_concl v \in edges_in_at_subset v.
Proof. intros. rewrite edge_of_concl_o. apply pick_unique_in. Qed.

Lemma concl_e (G : geos) :
  forall (v : G), vlabel v = concl_l -> target (edge_of_concl v) = v.
Proof.
  intros v Hv.
  assert (H := p_concl Hv).
  rewrite in_set in H; by apply /eqP.
Qed.

Lemma concl_set (G : geos) :
  forall (v : G), vlabel v = concl_l -> edges_in_at_subset v = [set edge_of_concl v].
Proof. intros. rewrite edge_of_concl_o. apply pick_unique_set. Qed.

Lemma concl_eq (G : geos) :
  forall (v : G), vlabel v = concl_l ->
  forall (e : edge G), target e = v -> e = edge_of_concl v.
Proof.
  intros v Hv e He.
  assert (H : e \in edges_in_at_subset v) by by rewrite in_set He.
  revert H. rewrite concl_set // in_set. by move => /eqP H.
Qed.


(** Other edge of an axiom *)
Lemma pre_proper_ax (G : geos) (v : G) (Hl : vlabel v = ax) :
  #|edges_out_at_subset v| = 2.
Proof. by rewrite p_deg Hl. Qed.

Definition other_ax (G : geos) (e : edge G) (H : vlabel (source e) = ax) : edge G :=
  other (pre_proper_ax H) (source_in_edges_out e).

Lemma other_ax_in_neq (G : geos) (e : edge G) (H : vlabel (source e) = ax) :
  source (other_ax H) = source e /\ other_ax H != e.
Proof.
  unfold other_ax.
  destruct (other_in_neq (pre_proper_ax H) (source_in_edges_out e)) as [Hd0 Hd1].
  by revert Hd0; rewrite in_set; move => /eqP Hd0.
Qed.

Lemma other_ax_set (G : geos) (e : edge G) (H : vlabel (source e) = ax) :
  edges_out_at_subset (source e) = [set e; other_ax H].
Proof. apply other_set. Qed.

Lemma other_ax_eq (G : geos) (e : edge G) (H : vlabel (source e) = ax) :
  forall (a : edge G), source a = source e /\ a <> e -> a = other_ax H.
Proof.
  intros a [Ha Ha'].
  assert (Hin : a \in edges_out_at_subset (source e)) by by rewrite in_set Ha.
  revert Hin.
  rewrite other_ax_set !in_set.
  by move => /orP [/eqP H' | /eqP H'].
Qed.


(** Other edge of a cut *)
Lemma pre_proper_cut (G : geos) (v : G) (Hl : vlabel v = cut) :
  #|edges_in_at_subset v| = 2.
Proof. by rewrite p_deg Hl. Qed.

Definition other_cut (G : geos) (e : edge G) (H : vlabel (target e) = cut) : edge G :=
  other (pre_proper_cut H) (target_in_edges_in e).

Lemma other_cut_in_neq (G : geos) (e : edge G) (H : vlabel (target e) = cut) :
  target (other_cut H) = target e /\ other_cut H != e.
Proof.
  unfold other_cut.
  destruct (other_in_neq (pre_proper_cut H) (target_in_edges_in e)) as [Hd0 Hd1].
  by revert Hd0; rewrite in_set; move => /eqP Hd0.
Qed.

Lemma other_cut_set (G : geos) (e : edge G) (H : vlabel (target e) = cut) :
  edges_in_at_subset (target e) = [set e; other_cut H].
Proof. apply other_set. Qed.

Lemma other_cut_eq (G : geos) (e : edge G) (H : vlabel (target e) = cut) :
  forall (a : edge G), target a = target e /\ a <> e -> a = other_cut H.
Proof.
  intros a [Ha Ha'].
  assert (Hin : a \in edges_in_at_subset (target e)) by by rewrite in_set Ha.
  revert Hin.
  rewrite other_cut_set !in_set.
  by move => /orP [/eqP H' | /eqP H'].
Qed.


(** Always an out or in edge *)
Lemma pick_edge_at_some : forall (G : geos), forall (v : G),
  pick_edge_at v \in edges_out_at_subset v :|: edges_in_at_subset v.
Proof.
  intros G v.
  unfold pick_edge_at.
  case: pickP; trivial.
  intro Hc. exfalso.
  assert (#|edges_out_at_subset v| = 0 /\ #|edges_in_at_subset v| = 0) as [Hcout Hcin].
  { enough (#|edges_out_at_subset v| <= 0 /\ #|edges_in_at_subset v| <= 0) by lia.
    assert (Hu : #|edges_out_at_subset v :|: edges_in_at_subset v| = 0) by by apply eq_card0.
    rewrite -!Hu.
    apply cardsUmax. }
  assert (Hfout := p_deg_out v); rewrite Hcout in Hfout;
  assert (Hfin := p_deg_in v); rewrite Hcin in Hfin.
  by destruct (vlabel v).
Qed.



(** ** Stratum 4: Proof Structure *)
(** * The rule of a node gives conditions on the formulae of its arrows *)
Definition proper_ax_cut (G : geos) := (*TODO with prop instead of bool ? *)
  forall (b : bool),
  let rule := if b then cut else ax in
  forall (v : G), vlabel v = rule -> exists el, exists er,
  (el \in edges_at_subset b v) && (er \in edges_at_subset b v) &&
  (elabel el == dual (elabel er)).

Definition proper_tens_parr (G : geos) :=
  forall (b : bool),
  let rule := if b then ⅋ else ⊗ in
  let form := if b then parr else tens in
  forall (v : G), vlabel v = rule ->
  elabel (ccl v) = form (elabel (left v)) (elabel (right v)).

Set Primitive Projections.
Record proof_structure : Type :=
  Proof_structure {
    geos_of :> geos;
    p_ax_cut : proper_ax_cut geos_of;
    p_tens_parr : proper_tens_parr geos_of;
  }.
Unset Primitive Projections.
Definition p_ax (G : proof_structure) := @p_ax_cut G false.
Definition p_cut (G : proof_structure) := @p_ax_cut G true.
Definition p_tens (G : proof_structure) := @p_tens_parr G false.
Definition p_parr (G : proof_structure) := @p_tens_parr G true.

(** * Derivated results on a proof structure *)
Definition proper_ax_bis (G : geos) :=
  forall (v : G) (Hl : vlabel v = ax),
  true_on2 (is_dual_f (elabel (g := G))) (pre_proper_ax Hl).

Definition proper_cut_bis (G : geos) :=
  forall (v : G) (Hl : vlabel v = cut),
  true_on2 (is_dual_f (elabel (g := G))) (pre_proper_cut Hl).

Lemma proper_ax_cut_bis (G : proof_structure) : proper_ax_bis G /\ proper_cut_bis G.
Proof.
  assert (H := p_ax_cut (p := G)).
  unfold proper_ax_bis, proper_cut_bis.
  split; [set b := false | set b := true];
  [set pre_proper := pre_proper_ax | set pre_proper := pre_proper_cut].
  all: intros v Hl.
  all: elim: (H b v Hl) => [el [er /andP[/andP[Hel Her] /eqP Heq]]].
  all: apply (simpl_sym (dual_sym_f (elabel (g := G))) (Ht := Hel)).
  all: assert (Ho : other (pre_proper G v Hl) Hel = er) by
    (symmetry; apply other_eq; trivial; intro Hc; contradict Heq; rewrite Hc; apply nesym, no_selfdual).
  all: by rewrite /is_dual_f /is_dual Ho Heq bidual.
Qed.

Lemma no_selfloop (G : proof_structure) : forall (e : edge G), source e <> target e.
Proof.
  intros e Hf.
  assert (Hin := p_deg_in (source e));
  assert (Hout := p_deg_out (source e)).
  assert (#|edges_in_at_subset (source e)| <> 0 /\ #|edges_out_at_subset (source e)| <> 0) as [? ?].
  { split; intro Hc;
    assert (Hf' : e \in set0) by (by rewrite -(cards0_eq Hc) in_set Hf);
    contradict Hf'; by rewrite in_set. }
  destruct (vlabel (source e)) eqn:Hl; try done;
  [assert (Hd := p_tens Hl) | assert (Hd := p_parr Hl)]; cbn in Hd.
  all: contradict Hd.
  all: assert (e = ccl (source e)) as <- by (apply ccl_eq; caseb).
  all: assert (Hdir : e \in edges_in_at_subset (source e)) by by rewrite in_set Hf.
  all: revert Hdir; rewrite right_set ?in_set; [ | caseb]; move => /orP[/eqP <- | /eqP <-].
  all: apply nesym; no_selfform.
Qed.



(** ** Operations on proof structures, at each strata *)
(** * Empty proof_structure *)
Definition v_graph : base_graph := {|
  vertex := [finType of void];
  edge := [finType of void];
  endpoint := fun _ => vfun;
  vlabel := vfun;
  elabel := vfun;
  |}.

Definition v_graph_left : graph_left := {|
  graph_of := v_graph;
  left := vfun;
  |}.

Definition v_order : seq v_graph := nil.

Definition v_graph_data : graph_data := {|
  graph_left_of := v_graph_left;
  order := v_order;
  |}.

Definition v_geos : geos.
Proof. by exists v_graph_data. Defined.

Definition v_ps : proof_structure.
Proof. by exists v_geos. Defined.



(** * Base case: proof structure of an axiom *)
Definition ax_graph (x : atom) : base_graph := {|
  vertex := [finType of 'I_3];
  edge := [finType of 'I_2];
  endpoint := fun b => match b with
  | true => fun e => match val e with
      | 0 => ord1
      | _ => ord2
  end
  | false => fun _ => ord0
  end;
  vlabel := fun v => match val v with
  | 0 => ax
  | _ => concl_l
  end;
  elabel := fun e => match val e with
  | 0 => covar x
  | _ => var x
  end;
  |}.
(*   c      covar x     ax   var x     c
     O     <--------    O   ------->   O
    ord1      ord0    ord0    ord1    ord2   *)

Definition ax_graph_left (x : atom) : graph_left := {|
  graph_of := ax_graph x;
  left := fun _ => ord0;
  |}.

Definition ax_graph_data (x : atom) : graph_data := {|
  graph_left_of := ax_graph_left x;
  order := ord1 :: ord2 :: nil;
  |}.


Lemma ax_p_deg (x : atom) : proper_degree (ax_graph_data x).
Proof.
  unfold proper_degree.
  intros [] v; destruct_I3 v.
  all: compute_card_subIn.
Qed.

Lemma ax_p_left (x : atom) : proper_left (ax_graph_data x).
Proof. intros v [Hl | Hl]; destruct_I3 v; by contradict Hl. Qed.

Lemma ax_p_order (x : atom) : proper_order (ax_graph_data x).
Proof. split; trivial. by intro v; destruct_I3 v. Qed.

Definition ax_geos (x : atom) : geos := {|
  graph_data_of := ax_graph_data x;
  p_deg := @ax_p_deg _;
  p_left := @ax_p_left _;
  p_order := ax_p_order _;
  |}.


Lemma ax_p_ax_cut (x : atom) : proper_ax_cut (ax_geos x).
Proof.
  unfold proper_ax_cut.
  intros [] v Hl; destruct_I3 v; try (by contradict Hl).
  exists ord0, ord1.
  by rewrite /edges_out_at_subset !in_set !eq_refl.
Qed.

Lemma ax_p_tens_parr (x : atom) : proper_tens_parr (ax_geos x).
Proof. unfold proper_tens_parr. intros [] v Hl; destruct_I3 v; by contradict Hl. Qed.

Definition ax_ps (x : atom) : proof_structure := {|
  geos_of := ax_geos x;
  p_ax_cut := @ax_p_ax_cut _;
  p_tens_parr := @ax_p_tens_parr _;
  |}.


(** Sequent of an axiom *)
Lemma ax_sequent (x : atom) : sequent (ax_geos x) = covar x :: var x :: nil.
Proof.
  unfold sequent.
  replace ([seq elabel (edge_of_concl i) | i <- order (ax_geos x)]) with ([:: elabel
    (edge_of_concl (ord1 : ax_geos x)); elabel (edge_of_concl (ord2 : ax_geos x))]) by by [].
  by assert (edge_of_concl (ord1 : ax_geos x) = ord0 /\ edge_of_concl (ord2 : ax_geos x) = ord1)
    as [-> ->] by (split; symmetry; by apply concl_eq).
Qed.



(** * Permuting the conclusions of a proof structure *)
Definition perm_graph_data (G : graph_data) (l l' : list formula) (sigma : Permutation_Type l l') :
  graph_data := {|
  graph_left_of := G;
  order := perm_of sigma (order G);
  |}.


Lemma perm_p_order (G : geos) (l l' : list formula) (sigma : Permutation_Type l l') :
  proper_order (perm_graph_data G sigma).
Proof.
  unfold proper_order, perm_graph_data; cbn.
  split.
  - intros.
    rewrite perm_of_in.
    apply p_order.
  - rewrite perm_of_uniq.
    apply p_order.
Qed.

Definition perm_geos (G : geos) (l l' : list formula) (sigma : Permutation_Type l l') :
  geos := {|
  graph_data_of := perm_graph_data G sigma;
  p_deg := @p_deg _;
  p_left := @p_left _;
  p_order := perm_p_order _ _;
  |}.

Definition perm_ps (G : proof_structure) (l l' : list formula) (sigma : Permutation_Type l l') :
  proof_structure := {|
  geos_of := perm_geos G sigma;
  p_ax_cut := @p_ax_cut _;
  p_tens_parr := @p_tens_parr _;
  |}.


(** Sequent of a permutation *)
Lemma perm_sequent (G : proof_structure) (l l' : list formula) (sigma : Permutation_Type l l')
  (H : sequent G = l) : sequent (perm_geos G sigma) = l'.
Proof.
  revert sigma; rewrite -H; intro.
  by rewrite /sequent -perm_of_map perm_of_consistent.
Qed.



(** * Disjoint union of proof structures *)
(** G0 ⊎ G1 is the disjoint union of G0 and G1 *)

(** Function left for a disjoint union *)
Definition union_left (G0 G1 : graph_left) : G0 ⊎ G1 -> edge (G0 ⊎ G1) :=
  fun v => match v with
  | inl u => inl (left u)
  | inr u => inr (left u)
  end.

Definition union_graph_left (G0 G1 : graph_left) : graph_left := {|
  graph_of := G0 ⊎ G1;
  left := @union_left _ _;
  |}.

(** Function order for a disjoint union *)
(* Put the two first premises at the beginning, then the tail of order G1, finally the tail of
order G0 *)
Definition union_order (G0 G1 : graph_data) : list (G0 ⊎ G1) :=
  match order G0, order G1 with
  | v0 :: o0, v1 :: o1 => inl v0 :: inr v1 :: map inr o1 ++ map inl o0
  | _, [::] => map inl (order G0)
  | [::], _ => map inr (order G1)
  end.

(** Graph data for a disjoint union *)
Definition union_graph_data (G0 G1 : graph_data) : graph_data := {|
  graph_left_of := union_graph_left G0 G1;
  order := union_order _ _;
  |}.

(** Useful lemmas on a disjoint union *)
Lemma union_edges_at (G0 G1 : graph_left) (i : bool) (b : bool) :
  let Gi (j : bool) := match j with
  | false => G0 | true => G1 end in
  let fv := match i return Gi i -> G0 ⊎ G1 with
  | false => inl | true => inr end in
  let fe := match i return edge (Gi i) -> edge (G0 ⊎ G1) with
  | false => inl | true => inr end in
  forall v : Gi i,
  edges_at_subset b (fv v) =i [set fe e | e in edges_at_subset b v].
Proof.
  intros Gi fv fe v; hnf.
  destruct i; intros [e | e].
  all: assert (injective fe) by (apply inl_inj || apply inr_inj).
  all: rewrite ?inj_imset // !in_set; cbn; trivial.
  all: apply /eqP /memPn; by move => ? /imsetP [? _] ->.
Qed.
Notation union_edges_at_inl := (union_edges_at (i := false)).
Notation union_edges_at_inr := (union_edges_at (i := true)).

Lemma union_order_in (G0 G1 : graph_data) (i : bool) :
  let Gi (j : bool) := match j with
  | false => G0 | true => G1 end in
  let fv := match i return Gi i -> G0 ⊎ G1 with
  | false => inl | true => inr end in
  forall v, (fv v \in order (union_graph_data G0 G1)) = (v \in order (Gi i)).
Proof.
  intros Gi fv v.
  destruct i; cbn; unfold union_order;
  induction (order G0) as [ | v0 o0 H0];
  induction (order G1) as [ | v1 o1 H1]; cbn; trivial.
  all: assert (injective fv) by (apply inl_inj || apply inr_inj).
  all: rewrite !in_cons ?mem_cat ?mem_map //; cbn.
  1: by destruct o0.
  2: by destruct o1.
  1: set vt := v1; set ot := o0; set fvn := inl.
  2: set vt := v0; set ot := o1; set fvn := inr.
  all: destruct (eq_comparable v vt) as [-> | Hneq]; [by rewrite eq_refl | ].
  all: revert Hneq; move => /eqP /negPf ->.
  all: assert (Hf : (fv v \in [seq fvn i | i <- ot]) = false) by (clear; by induction ot).
  all: by rewrite Hf ?orb_false_r.
Qed.
Notation union_order_inl := (union_order_in (i := false)).
Notation union_order_inr := (union_order_in (i := true)).


Lemma union_p_deg (G0 G1 : geos) : proper_degree (union_graph_data G0 G1).
Proof.
  unfold proper_degree.
  intros b [v | v]; cbn;
  [set fe := inl : edge G0 -> edge (G0 ⊎ G1) | set fe := inr : edge G1 -> edge (G0 ⊎ G1)].
  all: rewrite -(p_deg b v) -(card_imset (f := fe)); [ | apply inl_inj || apply inr_inj].
  all: apply eq_card.
  - apply union_edges_at_inl.
  - apply union_edges_at_inr.
Qed.

Lemma union_p_left (G0 G1 : geos) : proper_left (union_graph_data G0 G1).
Proof.
  unfold proper_left.
  intros [v | v] Hv;
  [set fe := inl : edge G0 -> edge (G0 ⊎ G1) | set fe := inr : edge G1 -> edge (G0 ⊎ G1)];
  [rewrite union_edges_at_inl | rewrite union_edges_at_inr].
  all: rewrite (inj_imset (f:= fe)); [ | apply inl_inj || apply inr_inj].
  all: by apply p_left.
Qed.

Lemma union_p_order (G0 G1 : geos) : proper_order (union_graph_data G0 G1).
Proof.
  unfold proper_order.
  assert (injective (inl : G0 -> G0 + G1) /\ injective (inr : G1 -> G0 + G1)) as [? ?] by by [].
  split.
  - destruct (p_order G0) as [? _];
    destruct (p_order G1) as [? _].
    intros [v | v];
    [rewrite union_order_inl | rewrite union_order_inr];
    by revert v.
  - destruct (p_order G0) as [_ U0];
    destruct (p_order G1) as [_ U1]; cbn.
    unfold union_order.
    destruct (order G0) as [ | v0 o0];
    destruct (order G1) as [ | v1 o1];
    rewrite ?map_inj_uniq //.
    revert U0 U1.
    rewrite 4!cons_uniq.
    move => /andP[VO0 U0] /andP[VO1 U1].
    rewrite cat_uniq in_cons !mem_cat !negb_or !map_inj_uniq ?mem_map //; cbn.
    splitb; clear.
    + by induction o1.
    + by induction o0.
    + induction o0; trivial.
      rewrite negb_or.
      splitb.
      by clear; induction o1.
Qed.

Definition union_geos (G0 G1 : geos) : geos := {|
  graph_data_of := union_graph_data G0 G1;
  p_deg := @union_p_deg _ _;
  p_left := @union_p_left _ _;
  p_order := union_p_order _ _;
  |}.

(** Useful lemmas on union_geos *)
Lemma union_right (G0 G1 : geos) :
  forall (v : union_geos G0 G1), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  right v = match v with
  | inl u => inl (right u)
  | inr u => inr (right u)
  end.
Proof.
  intros [v | v] Hv.
  all: symmetry; apply right_eq; trivial; cbn.
  all: rewrite right_e //; splitb; apply /eqP; cbn.
  all: by apply p_right.
Qed.

Lemma union_ccl (G0 G1 : geos) :
  forall (v : union_geos G0 G1), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  ccl v = match v with
  | inl u => inl (ccl u)
  | inr u => inr (ccl u)
  end.
Proof.
  intros [v | v] Hv.
  all: symmetry; apply ccl_eq; trivial; cbn.
  all: by rewrite ccl_e.
Qed.

Lemma union_edge_of_concl (G0 G1 : geos) :
  forall (v : union_geos G0 G1), vlabel v = c ->
  edge_of_concl v = match v with
  | inl u => inl (edge_of_concl u)
  | inr u => inr (edge_of_concl u)
  end.
Proof.
  intros [v | v] Hv.
  all: symmetry; apply concl_eq; trivial; cbn.
  all: by rewrite concl_e.
Qed.


Lemma union_p_ax_cut (G0 G1 : proof_structure) : proper_ax_cut (union_geos G0 G1).
Proof.
  unfold proper_ax_cut.
  intros b [v | v] Hl; cbn in *.
  all: destruct (p_ax_cut Hl) as [el [er He]].
  - exists (inl el), (inl er); by rewrite !union_edges_at_inl !inj_imset /=.
  - exists (inr el), (inr er); by rewrite !union_edges_at_inr !inj_imset /=.
Qed.

Lemma union_p_tens_parr (G0 G1 : proof_structure) : proper_tens_parr (union_geos G0 G1).
Proof.
  unfold proper_tens_parr.
  intros b [v | v] Hl;
  rewrite union_right ?union_ccl;
  try by apply p_tens_parr.
  all: destruct b; caseb.
Qed.

Definition union_ps (G0 G1 : proof_structure) : proof_structure := {|
  geos_of := union_geos G0 G1;
  p_ax_cut := @union_p_ax_cut _ _;
  p_tens_parr := @union_p_tens_parr _ _;
  |}.


(** Sequent of a union *)
Lemma union_sequent (G0 G1 : geos) : sequent (union_geos G0 G1) =
  match sequent G0, sequent G1 with
  | f0 :: s0, f1 :: s1 => f0 :: f1 :: s1 ++ s0
  | _, [::] => sequent G0
  | [::], _ => sequent G1
  end.
Proof.
  cbn; unfold union_order, sequent.
  destruct (order G0) as [ | v0 o0] eqn:H0;
  destruct (order G1) as [ | v1 o1] eqn:H1;
  trivial; cbn;
  try assert (vlabel v0 = c) by (apply p_order; rewrite H0 !in_cons; caseb);
  try assert (vlabel v1 = c) by (apply p_order; rewrite H1 !in_cons; caseb).
  all: rewrite !union_edge_of_concl //.
  all: apply /eqP; cbn; splitb; apply /eqP; trivial.
  all: rewrite ?map_cat -!map_comp /comp.
  3: f_equal.
  all: apply eq_in_map => e He.
  all: rewrite union_edge_of_concl //.
  all: apply p_order; cbn; rewrite /union_order ?H0 ?H1 !in_cons ?mem_cat.
  all: rewrite map_f; caseb.
Qed.



(** * Adding a tens/parr/cut node to a proof structure, replacing 2 conclusions *)
(* Add a tens/parr/cut node, without removing conclusions *)
Definition add_node_graph_1 (t : trilean) {G : base_graph} (e0 e1 : edge G) :=
  (* subgraph to add *)
  let graph_node (t' : trilean) := match t' with
  | tens_t => edge_graph (⊗) (tens (elabel e0) (elabel e1)) concl_l
  | parr_t => edge_graph (⅋) (parr (elabel e0) (elabel e1)) concl_l
  | cut_t => unit_graph cut
  end in
  let G1 (t' : trilean) := G ⊎ graph_node t' in
  (* node of the graph receving edges *)
  let target_node := match t return G1 t with
  | tens_t => inr (inl tt)
  | parr_t => inr (inl tt)
  | cut_t => inr tt
  end in
  (* duplicate edges *)
  G1 t ∔ [ inl (source e0) , elabel e0 , target_node ]
       ∔ [ inl (source e1) , elabel e1 , target_node ].

(* Remove the conclusions *)
Definition add_node_graph (t : trilean) {G : base_graph} (e0 e1 : edge G) :=
  induced ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)).

(** Function left for the graph with a new node *)
(* Function left for the intermediary graph *)
Definition add_node_left_1 (t : trilean) {G : graph_left} (e0 e1 : edge G) :=
  let G' := add_node_graph_1 t e0 e1 in
  fun (v : G') => match v return edge G' with
  | inl u => if (target (left u) == target e0) || (target (left u) == target e1) then Some None
             else Some (Some (inl (left u)))
(* artefact for when the value of left is nonsensical: if we remove left v, give it a new value *)
  | inr _ => Some None
  end.
(* TODO mettre grosse cond add_node_hyp en if : si oui comme là, sinon ne fait rien
-> voir si pas trop d'ennui de type dépendant *)
(* TODO opacifier les intermediaires apres avoir prouvé les lemmes utiles dessus 
+ faire ça aussi dans les autres def similaires *)

(* Graph before we remove the previous conclusions, useful when considering isomorphisms *)
Definition add_node_graph_left_1 (t : trilean) {G : graph_left} (e0 e1 : edge G) :
  graph_left := {|
  graph_of := add_node_graph_1 t e0 e1;
  left := @add_node_left_1 _ _ _ _;
  |}.

(* Necessary hypothesis : the nodes we remove have no input edges *)
Lemma add_node_consistent_left (t : trilean) {G : graph_left} (e0 e1 : edge G) :
  let S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1) in
  (forall e, source e != target e0) /\ (forall e, source e != target e1) ->
  forall v, add_node_left_1 v \in edge_set S.
Proof.
  destruct t; cbn;
  intros [? ?] [v | v];
  rewrite !in_set; cbn.
  all: splitb; case_if; by apply/eqP.
Qed.

(* Function left for the graph with a new node *)
Definition add_node_left (t : trilean) {G : graph_left} (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  add_node_graph t e0 e1 -> edge (add_node_graph t e0 e1) :=
  fun v => Sub (add_node_left_1 (val v)) (add_node_consistent_left H (val v)).

Definition add_node_graph_left (t : trilean) {G : graph_left} (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  graph_left := {|
  graph_of := add_node_graph t e0 e1;
  left := add_node_left H;
  |}.

(** Function order for the graph with a new node *)
(* Remove the 2 nodes from order *)
Definition add_node_order_1 {G : graph_data} (e0 e1 : edge G) :=
  [seq x <- order G | (x != target e0) && (x != target e1)].

(* Give order the type of the intermediary graph *)
Definition add_node_type_order (t : trilean) {G : graph_data} (e0 e1 : edge G) (l : list G) :
  list (add_node_graph_1 t e0 e1) := [seq (inl v) | v <- l].

(* Add the new conclusion if it exists *)
Definition add_node_order_2 (t : trilean) {G : graph_data} (e0 e1 : edge G) :=
  match t return list (add_node_graph_1 t e0 e1) with
  | tens_t | parr_t => [:: inr (inr tt)] | cut_t => nil end
  ++  add_node_type_order t e0 e1 (add_node_order_1 e0 e1).

Lemma add_node_consistent_order (t : trilean) {G : graph_data} (e0 e1 : edge G) :
  let S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1) in
  all (pred_of_set S) (add_node_order_2 t e0 e1).
Proof.
  apply /allP.
  intros x Hx.
  assert (inl (target e0) \notin (add_node_order_2 t e0 e1) /\
          inl (target e1) \notin (add_node_order_2 t e0 e1)) as [? ?].
  { rewrite -2!has_pred1 /add_node_order_2 /add_node_type_order /add_node_order_1.
    destruct t; cbn;
    rewrite 2!has_map /preim 2!has_pred1 2!mem_filter.
    all: by split; apply /negP; move => /andP[/andP[/eqP H0 /eqP H1] _]. }
  repeat (apply /setD1P; split); trivial;
  by apply (in_notin (l := add_node_order_2 t e0 e1)).
Qed.

Definition add_node_order (t : trilean) {G : graph_data} (e0 e1 : edge G) :
  list (vertex (add_node_graph t e0 e1)) :=
  sval (all_sigP (add_node_consistent_order t e0 e1)).

(** Graph data for adding a node *)
Definition add_node_graph_data (t : trilean) {G : graph_data} (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  graph_data := {|
  graph_left_of := add_node_graph_left t H;
  order := add_node_order _ _ _;
  |}.


(** Helpers for add_node *)
Lemma add_node_hyp (G : geos) (v0 v1 : G) (l : seq G) (H : order G = v0 :: v1 :: l) :
  (forall e : edge G, source e != target (edge_of_concl v0)) /\
  (forall e : edge G, source e != target (edge_of_concl v1)).
Proof.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  rewrite !concl_e //.
  split; [set v := v0; set Hv := Hv0 | set v := v1; set Hv := Hv1];
  intro e.
  all: apply /negP; intro; apply notF.
  all: assert (Hout : edges_out_at_subset v = set0)
    by (apply cards0_eq; by rewrite (p_deg_out v) Hv).
  all: by rewrite -(in_set0 e) -Hout in_set.
Qed.

Lemma add_node_new_edges_in (t : trilean) (G : graph_data) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  let S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1) in
  None \in edge_set S /\ Some None \in edge_set S.
Proof. intros. rewrite !in_set. splitb; try apply H; by destruct t. Qed.

Definition add_node_transport_1 (t : trilean) (G : graph_data) (e0 e1 : edge G) :
  edge G -> edge (add_node_graph_1 t e0 e1) :=
  fun e => if e == e1 then None
           else if e == e0 then Some None
           else Some (Some (inl e)).

Lemma add_node_transport_1_inj (t : trilean) (G : graph_data) (e0 e1 : edge G) :
  injective (add_node_transport_1 t e0 e1).
Proof.
  intros e e'.
  unfold add_node_transport_1; case_if.
  assert (H : Some (Some (inl e)) == (Some (Some (inl e')) : edge (add_node_graph_1 t e0 e1)))
    by by apply /eqP.
  by cbn in H; apply /eqP.
Qed.

Lemma add_node_transport_1_edges (t : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  forall (v : G), v != v0 /\ v != v1 ->
  edges_in_at_subset (inl v : add_node_graph_1 t (edge_of_concl v0) (edge_of_concl v1)) =
  [set add_node_transport_1 t (edge_of_concl v0) (edge_of_concl v1) e | e in edges_in_at_subset v].
Proof.
  set e0 := edge_of_concl v0;
  set e1 := edge_of_concl v1.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [? ?]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  intros v [? ?]; apply /setP; intro e.
  rewrite Imset.imsetE !in_set /add_node_transport_1.
  destruct e as [[[e | e] | ] | ]; cbn.
  - destruct (eq_comparable (target e) v) as [Heq | Hneq].
    + rewrite Heq eq_refl.
      symmetry; apply /imageP.
      exists e.
      * by rewrite in_set Heq.
      * case_if;
        contradict Heq;
        subst; rewrite concl_e //;
        apply nesym; by apply /eqP.
    + revert Hneq; move => /eqP Hneq.
      revert Hneq; move => /negPf Hneq; rewrite Hneq.
      symmetry; apply /negPf.
      apply /imageP; intros [x Hx Hxx].
      contradict Hxx.
      case_if.
      apply /eqP; cbn; apply /eqP.
      intro Hc. contradict Hx.
      by rewrite -Hc in_set Hneq.
  - symmetry; apply /negPf.
    apply /imageP; intros [x Hx Hxx].
    contradict Hxx.
    case_if.
  - destruct t; cbn.
    all: symmetry; apply /negPf.
    all: apply /imageP; intros [x Hx Hxx].
    all: contradict Hxx.
    all: case_if.
    all: contradict Hx; apply /negP.
    all: subst; rewrite in_set concl_e //.
    all: apply /eqP; apply nesym; by apply /eqP.
  - destruct t; cbn.
    all: symmetry; apply /negPf.
    all: apply /imageP; intros [x Hx Hxx].
    all: contradict Hxx.
    all: case_if.
    all: contradict Hx; apply /negP.
    all: subst; rewrite in_set concl_e //.
    all: apply /eqP; apply nesym; by apply /eqP.
Qed.

Lemma add_node_transport_1_label (t : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) : forall e,
  elabel (add_node_transport_1 t (edge_of_concl v0) (edge_of_concl v1) e) = elabel e.
Proof. intro; unfold add_node_transport_1; case_if. Qed.

Lemma add_node_transport_consistent (t : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  forall e, add_node_transport_1 t (edge_of_concl v0) (edge_of_concl v1) e \in
  edge_set ([set: add_node_graph_1 t (edge_of_concl v0) (edge_of_concl v1)] :\
    inl (target (edge_of_concl v0)) :\ inl (target (edge_of_concl v1))).
Proof.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [? ?]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  set e0 := edge_of_concl v0;
  set e1 := edge_of_concl v1;
  set S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1).
  destruct (add_node_new_edges_in t (add_node_hyp H)).
  intro e.
  unfold add_node_transport_1; case_if.
  rewrite !in_set.
  splitb.
  1,2: apply (add_node_hyp H).
  all: rewrite concl_e //; cbn.
  all: apply /negP; move => /eqP ?.
  1: set et := e1. 2: set et := e0.
  all: assert (Hc : e = et) by by apply concl_eq.
  all: by contradict Hc.
Qed.

Definition add_node_transport (t : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  edge G -> edge (add_node_graph_data t (add_node_hyp H)) :=
  fun e => Sub (add_node_transport_1 t (edge_of_concl v0) (edge_of_concl v1) e)
    (add_node_transport_consistent t H e).

Lemma add_node_transport_inj (t : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  injective (add_node_transport t H).
Proof. intros ? ? Heq. apply (add_node_transport_1_inj (EqdepFacts.eq_sig_fst Heq)). Qed.

Lemma add_node_transport_edges (t : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  forall (v : G) (Hv : inl v \in [set: add_node_graph_1 t (edge_of_concl v0) (edge_of_concl v1)] :\
    inl (target (edge_of_concl v0)) :\ inl (target (edge_of_concl v1))) (b : bool),
  edges_at_subset b (Sub (inl v) Hv : add_node_graph_data t _)
  = [set add_node_transport t H e | e in edges_at_subset b v].
Proof.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [? ?]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  assert (Hneqv : v0 <> v1).
  { elim (p_order G).
    rewrite H cons_uniq in_cons negb_or.
    by move => _ /andP[/andP[/eqP ? _] _]. }
  assert (Hneqe : e0 <> e1).
  { intro Heq. contradict Hneqv.
    rewrite -(concl_e (v := v0)) // -(concl_e (v := v1)) //.
    by f_equal. }
  intros v Hv b; apply /setP; intro e.
  assert ((target e0 == v) = false /\ (target e1 == v) = false) as [? ?].
    { split; apply /eqP; intro Hc.
      all: contradict Hv.
      all: rewrite -Hc !in_set eq_refl.
      all: by move => /andP[? /andP[? _]]. }
  set w := Sub (inl v) Hv : add_node_graph_data t (add_node_hyp H).
  set g := add_node_transport t H.
  set g_1 := add_node_transport_1 t e0 e1.
  set g_inj := add_node_transport_inj (t := t) (H := H).
  destruct e as [[[[e | e] | ] | ] He];
  rewrite in_set; cbn; rewrite !SubK; cbn.
  - assert (Heq : Sub (Some (Some (inl e))) He = g e).
    { apply /eqP; rewrite /g /add_node_transport sub_val_eq SubK /add_node_transport_1.
      case_if.
      all: contradict He.
      all: subst; rewrite !in_set eq_refl.
      all: by move => /andP[_ /andP[? /andP[? _]]]. }
    by rewrite Heq inj_imset // in_set.
  - symmetry; apply /negbTE.
    rewrite Imset.imsetE in_set.
    apply /imageP; move => [a _ A].
    assert (Hc : Some (Some (inr e)) = g_1 a) by apply (EqdepFacts.eq_sig_fst A).
    contradict Hc.
    unfold g_1, add_node_transport_1; case_if.
  - assert (Heq : Sub (Some None) He = g e0).
    { apply /eqP; rewrite /g /add_node_transport /eqP sub_val_eq SubK /add_node_transport_1.
      case_if. }
    rewrite Heq inj_imset // in_set.
    by destruct b, t.
  - assert (Heq : Sub None He = g e1).
    { apply /eqP; rewrite /g /add_node_transport sub_val_eq SubK /add_node_transport_1.
      case_if. by contradict Hneqe. }
    rewrite Heq inj_imset // in_set.
    by destruct b, t.
Qed.

Lemma add_node_transport_label (t : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) : forall e,
  elabel (add_node_transport t H e) = elabel e.
Proof. apply (add_node_transport_1_label _ H). Qed.

Lemma add_node_transport_sequent (t : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  [seq elabel (edge_of_concl i) | i <- order (add_node_graph_data t (add_node_hyp H))] =
  [seq elabel (match [pick x in edges_in_at_subset i] with
  | Some e => e | None => add_node_left_1 i end) | i <-
  [seq val i | i <- order (add_node_graph_data t (add_node_hyp H))]].
Proof.
  set e0 := edge_of_concl v0;
  set e1 := edge_of_concl v1.
  rewrite /add_node_graph_data /add_node_order /add_node_type_order /add_node_order_1 /edge_of_concl.
  set l0 := sval (all_sigP (add_node_consistent_order t e0 e1)).
  assert (Hlv : forall v, v \in l0 -> vlabel (val v) = concl_l).
  { intros [[v | v] Hv] Hl;
    revert Hl;
    rewrite in_seq_sig -(proj2_sig (all_sigP _)) /add_node_order_2; cbn.
    - destruct t.
      all: rewrite ?in_cons /add_node_type_order /add_node_order_1 mem_map ?mem_filter;
        [ | apply inl_inj]; cbn.
      all: move => /andP[_ ?].
      all: by apply p_order.
    - destruct t;
      [destruct v as [[] | []] |destruct v as [[] | []] | destruct v as []].
      all: rewrite ?in_cons /add_node_type_order // /add_node_order_1; cbn.
      all: intro Hc; contradict Hc; apply /negP.
      all: apply inr_seq_inl_filter. }
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [? ?]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  induction l0 as [ | [v Hv] l0 IH]; trivial.
  rewrite !map_cons IH; clear IH.
  2:{ intros u Hu. apply Hlv. rewrite in_cons Hu. caseb. }
  f_equal.
  assert (Hl : vlabel v = concl_l).
  { specialize (Hlv (Sub v Hv)).
    rewrite in_seq_sig SubK in_cons eq_refl in Hlv; cbn in Hlv.
    by rewrite -Hlv. }
  assert (v != inl v0 /\ v != inl v1) as [? ?].
  { assert (Hv' : v \in (setT :\ inl (target e0) :\ inl (target e1))) by apply Hv.
    rewrite !in_set !concl_e // in Hv'.
    revert Hv'; by move => /andP[? /andP[? _]]. }
  destruct v as [v | v].
  - by rewrite (add_node_transport_edges H) SubK (add_node_transport_1_edges _ H) //
        concl_set // !imset_set1 !pick1.
  - destruct t; [set t := tens_t | set t := parr_t | set t := cut_t];
    [destruct v as [[] | []] | destruct v as [[] | []] | destruct v as []];
    try by contradict Hl.
    all: assert (Hout_1 : edges_in_at_subset (inr (inr tt) : add_node_graph_1 t e0 e1)
      = [set Some (Some (inr None))])
      by (apply /setP; intro e; rewrite !in_set; by destruct e as [[[e | [[[] | []] | ]] | ] | ]).
    all: assert (Hss: Some (Some (inr None)) \in edge_set ([set: add_node_graph_1 t e0 e1]
      :\ inl (target e0) :\ inl (target e1))) by (rewrite !in_set; splitb; apply (add_node_hyp H)).
    all: set ss := Sub (Some (Some (inr None))) Hss : edge (add_node_graph_data t (add_node_hyp H)).
    all: assert (Hout : edges_in_at_subset (Sub (inr (inr tt)) Hv : add_node_graph_data t
      (add_node_hyp H)) = [set ss]) by
      (apply /setP; intro e; rewrite !in_set; by destruct e as [[[[e | [[[] | []] | ]] | ] | ] ?]).
    all: by rewrite !SubK Hout_1 Hout !pick1.
Qed.

(* We add the node if it respect the rules, otherwise we return the empty graph as an error *)
Definition add_node_graph_data_bis : trilean -> geos -> graph_data :=
  fun (t : trilean) (G : geos) =>
  match order G as o return order G = o -> graph_data with
  | v0 :: v1 :: _ => match t with
    | cut_t => if (elabel (edge_of_concl v0) == dual (elabel (edge_of_concl v1)))
      then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun _ => v_geos
    | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
    end
  | _ => fun _ => v_geos
  end Logic.eq_refl.


Lemma add_node_p_deg (t : trilean) (G : geos) : proper_degree (add_node_graph_data_bis t G).
Proof.
  unfold add_node_graph_data_bis.
  generalize (erefl (order G));
  destruct (order G) as [ | v0 [ | v1 l]] at 2 3;
  intro H; try (apply p_deg).
  revert t.
  enough (forall (t : trilean), proper_degree (add_node_graph_data t (add_node_hyp H))).
  { intros []; trivial. case_if. }
  intro t.
  unfold proper_degree.
  intros b [[v | v] Hv]; cbn.
  - by rewrite (add_node_transport_edges H) -(p_deg b v)
      -(card_imset (edges_at_subset b v) (add_node_transport_inj (t := t) (H := H))).
  - set e0 := edge_of_concl v0;
    set e1 := edge_of_concl v1;
    set S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1).
    destruct (add_node_new_edges_in t (add_node_hyp H)) as [Hn Hsn].
    set n := Sub None Hn : edge (add_node_graph_data t (add_node_hyp H));
    set sn := Sub (Some None) Hsn : edge (add_node_graph_data t (add_node_hyp H)).
    destruct t;
    [set t := tens_t | set t := parr_t | set t := cut_t].
    1,2: assert (Some (Some (inr None)) \in edge_set S /\ inr (inl tt) \in S /\ inr (inr tt) \in S)
          as [Hss [Htn Hcn]] by (rewrite !in_set; splitb).
    1,2: set ss := Sub (Some (Some (inr None))) Hss : edge (add_node_graph_data t (add_node_hyp H));
         set tn := Sub (inr (inl tt)) Htn : add_node_graph_data t (add_node_hyp H);
         set cn := Sub (inr (inr tt)) Hcn : add_node_graph_data t (add_node_hyp H).
    1,2: assert (edges_in_at_subset tn = [set n; sn] /\ edges_out_at_subset tn = [set ss] /\
                 edges_in_at_subset cn = [set ss] /\ edges_out_at_subset cn = set0)
          as [Htn_in [Htn_out [Hcn_in Hcn_out]]]
          by (splitb; apply /setP; intro e; rewrite !in_set;
            by destruct e as [[[[e | [[[] | []] | ]] | ] | ] ?]).
    3: assert (Htn : inr tt \in S) by (rewrite !in_set; apply /andP; by split).
    3: set tn := (Sub (inr tt) Htn : add_node_graph_data t (add_node_hyp H)).
    3: assert (edges_in_at_subset tn = [set n; sn] /\ edges_out_at_subset tn = set0)
        as [Htn_in Htn_out]
        by (split; apply /setP; intro e; rewrite !in_set; by destruct e as [[[[e | []] | ] | ] ?]).
    3: destruct v as [];
      replace Hv with Htn by apply eq_irrelevance.
    1,2: destruct v as [[] | []];
      [replace Hv with Htn by apply eq_irrelevance | replace Hv with Hcn by apply eq_irrelevance].
    all: destruct b; cbn.
    all: by rewrite ?Htn_in ?Htn_out ?Hcn_in ?Hcn_out ?cards2 ?cards1 ?cards0.
Qed.

Lemma add_node_p_left (t : trilean) (G : geos) : proper_left (add_node_graph_data_bis t G).
Proof.
  unfold add_node_graph_data_bis.
  generalize (erefl (order G));
  destruct (order G) as [ | v0 [ | v1 l]] at 2 3;
  intro H; try (apply p_left).
  revert t.
  enough (forall (t : trilean), proper_left (add_node_graph_data t (add_node_hyp H))).
  { intros []; trivial. case_if. }
  intro t.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  unfold proper_left.
  destruct (add_node_hyp H).
  intros [[v | v] Hv]; cbn;
  intro Hl; unfold add_node_left.
  - rewrite in_set; cbn.
    rewrite !SubK !concl_e // left_e //.
    case_if; apply /eqP; rewrite ?left_e //;
    destruct Hl as [Hl | Hl];
    contradict Hl; subst; by rewrite ?Hv0 ?Hv1.
  - destruct t;
    [destruct v as [[] | []] | destruct v as [[] | []] | destruct v as []].
    all: try (destruct Hl as [Hl | Hl]; by contradict Hl).
    all: by rewrite in_set !SubK.
Qed.

Lemma add_node_p_order (t : trilean) (G : geos) : proper_order (add_node_graph_data_bis t G).
Proof.
  unfold add_node_graph_data_bis.
  generalize (erefl (order G));
  destruct (order G) as [ | v0 [ | v1 l]] at 2 3;
  intro H; try (apply p_order).
  revert t.
  enough (forall (t : trilean), proper_order (add_node_graph_data t (add_node_hyp H))).
  { intros []; trivial. case_if. }
  intro t.
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  unfold proper_order, add_node_order.
  destruct (p_order G) as [Hv U].
  split; cbn.
  - intros [[v | v] Hin]; cbn;
    rewrite in_seq_sig SubK -(proj2_sig (all_sigP _)) /add_node_order_2.
    + apply (iff_stepl (A := v \in order G)); [ | by apply iff_sym].
      assert (v != target e0 /\ v != target e1) as [Hv0 Hv1].
      { split;
        apply /negP; move => /eqP Hc;
        contradict Hin; apply /negP;
        rewrite Hc !in_set;
        caseb. }
      destruct t;
      rewrite ?in_cons /add_node_type_order/ add_node_order_1 mem_map //; cbn; trivial.
      all: by rewrite mem_filter Hv0 Hv1.
    + destruct t;
      [destruct v as [[] | []] | destruct v as [[] | []] | destruct v as []].
      all: cbn; split; trivial; intro Hl; contradict Hl.
      all: rewrite // ?in_cons /add_node_order_2 /add_node_type_order /add_node_order_1;
           cbn; apply /negP.
      all: apply inr_seq_inl_filter.
  - rewrite uniq_seq_sig -(proj2_sig (all_sigP _)) /add_node_order_2.
    destruct t;
    rewrite ?cons_uniq /add_node_type_order /add_node_order_1.
    1,2: apply /andP; split; [apply (inr_seq_inl_filter (order G) _ (inr tt)) | ].
    all: rewrite map_inj_uniq //; cbn; trivial; by apply filter_uniq.
Qed.

Definition add_node_geos (t : trilean) (G : geos) : geos := {|
  graph_data_of := add_node_graph_data_bis t G;
  p_deg := @add_node_p_deg _ _;
  p_left := @add_node_p_left _ _;
  p_order := @add_node_p_order _ _;
  |}.


Lemma add_node_p_ax_cut (t : trilean) (G : proof_structure) : proper_ax_cut (add_node_geos t G).
Proof.
  remember (order G) as l eqn:H; symmetry in H.
  unfold add_node_geos, add_node_graph_data_bis, proper_ax_cut; cbn.
  enough (Hdone : forall (b : bool) (v : match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match t with
      | cut_t => if (elabel (edge_of_concl v0)) == (elabel (edge_of_concl v1)^)
        then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> v_graph_data
      | _ => fun Heq  => add_node_graph_data t (add_node_hyp Heq)
      end
    | _ => fun=> v_graph_data
    end H), vlabel v = (if b then cut else ax) ->
    exists (el er : edge (match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match t with
      | cut_t => if (elabel (edge_of_concl v0)) == (elabel (edge_of_concl v1)^)
        then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> v_graph_data
      | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
      end
    | _ => fun=> v_graph_data
    end H)), (el \in edges_at_subset b v) && (er \in edges_at_subset b v) &&
    (elabel el == dual (elabel er))) by by rewrite <-!H in Hdone.
  destruct l as [ | v0 [ | v1 l]]; try by [].
  enough (Hdone : t <> cut_t \/ elabel (edge_of_concl v0) = dual (elabel (edge_of_concl v1)) ->
    forall b (v : add_node_graph_data t (add_node_hyp H)),
    vlabel v = (if b then cut else ax) ->
    exists el er : edge (add_node_graph_data t (add_node_hyp H)),
    (el \in edges_at_subset b v) && (er \in edges_at_subset b v) && (elabel el == elabel er^)).
  { case_if; destruct t; by [] || (apply Hdone; caseb). }
  intros Hor b [[v | v] Hv] Hl; cbn in Hl; cbn.
  - elim (p_ax_cut Hl) => el [er /andP[/andP[Hel Her] /eqP Helr]].
    exists (add_node_transport t H el), (add_node_transport t H er).
    rewrite !(add_node_transport_edges H) !inj_imset ?Hel ?Her;
    [ | apply add_node_transport_inj | apply add_node_transport_inj]; cbn.
    rewrite /add_node_transport !SubK /add_node_transport_1.
    case_if; apply /eqP; by subst.
  - destruct b, t, v;
    try (by contradict Hl).
    set e0 := edge_of_concl v0;
    set e1 := edge_of_concl v1;
    set S := [set: add_node_graph_1 cut_t e0 e1] :\ inl (target e0) :\ inl (target e1).
    destruct (add_node_new_edges_in cut_t (add_node_hyp H)) as [Hn Hsn].
    set n := Sub None Hn : edge (add_node_graph_data cut_t (add_node_hyp H));
    set sn := Sub (Some None) Hsn : edge (add_node_graph_data cut_t (add_node_hyp H)).
    exists n, sn.
    assert (elabel e1 == dual (elabel e0))
      by (destruct Hor as [Hc | Heq]; by rewrite // Heq bidual).
    rewrite !in_set; cbn; by rewrite !SubK.
Qed.

Lemma add_node_p_tens_parr (t : trilean) (G : proof_structure) :
  proper_tens_parr (add_node_geos t G).
Proof.
  remember (order G) as l eqn:H; symmetry in H.
  unfold add_node_geos, add_node_graph_data_bis.
  intros b r f; cbn.
  enough (Hdone : forall (v : match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match t with
      | cut_t => if (elabel (edge_of_concl v0)) == (elabel (edge_of_concl v1)^)
        then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> v_graph_data
      | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
      end
    | _ => fun=> v_graph_data
    end H), vlabel v = r -> elabel (ccl v) = f (elabel (left v)) (elabel (right v)))
    by by rewrite <-!H in Hdone.
  destruct l as [ | v0 [ | v1 l]]; try done. revert t.
  enough (Hdone : forall t (v : add_node_graph_data t (add_node_hyp H)),
    vlabel v = r -> 
    elabel (ccl v) = f (elabel (left v)) (elabel (right v))).
  { intros []; try apply Hdone.
    specialize (Hdone cut_t). case_if. }
  intros t [[v | v] Hin] Hv;
  assert (Hor : vlabel v = ⊗ \/ vlabel v = ⅋) by (destruct b; caseb).
  - cbn in Hv; cbn in Hor.
    set w := Sub (inl v) Hin : add_node_graph_data t (add_node_hyp H).
    assert (Hneq := Hin); rewrite !in_set in Hneq; cbn in Hneq;
    revert Hneq; move => /andP[/eqP Hneq1 /andP[/eqP Hneq0 _]].
    assert (target (left v) <> target (edge_of_concl v0) /\ target (left v) <> target (edge_of_concl v1))
      as [? ?] by (by rewrite left_e // concl_e).
    assert (left v <> edge_of_concl v0 /\ left v <> edge_of_concl v1) as [? ?] by
      (split; intro Hc; [contradict Hneq0 | contradict Hneq1]; by rewrite -Hc left_e).
    assert (Hvw : left w = add_node_transport t H (left v)).
    { apply /eqP; rewrite /add_node_transport /add_node_left sub_val_eq SubK
        /add_node_transport_1 /add_node_left_1; apply /eqP.
      case_if. }
    rewrite Hvw add_node_transport_label.
    assert (ccl w \in edges_out_at_subset w /\ right w \in edges_in_at_subset w :\ left w)
      as [Hccl Hright].
    { rewrite /ccl /right !add_node_transport_edges !ccl_set // !right_set // !imset_set1 Hvw.
      replace ([set add_node_transport t H e | e in [set left v; right v]]
        :\ add_node_transport t H (left v)) with [set add_node_transport t H (right v)].
      2:{ rewrite imset_set2 set2D1 // inj_eq; [ | apply add_node_transport_inj].
        by apply p_right. }
      by rewrite !pick1 !in_set. }
    rewrite add_node_transport_edges Imset.imsetE in_set ccl_set // in Hccl.
    revert Hccl; move => /imageP [eccl Heccl_in Heccl_eq].
    revert Heccl_in; rewrite in_set; move => /eqP Heccl_in.
    rewrite Heccl_eq add_node_transport_label Heccl_in.
    rewrite add_node_transport_edges Imset.imsetE !in_set in Hright.
    revert Hright; move => /andP[Heright_neq /imageP [eright Heright_in Heright_eq]].
    rewrite Heright_eq add_node_transport_label.
    replace eright with (right v).
    2:{ revert Heright_in;
      rewrite right_set // !in_set; move => /orP[/eqP Heright_in | /eqP Heright_in //].
      contradict Heright_neq; apply /negP;
      rewrite negb_involutive Heright_eq Heright_in.
      cbn; rewrite !SubK /add_node_left_1 /add_node_transport_1.
      assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [? ?]
        by (split; apply p_order; rewrite H !in_cons; caseb).
      assert (v0 <> v1).
      { elim (p_order G).
        rewrite H cons_uniq in_cons negb_or.
        by move => _ /andP[/andP[/eqP ? _] _]. }
       assert (target (left v) <> target (edge_of_concl v0) /\
        target (left v) <> target (edge_of_concl v1)) as [? ?]
        by rewrite left_e //.
      case_if. }
    by apply p_tens_parr.
  - destruct t;
    [set t := tens_t | set t := parr_t | set t := cut_t];
    [destruct v as [[] | []] | destruct v as [[] | []] | destruct v as []];
    destruct b;
    try (by contradict Hv).
    all: set e0 := edge_of_concl v0;
      set e1 := edge_of_concl v1;
      set S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1).
    all: destruct (add_node_new_edges_in t (add_node_hyp H)) as [Hn Hsn].
    all: assert (Hss : Some (Some (inr None)) \in edge_set S) by
      (rewrite !in_set; splitb; try (apply (add_node_hyp H)); by destruct t).
    all: set n := Sub None Hn : edge (add_node_graph_data t (add_node_hyp H));
      set sn := Sub (Some None) Hsn : edge (add_node_graph_data t (add_node_hyp H));
      set ss := Sub (Some (Some (inr None))) Hss : edge (add_node_graph_data t (add_node_hyp H));
      set tn := Sub (inr (inl tt)) Hin : add_node_graph_data t (add_node_hyp H).
    all: assert (edges_in_at_subset tn = [set n; sn] /\ edges_out_at_subset tn = [set ss])
      as [Htn_in Htn_out] by (split; apply /setP; intro e; rewrite !in_set;
      by destruct e as [[[[e | [[[] | []] | ]] | ] | ] ?]).
    all: assert (Hleft : left tn = sn) by (apply /eqP; by rewrite sub_val_eq !SubK).
    all: assert (ccl tn = ss /\ right tn = n) as [Hccl Hright]
      by by rewrite /ccl /right Htn_in Htn_out set2C set2D1 // !pick1.
    all: by rewrite Hleft Hccl Hright.
Qed.

Definition add_node_ps (t : trilean) (G : proof_structure) : proof_structure := {|
  geos_of := add_node_geos t G;
  p_ax_cut := @add_node_p_ax_cut _ _;
  p_tens_parr := @add_node_p_tens_parr _ _ ;
  |}.


(** Sequent after adding a node *)
Lemma add_node_sequent (t : trilean) (G : geos) :
  let new := match order G with
    | v0 :: v1 :: _ => match t with
      | tens_t => [:: tens (elabel (edge_of_concl v0)) (elabel (edge_of_concl v1))]
      | parr_t => [:: parr (elabel (edge_of_concl v0)) (elabel (edge_of_concl v1))]
      | cut_t => nil
      end
    | _ => nil
    end in
  let old := match order G with
    | v0 :: v1 :: _ => match t with 
      | cut_t => if (elabel (edge_of_concl v0)) == (elabel (edge_of_concl v1)^)
              then behead (behead (sequent G))
              else nil
      | _ => behead (behead (sequent G))
      end
    | _ => nil
    end in
  sequent (add_node_geos t G) = new ++ old.
Proof.
  remember (order G) as l eqn:H; symmetry in H; cbn.
  assert ([seq elabel (edge_of_concl i) | i <- order (add_node_graph_data_bis t G)] =
    [seq elabel (edge_of_concl i) | i <- order (match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match t with
      | cut_t => if elabel (edge_of_concl v0) == elabel (edge_of_concl v1)^
        then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> v_graph_data
      | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
    end
    | _ => fun=> v_graph_data
    end H)]) as -> by by rewrite <-!H.
  destruct l as [ | v0 [ | v1 l]]; trivial.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [? ?]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  assert (match t with
    | cut_t => if elabel (edge_of_concl v0) == elabel (edge_of_concl v1)^
      then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> v_graph_data
    | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
    end H = match t with
    | cut_t => if elabel (edge_of_concl v0) == elabel (edge_of_concl v1)^
      then add_node_graph_data t (add_node_hyp H) else v_graph_data
    | _ => add_node_graph_data t (add_node_hyp H)
    end) as -> by (destruct t; trivial; case_if).
  rewrite /sequent H; cbn.
  enough ([seq elabel (edge_of_concl i) | i <- order (add_node_graph_data t (add_node_hyp H))] =
    match t with
    | tens_t => [:: elabel (edge_of_concl v0) ⊗ elabel (edge_of_concl v1)]
    | parr_t => [:: elabel (edge_of_concl v0) ⅋ elabel (edge_of_concl v1)]
    | cut_t => [::]
    end ++ [seq elabel (edge_of_concl i) | i <- l]).
  { destruct t; trivial. case_if. }
  set e0 := edge_of_concl v0;
  set e1 := edge_of_concl v1.
  assert (v0 != v1).
  { elim (p_order G).
    rewrite H cons_uniq in_cons negb_or.
    by move => _ /andP[/andP[? _] _]. }
  rewrite add_node_transport_sequent -(proj2_sig (all_sigP _)) /add_node_order_2
    /add_node_type_order /add_node_order_1.
  assert (Hr : [seq inl v | v <- order G & (v != target e0) && (v != target e1)]
    = ([seq inl v | v <- l] : seq (add_node_graph_1 t e0 e1))).
  { f_equal.
    rewrite H; cbn; rewrite !concl_e //.
    replace (v0 != v0) with false by (symmetry; by apply /negP /negP);
    replace (v1 != v1) with false by (symmetry; by apply /negP /negP);
    replace (v1 != v0) with true by (symmetry; apply /eqP; apply nesym; by apply /eqP); cbn.
    elim (p_order G).
    rewrite H !cons_uniq !in_cons !negb_or; clear.
    move => _ /andP[/andP[_ ?] /andP[? _]].
    rewrite -{2}(filter_predT l); apply eq_in_filter; intros ? ?.
    by rewrite !(in_notin (l := l)). }
  rewrite Hr map_cat -!map_comp /comp; clear Hr.
  assert (Hr : [seq elabel (match [pick x in edges_in_at_subset i] with
    | Some e => e | None => add_node_left_1 i end) | i <- match t return
    (seq (add_node_graph_1 t e0 e1)) with | cut_t => [::] | _ => [:: inr (inr tt)] end] =
    match t with | tens_t => [:: elabel e0 ⊗ elabel e1]
    | parr_t => [:: elabel e0 ⅋ elabel e1] | cut_t => [::] end).
  { destruct t; [set t := tens_t | set t := parr_t | set t := cut_t]; cbn; trivial.
    all: assert (Hr : edges_in_at_subset (inr (inr tt) : add_node_graph_1 t e0 e1) =
      [set Some (Some (inr None))]) by
      (apply /setP; intro e; rewrite !in_set; by destruct e as [[[e | [[[] | []] | ]] | ] | ]).
    all: by rewrite Hr pick1. }
  rewrite Hr; clear Hr.
  apply f_equal, eq_in_map; intros v Hv.
  assert (vlabel v = concl_l) by (apply p_order; rewrite H !in_cons; caseb).
  assert (v != v0 /\ v != v1) as [? ?].
  { elim (p_order G).
    rewrite H !cons_uniq !in_cons.
    move => _ /andP[/norP[_ Hn0] /andP[Hn1 _]].
    by rewrite !(in_notin (l := l)). }
  rewrite (add_node_transport_1_edges _ H) // concl_set // imset_set1 !pick1.
  apply (add_node_transport_1_label _ H).
Qed.



(** ** Proof Structure of a Proof Sequent *)
Definition add_node_tens (G0 G1 : proof_structure) := add_node_ps tens_t (union_ps G0 G1).
Definition add_node_cut (G0 G1 : proof_structure) := add_node_ps cut_t (union_ps G0 G1).
Definition add_node_parr (G : proof_structure) := add_node_ps parr_t G.

Fixpoint ps {l : list formula} (pi : ll l) : proof_structure := match pi with
  | ax_r x => ax_ps x
  | ex_r _ _ pi0 sigma => perm_ps (ps pi0) sigma
  | tens_r _ _ _ _ pi0 pi1 => add_node_tens (ps pi0) (ps pi1)
  | parr_r _ _ _ pi0 => add_node_parr (ps pi0)
  | cut_r _ _ _ pi0 pi1 => add_node_cut (ps pi0) (ps pi1)
  end.

Lemma ps_consistent {l : list formula} (pi : ll l) : sequent (ps pi) = l.
Proof.
  induction pi as [ | | A B l0 l1 pi0 H0 pi1 H1 | A B l0 pi0 H0 | A l0 l1 pi0 H0 pi1 H1].
  - apply ax_sequent.
  - by apply perm_sequent.
  - rewrite add_node_sequent union_sequent H0 H1; cbn.
    revert H0 H1.
    unfold union_order, sequent.
    destruct (order (ps pi0)) as [ | v0 o0] eqn:Ho0; try by [].
    destruct (order (ps pi1)) as [ | v1 o1] eqn:Ho1; try by [].
    assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [? ?]
      by (split; apply p_order; rewrite ?Ho0 ?Ho1 !in_cons; caseb).
    rewrite Ho0 Ho1 !union_edge_of_concl //.
    move => /eqP; cbn; move => /andP [/eqP -> _];
    move => /eqP; cbn; move => /andP [/eqP -> _] //.
  - rewrite add_node_sequent H0.
    revert H0.
    unfold sequent.
    destruct (order (ps pi0)) as [ | v0 [ | v1 o]] eqn:Ho; try by [].
    rewrite Ho.
    move => /eqP; cbn; by move => /andP [/eqP -> /andP[/eqP -> _]].
  - rewrite add_node_sequent union_sequent H0 H1; cbn.
    revert H0 H1.
    unfold union_order, sequent.
    destruct (order (ps pi0)) as [ | v0 o0] eqn:Ho0; try by [].
    destruct (order (ps pi1)) as [ | v1 o1] eqn:Ho1; try by [].
    assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [? ?]
      by (split; apply p_order; rewrite ?Ho0 ?Ho1 !in_cons; caseb).
    rewrite Ho0 Ho1 !union_edge_of_concl //.
    move => /eqP; cbn; move => /andP [/eqP -> _];
    move => /eqP; cbn; move => /andP [/eqP -> _].
    rewrite bidual.
    case_if.
Qed.



(** ** Cut Elimination *)
(** * Axiom - cut reduction *)
Definition red_ax_graph_1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : base_graph :=
  G ∔ [source (other_cut Hcut) , dual (elabel e) , target (other_ax Hax)].

Definition red_ax_graph (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : base_graph :=
  induced ([set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)).

Lemma red_ax_degenerate (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  source e = source (other_cut Hcut) <-> other_cut Hcut = other_ax Hax.
Proof.
  split; intro H.
  - apply other_ax_eq.
    rewrite H. splitb.
    apply /eqP; apply other_cut_in_neq.
  - rewrite H.
    by destruct (other_ax_in_neq Hax) as [-> _].
Qed.

Definition red_ax_left_1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : red_ax_graph_1 Hcut Hax -> edge (red_ax_graph_1 Hcut Hax) :=
  fun (v : red_ax_graph_1 Hcut Hax) =>
    if (left v == e) || (left v == other_cut Hcut) || (left v == other_ax Hax) then
      if source e == source (other_cut Hcut) then Some (pick_edge_at v)
      else None
    else Some (left v).

Lemma red_ax_consistent_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  let S := [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e) in
  forall (v : red_ax_graph Hcut Hax), red_ax_left_1 (val v) \in edge_set S.
Proof.
  intros S [v Hv].
  rewrite !in_set /red_ax_left_1; cbn.
  destruct (other_cut_in_neq Hcut) as [Htc Hneqc];
  destruct (other_ax_in_neq Hax) as [Hsa Hneqa].
  assert ((forall a, source a != target e) /\ forall a, target a != source e) as [? ?].
  { split; intro a; apply /eqP; intro Hc.
    1: assert (Hf := p_deg_out (target e)).
    2: assert (Hf := p_deg_in (source e)).
    all: rewrite ?Hcut ?Hax in Hf; cbn in Hf.
    all: assert (Hf' : a \in set0) by by rewrite -(cards0_eq Hf) in_set Hc.
    all: contradict Hf'; by rewrite in_set. }
  assert (Hm : source e = source (other_cut Hcut) -> forall b b',
    endpoint b (pick_edge_at v) != endpoint b' (other_cut Hcut)).
  { intros Hs b b'; apply /eqP; intro Hc.
    assert (Hc' : pick_edge_at v \in edges_at_subset b (endpoint b' e)) by
      (destruct b'; by rewrite in_set Hc ?Htc ?Hs).
    destruct (red_ax_degenerate Hcut Hax) as [Ho _].
    specialize (Ho Hs).
    contradict Hv; apply /negP.
    assert (Hvin := pick_edge_at_some v).
    revert Hvin; rewrite !in_set; move => /orP[/eqP Heq | /eqP Heq];
    destruct b, b';
    apply /nandP; rewrite andb_true_r !negb_involutive.
    all: try (contradict Hc'; apply /negP; by rewrite in_set).
    all: revert Hc'; rewrite ?other_cut_set ?other_ax_set !in_set; move => /orP[/eqP Hd | /eqP Hd];
      rewrite -Heq Hd ?Hs -?Htc ?Ho; caseb. }
  assert (Hm2 : source e <> source (other_cut Hcut) -> target (other_ax Hax) != target e).
  { intro Hs; apply /eqP; intro Hc.
    enough (Hdone : other_cut Hcut = other_ax Hax) by by rewrite Hdone Hsa in Hs.
    assert (Hm2 : other_ax Hax \in edges_in_at_subset (target e)) by by rewrite in_set Hc.
    revert Hm2; rewrite other_cut_set !in_set; move => /orP[/eqP Hd | /eqP Hd //].
    contradict Hd; apply /eqP; apply other_ax_in_neq. }
  splitb; case_if.
  all: try (apply /eqP; by apply nesym).
  all: try (rewrite -?Htc; by apply Hm).
  all: try by apply Hm2.
  - apply /eqP; intro Hc.
    assert (Hf : left v \in edges_out_at_subset (source e)) by by rewrite in_set Hc.
    contradict Hf; apply /negP.
    rewrite other_ax_set !in_set.
    splitb; by apply /eqP.
  - apply /eqP; intro Hc.
    assert (Hf : left v \in edges_in_at_subset (target e)) by by rewrite in_set Hc.
    contradict Hf; apply /negP.
    rewrite other_cut_set !in_set.
    splitb; by apply /eqP.
Qed. (* TODO essayer de simplifier (ça et les autres preuves de cette partie red) *)

Definition red_ax_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : red_ax_graph Hcut Hax -> edge (red_ax_graph Hcut Hax) :=
  fun v => Sub (red_ax_left_1 (val v)) (red_ax_consistent_left v).

Definition red_ax_graph_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : graph_left := {|
  graph_of := red_ax_graph Hcut Hax;
  left := @red_ax_left _ _ _ _;
  |}.

Lemma red_ax_consistent_order (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  all (pred_of_set ([set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e))) (order G).
Proof.
  apply /allP; intros v Hv.
  assert (Hl : vlabel v = concl_l) by by apply p_order.
  repeat (apply /setD1P; split); trivial.
  all: apply /eqP; intro Hc; contradict Hl; by rewrite Hc ?Hcut ?Hax.
Qed.

Definition red_ax_order (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : seq (red_ax_graph Hcut Hax) :=
  sval (all_sigP (red_ax_consistent_order Hcut Hax)).

Definition red_ax_graph_data (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : graph_data := {|
  graph_left_of := red_ax_graph_left Hcut Hax;
  order := red_ax_order _ _;
  |}.

Definition red_ax_transport (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : red_ax_graph_data Hcut Hax) :=
  fun (a : edge (red_ax_graph_data Hcut Hax)) => match val a with
  | None => if b then other_ax Hax else other_cut Hcut
  | Some a' => a'
  end.
Notation red_ax_transport_out := (@red_ax_transport _ _ _ _ false).
Notation red_ax_transport_in := (@red_ax_transport _ _ _ _ true).

Lemma red_ax_transport_inj (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : red_ax_graph_data Hcut Hax) :
  {in edges_at_subset b v &, injective (@red_ax_transport _ _ Hcut Hax b v)}.
Proof.
  destruct (other_cut_in_neq Hcut) as [Hc0 Hc1].
  destruct (other_ax_in_neq Hax) as [Ha0 Ha1].
  destruct v as [v Hv]; intros a a'.
  rewrite !in_set /red_ax_transport; cbn; rewrite !SubK.
  destruct a as [[a | ] Hain], a' as [[a' | ] Hain']; cbn.
  1:{ move => /eqP Ha /eqP Ha' Heq.
    by apply /eqP; rewrite sub_val_eq SubK Heq. }
  3:{ intros.
    by apply /eqP; rewrite sub_val_eq SubK. }
  all: move => /eqP Ha /eqP Ha' Heq.
  1: contradict Hain; apply /negP.
  2: contradict Hain'; apply /negP.
  all: destruct b.
  all: subst; rewrite !in_set; cbn.
  all: rewrite ?Ha0 ?Hc0; caseb.
Qed.

Lemma red_ax_transport_edges (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  edges_at_subset b v =
  [set red_ax_transport b (Sub v Hv) a | a in edges_at_subset b (Sub v Hv : red_ax_graph_data Hcut Hax)].
Proof.
  assert ((forall a, source a != target e) /\ forall a, target a != source e) as [? ?].
  { split; intro a; apply /eqP; intro Ha;
    [assert (Hf := p_deg_out (target e)) | assert (Hf := p_deg_in (source e))].
    all: rewrite ?Hcut ?Hax in Hf; cbn in Hf.
    all: assert (Hdone : a \in set0) by by rewrite -(cards0_eq Hf) in_set Ha.
    all: contradict Hdone; by rewrite in_set. }
  assert (v != source e /\ v != target e) as [Hvs Hvt]
    by (revert Hv; rewrite !in_set; by move => /andP[? /andP[? _]]).
  destruct (other_cut_in_neq Hcut) as [Hc0 Hc1].
  destruct (other_ax_in_neq Hax) as [Ha0 Ha1].
  apply /setP; intro a.
  rewrite Imset.imsetE !in_set.
  symmetry; apply /imageP; case_if.
  - assert (a <> e) by
      by (intro Hc; destruct b; subst; [by rewrite eq_refl in Hvt | by rewrite eq_refl in Hvs]).
    destruct (eq_comparable a (other_cut Hcut)) as [Heqc | Hneqc];
    [ | destruct (eq_comparable a (other_ax Hax)) as [Heqa | Hneqa]].
    + destruct b.
      { contradict Hvt; apply /negP; rewrite negb_involutive; apply /eqP.
        subst.
        apply other_cut_in_neq. }
      assert (Hn : None \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)).
      { rewrite !in_set; cbn; rewrite -!Heqc. subst.
        splitb.
        apply /eqP; intro Hf.
        assert (Hin : other_ax Hax \in edges_in_at_subset (target e))
          by by rewrite in_set Hf.
        revert Hin.
        rewrite other_cut_set !in_set.
        move => /orP[/eqP Hin | /eqP Hin].
        - contradict Hin; apply /eqP.
          apply other_ax_in_neq.
        - contradict Hvs; apply /negP; rewrite negb_involutive; apply /eqP.
          by rewrite -Hin Ha0. }
      subst.
      exists (Sub None Hn).
      * rewrite !in_set sub_val_eq !SubK; by apply /eqP.
      * by rewrite /red_ax_transport SubK.
    + destruct b.
      2:{ contradict Hvs; apply /negP; rewrite negb_involutive; apply /eqP.
          subst.
          apply other_ax_in_neq. }
      assert (Hn : None \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)).
      { rewrite !in_set; cbn; rewrite -!Heqa. subst.
        splitb.
        apply /eqP; intro Hf.
        assert (Hin : other_cut Hcut \in edges_out_at_subset (source e))
          by by rewrite in_set Hf.
        revert Hin.
        rewrite other_ax_set !in_set.
        move => /orP[/eqP Hin | /eqP Hin].
        - contradict Hin; by apply /eqP.
        - by rewrite Hin in Hneqc. }
      subst.
      exists (Sub None Hn).
      * rewrite !in_set sub_val_eq !SubK; by apply /eqP.
      * by rewrite /red_ax_transport SubK.
    + assert (Ha : Some a \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)).
      { rewrite !in_set; cbn.
        splitb; destruct b; subst; try by [].
        - apply /eqP; intro Hf.
          assert (Hc : a \in edges_out_at_subset (source e)) by by rewrite in_set Hf.
          revert Hc; rewrite other_ax_set !in_set; by move => /orP[/eqP ? | /eqP ?].
        - apply /eqP; intro Hf.
          assert (Hc : a \in edges_in_at_subset (target e)) by by rewrite in_set Hf.
          revert Hc; rewrite other_cut_set !in_set; by move => /orP[/eqP ? | /eqP ?]. }
      exists (Sub (Some a) Ha).
      * rewrite !in_set sub_val_eq !SubK; by apply /eqP.
      * by rewrite /red_ax_transport SubK.
  - intros [[x Hxin] Hx Hxx].
    rewrite /red_ax_transport SubK in Hxx.
    destruct x as [x | ].
    + contradict Hx; apply /negP.
      rewrite in_set; cbn; rewrite SubK; apply /eqP.
      by rewrite -Hxx.
    + contradict Hx; apply /negP.
      rewrite in_set; cbn; rewrite !SubK; apply /eqP.
      destruct b; by rewrite -Hxx.
Qed.
Notation red_ax_transport_edges_out := (@red_ax_transport_edges _ _ _ _ false).
Notation red_ax_transport_edges_in := (@red_ax_transport_edges _ _ _ _ true).

Lemma red_ax_transport_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  vlabel v = ⊗ \/ vlabel v = ⅋ ->
  red_ax_transport_in (Sub v Hv) (left (Sub v Hv : red_ax_graph_data Hcut Hax)) = left v.
Proof.
  intro Hl.
  cbn; rewrite /red_ax_transport /red_ax_left /red_ax_left_1 !SubK.
  assert (left v <> e).
  { intro Hf.
    assert (H := left_e Hl).
    rewrite Hf in H.
    contradict Hv; apply /negP.
    rewrite !in_set H.
    caseb. }
  assert (left v <> other_cut Hcut).
  { intro Hf.
    assert (Hc := left_e Hl); contradict Hc.
    destruct (other_cut_in_neq Hcut) as [Hc0 _].
    rewrite Hf Hc0.
    intro Hc.
    clear - Hl Hc Hcut; contradict Hcut.
    destruct Hl as [Hl | Hl];
    by rewrite Hc Hl. }
  case_if.
  destruct (red_ax_degenerate Hcut Hax) as [Ho _].
  enough (left v = other_cut Hcut) by by [].
  replace (left v) with (other_ax Hax); symmetry.
  by apply Ho.
Qed.


Lemma red_ax_p_deg (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_degree (red_ax_graph_data Hcut Hax).
Proof.
  unfold proper_degree, red_ax_graph_data.
  intros b [v Hv]; cbn.
  rewrite -(p_deg b v) (red_ax_transport_edges _ Hv) card_in_imset //.
  apply red_ax_transport_inj.
Qed.

Lemma red_ax_p_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_left (red_ax_graph_data Hcut Hax).
Proof.
  unfold proper_left, red_ax_graph_data.
  intros [v Hv] Hl; cbn in *.
  assert (H := p_left Hl).
  revert H; rewrite (red_ax_transport_edges_in Hv) Imset.imsetE in_set; move => /imageP [a Ha Heq].
  enough (Hdone : red_ax_left (Sub v Hv) = a) by by rewrite Hdone.
  symmetry; apply /eqP; rewrite /red_ax_left sub_val_eq /red_ax_left_1 SubK Heq; apply /eqP.
  destruct (other_cut_in_neq Hcut) as [Hc0 Hc1].
  destruct (other_ax_in_neq Hax) as [Ha0 Ha1].
  destruct a as [a Hain].
  rewrite /red_ax_transport SubK.
  destruct a as [a | ].
  - assert (a <> e /\ a <> other_cut Hcut /\ a <> other_ax Hax) as [? [? ?]].
    { splitb;
      intro Hc; subst;
      clear - Hain Hc0 Ha0; contradict Hain; apply /negP.
      all: rewrite !in_set; cbn.
      all: rewrite ?Hc0 ?Ha0; caseb. }
    case_if.
  - revert Ha.
    rewrite in_set; cbn; rewrite /red_ax_transport !SubK.
    move => /eqP Ha.
    rewrite -!Ha eq_refl.
    revert Ha1 Hc1; move => /eqP Ha1 /eqP Hc1.
    assert (other_ax Hax <> other_cut Hcut).
    { intro Hf.
      clear Heq; contradict Hain; apply /negP.
      rewrite !in_set; cbn; rewrite Hf Hc0; caseb. }
    assert (source e <> source (other_cut Hcut)).
    { intro Hf.
      destruct (red_ax_degenerate Hcut Hax) as [Ho _].
      specialize (Ho Hf).
      by symmetry in Ho. }
    case_if.
Qed.

Lemma red_ax_p_order (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_order (red_ax_graph_data Hcut Hax).
Proof.
  unfold proper_order, red_ax_graph_data, red_ax_order; cbn.
  split.
  - intros [? ?]; cbn.
    rewrite in_seq_sig SubK -(proj2_sig (all_sigP _)).
    apply p_order.
  - rewrite uniq_seq_sig -(proj2_sig (all_sigP _)).
    apply p_order.
Qed.

Definition red_ax_geos (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : geos := {|
  graph_data_of := red_ax_graph_data Hcut Hax;
  p_deg := @red_ax_p_deg _ _ _ _;
  p_left := @red_ax_p_left _ _ _ _;
  p_order := @red_ax_p_order _ _ _ _;
  |}.

Lemma red_ax_transport_right (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  vlabel v = ⊗ \/ vlabel v = ⅋ ->
  red_ax_transport_in (Sub v Hv) (right (Sub v Hv : red_ax_geos Hcut Hax)) = right v.
Proof.
  intro Hl.
  set w := Sub v Hv : red_ax_geos Hcut Hax.
  apply right_eq; trivial.
  assert (Hdone : red_ax_transport_in w (right w) \in edges_in_at_subset (v : G)).
  { rewrite (red_ax_transport_edges_in Hv).
    by apply imset_f, (@p_right _ w). }
  revert Hdone; rewrite in_set; move => /eqP Hdone.
  splitb.
  rewrite -(red_ax_transport_left Hv) //.
  intro Hf.
  assert (Hl' : vlabel w = ⊗ \/ vlabel w = ⅋) by (cbn; by rewrite SubK).
  assert (Hle := p_left Hl').
  destruct (p_right Hl') as [Hr Hc].
  contradict Hc; apply /negP; rewrite negb_involutive; apply /eqP.
  by apply (red_ax_transport_inj Hr Hle).
Qed.

Lemma red_ax_transport_ccl (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  vlabel v = ⊗ \/ vlabel v = ⅋ ->
  red_ax_transport_out (Sub v Hv) (ccl (Sub v Hv : red_ax_geos Hcut Hax)) = ccl v.
Proof.
  intro Hl.
  set w := Sub v Hv : red_ax_geos Hcut Hax.
  apply ccl_eq; trivial.
  assert (Hdone : red_ax_transport_out w (ccl w) \in edges_out_at_subset (v : G)).
  { rewrite (red_ax_transport_edges_out Hv).
    by apply imset_f, (@p_ccl _ w). }
  revert Hdone; rewrite in_set; by move => /eqP Hdone.
Qed.

Lemma red_ax_transport_edge_of_concl (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  vlabel v = c ->
  red_ax_transport_in (Sub v Hv) (edge_of_concl (Sub v Hv : red_ax_geos Hcut Hax)) = edge_of_concl v.
Proof.
  intro Hl.
  set w := Sub v Hv : red_ax_geos Hcut Hax.
  apply concl_eq; trivial.
  assert (Hdone : red_ax_transport_in w (edge_of_concl w) \in edges_in_at_subset (v : G)).
  { rewrite (red_ax_transport_edges_in Hv).
    by apply imset_f, (@p_concl _ w). }
  revert Hdone; rewrite in_set; by move => /eqP Hdone.
Qed.

Lemma red_ax_transport_label (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  forall a, elabel a = elabel (red_ax_transport b (Sub v Hv) a).
Proof.
  unfold red_ax_transport.
  intros [a Ha].
  rewrite !SubK; cbn.
  destruct a as [a | ]; try done.
  assert (dual (elabel e) = elabel (other_ax Hax) /\ dual (elabel e) = elabel (other_cut Hcut)) as [? ?].
  { destruct (proper_ax_cut_bis G) as [Hpax Hpcut].
    specialize (Hpax (source e) Hax);
    specialize (Hpcut (target e) Hcut).
    unfold true_on2 in Hpax;
    unfold true_on2 in Hcut.
    specialize (Hpax e (source_in_edges_out e));
    specialize (Hpcut e (target_in_edges_in e)).
    unfold is_dual_f, is_dual in Hpax;
    unfold is_dual_f, is_dual in Hpcut.
    by revert Hpax Hpcut; move => /eqP Hpax /eqP Hpcut. }
  case_if.
Qed.


Lemma red_ax_p_ax_cut (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_ax_cut (red_ax_geos Hcut Hax).
Proof.
  unfold proper_ax_cut.
  intros b [v Hv] Hl; cbn in Hl.
  destruct (p_ax_cut Hl) as [el [er H]].
  revert H.
  rewrite (red_ax_transport_edges b Hv).
  move => /andP[/andP[Hel Her] /eqP Heq].
  revert Hel; rewrite Imset.imsetE in_set; move => /imageP [El ? HeEl];
  revert Her; rewrite Imset.imsetE in_set; move => /imageP [Er ? HeEr].
  exists El, Er.
  splitb; apply /eqP.
  by rewrite !(red_ax_transport_label b Hv) -HeEl -HeEr.
Qed.

Lemma red_ax_p_tens_parr (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_tens_parr (red_ax_geos Hcut Hax).
Proof.
  unfold proper_tens_parr.
  intros b [v Hv] Hl; cbn in Hl.
  rewrite (red_ax_transport_label false Hv) 2!(red_ax_transport_label true Hv)
    red_ax_transport_left ?red_ax_transport_right ?red_ax_transport_ccl;
  try (destruct b; by caseb).
  by apply p_tens_parr.
Qed.

Definition red_ax_ps (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proof_structure := {|
  geos_of := red_ax_geos Hcut Hax;
  p_ax_cut := @red_ax_p_ax_cut _ _ _ _;
  p_tens_parr := @red_ax_p_tens_parr _ _ _ _;
  |}.


(** Sequent of an axiom - cut reduction *)
Lemma red_ax_sequent (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  sequent (red_ax_ps Hcut Hax) = sequent G.
Proof.
  assert (sequent (red_ax_ps Hcut Hax) = [seq elabel (red_ax_transport_in v (edge_of_concl v)) |
    v <- red_ax_order Hcut Hax]) as ->.
  { apply eq_map; intros [? ?].
    apply red_ax_transport_label. }
  assert ([seq elabel (red_ax_transport_in v (edge_of_concl v)) | v <- red_ax_order Hcut Hax] =
    [seq elabel ((edge_of_concl v)) | v <- [seq val v | v <- red_ax_order Hcut Hax]]) as ->.
  { rewrite -map_comp.
  apply (@eq_in_map _); intros [a Ha] Ho.
  rewrite !red_ax_transport_edge_of_concl ?SubK //.
  by assert (vlabel (Sub a Ha : red_ax_graph Hcut Hax) = c)
    by by apply (p_order (red_ax_geos Hcut Hax)). }
  by rewrite -(proj2_sig (all_sigP _)).
Qed.

(** Decreasing number of vertices *)
(* TOTHINK nb without cut vertices ? *)
Lemma red_ax_nb (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  #|red_ax_graph Hcut Hax| = #|G| - 2.
Proof.
  set f := fun (v : red_ax_graph_data Hcut Hax) => val v : G.
  rewrite -(card_imset (f := f)); [ | apply val_inj].
  assert (#|setT :\ (source e) :\ (target e)| = #|G| - 2) as <-.
  { replace (#|G|) with ((source e \in [set: G]) + #|[set: G] :\ source e|)
      by by rewrite -(cardsD1 (source e)) cardsT.
    replace (#|[set: G] :\ source e|) with
      ((target e \in [set: G] :\ source e) + #|[set: G] :\ source e :\ target e|)
      by by rewrite -(cardsD1 (target e)).
    rewrite !in_set.
    assert (target e != source e).
    { apply /negP; move => /eqP Hf.
      clear f; contradict Hcut.
      by rewrite Hf Hax. }
    lia. }
  apply eq_card; intro v.
  rewrite Imset.imsetE in_set.
  destruct (v \in [set: G] :\ source e :\ target e) eqn:Hv.
  - apply /imageP.
    by exists (Sub v Hv).
  - apply /imageP; intros [u _ Heq].
    by rewrite Heq /f (proj2_sig u) in Hv.
Qed.


(** * Tensor - cut reduction *)
Definition red_tens_graph_1 (G : graph_data) (et ep : edge G) :
  base_graph :=
  let ltens := left (source et) in
  let rtens := right (source et) in
  let lparr := left (source ep) in
  let rparr := right (source ep) in
  G ∔ cut ∔ cut
    ∔ [inl (inl (source ltens)) , elabel (ltens) , inl (inr tt)]
    ∔ [inl (inl (source rtens)) , elabel (rtens) , inr tt]
    ∔ [inl (inl (source lparr)) , elabel (lparr) , inr tt]
    ∔ [inl (inl (source rparr)) , elabel (rparr) , inl (inr tt)].

Definition red_tens_graph (G : graph_data) (v : G) (et ep : edge G) : base_graph :=
  induced ([set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\ (inl (inl (source ep)))
  :\ (inl (inl v))).

Lemma red_tens_cut_set (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  edges_in_at_subset v = [set et; ep].
Proof.
  rewrite -Het in Hcut.
  rewrite -Het other_cut_set.
  replace ep with (other_cut Hcut); trivial.
  symmetry; apply other_cut_eq.
  rewrite Het Hep; splitb.
  intro Hc; contradict Hparr.
  by rewrite Hc Htens.
Qed.

Lemma red_tens_ineq_in (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  (forall a, source a != v) /\
  source (left (source et)) != source et /\
  source (right (source et)) != source et /\
  source (left (source ep)) != source ep /\
  source (right (source ep)) != source ep /\
  source (left (source et)) != source ep /\
  source (right (source et)) != source ep /\
  source (left (source ep)) != source et /\
  source (right (source ep)) != source et.
Proof.
  assert (forall a, source a != v).
  { intro a; apply /eqP; intro Ha.
    assert (Hf := p_deg_out v).
    rewrite Hcut in Hf; cbn in Hf.
    assert (Hdone : a \in set0) by by rewrite -(cards0_eq Hf) in_set Ha.
    contradict Hdone; by rewrite in_set. }
  assert (source (left (source et)) != source ep /\ source (right (source et)) != source ep /\
    source (left (source ep)) != source et /\ source (right (source ep)) != source et /\
    source (left (source et)) != source et /\ source (right (source et)) != source et /\
    source (left (source ep)) != source ep /\ source (right (source ep)) != source ep)
    as [? [? [? [? [? [? [? ?]]]]]]].
  { splitb; apply /eqP; intro Hc;
    [set a := et | set a := et | set a := ep | set a := ep | set a := et | set a := et | set a := ep | set a := ep];
    [set b := ep | set b := ep | set b := et | set b := et | set b := et | set b := et | set b := ep | set b := ep];
    [set f := @left G | set f :=  @right G | set f := @left G | set f := @right G
    | set f := @left G | set f :=  @right G | set f := @left G | set f := @right G].
    all: assert (Hc0 : f (source a) = ccl (source b)) by (apply ccl_eq; caseb).
    all: assert (Hc1 : b = ccl (source b)) by (apply ccl_eq; caseb).
    all: assert (Hc2 : source a = v) by
      (replace v with (target b); rewrite Hc1 -Hc0 ?left_e ?right_e; caseb).
    all: contradict Hcut; by rewrite -Hc2 ?Htens ?Hparr. }
  splitb.
Qed.

Lemma red_tens_ineq_if (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  left (source et) <> right (source et) /\ right (source et) <> left (source et) /\
  left (source ep) <> right (source ep) /\ right (source ep) <> left (source ep) /\
  left (source et) <> left (source ep) /\ left (source ep) <> left (source et) /\
  left (source et) <> right (source ep) /\ right (source ep) <> left (source et) /\
  left (source ep) <> right (source et) /\ right (source et) <> left (source ep) /\
  right (source et) <> right (source ep) /\ right (source ep) <> right (source et).
Proof.
  assert (right (source et) <> left (source et) /\ right (source ep) <> left (source ep)) as [? ?].
  { elim: (@p_right _ (source et)); [ | caseb]; move => _ /eqP ?;
    elim: (@p_right _ (source ep)); [ | caseb]; move => _ /eqP ?.
    by split. }
  assert (Hf : source et <> source ep) by (intro Hf; contradict Htens; by rewrite Hf Hparr).
  assert (left (source et) <> left (source ep) /\ left (source et) <> right (source ep) /\
    right (source et) <> left (source ep) /\ right (source et) <> right (source ep)) as [? [? [? ?]]].
  { splitb; intro Hc; contradict Hf.
    1: rewrite -(@left_e _ (source et)) -1?(@left_e _ (source ep)); caseb.
    2: rewrite -(@left_e _ (source et)) -1?(@right_e _ (source ep)); caseb.
    3: rewrite -(@right_e _ (source et)) -1?(@left_e _ (source ep)); caseb.
    4: rewrite -(@right_e _ (source et)) -1?(@right_e _ (source ep)); caseb.
    all: by rewrite Hc. }
  assert (left (source et) <> right (source et) /\ left (source ep) <> right (source ep) /\
    left (source ep) <> left (source et) /\ right (source ep) <> left (source et) /\
    left (source ep) <> right (source et) /\ right (source ep) <> right (source et))
    as [? [? [? [? [? ?]]]]] by (splitb; by apply nesym).
  splitb.
Qed.

Lemma red_tens_new_edges_in (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  let S := [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\ (inl (inl (source ep)))
    :\ (inl (inl v)) in
  Some (Some (Some None)) \in edge_set S /\ Some (Some None) \in edge_set S /\
  Some None \in edge_set S /\ None \in edge_set S.
Proof.
  destruct (red_tens_ineq_in Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? ?]]]]]]]].
  intro. rewrite !in_set; cbn. splitb.
Qed.

Definition red_tens_left_1 (G : graph_data) (et ep : edge G) :
  red_tens_graph_1 et ep -> edge (red_tens_graph_1 et ep) :=
  fun v => match v with
  | inl (inl v) =>
    if left v == left (source et) then Some (Some (Some None))
    else if left v == right (source et) then Some (Some None)
    else if left v == left (source ep) then Some None
    else if left v == right (source ep) then None
    else if left v == et then None
    else if left v == ep then None
    else Some (Some (Some (Some (inl (inl (left v))))))
  | _ => None
  end.

Lemma red_tens_consistent_left (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  let S := [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\ (inl (inl (source ep)))
    :\ (inl (inl v)) in
  forall (u : red_tens_graph v et ep), red_tens_left_1 (val u) \in edge_set S.
Proof.
  intros S [u Hu].
  destruct (red_tens_ineq_in Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? ?]]]]]]]].
  destruct (red_tens_new_edges_in Hcut Het Hep Htens Hparr) as [? [? [? ?]]].
  rewrite !in_set /red_tens_left_1 !SubK.
  destruct u as [[u | ] | ]; cbn;
  case_if; splitb.
  all: apply /eqP; intro Hc.
  - assert (Heq : ep = ccl (source ep)) by (apply ccl_eq; caseb).
    assert (Heq2: left u = ccl (source ep)) by (apply ccl_eq; caseb).
    by rewrite -Heq in Heq2.
  - assert (Heq : et = ccl (source et)) by (apply ccl_eq; caseb).
    assert (Heq2: left u = ccl (source et)) by (apply ccl_eq; caseb).
    by rewrite -Heq in Heq2.
  - assert (Hin : left u \in edges_in_at_subset v) by by rewrite in_set Hc.
    revert Hin. rewrite (red_tens_cut_set Hcut Het Hep Htens Hparr) !in_set. by move => /orP[/eqP ? | /eqP ?].
  - assert (Hin : left u \in edges_in_at_subset (source ep)) by by rewrite in_set Hc.
    revert Hin. rewrite right_set ?in_set; caseb; by move => /orP[/eqP ? | /eqP ?].
  - assert (Hin : left u \in edges_in_at_subset (source et)) by by rewrite in_set Hc.
    revert Hin. rewrite right_set ?in_set; caseb; by move => /orP[/eqP ? | /eqP ?].
Qed.

Definition red_tens_left (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  red_tens_graph v et ep -> edge (red_tens_graph v et ep) :=
  fun u => Sub (red_tens_left_1 (val u)) (red_tens_consistent_left Hcut Het Hep Htens Hparr u).

Definition red_tens_graph_left (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) : graph_left := {|
  graph_of := red_tens_graph v et ep;
  left := red_tens_left Hcut Het Hep Htens Hparr;
  |}.

Definition red_tens_order_1 (G : graph_data) (et ep : edge G) :
  list (red_tens_graph_1 et ep) := [seq (inl (inl v)) | v <- order G].

Lemma red_tens_consistent_order (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  let S := [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\ (inl (inl (source ep)))
  :\ (inl (inl v)) in
  all (pred_of_set S) (red_tens_order_1 et ep).
Proof.
  rewrite /red_tens_order_1 all_map.
  apply /allP; intros u Hu; cbn.
  assert (Hl : vlabel u = concl_l) by by apply p_order.
  repeat (apply /setD1P; split); trivial; cbn.
  all: apply /eqP; intro Hc; contradict Hl; by rewrite Hc ?Hcut ?Htens ?Hparr.
Qed.

Definition red_tens_order (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  seq (red_tens_graph v et ep) := sval (all_sigP (red_tens_consistent_order Hcut Het Hep Htens Hparr)).

Definition red_tens_graph_data (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) : graph_data := {|
  graph_left_of := red_tens_graph_left Hcut Het Hep Htens Hparr;
  order := red_tens_order Hcut Het Hep Htens Hparr;
  |}.

Definition red_tens_transport (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :=
  fun (a : edge (red_tens_graph_data Hcut Het Hep Htens Hparr)) => match val a with
  | None => right (source ep)
  | Some None => left (source ep)
  | Some (Some None) => right (source et)
  | Some (Some (Some None)) => left (source et)
  | Some (Some (Some (Some (inl (inl a))))) => a
  | Some (Some (Some (Some (inl (inr a))))) => match a with end
  | Some (Some (Some (Some (inr a)))) => match a with end
  end.

Lemma red_tens_transport_inj (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  injective (@red_tens_transport _ _ Hcut _ _ Het Hep Htens Hparr).
Proof.
  intros [a Ha] [b Hb].
  rewrite /red_tens_transport !SubK.
  intro H.
  apply /eqP; rewrite sub_val_eq SubK; apply /eqP.
  revert Ha Hb.
  rewrite !in_set.
  destruct (red_tens_ineq_if Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]].
  destruct a as [[[[[[a | []] | []] | ] | ] | ] | ], b as [[[[[[b | []] | []] | ] | ] | ] | ];
  subst; cbn; try by [].
  all: rewrite ?left_e ?right_e; caseb.
  all: try (by move => /andP[_ /andP[_ /andP[/eqP ? /andP[/eqP ? _]]]] _);
       try (by move => _ /andP[_ /andP[_ /andP[/eqP ? /andP[/eqP ? _]]]]).
Qed.

Lemma red_tens_transport_edges (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (b : bool) (u : G) (Hu : inl (inl u) \in
  (setT :\ (inl (inl (source et))) :\ (inl (inl (source ep))) :\ (inl (inl v)))),
  edges_at_subset b u =
  [set red_tens_transport a | a in edges_at_subset b (Sub (inl (inl u)) Hu : red_tens_graph_data Hcut Het Hep Htens Hparr)].
Proof.
  set S := [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\ (inl (inl (source ep))) :\ (inl (inl v)).
  intros b u Hu; apply /setP; intro a.
  rewrite Imset.imsetE !in_set.
  symmetry; apply /imageP; case_if.
  - subst u.
    destruct (red_tens_ineq_in Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? ?]]]]]]]].
    destruct (red_tens_new_edges_in Hcut Het Hep Htens Hparr) as [Insssn [Inssn [Insn Inn]]].
    assert (a <> et /\ a <> ep) as [? ?].
    { split; intro Hc; contradict Hu; apply /negP; subst.
      all: rewrite !in_set; cbn.
      all: destruct b; caseb.
      rewrite Hep; caseb. }
    destruct (eq_comparable a (left (source et)));
    [ | destruct (eq_comparable a (left (source ep)))];
    [ | | destruct (eq_comparable a (right (source et)))];
    [ | | | destruct (eq_comparable a (right (source ep)))];
    try subst a.
    5:{ assert (Ina : Some (Some (Some (Some (inl (inl a))))) \in edge_set S).
        { rewrite !in_set; cbn. splitb.
          all: apply /eqP; intro Hf.
          - assert (a = ccl (source ep) /\ ep = ccl (source ep))
              as [? ?] by (split; apply ccl_eq; caseb).
            by assert (a = ep) by by subst.
          - assert (a = ccl (source et) /\ et = ccl (source et))
              as [? ?] by (split; apply ccl_eq; caseb).
            by assert (a = et) by by subst.
          - assert (Hin : a \in edges_in_at_subset v) by by rewrite in_set Hf.
            revert Hin; rewrite (red_tens_cut_set Hcut Het Hep Htens Hparr) !in_set; by move => /orP[/eqP ? | /eqP ?].
          - assert (Hin : a \in edges_in_at_subset (source ep)) by by rewrite in_set Hf.
            revert Hin; rewrite right_set ?in_set; [ | caseb]; by move => /orP[/eqP ? | /eqP ?].
          - assert (Hin : a \in edges_in_at_subset (source et)) by by rewrite in_set Hf.
            revert Hin; rewrite right_set ?in_set; [ | caseb]; by move => /orP[/eqP ? | /eqP ?]. }
        exists (Sub (Some (Some (Some (Some (inl (inl a)))))) Ina).
        - rewrite !in_set; cbn; rewrite !SubK; cbn; by apply /eqP.
        - by rewrite /red_tens_transport SubK. }
    all: destruct b;
      [contradict Hu; apply /negP; rewrite !in_set ?left_e ?right_e; caseb | ].
    4: exists (Sub None Inn).
    3: exists (Sub (Some (Some None)) Inssn).
    2: exists (Sub (Some None) Insn).
    1: exists (Sub (Some (Some (Some None))) Insssn).
    1,3,5,7: rewrite !in_set; cbn; rewrite !SubK; by cbn.
    all: by rewrite /red_tens_transport SubK.
  - intros [[[[[[[[d | []] | []] | ] | ] | ] | ] ?] Hdin Hdeq].
    all: rewrite /red_tens_transport !SubK in Hdeq; subst a.
    all: revert Hdin; rewrite !in_set; cbn; rewrite !SubK; cbn; move => /eqP Hd //.
    all: destruct b; contradict Hd; try by [].
    all: apply /eqP; cbn; by apply /eqP.
Qed.

Lemma red_tens_transport_left (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (u : G) (Hu : inl (inl u) \in [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\
    (inl (inl (source ep))) :\ (inl (inl v))),
  vlabel u = ⊗ \/ vlabel u = ⅋ ->
  red_tens_transport (left (Sub (inl (inl u)) Hu : red_tens_graph_data Hcut Het Hep Htens Hparr)) = left u.
Proof.
  intros u Hu Hl.
  cbn; rewrite /red_tens_transport /red_tens_left /red_tens_left_1 !SubK.
  revert Hu.
  rewrite !in_set; cbn.
  move => /andP[/eqP Hu /andP[/eqP ? /andP[/eqP ? _]]].
  case_if.
  all: contradict Hu.
  all: rewrite -(left_e Hl).
  all: by subst.
Qed.


Lemma red_tens_p_deg (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  proper_degree (red_tens_graph_data Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_degree, red_tens_graph_data.
  destruct (red_tens_new_edges_in Hcut Het Hep Htens Hparr) as [Insssn [Inssn [Insn Inn]]].
  set n := Sub None Inn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr);
  set sn := Sub (Some None) Insn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr);
  set ssn := Sub (Some (Some None)) Inssn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr);
  set sssn := Sub (Some (Some (Some None))) Insssn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr).
  intros b [[[u | []] | []] Hu]; cbn.
  - rewrite -(p_deg b u) (red_tens_transport_edges _ _ _ _ _ _ Hu) card_imset //.
    apply red_tens_transport_inj.
  - assert (edges_in_at_subset (Sub (inl (inr tt)) Hu : red_tens_graph_data Hcut Het Hep Htens Hparr) = [set sssn; n]
      /\ edges_out_at_subset (Sub (inl (inr tt)) Hu : red_tens_graph_data Hcut Het Hep Htens Hparr) = set0) as [Hin Hout].
    { split; apply /setP; intro a; rewrite !in_set.
      all: by destruct a as [[[[[[[a | []] | []] | ] | ] | ] | ] ?]. }
    destruct b;
    by rewrite ?Hin ?Hout ?cards2 ?cards0.
  - assert (edges_in_at_subset (Sub (inr tt) Hu : red_tens_graph_data Hcut Het Hep Htens Hparr) = [set ssn; sn]
      /\ edges_out_at_subset (Sub (inr tt) Hu : red_tens_graph_data Hcut Het Hep Htens Hparr) = set0) as [Hin Hout].
    { split; apply /setP; intro a; rewrite !in_set.
      all: by destruct a as [[[[[[[a | []] | []] | ] | ] | ] | ] ?]. }
    destruct b;
    by rewrite ?Hin ?Hout ?cards2 ?cards0.
Qed.

Lemma red_tens_p_left (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  proper_left (red_tens_graph_data Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_left.
  intros [[[u | []] | []] Hu] Hl; cbn in *;
  try (destruct Hl as [Hl | Hl]; by contradict Hl).
  assert (H := p_left Hl).
  revert H; rewrite (red_tens_transport_edges _ _ _ _ _ true Hu) Imset.imsetE in_set;
  move => /imageP [a Ha Heq].
  enough (Hdone : red_tens_left Hcut Het Hep Htens Hparr (Sub (inl (inl u)) Hu) = a)
    by by rewrite Hdone.
  rewrite -(red_tens_transport_left _ _ _ _ _ Hu Hl) in Heq.
  apply (red_tens_transport_inj Heq).
Qed.

Lemma red_tens_p_order (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  proper_order (red_tens_graph_data Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_order, red_tens_graph_data, red_tens_order; cbn.
  split.
  - intros [[[u | ] | ] ?]; cbn;
    rewrite in_seq_sig SubK -(proj2_sig (all_sigP _)) /red_tens_order_1.
    { rewrite mem_map; [ | apply inj_comp; apply inl_inj].
      apply p_order. }
    all: split; intro H; try by [].
    all: contradict H; apply /negP.
    all: clear; by induction (order G).
  - rewrite uniq_seq_sig -(proj2_sig (all_sigP _)) /red_tens_order_1.
    rewrite map_inj_uniq; [ | apply inj_comp; apply inl_inj].
    apply p_order.
Qed.

Definition red_tens_geos (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) : geos := {|
  graph_data_of := red_tens_graph_data Hcut Het Hep Htens Hparr;
  p_deg := @red_tens_p_deg _ _ _ _ _ _ _ _ _;
  p_left := @red_tens_p_left _ _ _ _ _ _ _ _ _;
  p_order := @red_tens_p_order _ _ _ _ _ _ _ _ _;
  |}.

Lemma red_tens_transport_right (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (u : G) (Hu : inl (inl u) \in [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\
    (inl (inl (source ep))) :\ (inl (inl v))),
  vlabel u = ⊗ \/ vlabel u = ⅋ ->
  red_tens_transport (right (Sub (inl (inl u)) Hu : red_tens_geos Hcut Het Hep Htens Hparr)) = right u.
Proof.
  intros u Hu Hl.
  set w : red_tens_geos Hcut Het Hep Htens Hparr := Sub (inl (inl u)) Hu.
  apply right_eq; trivial.
  assert (Hdone : red_tens_transport (right w) \in edges_in_at_subset u).
  { rewrite (red_tens_transport_edges _ _ _ _ _ true Hu).
    by apply imset_f, (@p_right _ w). }
  revert Hdone; rewrite in_set; move => /eqP Hdone.
  splitb.
  rewrite -(red_tens_transport_left _ _ _ _ _ Hu) // -/w.
  intro Hf.
  assert (Hl' : vlabel w = ⊗ \/ vlabel w = ⅋) by by [].
  destruct (p_right Hl') as [_ Hc].
  contradict Hc; apply /negP; rewrite negb_involutive; apply /eqP.
  by apply red_tens_transport_inj.
Qed.

Lemma red_tens_transport_ccl (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (u : G) (Hu : inl (inl u) \in [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\
    (inl (inl (source ep))) :\ (inl (inl v))),
  vlabel u = ⊗ \/ vlabel u = ⅋ ->
  red_tens_transport (ccl (Sub (inl (inl u)) Hu : red_tens_geos Hcut Het Hep Htens Hparr)) = ccl u.
Proof.
  intros u Hu Hl.
  set w : red_tens_geos Hcut Het Hep Htens Hparr := Sub (inl (inl u)) Hu.
  apply ccl_eq; trivial.
  assert (Hdone : red_tens_transport (ccl w) \in edges_out_at_subset u).
  { rewrite (red_tens_transport_edges _ _ _ _ _ false Hu).
    by apply imset_f, (@p_ccl _ w). }
  revert Hdone; rewrite in_set; by move => /eqP Hdone.
Qed.

Lemma red_tens_transport_edge_of_concl (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (u : G) (Hu : inl (inl u) \in [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\
    (inl (inl (source ep))) :\ (inl (inl v))),
  vlabel u = c ->
  red_tens_transport (edge_of_concl (Sub (inl (inl u)) Hu : red_tens_geos Hcut Het Hep Htens Hparr)) = edge_of_concl u.
Proof.
  intros u Hu Hl.
  set w : red_tens_geos Hcut Het Hep Htens Hparr := Sub (inl (inl u)) Hu.
  apply concl_eq; trivial.
  assert (Hdone : red_tens_transport (edge_of_concl w) \in edges_in_at_subset u).
  { rewrite (red_tens_transport_edges _ _ _ _ _ true Hu).
    by apply imset_f, (@p_concl _ w). }
  revert Hdone; rewrite in_set; by move => /eqP Hdone.
Qed.

Lemma red_tens_transport_label (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (a : edge (red_tens_geos Hcut Het Hep Htens Hparr)), elabel a = elabel (red_tens_transport a).
Proof. by intros [[[[[[[? | []] | []] | ] | ] | ] | ] ?]. Qed.


Lemma red_tens_p_ax_cut (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  proper_ax_cut (red_tens_geos Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_ax_cut.
  destruct (red_tens_new_edges_in Hcut Het Hep Htens Hparr) as [Insssn [Inssn [Insn Inn]]].
  set n := Sub None Inn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr);
  set sn := Sub (Some None) Insn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr);
  set ssn := Sub (Some (Some None)) Inssn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr);
  set sssn := Sub (Some (Some (Some None))) Insssn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr).
  destruct (proper_ax_cut_bis G) as [_ Hpcut].
  assert (Hvet : et \in edges_in_at_subset v) by by rewrite in_set Het.
  specialize (Hpcut _ Hcut _ Hvet).
  unfold is_dual_f, is_dual in Hpcut; revert Hpcut; move => /eqP Hpcut.
  assert (Ht := p_tens Htens); cbn in Ht.
  assert (Hp := p_parr Hparr); cbn in Hp.
  assert (et = ccl (source et) /\ ep = ccl (source ep)) as [Hct Hcp] by (split; apply ccl_eq; caseb).
  rewrite -Hct in Ht;
  rewrite -Hcp in Hp.
  assert (Hoep : ep = other (pre_proper_cut Hcut) Hvet).
  { apply other_eq.
    - by rewrite in_set Hep.
    - intro Hc; clear - Hc Htens Hparr; contradict Hparr.
      by rewrite Hc Htens. }
  rewrite -Hoep Ht Hp in Hpcut; cbn in Hpcut; clear Hoep Hvet Hct Hcp Ht Hp.
  inversion Hpcut as [[H0 H1]]; clear Hpcut.
  intros b [[[u | []] | []] Hu] Hl; cbn in Hl.
  { destruct (p_ax_cut Hl) as [el [er H]].
    revert H.
    rewrite (red_tens_transport_edges _ _ _ _ _ b Hu).
    move => /andP[/andP[Hel Her] /eqP Heq].
    revert Hel; rewrite Imset.imsetE in_set; move => /imageP [El ? HeEl];
    revert Her; rewrite Imset.imsetE in_set; move => /imageP [Er ? HeEr].
    exists El, Er.
    splitb; apply /eqP.
    by rewrite !red_tens_transport_label -HeEl -HeEr. }
  all: destruct b; try by [].
  1: exists sssn, n.
  2: exists ssn, sn.
  all: rewrite !in_set; cbn; rewrite !SubK; cbn; apply /eqP.
  all: by rewrite -?H0 -?H1 bidual.
Qed.

Lemma red_tens_p_tens_parr (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  proper_tens_parr (red_tens_geos Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_tens_parr.
  intros b [[[u | []] | []] Hu] Hl; cbn in Hl.
  all: try (destruct b; by contradict Hl).
  rewrite !red_tens_transport_label red_tens_transport_left ?red_tens_transport_right ?red_tens_transport_ccl;
  try (destruct b; by caseb).
  by apply p_tens_parr.
Qed.

Definition red_tens_ps (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) : proof_structure := {|
  geos_of := red_tens_geos  Hcut Het Hep Htens Hparr;
  p_ax_cut := @red_tens_p_ax_cut _ _ _ _ _ _ _ _ _;
  p_tens_parr := @red_tens_p_tens_parr _ _ _ _ _ _ _ _ _;
  |}.


(** Sequent of an tensor - cut reduction *)
Lemma red_tens_sequent (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  sequent (red_tens_geos Hcut Het Hep Htens Hparr) = sequent G.
Proof.
  transitivity ([seq elabel (@red_tens_transport _ _ Hcut _ _ Het Hep Htens Hparr (edge_of_concl u)) |
    u <- red_tens_order Hcut Het Hep Htens Hparr]).
  { apply eq_map; intros [? ?].
    apply red_tens_transport_label. }
  destruct (red_tens_new_edges_in Hcut Het Hep Htens Hparr) as [_ [_ [_ Inn]]].
  set n := Sub None Inn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr).
  assert ([seq elabel (red_tens_transport (edge_of_concl u)) | u <- red_tens_order Hcut Het Hep Htens Hparr] =
    [seq (match u with | inl (inl u) => elabel (edge_of_concl u) | _ => elabel n end)
    | u <- [seq val u | u <- red_tens_order Hcut Het Hep Htens Hparr]]) as ->.
  { rewrite -map_comp.
    apply (@eq_in_map _); intros [a Ha].
    rewrite /red_tens_order in_seq_sig !SubK -(proj2_sig (all_sigP _)) /red_tens_order_1.
    move => /mapP [x Hx Hax].
    assert (Hxx : inl (inl x) \in [set: red_tens_graph_1 et ep] :\ inl (inl (source et))
      :\ inl (inl (source ep)):\ inl (inl v)) by by rewrite -Hax.
    assert (Sub a Ha = Sub (inl (inl x)) Hxx) as -> by (apply /eqP; by rewrite sub_val_eq SubK Hax).
    rewrite red_tens_transport_edge_of_concl /comp ?SubK //; by apply p_order. }
  rewrite -(proj2_sig (all_sigP _)) /red_tens_order_1 -map_comp.
  by apply eq_map.
Qed.

(** Decreasing number of vertices *)
Lemma red_tens_nb (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  #|red_tens_graph v et ep| = #|G| - 1.
Proof.
  set f := fun (u : red_tens_graph v et ep) => match val u with
  | inl (inl u) => u
  | inl (inr _) => source et
  | inr _ => source ep
  end.
  assert (injective f).
  { assert (source et <> source ep).
    { intro Hc. contradict Htens.
      by rewrite Hc Hparr. }
    assert (source ep <> source et) by by apply nesym.
    intros [[[u | []] | []] Hu] [[[u' | []] | []] Hu'];
    rewrite /f !SubK;
    intro Heq.
    all: apply /eqP; rewrite // sub_val_eq SubK ?Heq //; cbn.
    all: revert Hu Hu'.
    all: rewrite !in_set Heq; cbn.
    all: (try by move => /andP[/eqP ? /andP[/eqP ? /andP[/eqP ? _]]] _);
      try by move => _ /andP[/eqP ? /andP[/eqP ? /andP[/eqP ? _]]]. }
  rewrite -(card_imset (f := f)) //.
  assert (#|setT :\ v| = #|G| - 1) as <-.
  { replace (#|G|) with ((v \in [set: G]) + #|[set: G] :\ v|)
      by by rewrite -(cardsD1 v) cardsT.
    rewrite in_set.
    lia. }
  apply eq_card; intro u.
  rewrite Imset.imsetE !in_set andb_true_r.
  destruct (eq_comparable u v) as [Heq | Hneq].
  - subst; rewrite eq_refl; cbn.
    apply /imageP; intros [[[[u | []] | []] Hin] _ Huv];
    rewrite /f SubK in Huv.
    + revert Hin; rewrite !in_set; cbn.
      move => /andP[/eqP ? /andP[/eqP ? /andP[/eqP ? _]]].
      by subst.
    + contradict Htens.
      by rewrite -Huv Hcut.
    + contradict Hparr.
      by rewrite -Huv Hcut.
  - transitivity true.
    2:{ symmetry; by apply /negP /negP /eqP. }
    apply /imageP.
    set S := [set: red_tens_graph_1 et ep] :\ inl (inl (source et))
      :\ inl (inl (source ep)):\ inl (inl v).
    destruct (eq_comparable u (source et));
    [ | destruct (eq_comparable u (source ep))].
    + assert (Hin : inl (inr tt) \in S) by by rewrite !in_set.
      by exists (Sub (inl (inr tt)) Hin).
    + assert (Hin : inr tt \in S) by by rewrite !in_set.
      by exists (Sub (inr tt) Hin).
    + assert (Hin : inl (inl u) \in S) by
        (rewrite !in_set; cbn; splitb; by apply /eqP).
      by exists (Sub (inl (inl u)) Hin).
Qed.


(** * Cut reduction preocedure *)
Lemma red_term (G : proof_structure) (v : G) (H : vlabel v = cut) :
  [exists e, (target e == v) && (vlabel (source e) == ax)] || [exists et, exists ep,
  (target et == v) && (target ep == v) && (vlabel (source et) == ⊗) && (vlabel (source ep) == ⅋)].
Proof.
  enough (Hdone : (exists e, target e = v /\ vlabel (source e) = ax) \/
    exists et ep, target et = v /\ target ep = v /\ vlabel (source et) = ⊗ /\ vlabel (source ep) = ⅋).
  { destruct Hdone as [[e [He0 He1]] | [et [ep [He0 [He1 [He2 He3]]]]]].
    - apply /orP; left. apply /existsP; exists e. rewrite He0 He1. splitb.
    - apply /orP; right. apply /existsP; exists et. apply /existsP; exists ep. rewrite He0 He1 He2 He3. splitb. }
  destruct (p_cut H) as [e [e' H']];
  revert H'; rewrite !in_set; move => /andP[/andP[/eqP Hin /eqP Hin'] /eqP Heq].
  rewrite -Hin in H.
  assert (Hout := p_deg_out (source e)).
  assert (Hout' := p_deg_out (source e')).
  assert (#|edges_out_at_subset (source e)| <> 0 /\ #|edges_out_at_subset (source e')| <> 0) as [? ?].
  { split; intro Hc; [set f := e | set f := e'].
    all: assert (Hf : f \in set0) by by rewrite -(cards0_eq Hc) in_set.
    all: contradict Hf; by rewrite in_set. }
  destruct (vlabel (source e)) eqn:Hle; try done;
  destruct (vlabel (source e')) eqn:Hle'; try done.
  all: try (by left; exists e; splitb).
  all: try (by left; exists e'; splitb).
  - contradict Heq.
    assert (Heqe : e = ccl (source e)) by (apply ccl_eq; trivial; caseb).
    assert (Hel : elabel e = tens (elabel (left (source e))) (elabel (right (source e))))
      by (rewrite {1}Heqe; by apply p_tens).
    assert (Heqe' : e' = ccl (source e')) by (apply ccl_eq; trivial; caseb).
    assert (Hel' : elabel e' = tens (elabel (left (source e'))) (elabel (right (source e'))))
      by (rewrite {1}Heqe'; by apply p_tens).
    by rewrite Hel Hel'.
  - right; exists e, e'; splitb.
  - right; exists e', e; splitb.
  - contradict Heq.
    assert (Heqe : e = ccl (source e)) by (apply ccl_eq; trivial; caseb).
    assert (Hel : elabel e = parr (elabel (left (source e))) (elabel (right (source e))))
      by (rewrite {1}Heqe; by apply p_parr).
    assert (Heqe' : e' = ccl (source e')) by (apply ccl_eq; trivial; caseb).
    assert (Hel' : elabel e' = parr (elabel (left (source e'))) (elabel (right (source e'))))
      by (rewrite {1}Heqe'; by apply p_parr).
    by rewrite Hel Hel'.
Qed.

Definition red_one (G : proof_structure) (v : G) (H : vlabel v = cut) : proof_structure.
Proof.
  elim: (orb_sum (red_term H)).
  - move => /existsP /sigW [e /andP[/eqP He /eqP Hax]].
    rewrite -He in H.
    apply (red_ax_ps H Hax).
  - move => /existsP /sigW [et /existsP /sigW [ep /andP[/andP[/andP[/eqP Het /eqP Hep] /eqP Htens] /eqP Hparr]]].
    apply (red_tens_ps H Het Hep Htens Hparr).
Defined.

Lemma red_one_sequent (G : proof_structure) (v : G) (H : vlabel v = cut) :
  sequent (red_one H) = sequent G.
Proof.
  unfold red_one.
  elim: (orb_sum (red_term H)) => Hex /=.
  - elim: (sigW (elimTF existsP Hex)) => {Hex} e /andP[He Hax].
    set Hr := elimTF eqP He; destruct Hr.
    apply red_ax_sequent.
  - elim: (sigW (elimTF existsP Hex)) => {Hex} et Hex.
    elim: (sigW (elimTF existsP Hex)) => {Hex} ep /andP[/andP[/andP[Het Hep] Htens] Hparr].
    apply red_tens_sequent.
Qed.

Lemma red_one_nb (G : proof_structure) (v : G) (H : vlabel v = cut) :
  #|red_one H| < #|G|.
Proof.
  unfold red_one.
  assert (#|G| <> 0) by by apply fintype0.
  elim: (orb_sum (red_term H)) => Hex /=.
  - elim: (sigW (elimTF existsP Hex)) => {Hex} e /andP[He Hax].
    set Hr := elimTF eqP He; destruct Hr.
    rewrite red_ax_nb.
    set n := #|G|; lia.
  - elim: (sigW (elimTF existsP Hex)) => {Hex} et Hex.
    elim: (sigW (elimTF existsP Hex)) => {Hex} ep /andP[/andP[/andP[Het Hep] Htens] Hparr].
    rewrite red_tens_nb //; try by apply /eqP.
    set n := #|G|; lia.
Qed.

Definition has_cut (G : base_graph) := #|[set v : G | vlabel v == cut]| != 0.

Lemma has_cutP (G : base_graph) : reflect (has_cut G) [exists v : G, vlabel v == cut].
Proof.
  apply iff_reflect; split; unfold has_cut; intro H.
  - rewrite eqn0Ngt negb_involutive card_gt0 in H. revert H; move => /set0Pn [e H].
    rewrite in_set in H.
    apply /existsP. by exists e.
  - revert H; move => /existsP [v Hm].
    rewrite eqn0Ngt negb_involutive card_gt0.
    apply /set0Pn. exists v. by rewrite in_set.
Qed.

Definition red_all (G : proof_structure) : {P : proof_structure | sequent P = sequent G & ~(has_cut P)}.
Proof.
  revert G.
  enough (Hm : forall n (G : proof_structure), #|G| = n ->
    {P : proof_structure | sequent P = sequent G & ~(has_cut P)})
    by (intro G; by apply (Hm #|G|)).
  intro n; induction n as [n IH] using lt_wf_rect; intros G Hc.
  have [H | H] := altP (@has_cutP G).
  + revert H; move => /has_cutP /existsP /sigW [v /eqP Hcut].
    rewrite -(red_one_sequent Hcut).
    assert (Hc' := red_one_nb Hcut).
    apply (IH #|red_one Hcut|); lia.
  + eexists G; trivial.
    revert H; by move => /has_cutP H.
Qed.

Definition red (G : proof_structure) : proof_structure := proj1_sig (red_all G).

Lemma red_sequent (G : proof_structure) : sequent (red G) = sequent G.
Proof. by destruct (proj2_sig (red_all G)). Qed.

Lemma red_has_cut (G : proof_structure) : ~ has_cut (red G).
Proof. by destruct (proj2_sig (red_all G)). Qed.


Fixpoint nb_cut l (pi : ll l) := match pi with
  | ax_r x => 0
  | ex_r _ _ pi0 _ => nb_cut pi0
  | tens_r _ _ _ _ pi0 pi1 => nb_cut pi0 + nb_cut pi1
  | parr_r _ _ _ pi0 => nb_cut pi0
  | cut_r _ _ _ pi0 pi1 => nb_cut pi0 + nb_cut pi1 + 1
  end.

Lemma ps_nb_cut l (pi : ll l) : #|[set v : ps pi | vlabel v == cut]| = nb_cut pi.
Proof.
  induction pi as [x | | A B l0 l1 pi0 H0 pi1 H1 | A B l0 pi0 H0 | A l0 l1 pi0 H0 pi1 H1].
  - enough (H : [set v : ax_ps x | vlabel v == cut] = set0) by by rewrite H cards0.
    apply /setP; intro v; destruct_I3 v;
    by rewrite !in_set.
  - by [].
  - rewrite /= -H0 -H1.
Abort.
(* TODO Lemma : nb cut ps (pi) = nb cut pi, idem other rules + mettre ça vers ps
-> vraiment utile ? ça a l'air mieux dans le sens sequentialisation ... *)
(* lemma: sub-confluence + convergence *)



(** ** Correctness Criteria: Danos-Regnier *)
(** * Concepts of graph theory *)
Definition upath {Lv Le : Type} {G : graph Lv Le} := seq ((edge G) * bool).
Notation forward e := (e, true).
Notation backward e := (e, false).
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
  move => /andP[/eqP -> W]. splitb.
  specialize (IH _ _ W). by destruct IH as [_ <-].
Qed.

Lemma uwalk_eq {Lv Le : Type} {G : graph Lv Le} (p : upath) :
  forall (x y s t : G), p <> nil -> uwalk x y p -> uwalk s t p -> x = s /\ y = t.
Proof.
  induction p as [ | (e, b) p IH]; try by [].
  move => x y s t _ /andP[/eqP w W] /andP[/eqP w' W']; subst x s. splitb.
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
  - revert Wp; cbn; move => /andP[/eqP <- Wp]. splitb.
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
  - cbn. splitb.
    assert (H := uwalk_sub_middle W). cbn in H. by rewrite -H.
  - cbn in *. revert W; move => /andP[/eqP -> W].
    splitb; apply (Hp _ _ _ W).
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
  all: apply /eqP; cbn; apply /eqP; case_if.
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
  rewrite uwalk_rcons negb_involutive. splitb.
  by apply H.
Qed.


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
  splitb.
  - apply (uwalk_cat Wp Wq).
  - rewrite map_cat cat_uniq. splitb.
    by rewrite /disjoint_upaths disjoint_sym disjoint_has in D.
  - rewrite map_cat mem_cat. splitb.
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
  splitb; apply (uwalk_sub_1 W).
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
  move =>/andP[/andP[W U] N]. splitb.
  - by apply uwalk_rev.
  - by rewrite map_comp upath_rev_fst map_rev rev_uniq -map_comp.
  - by rewrite map_comp upath_rev_fst map_rev -has_pred1 has_rev has_pred1 -map_comp.
Qed.

Definition upath_revS {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : Simpl_upath f s t) :=
  {| upval := upath_rev p ; upvalK := upath_revK (upvalK p) |}. (* TODO homogeneiser noms *)

Lemma upath_nilK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G) :
  simpl_upath f s s [::].
Proof. unfold simpl_upath; cbn. splitb. Qed.

Definition upath_nil {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G) :=
  {| upval := [::] ; upvalK := upath_nilK f s |}.


Definition uacyclic {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :=
  forall (x : G) (p : Simpl_upath f x x), p = upath_nil f x.

Definition uconnected {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :=
  forall (x y : G), exists (_ : Simpl_upath f x y), true.

(** Identify all premises of a ⅋ node *)
Definition switching {G : graph_left} : edge G -> option (edge G) :=
  fun e => Some (if vlabel (target e) == ⅋ then left (target e) else e).

(** Paths in the left switching graph *)
Definition switching_left {G : graph_left} : edge G -> option (edge G) :=
  fun e => if vlabel (target e) == ⅋ then if e == left (target e) then None else Some e else Some e.

(* All switching graphs have the same number of connected components:
   any one is connected iff the graph where we remove all lefts is connected *)
Definition correct (G : graph_left) := uacyclic (@switching G) /\ uconnected (@switching_left G).


Definition iso_path (F G : base_graph) (h : F ≃ G) : upath -> upath :=
  fun p => [seq (h.e e.1, e.2) | e <- p].

Lemma iso_walk (F G : base_graph) (h : F ≃ G) :
  forall p s t, uwalk s t p -> uwalk (h s) (h t) (iso_path h p).
Proof.
  intro p; induction p as [ | u p HP]; intros s t; cbn.
  + by move => /eqP ->.
  + move => /andP[/eqP w W].
    rewrite !endpoint_iso !iso_noflip w.
    splitb. by apply HP.
Qed.


(** Isomorphism between graph_left *)
Set Primitive Projections.
Record iso_left (F G: graph_left) := Iso_left {
  iso_of :> iso F G;
  left_iso: forall v, vlabel v = ⅋ -> left (iso_of v) = iso_of.e (left v) }.
Unset Primitive Projections.
Infix "≃l" := iso_left (at level 79).

Definition iso_left_id G : G ≃l G.
Proof. by exists (@iso_id _ _ G). Defined.

Definition iso_left_sym F G : F ≃l G -> G ≃l F.
Proof.
  move => f.
  exists (iso_sym f).
  move => ? ?; cbn.
  apply /eqP. by rewrite -bij_eqLR -left_iso -?(vlabel_iso f) bijK'.
Defined.

Definition iso_left_comp F G H : F ≃l G -> G ≃l H -> F ≃l H.
Proof.
  move => f g.
  exists (iso_comp f g).
  move => ? ?.
  by rewrite !left_iso // vlabel_iso.
Defined.

Global Instance iso_left_Equivalence: CEquivalence iso_left.
Proof. constructor. exact @iso_left_id. exact @iso_left_sym. exact @iso_left_comp. Defined.


Lemma iso_path_switchingK (F G : graph_left) (h : F ≃l G) : forall p s t,
  simpl_upath switching s t p -> simpl_upath switching (h s) (h t) (iso_path h p).
Proof.
  move => p s t /andP[/andP[W U] N]. splitb.
  - by apply iso_walk.
  - rewrite -map_comp /comp; cbn.
    assert (H : forall e, switching (h.e e) = option_map h.e (switching e)).
    { intro e; apply /eqP; cbn; apply /eqP.
      rewrite /switching !endpoint_iso iso_noflip vlabel_iso; cbn.
      case_if.
      apply h. apply /eqP; cbn; by apply /eqP. }
    replace [seq switching (h.e x.1) | x <- p] with [seq option_map h.e (switching x.1) | x <- p]
      by (apply eq_map; intros []; by rewrite H).
    rewrite /switching map_comp map_inj_uniq // in U.
    cbn; by rewrite map_comp map_inj_uniq // map_comp map_inj_uniq.
  - rewrite -map_comp /comp; cbn.
    clear; by induction p.
Qed.

Definition iso_path_switching (F G : graph_left) (h : F ≃l G) (s t : F) :
  Simpl_upath switching s t -> Simpl_upath switching (h s) (h t) :=
  fun sp => let (p, P) := sp in {| upval := iso_path h p; upvalK := iso_path_switchingK h P |}.

Lemma iso_path_switching_inj (F G : graph_left) (h : F ≃l G) :
  forall s t, injective (@iso_path_switching _ _ h s t).
Proof.
  move => s t [p P] [q Q] /eqP; cbn; move => /eqP Heq.
  apply /eqP; cbn; apply /eqP.
  revert Heq. apply inj_map => [[e b] [f c]] /=.
  move => /eqP; cbn; move => /andP[/eqP Heq /eqP ->].
  apply /eqP; splitb; cbn; apply /eqP.
  revert Heq. by apply bij_injective.
Qed.

Lemma iso_path_nil (F G : graph_left) (h : F ≃l G) :
  forall (s : F), iso_path_switching h (upath_nil switching s) = upath_nil switching (h s).
Proof. intros. by apply /eqP. Qed.

Lemma iso_path_switching_leftK (F G : graph_left) (h : F ≃l G) : forall p s t,
  simpl_upath switching_left s t p -> simpl_upath switching_left (h s) (h t) (iso_path h p).
Proof.
  move => p s t /andP[/andP[W U] N].
  assert (H : forall e, switching_left (h.e e) = option_map h.e (switching_left e)).
  { intro e.
    rewrite /switching_left !endpoint_iso iso_noflip vlabel_iso; cbn.
    case_if.
    - enough (e = left (target e)) by by [].
      apply /eqP; rewrite -(bij_eq (f := h.e)) //; apply /eqP.
      rewrite -left_iso //. by (apply /eqP; cbn; apply /eqP).
    - enough (h.e (left (target e)) = left (h (target (left (target e))))) by by [].
      replace (left (target e)) with e in * at 2.
      rewrite left_iso //. by apply /eqP; cbn; apply /eqP. }
 splitb.
  - by apply iso_walk.
  - rewrite -map_comp /comp; cbn.
    enough ([seq switching_left (h.e x.1) | x <- p] = [seq Some (h.e x.1) | x <- p] /\
      [seq switching_left e.1 | e <- p] = [seq Some x.1 | x <- p]) as [Hr' Hr].
    { rewrite Hr map_comp map_inj_uniq // in U.
      by rewrite Hr' map_comp map_inj_uniq // map_comp map_inj_uniq. }
    split; apply eq_in_map; intros (e, b) E.
    all: rewrite ?H /switching_left.
    all: case_if.
    all: contradict N; apply /negP; rewrite negb_involutive.
    all: enough (Hn : None = switching_left (e, b).1) by
      (rewrite Hn; by apply (map_f (fun a => switching_left a.1))).
    all: unfold switching_left; case_if.
    all: replace (left (target e)) with e in *.
    all: enough (true == false) by by [].
    all: by replace true with (eqb_rule (vlabel (target e)) (⅋)) by by apply /eqP.
  - rewrite -map_comp /comp; cbn.
    apply /(nthP None). move => [n Hc] Hf.
    rewrite size_map in Hc.
    enough (nth None [seq switching_left x.1 | x <- p] n = None).
    { contradict N; apply /negP; rewrite negb_involutive.
      apply /(nthP None). rewrite size_map. by exists n. }
    revert Hf.
    rewrite !(nth_map (forward (left s)) None) // H.
    unfold switching_left; case_if.
Qed.

Definition iso_path_switching_left (F G : graph_left) (h : F ≃l G) (s t : F) :
  Simpl_upath switching_left s t -> Simpl_upath switching_left (h s) (h t) :=
  fun sp => let (p, P) := sp in {| upval := iso_path h p; upvalK := iso_path_switching_leftK h P |}.

Lemma iso_correct (F G : graph_left) : F ≃l G -> correct G -> correct F.
Proof.
  intros h [A C]; split.
  - intros ? ?.
    apply (@iso_path_switching_inj _ _ h).
    rewrite iso_path_nil.
    apply A.
  - intros u v. destruct (C (h u) (h v)) as [p _].
    set h' := iso_left_sym h.
    rewrite -(bijK' h' u) -(bijK' h' v).
    by exists (iso_path_switching_left h' p).
Qed.


(** Isomorphism between graph_data *)
Set Primitive Projections.
Record iso_data (F G: graph_data) := Iso_order {
  iso_left_of :> iso_left F G;
  order_iso: order G = [seq iso_left_of v | v <- order F] }.
Unset Primitive Projections.
Infix "≃d" := iso_data (at level 79).

Definition iso_data_id G : G ≃d G.
Proof. exists (@iso_left_id G). symmetry; by apply map_id. Defined.

Definition iso_data_sym F G : F ≃d G -> G ≃d F.
Proof.
  move => f.
  exists (iso_left_sym f).
  rewrite -(map_id (order F)) (order_iso f) -map_comp /=.
  apply eq_map => v /=.
  symmetry; apply (bijK).
Defined.

Definition iso_data_comp F G H : F ≃d G -> G ≃d H -> F ≃d H.
Proof.
  move => f g.
  exists (iso_left_comp f g).
  by rewrite (order_iso g) (order_iso f) -map_comp.
Defined.

Global Instance iso_data_Equivalence: CEquivalence iso_data.
Proof. constructor. exact @iso_data_id. exact @iso_data_sym. exact @iso_data_comp. Defined.

Lemma p_deg_iso (F G : graph_data) : F ≃ G -> proper_degree G -> proper_degree F.
Proof.
  intros h H b v.
  specialize (H b (h v)).
  rewrite ->vlabel_iso in H. rewrite -H.
Abort.
(* TODO proper degr dans base graph + idem ce lemma *)
Lemma p_left_iso (F G : graph_data) : F ≃l G -> proper_left G -> proper_left F.
Proof.
  intros h H v Hl.
Abort. (* TODO pour ça il faut left egal aussi sur les tens ... -> faire un 2e iso left, qui implique le 1er ?*)

Lemma p_order_iso F G : F ≃d G -> proper_order G -> proper_order F.
Proof.
  intros h [In U].
  split.
  - intro v.
    specialize (In (h v)). rewrite ->vlabel_iso in In.
    symmetry; symmetry in In. apply (@iff_stepl _ _ _ In).
    by rewrite (order_iso h) mem_map.
  - by rewrite (order_iso h) map_inj_uniq in U.
Qed.
(* TODO lemma F iso G -> F : proper_ -> G : proper_ pour geos et ps *)


(** * Basic operations respecting correctness *)
(** Making the disjoint union and adding an edge from the first graph to the second *)
Definition union_edge_graph {Lv Le : Type} (G0 G1 : graph Lv Le) (x : G0) (y : G1) (A : Le) : graph Lv Le :=
  (G0 ⊎ G1) ∔ [inl x, A, inr y].

Definition union_edge_left (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  union_edge_graph x y A -> edge (union_edge_graph x y A) :=
  fun v => Some (match v with
  | inl v => inl (left v)
  | inr v => inr (left v)
  end).

Definition union_edge_graph_left (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) : graph_left := {|
  graph_of := union_edge_graph x y A;
  left := @union_edge_left _ _ _ _ _;
  |}.

Lemma union_edge_switching_0 (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  (fun e : edge (union_edge_graph_left x y A) * bool => switching e.1) \o
  (fun x : edge G0 * bool => (Some (inl x.1), x.2)) =1 fun e => Some (option_map inl (switching e.1)).
Proof. intros (?, ?). unfold switching; cbn. case_if. Qed.

Lemma union_edge_switching_1 (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  (fun e : edge (union_edge_graph_left x y A) * bool => switching e.1) \o
  (fun x : edge G1 * bool => (Some (inr x.1), x.2)) =1 fun e => Some (option_map inr (switching e.1)).
Proof. intros (?, ?). unfold switching; cbn. case_if. Qed.

Lemma union_edge_switching_left_0 (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  (fun e : edge (union_edge_graph_left x y A) * bool => switching_left e.1) \o
  (fun x : edge G0 * bool => (Some (inl x.1), x.2)) =1
  fun e => option_map Some (option_map inl (switching_left e.1)).
Proof. intros (?, ?). unfold switching_left; cbn. case_if. Qed.

Lemma union_edge_switching_left_1 (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  (fun e : edge (union_edge_graph_left x y A) * bool => switching_left e.1) \o
  (fun x : edge G1 * bool => (Some (inr x.1), x.2)) =1
  fun e => option_map Some (option_map inr (switching_left e.1)).
Proof. intros (?, ?). unfold switching_left; cbn. case_if. Qed.

Lemma union_edge_lrN (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall p u v, simpl_upath (@switching (union_edge_graph_left x y A)) (inl u) (inr v) p ->
  forward None \in p.
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => u v /andP[/andP[/eqP ? _] _]. }
  rewrite /simpl_upath cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]].
  destruct e as [[e | e] | ]; [ | by destruct b | by destruct b].
  enough (forward None \in p) by caseb.
  destruct (utarget (Some (inl e) : edge (union_edge_graph_left x y A), b)) as [w | w] eqn:Hw; try by [].
  apply (Hp w v).
  splitb. by rewrite -Hw.
Qed.

Lemma union_edge_Nlr (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall (p : upath) (u v : union_edge_graph_left x y A), simpl_upath switching u v p ->
  forward None \in p -> (exists u' v', u = inl u' /\ v = inr v').
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => *. }
  rewrite /simpl_upath cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]] /orP[/andP[/eqP He /eqP Hb] | H].
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | v]; cbn.
    2:{ by exists x, v. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (Hin : forward None \in upath_rev p).
    { apply (@union_edge_lrN _ _ _ _ _ _ v y), upath_revK. splitb. }
    rewrite (upath_rev_in p) in Hin.
    by rewrite (map_f _ Hin).
  - assert (Hs : simpl_upath switching (utarget (e, b)) v p) by splitb.
    specialize (Hp _ _ Hs H); clear Hs. destruct Hp as [u' [v' [Hu ->]]].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u, v'. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (e = None) as -> by by destruct e as [[e | e] | ].
    assert (H' : forward None \in p) by by [].
    apply (map_f (fun x => switching x.1) H').
Qed.

Lemma union_edge_Nrl (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall (p : upath) (u v : union_edge_graph_left x y A), simpl_upath switching u v p ->
  backward None \in p -> exists u' v', u = inr u' /\ v = inl v'.
Proof.
  intros p ? ? P ?.
  assert (Hin : forward None \in upath_rev p) by by rewrite (upath_rev_in p).
  destruct (union_edge_Nlr (upath_revK P) Hin) as [u' [v' [-> ->]]].
  by exists v', u'.
Qed.

Lemma union_edge_ll (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall p u v, simpl_upath (@switching (union_edge_graph_left x y A)) (inl u) (inl v) p ->
  { q : upath | simpl_upath switching u v q & p = [seq (Some (inl x.1), x.2) | x <- q] }.
Proof.
  intros p u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn /negP. move => /existsP [[] N].
    - by destruct (union_edge_Nlr P N) as [u' [v' [Hu Hv]]].
    - by destruct (union_edge_Nrl P N) as [u' [v' [Hu Hv]]]. }
  revert P; move => /andP[/andP[W U] N].
  revert u v W U N Hin. induction p as [ | [[[e | e] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hin.
    assert (Ht : forall b : bool_eqType, (None, b) \notin p).
    { apply /existsPn /negP. move => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP; rewrite negb_involutive.
      caseb. }
    specialize (IH _ _ W U1 N1 Ht). destruct IH as [p' P' Hp]. subst p.
    exists ((e, b) :: p').
    + revert P'. unfold simpl_upath; cbn. move => /andP[/andP[W' U'] N'].
      splitb.
      * revert w. move => /eqP. by cbn.
      * clear - U0.
        rewrite -map_comp (eq_map (union_edge_switching_0 x y A) p') in U0.
        assert (He : switching (Some (inl e) : edge (union_edge_graph_left x y A)) =
          Some (option_map inl (switching e))).
        { replace e with ((forward e).1) by trivial. by rewrite -union_edge_switching_0. }
        rewrite He map_comp mem_map // map_comp mem_map // in U0.
        intros [a | ] [b | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
    + by rewrite map_cons.
  - by [].
  - move => ? ? ? ? ? Hf; clear - Hf.
    specialize (Hf b). contradict Hf; apply /negP.
    rewrite in_cons negb_involutive.
    caseb.
Qed.

Lemma union_edge_rr (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall p u v, simpl_upath (@switching (union_edge_graph_left x y A)) (inr u) (inr v) p ->
  { p' : upath | simpl_upath switching u v p' & p = [seq (Some (inr x.1), x.2) | x <- p'] }.
Proof.
  intros p u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn /negP. move => /existsP [[] N].
    - by destruct (union_edge_Nlr P N) as [u' [v' [Hu Hv]]].
    - by destruct (union_edge_Nrl P N) as [u' [v' [Hu Hv]]]. }
  revert P; move => /andP[/andP[W U] N].
  revert u v W U N Hin. induction p as [ | [[[e | e] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - by [].
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hin.
    assert (Ht : forall b : bool_eqType, (None, b) \notin p).
    { apply /existsPn /negP. move => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP; rewrite negb_involutive.
      caseb. }
    specialize (IH _ _ W U1 N1 Ht). destruct IH as [p' P' Hp]. subst p.
    exists ((e, b) :: p').
    + revert P'. unfold simpl_upath; cbn. move => /andP[/andP[W' U'] N'].
      splitb.
      * revert w. move => /eqP. by cbn.
      * clear - U0.
        rewrite -map_comp (eq_map (union_edge_switching_1 x y A) p') in U0.
        assert (He : switching (Some (inr e) : edge (union_edge_graph_left x y A)) =
          Some (option_map inr (switching e))).
        { replace e with ((forward e).1) by trivial. by rewrite -(union_edge_switching_1 x y A). }
        rewrite He map_comp mem_map // map_comp mem_map // in U0.
        intros [a | ] [b | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
    + by rewrite map_cons.
  - move => ? ? ? ? ? Hf; clear - Hf.
    specialize (Hf b). contradict Hf; apply /negP.
    rewrite in_cons negb_involutive.
    caseb.
Qed. (* TODO gros copie collé, voir si on peut faire mieux *)

Lemma union_edge_to_ll (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall p u v, simpl_upath switching_left u v p ->
  simpl_upath (@switching_left (union_edge_graph_left x y A)) (inl u) (inl v) [seq (Some (inl x.1), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold simpl_upath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : simpl_upath switching_left (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH; move => /andP[/andP[W' U'] N'].
  splitb.
  + rewrite -map_comp (eq_map (union_edge_switching_left_0 x y A) p).
    assert (switching_left (Some (inl e) : edge (union_edge_graph_left x y A)) =
      option_map Some (option_map inl (switching_left e))) as ->.
    { replace e with ((forward e).1) by trivial. by rewrite -union_edge_switching_left_0. }
    rewrite map_comp mem_map 1?map_comp 1?mem_map //.
    all: intros [a | ] [c | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
  + assert (Hd := union_edge_switching_left_0 x y A (forward e)).
    revert Hd. move => /eqP Hd. cbn in Hd. revert Hd. move => /eqP ->.
    by destruct (switching_left e).
Qed.

Lemma union_edge_to_rr (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall p u v, simpl_upath switching_left u v p ->
  simpl_upath (@switching_left (union_edge_graph_left x y A)) (inr u) (inr v) [seq (Some (inr x.1), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold simpl_upath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : simpl_upath switching_left (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH; move => /andP[/andP[W' U'] N'].
  splitb.
  + rewrite -map_comp (eq_map (union_edge_switching_left_1 x y A) p).
    assert (switching_left (Some (inr e) : edge (union_edge_graph_left x y A)) =
      option_map Some (option_map inr (switching_left e))) as ->.
    { replace e with ((forward e).1) by trivial. by rewrite -union_edge_switching_left_1. }
    rewrite map_comp mem_map 1?map_comp 1?mem_map //.
    all: intros [a | ] [c | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
  + assert (Hd := union_edge_switching_left_1 x y A (forward e)).
    revert Hd. move => /eqP Hd. cbn in Hd. revert Hd. move => /eqP ->.
    by destruct (switching_left e).
Qed. (* TODO gros copie collé, voir si on peut faire mieux *)

Lemma union_edge_to_lr (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  uconnected (@switching_left G0) -> uconnected (@switching_left G1) ->
  forall u v, exists _ :
  Simpl_upath (@switching_left (union_edge_graph_left x y A)) (inl u) (inr v), true.
Proof.
  move => C0 C1 u v.
  destruct (C0 u x) as [[p0 P0] _].
  assert (Q0 := union_edge_to_ll x y A P0).
  set q0 : @upath _ _ (union_edge_graph_left x y A) := [seq (Some (inl x.1), x.2) | x <- p0].
  destruct (C1 y v) as [[p1 P1] _].
  assert (Q1 := union_edge_to_rr x y A P1).
  set q1 : @upath _ _ (union_edge_graph_left x y A) := [seq (Some (inr x.1), x.2) | x <- p1].
  set qn : @upath _ _ (union_edge_graph_left x y A) := [:: forward None].
  assert (Qn : simpl_upath (@switching_left (union_edge_graph_left x y A)) (inl x) (inr y) qn).
  { unfold simpl_upath; cbn. repeat (apply /andP; split); trivial.
    rewrite mem_seq1 /switching_left; cbn. case_if. }
  set L := {| upval := q0 ; upvalK := Q0 |};
  set R := {| upval := q1 ; upvalK := Q1 |};
  set N := {| upval := qn ; upvalK := Qn |}.
  assert (Some None \notin [seq switching_left x0.1 | x0 <- q0] /\
    Some None \notin [seq switching_left x0.1 | x0 <- q1]) as [? ?].
  { rewrite /q0 /q1 -2!map_comp (eq_map (union_edge_switching_left_0 x y A))
      (eq_map (union_edge_switching_left_1 x y A)).
    split; apply /mapP; intros [(?, ?) _ Heq].
    all: contradict Heq.
    all: unfold switching_left; case_if. }
  assert (None \notin [seq switching_left x0.1 | x0 <- q0] /\
    None \notin [seq switching_left x0.1 | x0 <- q1]) as [? ?].
  { split; apply /negP; intro Hf;
    [clear - Hf Q0; revert Q0; move => /andP[/andP[_ _] Hc]
    | clear - Hf Q1; revert Q1; move => /andP[/andP[_ _] Hc]].
    all: contradict Hf; by apply /negP. }
  assert (disjoint_upaths switching_left N L /\ disjoint_upaths switching_left N R) as [Dl Dr].
  { split; apply /disjointP; intros [[e | ] | ]; cbn.
    all: try (move => _; by apply /negP).
    all: move => Hf _; revert Hf; rewrite mem_seq1 /switching_left; cbn.
    all: case_if. }
    rewrite /disjoint_upaths disjoint_sym in Dl.
  assert (D : disjoint_upaths switching_left (upath_cat Dl) R).
  { rewrite /disjoint_upaths /upath_cat /= map_cat disjoint_cat. splitb.
    apply /disjointP. intros [[[e | e] | ] | ]; cbn.
    - move => _; apply /negP.
      rewrite /q1 -map_comp (eq_map (union_edge_switching_left_1 x y A)).
      apply /mapP. intros [(?, ?) _ Heq]. contradict Heq.
      unfold switching_left. case_if.
    - move => Hf _; revert Hf; apply /negP.
      rewrite /q0 -map_comp (eq_map (union_edge_switching_left_0 x y A)).
      apply /mapP. intros [(?, ?) _ Heq]. contradict Heq.
      unfold switching_left. case_if.
    - move => _; by apply /negP.
    - move => _; by apply /negP. }
  by exists (upath_cat D).
Qed.

Lemma union_edge_to_rl (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  uconnected (@switching_left G0) -> uconnected (@switching_left G1) ->
  forall u v, exists _ : Simpl_upath (@switching_left (union_edge_graph_left x y A)) (inr u) (inl v), true.
Proof.
  intros C0 C1 u v.
  destruct (union_edge_to_lr x y A C0 C1 v u) as [p _].
  by exists (upath_revS p).
Qed.

Lemma union_edge_correct (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  correct G0 -> correct G1 -> correct (union_edge_graph_left x y A).
Proof.
  intros [A0 C0] [A1 C1]. split.
  - intros [u | u] p; apply /eqP; cbn; apply /eqP.
    + destruct (union_edge_ll (upvalK p)) as [q Q Heq].
      rewrite Heq.
      enough (q = nil) as -> by trivial.
      assert (Hf := A0 u {| upval := q ; upvalK := Q |}).
      by revert Hf; move => /eqP; cbn; move => /eqP ->.
    + destruct (union_edge_rr (upvalK p)) as [q Q Heq].
      rewrite Heq.
      enough (q = nil) as -> by trivial.
      assert (Hf := A1 u {| upval := q ; upvalK := Q |}).
      by revert Hf; move => /eqP; cbn; move => /eqP ->.
  - intros [u | u] [v | v].
    + destruct (C0 u v) as [[p P] _].
      by exists {| upval := [seq (Some (inl x.1), x.2) | x <- p] : @upath _ _ (union_edge_graph_left x y A) ;
        upvalK := (union_edge_to_ll x y A P) |}.
    + by apply union_edge_to_lr.
    + by apply union_edge_to_rl.
    + destruct (C1 u v) as [[p P] _].
      by exists {| upval := [seq (Some (inr x.1), x.2) | x <- p] : @upath _ _ (union_edge_graph_left x y A) ;
        upvalK := (union_edge_to_rr x y A P) |}.
Qed.


(** Adding a non-parr node below a vertex *)
Definition add_concl_graph {Lv Le : Type} (G : graph Lv Le) (x : G) (R : Lv) (A : Le) : graph Lv Le :=
  G ∔ R ∔ [inl x, A, inr tt].

Definition add_concl_left (G : graph_left) (x : G) (R : rule) (A : formula) :
  add_concl_graph x R A -> edge (add_concl_graph x R A) :=
  fun u => match u with
  | inl u => Some (inl (left u))
  | inr _ => None
  end.

Definition add_concl_graph_left (G : graph_left) (x : G) (R : rule) (A : formula) : graph_left := {|
  graph_of := add_concl_graph x R A;
  left := @add_concl_left _ _ _ _;
  |}.


Lemma add_concl_switching (G : graph_left) (x : G) (R : rule) (A : formula) :
  (fun e : edge (add_concl_graph_left x R A) * bool => switching e.1) \o
  (fun e : edge G * bool => (Some (inl e.1), e.2)) =1
  fun e => Some (option_map inl (switching e.1)).
Proof. intros (?, ?). unfold switching; cbn. case_if. Qed.

Lemma add_concl_switching_left (G : graph_left) (x : G) (R : rule) (A : formula) :
  (fun e : edge (add_concl_graph_left x R A) * bool => switching_left e.1) \o
  (fun e : edge G * bool => (Some (inl e.1), e.2)) =1
  fun e => option_map Some (option_map inl (switching_left e.1)).
Proof. intros (?, ?). unfold switching_left; cbn. case_if. Qed.

Lemma add_concl_lrN (G : graph_left) (x : G) (R : rule) (A : formula)
  {I : eqType} (f : edge (add_concl_graph_left x R A) -> option I) :
  forall p u, simpl_upath f (inl u) (inr tt) p ->
  forward None \in p.
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => u /andP[/andP[/eqP ? _] _]. }
  rewrite /simpl_upath cons_uniq in_cons.
  move => u /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]].
  destruct e as [[e | []] | ]; [ | by destruct b].
  enough (forward None \in p) by caseb.
  destruct (utarget (Some (inl e) : edge (add_concl_graph_left x R A), b)) as [w | w] eqn:Hw; try by [].
  apply (Hp w).
  splitb. by rewrite -Hw. 
Qed.

Lemma add_concl_Nlr (G : graph_left) (x : G) (R : rule) (A : formula)
  {I : finType} (f : edge (add_concl_graph_left x R A) -> option I) :
  forall (p : upath) (u v : add_concl_graph_left x R A), simpl_upath f u v p ->
  forward None \in p -> (exists u', u = inl u' /\ v = inr tt).
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => *. }
  rewrite /simpl_upath cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]] /orP[/andP[/eqP He /eqP Hb] | H].
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | []]; cbn.
    2:{ by exists x. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (Hin : forward None \in upath_rev p).
    { apply (@add_concl_lrN _ _ _ _ _ f _ v), upath_revK. splitb. }
    rewrite (upath_rev_in p) in Hin.
    by rewrite (map_f _ Hin).
  - assert (Hs : simpl_upath f (utarget (e, b)) v p) by splitb.
    specialize (Hp _ _ Hs H); clear Hs. destruct Hp as [u' [Hu ->]].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (e = None) as -> by by destruct e as [[e | e] | ].
    assert (H' : forward None \in p) by by [].
    apply (map_f (fun x => f x.1) H').
Qed.

Lemma add_concl_Nrl (G : graph_left) (x : G) (R : rule) (A : formula)
  {I : finType} (f : edge (add_concl_graph_left x R A) -> option I) :
  forall (p : upath) (u v : add_concl_graph_left x R A), simpl_upath f u v p ->
  backward None \in p -> exists v', u = inr tt /\ v = inl v'.
Proof.
  intros p ? ? P ?.
  assert (Hin : forward None \in upath_rev p) by by rewrite (upath_rev_in p).
  destruct (add_concl_Nlr (upath_revK P) Hin) as [u' [-> ->]].
  by exists u'.
Qed.

Lemma add_concl_ll (G : graph_left) (x : G) (R : rule) (A : formula) :
  forall p u v, simpl_upath (@switching (add_concl_graph_left x R A)) (inl u) (inl v) p ->
  { q : upath | simpl_upath switching u v q & p = [seq (Some (inl x.1), x.2) | x <- q] }.
Proof.
  intros p u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn /negP; move => /existsP [[] ?];
    [destruct (add_concl_Nlr P) as [? [? ?]] | destruct (add_concl_Nrl P) as [? [? ?]]];
    caseb. }
  revert P; move => /andP[/andP[W U] N].
  revert u v W U N Hin. induction p as [ | [[[e | []] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hin.
    assert (Hin' : forall b, (None, b) \notin p).
    { apply /existsPn /negP; move => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP; rewrite negb_involutive; caseb. }
    specialize (IH _ _ W U1 N1 Hin). destruct IH as [p' P' Hp]. subst p.
    exists ((e, b) :: p').
    + revert P'. unfold simpl_upath; cbn. move => /andP[/andP[W' U'] N'].
      splitb.
      * revert w. move => /eqP. by cbn.
      * clear - U0.
        rewrite -map_comp (eq_map (add_concl_switching x R A) p') in U0.
        assert (He : switching (Some (inl e) : edge (add_concl_graph_left x R A)) =
          Some (option_map inl (switching e))).
        { replace e with ((forward e).1) by trivial. by rewrite -add_concl_switching. }
        rewrite He map_comp mem_map // map_comp mem_map // in U0.
        intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
    + by rewrite map_cons.
  - move => ? ? ? ? ? Hf; clear - Hf.
    specialize (Hf b). contradict Hf; apply /negP.
    rewrite in_cons negb_involutive.
    caseb.
Qed.

Lemma add_concl_rr (G : graph_left) (x : G) (R : rule) (A : formula) :
  forall p, simpl_upath (@switching (add_concl_graph_left x R A)) (inr tt) (inr tt) p ->
  p = nil.
Proof.
  intro p; destruct p as [ | (e, b) p]; trivial; unfold simpl_upath; cbn.
  move => /andP[/andP[/andP[/eqP w W] /andP[U0 U1]] /norP[/eqP N0 N1]].
  assert (P : simpl_upath (@switching (add_concl_graph_left x R A)) (utarget (e, b)) (inr tt) p)
    by splitb.
  destruct e as [[e | []] | ], b; try by []; cbn in P.
  contradict U0; apply /negP; rewrite negb_involutive.
  apply (map_f (fun e => switching e.1) (add_concl_lrN P)).
Qed.

Lemma add_concl_to_ll (G : graph_left) (x : G) (R : rule) (A : formula) :
  forall p u v, simpl_upath switching_left u v p ->
  simpl_upath (@switching_left (add_concl_graph_left x R A)) (inl u) (inl v)
    [seq (Some (inl x.1), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold simpl_upath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : simpl_upath switching_left (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH; move => /andP[/andP[W' U'] N'].
  splitb.
  + rewrite -map_comp (eq_map (add_concl_switching_left _ _ _) p).
    assert (Hs : switching_left (Some (inl e) : edge (add_concl_graph_left x R A)) =
      option_map Some (option_map inl (switching_left e))).
    { replace e with ((forward e).1) by trivial. by rewrite -add_concl_switching_left. }
    rewrite Hs map_comp mem_map 1?map_comp 1?mem_map //.
    all: intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
  + assert (Hd := add_concl_switching_left x R A (forward e)).
    revert Hd. move => /eqP Hd. cbn in Hd. revert Hd. move => /eqP ->.
    by destruct (switching_left e).
Qed.

Lemma add_concl_to_lr (G : graph_left) (x : G) (R : rule) (A : formula) :
  R <> ⅋ -> uconnected (@switching_left G) -> forall u, exists _ :
  Simpl_upath (@switching_left (add_concl_graph_left x R A)) (inl u) (inr tt), true.
Proof.
  move => HR C u.
  destruct (C u x) as [[p P] _].
  assert (Q := add_concl_to_ll x R A P).
  set q : @upath _ _ (add_concl_graph_left x R A) := [seq (Some (inl x.1), x.2) | x <- p].
  set qn : @upath _ _ (add_concl_graph_left x R A) := [:: forward None].
  assert (Qn : simpl_upath (@switching_left (add_concl_graph_left x R A)) (inl x) (inr tt) qn).
  { unfold simpl_upath; cbn. repeat (apply /andP; split); trivial.
    rewrite in_cons in_nil. apply /norP; split; trivial.
    unfold switching_left. case_if.
    contradict HR. apply /eqP. cbn. by apply /eqP. }
  set L := {| upval := q ; upvalK := Q |};
  set N := {| upval := qn ; upvalK := Qn |}.
  assert (D : disjoint_upaths switching_left L N).
  { apply /disjointP; intros [[[e | []] | ] | ]; cbn.
    - move => _; apply /negP.
      rewrite in_cons in_nil. apply /norP; split; trivial.
      unfold switching_left. case_if.
    - move => Hf _; revert Hf; apply /negP.
      rewrite /q -map_comp (eq_map (add_concl_switching_left _ _ _)).
      apply /mapP; intros [(?, ?) _ Heq]. contradict Heq.
      unfold switching_left; case_if.
    - move => _; apply /negP.
      rewrite in_cons in_nil. apply /norP; split; trivial.
      unfold switching_left. case_if.
      contradict HR. apply /eqP. cbn. by apply /eqP. }
  by exists (upath_cat D).
Qed.

Lemma add_concl_to_rl (G : graph_left) (x : G) (R : rule) (A : formula) :
  R <> ⅋ -> uconnected (@switching_left G) -> forall v, exists _ :
  Simpl_upath (@switching_left (add_concl_graph_left x R A)) (inr tt) (inl v), true.
Proof.
  intros HR C u.
  destruct (add_concl_to_lr x A HR C u) as [p _].
  by exists (upath_revS p).
Qed.

Lemma add_concl_correct (G : graph_left) (x : G) (R : rule) (F : formula) :
  R <> ⅋ -> correct G -> correct (add_concl_graph_left x R F).
Proof.
  intros HR [A C]. split.
  - intros [u | []] p; apply /eqP; cbn; apply /eqP.
    + destruct (add_concl_ll (upvalK p)) as [q Q Heq].
      rewrite Heq.
      enough (q = nil) as -> by trivial.
      assert (Hf := A u {| upval := q ; upvalK := Q |}).
      by revert Hf; move => /eqP; cbn; move => /eqP ->.
    + apply (add_concl_rr (upvalK p)).
  - intros [u | []] [v | []].
    + destruct (C u v) as [[p P] _].
      by exists {| upval := [seq (Some (inl x.1), x.2) | x <- p] : @upath _ _ (add_concl_graph_left x R F) ;
        upvalK := (add_concl_to_ll _ _ _ P) |}.
    + by apply add_concl_to_lr.
    + by apply add_concl_to_rl.
    + by exists (upath_nil switching_left (inr tt : add_concl_graph_left x R F)).
Qed.

Lemma rem_concl_to_ll (G : graph_left) (x : G) (R : rule) (A : formula) :
  forall p u v, simpl_upath switching u v p ->
  simpl_upath (@switching (add_concl_graph_left x R A)) (inl u) (inl v)
    [seq (Some (inl x.1), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold simpl_upath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : simpl_upath switching (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH; move => /andP[/andP[W' U'] N'].
  splitb.
  rewrite -map_comp (eq_map (add_concl_switching _ _ _) p).
  assert (Hs : switching (Some (inl e) : edge (add_concl_graph_left x R A)) =
    Some (option_map inl (switching e))).
  { replace e with ((forward e).1) by trivial. by rewrite -add_concl_switching. }
  rewrite Hs map_comp mem_map 1?map_comp 1?mem_map //.
  all: intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
Qed.

Lemma rem_concl_ll (G : graph_left) (x : G) (R : rule) (A : formula) :
  forall p u v, simpl_upath (@switching_left (add_concl_graph_left x R A)) (inl u) (inl v) p ->
  { q : upath | simpl_upath switching_left u v q & p = [seq (Some (inl x.1), x.2) | x <- q] }.
Proof.
  intros p u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn /negP; move => /existsP [[] ?];
    [destruct (add_concl_Nlr P) as [? [? ?]] | destruct (add_concl_Nrl P) as [? [? ?]]];
    caseb. }
  revert P; move => /andP[/andP[W U] N].
  revert u v W U N Hin. induction p as [ | [[[e | []] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hin.
    assert (Hin' : forall b, (None, b) \notin p).
    { apply /existsPn /negP; move => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP; rewrite negb_involutive; caseb. }
    specialize (IH _ _ W U1 N1 Hin). destruct IH as [p' P' Hp]. subst p.
    exists ((e, b) :: p').
    + revert P'. unfold simpl_upath; cbn. move => /andP[/andP[W' U'] N'].
      splitb.
      * revert w. move => /eqP. by cbn.
      * clear - U0.
        rewrite -map_comp (eq_map (add_concl_switching_left x R A) p') in U0.
        assert (He : switching_left (Some (inl e) : edge (add_concl_graph_left x R A)) =
          option_map Some (option_map inl (switching_left e))).
        { replace e with ((forward e).1) by trivial. by rewrite -add_concl_switching_left. }
        rewrite He 2?map_comp 2?mem_map // in U0.
        all: intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
      * assert (Hr : switching_left (Some (inl e) : edge (add_concl_graph_left x R A)) =
          ((fun f : edge (add_concl_graph_left x R A) * _ => switching_left f.1) \o
          (fun f => (Some (inl f.1), f.2))) (forward e)) by by [].
        rewrite Hr add_concl_switching_left /= in N0.
        by destruct (switching_left e).
    + by rewrite map_cons.
  - move => ? ? ? ? ? Hf; clear - Hf.
    specialize (Hf b). contradict Hf; apply /negP.
    rewrite in_cons negb_involutive.
    caseb.
Qed.

Lemma rem_concl_correct (G : graph_left) (x : G) (R : rule) (F : formula) :
  correct (add_concl_graph_left x R F) -> correct G.
Proof.
  intros [A C]. split.
  - intros u p; apply /eqP; cbn; apply /eqP.
    assert (H := rem_concl_to_ll x R F (upvalK p)).
    specialize (A _ {| upval := [seq (Some (inl e.1) : edge (add_concl_graph_left x R F), e.2)
      | e <- upval p] ; upvalK := H |}).
  revert A; move => /eqP; cbn; move => /eqP A.
  clear - A; by induction (upval p).
  - intros u v.
    specialize (C (inl u) (inl v)). destruct C as [p _].
    destruct (rem_concl_ll (upvalK p)) as [q Q _].
    by exists {| upval := q ; upvalK := Q |}.
Qed.


(** Adding a parr below 2 vertices *)
Definition add_parr_graph (G : base_graph) (vl vr : G) (Al Ar : formula) : base_graph :=
  G ∔ ⅋ ∔ [inl vl, Al, inr tt] ∔ [inl vr, Ar, inr tt].

Definition add_parr_left (G : graph_left) (vl vr : G) (Al Ar : formula) :
  add_parr_graph vl vr Al Ar -> edge (add_parr_graph vl vr Al Ar) :=
  fun u => match u with
  | inl u => Some (Some (inl (left u)))
  | inr _ => Some None
  end.

Definition add_parr_graph_left (G : graph_left) (vl vr : G) (Al Ar : formula) : graph_left := {|
  graph_of := add_parr_graph vl vr Al Ar;
  left := @add_parr_left _ _ _ _ _;
  |}.

Lemma add_parr_switching (G : graph_left) (vl vr : G) (Al Ar : formula) :
  (fun e : edge (add_parr_graph_left vl vr Al Ar) * bool => switching e.1) \o
  (fun x : edge G * bool => (Some (Some (inl x.1)), x.2)) =1
  fun e => Some (Some (option_map inl (switching e.1))).
Proof. intros (?, ?). unfold switching; cbn. case_if. Qed.

Lemma add_parr_switching_left (G : graph_left) (vl vr : G) (Al Ar : formula) :
  (fun e : edge (add_parr_graph_left vl vr Al Ar) * bool => switching_left e.1) \o
  (fun x : edge G * bool => (Some (Some (inl x.1)), x.2)) =1
  fun e => option_map (Some \o Some) (option_map inl (switching_left e.1)).
Proof. intros (?, ?). unfold switching_left; cbn. case_if. Qed.

Lemma add_parr_lrN (G : graph_left) (vl vr : G) (Al Ar : formula) :
  forall p u, simpl_upath (@switching (add_parr_graph_left vl vr Al Ar)) (inl u) (inr tt) p ->
  forward None \in p \/ forward (Some None) \in p.
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => u /andP[/andP[/eqP ? _] _]. }
  rewrite /simpl_upath cons_uniq in_cons.
  move => u /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]].
  destruct e as [[[e | []] | ] | ]; [ | destruct b; caseb | destruct b; caseb].
  enough (forward None \in p \/ forward (Some None) \in p) by caseb.
  destruct (utarget (Some (Some (inl e)) : edge (add_parr_graph_left vl vr Al Ar), b)) as [w | w] eqn:Hw; try by [].
  apply (Hp w).
  splitb. by rewrite -Hw.
Qed.

Lemma add_parr_Nlr (G : graph_left) (vl vr : G) (Al Ar : formula) :
  forall (p : upath) (u v : add_parr_graph_left vl vr Al Ar), simpl_upath switching u v p ->
  forward None \in p \/ forward (Some None) \in p -> (exists u', u = inl u' /\ v = inr tt).
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => ? ? ? [? | ?]. }
  rewrite /simpl_upath cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]]
    [/orP[/andP[/eqP He /eqP Hb] | H] | /orP[/andP[/eqP He /eqP Hb] | H]].
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | []]; cbn.
    2:{ by exists vr. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
    { apply (@add_parr_lrN _ _ _ _ _ _ v), upath_revK. splitb. }
    rewrite 2!(upath_rev_in p) in Hin.
    destruct Hin as [Hin | Hin];
    by rewrite (map_f _ Hin).
  - assert (Hs : simpl_upath switching (utarget (e, b)) v p) by splitb.
    specialize (Hp _ _ Hs); clear Hs. destruct Hp as [u' [Hu ->]]; [caseb | ].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (H' : forward None \in p) by by [].
    destruct e as [[[e | []] | ] | ]; try by [].
    all: apply (map_f (fun x => switching x.1) H').
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | []]; cbn.
    2:{ by exists vl. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
    { apply (@add_parr_lrN _ _ _ _ _ _ v), upath_revK. splitb. }
    rewrite 2!(upath_rev_in p) in Hin.
    destruct Hin as [Hin | Hin];
    by rewrite (map_f _ Hin).
  - assert (Hs : simpl_upath switching (utarget (e, b)) v p) by splitb.
    specialize (Hp _ _ Hs); clear Hs. destruct Hp as [u' [Hu ->]]; [caseb | ].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (H' : forward (Some None) \in p) by by [].
    destruct e as [[[e | []] | ] | ]; try by [].
    all: apply (map_f (fun x => switching x.1) H').
Qed.

Lemma add_parr_Nrl (G : graph_left) (vl vr : G) (Al Ar : formula) :
  forall (p : upath) (u v : add_parr_graph_left vl vr Al Ar), simpl_upath switching u v p ->
  backward None \in p \/ backward (Some None) \in p -> exists v', u = inr tt /\ v = inl v'.
Proof.
  intros p ? ? P Hn.
  assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
  { rewrite !(upath_rev_in p). destruct Hn; caseb. }
  destruct (add_parr_Nlr (upath_revK P) Hin) as [u' [-> ->]].
  by exists u'.
Qed.

Lemma add_parr_ll (G : graph_left) (vl vr : G) (Al Ar : formula) :
  forall p u v, simpl_upath (@switching (add_parr_graph_left vl vr Al Ar)) (inl u) (inl v) p ->
  { q : upath | simpl_upath switching u v q & p = [seq (Some (Some (inl x.1)), x.2) | x <- q] }.
Proof.
  intros p u v P.
  assert ((forall b, (None, b) \notin p) /\ forall b, (Some None, b) \notin p) as [Hinn Hinsn].
  { split.
    all: apply /existsPn /negP; move => /existsP [[] ?];
      [destruct (add_parr_Nlr P) as [? [? ?]] | destruct (add_parr_Nrl P) as [? [? ?]]];
      caseb. }
  revert P; move => /andP[/andP[W U] N].
  revert u v W U N Hinn Hinsn. induction p as [ | [[[[e | []] | ] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hinn Hinsn.
    assert ((forall b, (None, b) \notin p) /\ forall b, (Some None, b) \notin p) as [Hinn' Hinsn'].
    { split; apply /existsPn /negP; move => /existsP [bf Hf].
      - specialize (Hinn bf); contradict Hinn; apply /negP; rewrite negb_involutive; caseb.
      - specialize (Hinsn bf); contradict Hinsn; apply /negP; rewrite negb_involutive; caseb. }
    specialize (IH _ _ W U1 N1 Hinn' Hinsn'). destruct IH as [p' P' Hp]. subst p.
    exists ((e, b) :: p').
    + revert P'. unfold simpl_upath; cbn. move => /andP[/andP[W' U'] N'].
      splitb.
      * revert w. move => /eqP. by cbn.
      * clear - U0.
        rewrite -map_comp (eq_map (add_parr_switching vl vr Al Ar) p') in U0.
        assert (He : switching (Some (Some (inl e)) : edge (add_parr_graph_left vl vr Al Ar)) =
          Some (Some (option_map inl (switching e)))).
        { replace e with ((forward e).1) by trivial. by rewrite -add_parr_switching. }
        rewrite He map_comp mem_map // map_comp mem_map // map_comp mem_map // in U0.
        intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
    + by rewrite map_cons.
  - move => ? ? ? ? ? ? Hf; clear - Hf.
    specialize (Hf b). contradict Hf; apply /negP.
    rewrite in_cons negb_involutive.
    caseb.
  - move => ? ? ? ? ? Hf; clear - Hf.
    specialize (Hf b). contradict Hf; apply /negP.
    rewrite in_cons negb_involutive.
    caseb.
Qed.

Lemma add_parr_rr (G : graph_left) (vl vr : G) (Al Ar : formula) :
  forall p, simpl_upath (@switching (add_parr_graph_left vl vr Al Ar)) (inr tt) (inr tt) p ->
  p = nil.
Proof.
  intro p; destruct p as [ | (e, b) p]; trivial; unfold simpl_upath; cbn.
  move => /andP[/andP[/andP[/eqP w W] /andP[U0 U1]] /norP[/eqP N0 N1]].
  assert (P : simpl_upath (@switching (add_parr_graph_left vl vr Al Ar)) (utarget (e, b)) (inr tt) p)
    by splitb.
  destruct e as [[[e | []] | ] | ], b; try by []; cbn in P.
  all: contradict U0; apply /negP; rewrite negb_involutive.
  all: destruct (add_parr_lrN P) as [Hin | Hin].
  all: apply (map_f (fun e => switching e.1) Hin).
Qed.

Lemma add_parr_to_ll (G : graph_left) (vl vr : G) (Al Ar : formula) :
  forall p u v, simpl_upath switching_left u v p ->
  simpl_upath (@switching_left (add_parr_graph_left vl vr Al Ar)) (inl u) (inl v)
    [seq (Some (Some (inl x.1)), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold simpl_upath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : simpl_upath switching_left (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH; move => /andP[/andP[W' U'] N'].
  splitb.
  + rewrite -map_comp (eq_map (add_parr_switching_left _ _ _ _) p).
    assert (Hs : switching_left (Some (Some (inl e)) : edge (add_parr_graph_left vl vr Al Ar)) =
      option_map (Some \o Some) (option_map inl (switching_left e))).
    { replace e with ((forward e).1) by trivial. by rewrite -add_parr_switching_left. }
    rewrite Hs map_comp mem_map 1?map_comp 1?mem_map //.
    all: intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
  + assert (Hd := add_parr_switching_left vl vr Al Ar (forward e)).
    revert Hd. move => /eqP Hd. cbn in Hd. revert Hd. move => /eqP ->.
    by destruct (switching_left e).
Qed.

Lemma add_parr_to_lr (G : graph_left) (vl vr : G) (Al Ar : formula) :
  uconnected (@switching_left G) -> forall u, exists _ :
  Simpl_upath (@switching_left (add_parr_graph_left vl vr Al Ar)) (inl u) (inr tt), true.
Proof.
  move => C u.
  destruct (C u vr) as [[p P] _].
  assert (Q := add_parr_to_ll vl vr Al Ar P).
  set q : @upath _ _ (add_parr_graph_left vl vr Al Ar) := [seq (Some (Some (inl x.1)), x.2) | x <- p].
  set qn : @upath _ _ (add_parr_graph_left vl vr Al Ar) := [:: forward None].
  assert (Qn : simpl_upath (@switching_left (add_parr_graph_left vl vr Al Ar)) (inl vr) (inr tt) qn).
  { unfold simpl_upath; cbn. splitb. }
  set L := {| upval := q ; upvalK := Q |};
  set N := {| upval := qn ; upvalK := Qn |}.
  assert (D : disjoint_upaths switching_left L N).
  { apply /disjointP; intros [[[e | ] | ] | ]; cbn.
    all: try (move => _; by apply /negP).
    move => Hf _; revert Hf; apply /negP.
    rewrite /q -map_comp (eq_map (add_parr_switching_left vl vr Al Ar)).
    apply /mapP; intros [(?, ?) _ Heq]. contradict Heq.
    unfold switching_left; case_if. }
  by exists (upath_cat D).
Qed.

Lemma add_parr_to_rl (G : graph_left) (vl vr : G) (Al Ar : formula) :
  uconnected (@switching_left G) -> forall v, exists _ :
  Simpl_upath (@switching_left (add_parr_graph_left vl vr Al Ar)) (inr tt) (inl v), true.
Proof.
  intros C u.
  destruct (add_parr_to_lr vl vr Al Ar C u) as [p _].
  by exists (upath_revS p).
Qed.

Lemma add_parr_correct (G : graph_left) (vl vr : G) (Al Ar : formula) :
  correct G -> correct (add_parr_graph_left vl vr Al Ar).
Proof.
  intros [A C]. split.
  - intros [u | []] p; apply /eqP; cbn; apply /eqP.
    + destruct (add_parr_ll (upvalK p)) as [q Q Heq].
      rewrite Heq.
      enough (q = nil) as -> by trivial.
      assert (Hf := A u {| upval := q ; upvalK := Q |}).
      by revert Hf; move => /eqP; cbn; move => /eqP ->.
    + apply (add_parr_rr (upvalK p)).
  - intros [u | []] [v | []].
    + destruct (C u v) as [[p P] _].
      by exists {| upval := [seq (Some (Some (inl x.1)), x.2) | x <- p] : @upath _ _ (add_parr_graph_left vl vr Al Ar) ;
        upvalK := (add_parr_to_ll _ _ _ _ P) |}.
    + by apply add_parr_to_lr.
    + by apply add_parr_to_rl.
    + by exists (upath_nil switching_left (inr tt : add_parr_graph_left vl vr Al Ar)).
Qed.


(** * Soundness of correctness *)
Lemma v_correct : correct v_graph_data.
Proof. split; intros []. Qed.


Lemma ax_correct (x : atom) : correct (ax_graph_left x).
Proof.
  split.
  - intros u [p P]; destruct_I3 u; apply /eqP; cbn; apply /eqP.
    all: destruct p as [ | [a [ | ]] [ | [b [ | ]] [ | [c [ | ]] p]]];
      try (destruct_I2 a); try (destruct_I2 b); try (destruct_I2 c);
      try by [].
    all: contradict P; apply /negP; cbn; caseb.
  - set fp : ps (ax_r x) -> ps (ax_r x) -> @upath _ _ (ps (ax_r x)) :=
      fun u v => match val u, val v with
      | 0, 1 => forward ord0 :: nil
      | 0, 2 => forward ord1 :: nil
      | 1, 0 => backward ord0 :: nil
      | 1, 2 => backward ord0 :: forward ord1 :: nil
      | 2, 0 => backward ord1 :: nil
      | 2, 1 => backward ord1 :: forward ord0 :: nil
      | _, _ => nil
      end.
    intros u v; set p := fp u v.
    assert (H : simpl_upath switching_left u v p) by by destruct_I3 u; destruct_I3 v.
    by exists {| upval := p; upvalK := H |}.
Qed.

(** * Stratum 5: Proof-nets *)
Set Primitive Projections.
Record proof_net : Type :=
  Proof_net {
    ps_of :> proof_structure;
    p_correct : correct ps_of;
  }.
Unset Primitive Projections.
(* TODO correctness + proof_net dans def strates *)

Lemma add_node_s0 (t : trilean) (G : base_graph) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  (inl (source e0)) \in ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)).
Proof. destruct H. rewrite !in_set; cbn. splitb. Qed.
Lemma add_node_s1 (t : trilean) (G : base_graph) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  (inl (source e1)) \in ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)).
Proof. destruct H. rewrite !in_set; cbn. splitb. Qed.

Definition add_node_iso_v_bij_fwd (t : trilean) (G : base_graph) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  @add_concl_graph _ _
    (@add_concl_graph _ _
      (add_node_graph t e0 e1) (Sub (inl (source e0)) (add_node_s0 _ H)) c (elabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ H))) c (elabel e1) ->
  add_node_graph_1 t e0 e1 :=
  fun v => match v with
  | inl (inl (exist u _)) => u
  | inl (inr tt)          => inl (target e0)
  | inr tt                => inl (target e1)
  end.

Definition add_node_iso_v_bij_bwd (t : trilean) (G : base_graph) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  add_node_graph_1 t e0 e1 ->
  @add_concl_graph _ _
    (@add_concl_graph _ _
      (add_node_graph t e0 e1) (Sub (inl (source e0)) (add_node_s0 _ H)) c (elabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ H))) c (elabel e1) :=
  fun v => if @boolP (v \in [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1))
  is AltTrue p then inl (inl (Sub v p)) else if v == inl (target e0) then inl (inr tt) else inr tt.

Lemma add_node_iso_v_bijK (t : trilean) (G : base_graph) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1))
  (H' : target e1 <> target e0) :
  cancel (@add_node_iso_v_bij_fwd t _ _ _ H) (@add_node_iso_v_bij_bwd t _ _ _ H).
Proof.
  intros [[[v V] | []] | []]; cbn; unfold add_node_iso_v_bij_bwd.
  - case: {-}_ /boolP => [? | ?].
    + apply /eqP; cbn; apply /eqP. by rewrite SubK.
    + by contradict V; apply /negP.
  - case: {-}_ /boolP => [Hc | ?].
    + contradict Hc; apply /negP.
      rewrite !in_set. caseb.
    + case_if.
  - case: {-}_ /boolP => [Hc | ?].
    + contradict Hc; apply /negP.
      rewrite !in_set. caseb.
    + case_if.
Qed.

Lemma add_node_iso_v_bijK' (t : trilean) (G : base_graph) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  cancel (@add_node_iso_v_bij_bwd t _ _ _ H) (@add_node_iso_v_bij_fwd t _ _ _ H).
Proof.
  intros [v | v]; unfold add_node_iso_v_bij_bwd.
  - case: {-}_ /boolP => [? | In]; cbn.
    + apply /eqP; cbn; by apply /eqP.
    + case_if.
      apply /eqP; cbn; apply /eqP.
      rewrite !in_set in In.
      revert In. move => /nandP[E | /nandP[E | //]].
      all: revert E; rewrite negb_involutive; cbn; move => /eqP E //.
  - case: {-}_ /boolP => [? | In]; cbn.
    + apply /eqP; cbn; by apply /eqP.
    + contradict In; apply /negP.
      rewrite !in_set. splitb.
Qed.

Definition add_node_iso_v (t : trilean) (G : base_graph) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1))
  (H' : target e1 <> target e0) := {|
  bij_fwd := @add_node_iso_v_bij_fwd t _ _ _ H;
  bij_bwd:= @add_node_iso_v_bij_bwd _ _ _ _ _;
  bijK:= add_node_iso_v_bijK H';
  bijK':= add_node_iso_v_bijK' _;
  |}.

Definition add_node_iso_e_bij_fwd (t : trilean) (G : base_graph) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  edge (@add_concl_graph _ _
    (@add_concl_graph _ _
      (add_node_graph t e0 e1) (Sub (inl (source e0)) (add_node_s0 _ H)) c (elabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ H))) c (elabel e1)) ->
  edge (add_node_graph_1 t e0 e1) :=
  fun e => match e with
  | Some (inl (Some (inl (exist a _)))) => a
  | Some (inl (Some (inr a)))           => match a with end
  | Some (inl (None))                   => (Some (Some (inl e0)))
  | Some (inr a)                        => match a with end
  | None                                => Some (Some (inl e1))
  end.

Definition add_node_iso_e_bij_bwd (t : trilean) (G : base_graph) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  edge (add_node_graph_1 t e0 e1) ->
  edge (@add_concl_graph _ _
    (@add_concl_graph _ _
      (add_node_graph t e0 e1) (Sub (inl (source e0)) (add_node_s0 _ H)) c (elabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ H))) c (elabel e1)) :=
  fun e => if @boolP (e \in edge_set ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)))
  is AltTrue p then Some (inl (Some (inl (Sub e p))))
  else if e == Some (Some (inl e0)) then Some (inl (None)) else None.
(* TODO bien long à compiler ... *)

Lemma add_node_iso_e_bijK (t : trilean) (G : base_graph) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1))
  (H' : target e1 <> target e0) :
  cancel (@add_node_iso_e_bij_fwd t _ _ _ H) (@add_node_iso_e_bij_bwd t _ _ _ H).
Proof.
  intros [[[[[e E] | []] | ] | []] | ]; cbn; unfold add_node_iso_e_bij_bwd.
  - case: {-}_ /boolP => [? | ?].
    + apply /eqP; cbn. rewrite SubK. destruct e as [[[? | ?] | ] | ]; by cbn.
    + by contradict E; apply /negP.
  - case: {-}_ /boolP => [Hc | ?].
    + contradict Hc; apply /negP.
      rewrite !in_set. caseb.
    + case_if.
  - case: {-}_ /boolP => [Hc | ?].
    + contradict Hc; apply /negP.
      rewrite !in_set. caseb.
    + case_if.
      by subst e0.
Qed.

Lemma add_node_iso_e_bijK' (t : trilean) (G : geos) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1))
  (H' : vlabel (target e0) = c /\ vlabel (target e1) = c) :
  cancel (@add_node_iso_e_bij_bwd t _ _ _ H) (@add_node_iso_e_bij_fwd t _ _ _ H).
Proof.
  intros [[[e | e] | ] | ]; unfold add_node_iso_e_bij_bwd.
  - case: {-}_ /boolP => [? | In]; cbn.
    + apply /eqP; cbn; by apply /eqP.
    + case_if.
      apply /eqP; cbn; apply /eqP.
      rewrite !in_set in In.
      revert In. move => /nandP[/nandP[E | /nandP[E | //]] | /nandP[E | /nandP[E | //]]].
      all: revert E; rewrite negb_involutive; cbn; move => /eqP E //.
      * destruct H as [_ H]. specialize (H e). by rewrite E eq_refl in H.
      * destruct H as [H _]. specialize (H e). by rewrite E eq_refl in H.
      * destruct H' as [_ H']. transitivity (edge_of_concl (target e1)); [ | symmetry]; by apply concl_eq.
      * enough (e = e0) by by [].
        destruct H' as [H' _]. transitivity (edge_of_concl (target e0)); [ | symmetry]; by apply concl_eq.
  - case: {-}_ /boolP => [? | In]; cbn.
    + apply /eqP; cbn; by apply /eqP.
    + contradict In; apply /negP.
      by rewrite !in_set.
  - case: {-}_ /boolP => [? | In]; cbn.
    + apply /eqP; cbn; by apply /eqP.
    + contradict In; apply /negP.
      rewrite !in_set negb_involutive. splitb; cbn.
      * destruct H as [_ H]. by specialize (H e0).
      * destruct H as [H _]. by specialize (H e0).
      * by destruct t.
      * by destruct t.
  - case: {-}_ /boolP => [? | In]; cbn.
    + apply /eqP; cbn; by apply /eqP.
    + contradict In; apply /negP.
      rewrite !in_set negb_involutive. splitb; cbn.
      * destruct H as [_ H]. by specialize (H e1).
      * destruct H as [H _]. by specialize (H e1).
      * by destruct t.
      * by destruct t.
Qed.

Definition add_node_iso_e (t : trilean) (G : geos) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1))
  (H' : target e1 <> target e0)
  (H'' : vlabel (target e0) = c /\ vlabel (target e1) = c) := {|
  bij_fwd := @add_node_iso_e_bij_fwd t _ _ _ H;
  bij_bwd:= @add_node_iso_e_bij_bwd _ _ _ _ _;
  bijK:= add_node_iso_e_bijK H';
  bijK':= add_node_iso_e_bijK' _ H'';
  |}.

Lemma add_node_iso_ihom (t : trilean) (G : geos) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1))
  (H' : target e1 <> target e0)
  (H'' : vlabel (target e0) = c /\ vlabel (target e1) = c) :
  is_ihom (add_node_iso_v t H H') (add_node_iso_e t H H' H'') pred0.
Proof.
  destruct H''. split.
  - by intros [[[[[? ?] | []] | ] | []] | ] [].
  - by intros [[[? ?] | []] | []].
  - by intros [[[[[? ?] | []] | ] | []] | ].
Qed.

Definition add_node_iso (t : trilean) (G : geos) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1))
  (H' : target e1 <> target e0)
  (H'' : vlabel (target e0) = c /\ vlabel (target e1) = c) := {|
  iso_v := add_node_iso_v t H H';
  iso_e := add_node_iso_e t H H' H'';
  iso_d := pred0;
  iso_ihom := add_node_iso_ihom _ _ _ _ |}.

Lemma add_node_isol (t : trilean) (G : geos) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1))
  (H' : target e1 <> target e0)
  (H'' : vlabel (target e0) = c /\ vlabel (target e1) = c) :
 (@add_concl_graph_left
    (@add_concl_graph_left
      (add_node_graph_left t H) (Sub (inl (source e0)) (add_node_s0 _ H)) c (elabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ H))) c (elabel e1)) ≃l
  add_node_graph_left_1 t e0 e1.
Proof.
  exists (add_node_iso t H H' H'').
  intros [[[[? | ?] ?] | []] | []] ?; cbn; trivial.
  - case_if.
  - by apply /eqP; cbn.
Qed.


Definition add_node_parr_iso_0 (G : base_graph) (e0 e1 : edge G) :
  (G ⊎ unit_graph (⅋) ⊎ unit_graph c)
  ∔ [inl (inl (source e0)), elabel e0, inl (inr tt)]
  ∔ [inl (inr tt), elabel e0 ⅋ elabel e1, inr tt]
  ≃ (G ⊎ (unit_graph (⅋) ⊎ unit_graph c))
  ∔ [inr (inl tt), elabel e0 ⅋ elabel e1, inr (inr tt)]
  ∔ [inl (source e0), elabel e0, inr (inl tt)].
Proof.
  etransitivity. apply add_edge_C. symmetry.
  apply (add_edge_iso (add_edge_iso (union_A G (unit_graph (⅋)) (unit_graph c))
    (inr (inl tt)) (elabel e0 ⅋ elabel e1) (inr (inr tt)))).
Defined.

Definition add_node_parr_iso_1 (G : base_graph) (e0 e1 : edge G) :
  (G ⊎ unit_graph (⅋) ⊎ unit_graph c)
  ∔ [inl (inl (source e0)), elabel e0, inl (inr tt)]
  ∔ [inl (inl (source e1)), elabel e1, inl (inr tt)]
  ∔ [inl (inr tt), elabel e0 ⅋ elabel e1, inr tt]
  ≃ (G ⊎ (unit_graph (⅋) ⊎ unit_graph c))
  ∔ [inr (inl tt), elabel e0 ⅋ elabel e1, inr (inr tt)]
  ∔ [inl (source e0), elabel e0, inr (inl tt)]
  ∔ [inl (source e1), elabel e1, inr (inl tt)].
Proof.
  etransitivity. apply add_edge_C.
  apply (add_edge_iso (add_node_parr_iso_0 e0 e1)).
Defined.

Definition add_node_parr_iso_2 (G : base_graph) (e0 e1 : edge G) :
  (G ⊎ unit_graph (⅋) ⊎ unit_graph c)
  ∔ [inl (inl (source e0)), elabel e0, inl (inr tt)]
  ∔ [inl (inl (source e1)), elabel e1, inl (inr tt)] ≃ 
  ((G ⊎ unit_graph (⅋))
  ∔ [inl (source e0), elabel e0, inr tt]) ∔ [inl (source e1), 
   elabel e1, inr tt] ⊎ unit_graph c .
Proof.
  etransitivity.
  - symmetry. apply (add_edge_iso (@union_add_edge_l _ _ (G ⊎ unit_graph (⅋)) _ _ _ _)).
  - symmetry. apply union_add_edge_l.
Defined.

Definition add_node_parr_iso (G : base_graph) (e0 e1 : edge G) :
  add_node_graph_1 parr_t e0 e1 ≃
  @add_concl_graph _ _ (add_parr_graph (source e0) (source e1) (elabel e0) (elabel e1))
  (inr tt) c (elabel e0 ⅋ elabel e1).
Proof.
  unfold add_node_graph_1, add_concl_graph, add_parr_graph, edge_graph, two_graph, "∔".
  etransitivity. apply (add_edge_iso (add_edge_iso (@union_add_edge_r _ _ G _ _ _ _) _ _ _)).
  etransitivity. symmetry. apply add_node_parr_iso_1.
  apply (add_edge_iso (add_node_parr_iso_2 e0 e1)).
Defined.

Lemma add_node_parr_isol (G : geos) (e0 e1 : edge G)
  (H' : vlabel (target e0) = c /\ vlabel (target e1) = c) :
  add_node_graph_left_1 parr_t e0 e1 ≃l
  @add_concl_graph_left (add_parr_graph_left (source e0) (source e1) (elabel e0) (elabel e1))
  (inr tt) c (elabel e0 ⅋ elabel e1).
Proof.
  exists (add_node_parr_iso _ _).
  intros [v | [[] | []]] V; apply /eqP; cbn; try by [].
  case_if.
  all: destruct H' as [H0 H1].
  all: rewrite ->left_e in *; caseb.
  all: subst v; cbn in V.
  all: contradict V.
  all: by rewrite ?H0 ?H1.
Defined.

Lemma add_node_parr_correct (G : proof_structure) : correct G -> correct (add_node_parr G).
Proof.
  intro H.
  remember (order G) as l eqn:Hl; symmetry in Hl.
  enough (Hdone : correct (match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => fun Heq => add_node_graph_data parr_t (add_node_hyp Heq)
    | _ => fun=> v_graph_data
    end Hl)) by by subst l.
  destruct l as [ | v0 [ | v1 l]]; try apply v_correct.
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  enough (H': correct (@add_concl_graph_left (@add_concl_graph_left (add_node_graph_left parr_t (add_node_hyp Hl))
    (Sub (inl (source e0)) (add_node_s0 _ (add_node_hyp Hl))) c (elabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ (add_node_hyp Hl)))) c (elabel e1)))
    by apply (rem_concl_correct (rem_concl_correct H')).
  assert (vlabel v0 = c /\ vlabel v1 = c) as [? ?]
    by (split; apply p_order; rewrite Hl !in_cons; caseb).
  assert (H'' : vlabel (target e0) = c /\ vlabel (target e1) = c)
    by by rewrite !concl_e.
  assert (H' : target e1 <> target e0).
  { rewrite !concl_e //. apply nesym.
    elim (p_order G).
    rewrite Hl cons_uniq in_cons negb_or.
    by move => _ /andP[/andP[/eqP ? _] _]. }
  by apply (iso_correct (add_node_isol parr_t (add_node_hyp Hl) H' H'')),
    (iso_correct (add_node_parr_isol H'')), add_concl_correct, add_parr_correct.
Qed.


Definition add_node_tens_iso_0 (G0 G1 : base_graph) (e0 : edge G0) (e1 : edge G1) :
  G0 ⊎ G1 ⊎ (unit_graph (⊗) ⊎ unit_graph c)
  ∔ [inl tt, elabel e0 ⊗ elabel e1, inr tt]
  ≃
  (G0 ⊎ G1 ⊎ unit_graph (⊗) ⊎ unit_graph c)
  ∔ [inl (inr tt), elabel e0 ⊗ elabel e1, inr tt].
Proof.
  etransitivity. apply (@union_add_edge_r _ _ (G0 ⊎ G1) (unit_graph _ ⊎ unit_graph _) _ _ _).
  apply (add_edge_iso (union_A (G0 ⊎ G1) (unit_graph _) (unit_graph _))).
Defined.

Definition add_node_tens_iso_1 (G0 G1 : base_graph) (e0 : edge G0) (e1 : edge G1) :
  ((G1 ⊎ (G0 ⊎ unit_graph (⊗))
  ∔ [inl (source e0), elabel e0, inr tt])
  ∔ [inl (source e1), elabel e1, inr (inr tt)]
  ⊎ unit_graph c)
  ≃
  ((G1 ⊎ (G0 ⊎ unit_graph (⊗)))
  ∔ [inr (inl (source e0)), elabel e0, inr (inr tt)]
  ∔ [inl (source e1), elabel e1, inr (inr tt)]
  ⊎ unit_graph c).
Proof.
  apply union_iso.
  - apply (add_edge_iso (@union_add_edge_r _ _ _ (_ ⊎ unit_graph _) _  _ _) (inl (source e1)) _ (inr (inr tt))).
  - reflexivity.
Defined.

Definition add_node_tens_iso_2 (G0 G1 : base_graph) (e0 : edge G0) (e1 : edge G1) :
  ((G1 ⊎ (G0 ⊎ unit_graph (⊗)))
  ∔ [inr (inl (source e0)), elabel e0, inr (inr tt)]
  ∔ [inl (source e1), elabel e1, inr (inr tt)]
  ⊎ unit_graph c)
  ≃
  ((G1 ⊎ (G0 ⊎ unit_graph (⊗))) ⊎ unit_graph c)
  ∔ [inl (inr (inl (source e0))), elabel e0, inl (inr (inr tt))]
  ∔ [inl (inl (source e1)), elabel e1, inl (inr (inr tt))].
Proof.
  etransitivity. apply union_add_edge_l.
  apply (add_edge_iso (@union_add_edge_l _ _ (_ ⊎ (_ ⊎ unit_graph _)) _ _ _ _)).
Defined.

Definition add_node_tens_iso_3 (G0 G1 : base_graph) (e0 : edge G0) (e1 : edge G1) :
  (G1 ⊎ (G0 ⊎ unit_graph (⊗))) ⊎ unit_graph c ≃ G0 ⊎ G1 ⊎ unit_graph (⊗) ⊎ unit_graph c.
Proof.
  apply union_iso; [ | reflexivity].
  etransitivity. apply union_A.
  apply union_iso; [ | reflexivity].
  apply union_C.
Defined.

Definition add_node_tens_iso (G0 G1 : base_graph) (e0 : edge G0) (e1 : edge G1) :
  @add_node_graph_1 tens_t (G0 ⊎ G1) (inl e0) (inr e1) ≃
  @add_concl_graph _ _
    (@union_edge_graph _ _ G1
      (@add_concl_graph _ _ G0 (source e0) (⊗) (elabel e0))
      (source e1) (inr tt) (elabel e1))
  (inr (inr tt)) c (elabel e0 ⊗ elabel e1).
Proof.
  unfold add_node_graph_1, union_edge_graph, add_concl_graph, edge_graph, two_graph, "∔".
  etransitivity. apply (add_edge_iso (add_edge_iso (add_node_tens_iso_0 e0 e1) _ _ _)).
  etransitivity. apply (add_edge_iso (@add_edge_C _ _ _ _ _ _ _ _ _)).
  etransitivity. apply add_edge_C.
  symmetry.
  etransitivity. apply (add_edge_iso (add_node_tens_iso_1 e0 e1)).
  etransitivity. apply (add_edge_iso (add_node_tens_iso_2 e0 e1)).
  apply (add_edge_iso (add_edge_iso (add_edge_iso (add_node_tens_iso_3 e0 e1) (inl (inr (inl (source e0))))
    _ (inl (inr (inr tt)))) (inl (inl (source e1))) _ (inl (inr (inr tt))))).
Defined.

Lemma add_node_tens_isol (G0 G1 : geos) (e0 : edge G0) (e1 : edge G1)
  (H : vlabel (target e0) = c /\ vlabel (target e1) = c) :
  @add_node_graph_left_1 tens_t (union_graph_left G0 G1) (inl e0) (inr e1) ≃l
  @add_concl_graph_left
    (@union_edge_graph_left G1
      (@add_concl_graph_left G0 (source e0) (⊗) (elabel e0))
      (source e1) (inr tt) (elabel e1))
  (inr (inr tt)) c (elabel e0 ⊗ elabel e1).
Proof.
  exists (add_node_tens_iso _ _).
  destruct H as [H0 H1].
  intros [[v | v] | [[] | []]] V; apply /eqP; cbn; try by [].
  all: case_if.
  all: rewrite ->left_e in *; caseb.
  all: subst v; cbn in V.
  all: contradict V.
  all: by rewrite ?H0 ?H1.
Defined.

Lemma add_node_tens_correct (G0 G1 : proof_structure) :
  (exists v0 l0, order G0 = v0 :: l0) -> (exists v1 l1, order G1 = v1 :: l1) ->
  correct G0 -> correct G1 -> correct (add_node_tens G0 G1).
Proof.
  intros [v0 [l0 Hl0]] [v1 [l1 Hl1]] H0 H1.
  remember (order (union_geos G0 G1)) as l eqn:Hl; symmetry in Hl.
  enough (Hdone : correct (match l return (order (union_geos G0 G1) = l -> graph_data) with
    | v0 :: v1 :: _ => fun Heq => add_node_graph_data tens_t (add_node_hyp Heq)
    | _ => fun=> v_graph_data
    end Hl)) by by subst l.
  assert (exists l', l = inl v0 :: inr v1 :: l') as [l' Hl'].
  { subst l. cbn.
    rewrite /union_order Hl0 Hl1.
    by exists ([seq inr i | i <- l1] ++ [seq inl i | i <- l0]). }
  revert Hl. subst l. intro Hl.
  set e0 := edge_of_concl (inl v0 : union_geos G0 G1);
  set e1 := edge_of_concl (inr v1 : union_geos G0 G1).
  enough (H': correct (@add_concl_graph_left (@add_concl_graph_left (add_node_graph_left tens_t (add_node_hyp Hl))
    (Sub (inl (source e0)) (add_node_s0 _ (add_node_hyp Hl))) c (elabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ (add_node_hyp Hl)))) c (elabel e1)))
    by apply (rem_concl_correct (rem_concl_correct H')).
  assert (vlabel v0 = c /\ vlabel v1 = c) as [? ?]
    by (split; apply p_order; rewrite ?Hl0 ?Hl1 !in_cons; caseb).
  assert (H'' : vlabel (target e0) = c /\ vlabel (target e1) = c)
    by by rewrite !concl_e.
  assert (H' : target e1 <> target e0) by by rewrite !concl_e.
  apply (iso_correct (add_node_isol tens_t (add_node_hyp Hl) H' H'')).
  rewrite /e0 /e1 !union_edge_of_concl // in H''. cbn in H''.
  rewrite !union_edge_of_concl //.
  by apply (iso_correct (add_node_tens_isol H'')), add_concl_correct, union_edge_correct, add_concl_correct.
Qed.


Definition add_node_cut_iso_0 (G0 G1 : base_graph) (e0 : edge G0) (e1 : edge G1) :
  G1 ⊎ (G0 ⊎ unit_graph cut) ≃ G0 ⊎ G1 ⊎ unit_graph cut.
Proof.
  etransitivity. apply union_A.
  apply union_iso; [ | reflexivity].
  apply union_C.
Defined.

Definition add_node_cut_iso (G0 G1 : base_graph) (e0 : edge G0) (e1 : edge G1) :
  @add_node_graph_1 cut_t (G0 ⊎ G1) (inl e0) (inr e1) ≃
  @union_edge_graph _ _ G1 (@add_concl_graph _ _ G0 (source e0) cut (elabel e0))
    (source e1) (inr tt) (elabel e1).
Proof.
  unfold add_node_graph_1, union_edge_graph, add_concl_graph, edge_graph, two_graph, "∔"; cbn.
  symmetry.
  etransitivity. apply (add_edge_iso (@union_add_edge_r _ _ _ _ _ _ _)).
  apply (add_edge_iso (@add_edge_iso _ _ _ _ (add_node_cut_iso_0 e0 e1)
    (inr (inl (source e0))) _ (inr (inr tt)))).
Defined.

Lemma add_node_cut_isol (G0 G1 : geos) (e0 : edge G0) (e1 : edge G1)
  (H : vlabel (target e0) = c /\ vlabel (target e1) = c) :
  @add_node_graph_left_1 cut_t (union_graph_left G0 G1) (inl e0) (inr e1) ≃l
  @union_edge_graph_left G1 (@add_concl_graph_left G0 (source e0) cut (elabel e0))
    (source e1) (inr tt) (elabel e1).
Proof.
  exists (add_node_cut_iso _ _).
  destruct H as [H0 H1].
  intros [[v | v] | []] V; apply /eqP; cbn; try by [].
  all: case_if.
  all: rewrite ->left_e in *; caseb.
  all: subst v; cbn in V.
  all: contradict V.
  all: by rewrite ?H0 ?H1.
Defined.

Lemma add_node_cut_correct (G0 G1 :proof_structure) :
  (exists v0 l0, order G0 = v0 :: l0) -> (exists v1 l1, order G1 = v1 :: l1) ->
  correct G0 -> correct G1 -> correct (add_node_cut G0 G1).
Proof.
  intros [v0 [l0 Hl0]] [v1 [l1 Hl1]] H0 H1.
  remember (order (union_geos G0 G1)) as l eqn:Hl; symmetry in Hl.
cbn. unfold add_node_graph_data_bis.
  enough (Hdone : correct (match l return (order (union_geos G0 G1) = l -> graph_data) with
    | v0 :: v1 :: _ => if elabel (edge_of_concl v0) == elabel (edge_of_concl v1)^
           then fun Heq  => add_node_graph_data cut_t (add_node_hyp Heq)
           else fun=> v_graph_data
    | _ => fun=> v_graph_data
    end Hl)) by by subst l.
  assert (exists l', l = inl v0 :: inr v1 :: l') as [l' Hl'].
  { subst l. cbn.
    rewrite /union_order Hl0 Hl1.
    by exists ([seq inr i | i <- l1] ++ [seq inl i | i <- l0]). }
  revert Hl. subst l. intro Hl.
  case_if; [ | apply v_correct].
  set e0 := edge_of_concl (inl v0 : union_geos G0 G1);
  set e1 := edge_of_concl (inr v1 : union_geos G0 G1).
  enough (H': correct (@add_concl_graph_left (@add_concl_graph_left (add_node_graph_left cut_t (add_node_hyp Hl))
    (Sub (inl (source e0)) (add_node_s0 _ (add_node_hyp Hl))) c (elabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ (add_node_hyp Hl)))) c (elabel e1)))
    by apply (rem_concl_correct (rem_concl_correct H')).
  assert (vlabel v0 = c /\ vlabel v1 = c) as [? ?]
    by (split; apply p_order; rewrite ?Hl0 ?Hl1 !in_cons; caseb).
  assert (H'' : vlabel (target e0) = c /\ vlabel (target e1) = c)
    by by rewrite !concl_e.
  assert (H' : target e1 <> target e0) by by rewrite !concl_e.
  apply (iso_correct (add_node_isol cut_t (add_node_hyp Hl) H' H'')).
  rewrite /e0 /e1 !union_edge_of_concl // in H''. cbn in H''.
  rewrite !union_edge_of_concl //.
  by apply (iso_correct (add_node_cut_isol H'')), union_edge_correct, add_concl_correct.
Qed.


Lemma sound l (pi : ll l) : correct (ps pi).
Proof.
  induction pi as [ | | ? ? ? ? pi0 ? pi1 ? | | ? ? ? pi0 ? pi1 ?].
  - apply ax_correct.
  - trivial.
  - apply add_node_tens_correct; trivial.
    + destruct (order (ps pi0)) as [ | v O] eqn:HO.
      * exfalso.
        assert (Hf : sequent (ps pi0) = [::]) by by rewrite /sequent HO.
        by rewrite ps_consistent in Hf.
      * by exists v, O.
    + destruct (order (ps pi1)) as [ | v O] eqn:HO.
      * exfalso.
        assert (Hf : sequent (ps pi1) = [::]) by by rewrite /sequent HO.
        by rewrite ps_consistent in Hf.
      * by exists v, O.
  - by apply add_node_parr_correct.
  - apply add_node_cut_correct; trivial.
    + destruct (order (ps pi0)) as [ | v O] eqn:HO.
      * exfalso.
        assert (Hf : sequent (ps pi0) = [::]) by by rewrite /sequent HO.
        by rewrite ps_consistent in Hf.
      * by exists v, O.
    + destruct (order (ps pi1)) as [ | v O] eqn:HO.
      * exfalso.
        assert (Hf : sequent (ps pi1) = [::]) by by rewrite /sequent HO.
        by rewrite ps_consistent in Hf.
      * by exists v, O.
Qed.

(** * Proof Net of a Proof Sequent *)
Definition pn {l : list formula} (pi : ll l) : proof_net := {|
  ps_of := ps pi;
  p_correct := sound pi;
  |}.


(** * Cut elimination preserves correctness *)
Unset Mangle Names.

Lemma red_ax_correct (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  correct G -> correct (red_ax_geos Hcut Hax).
Proof.
Abort.

Lemma red_tens_correct (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  correct G -> correct (red_tens_geos Hcut Het Hep Htens Hparr).
Proof.
Abort.

(* TODO mettre tout ça au niveau de redcut et definir red one et red sur
des proof net plutot que des proof structures *)

(* sequentialisation : fonction reliant regles à noeuds => nb cut + quels tens lies à des cut *)
(* seuentialisation sans coupure puis avec (+ de cas ou en remplacant par des tens )*)

Definition terminal_node (G : graph_left) (v : G) : bool :=
  match vlabel v with
  | ax => [forall e, (source e != v) || (vlabel (target e) == c)]
  | ⊗ | ⅋ => vlabel (target (ccl v)) == c
  | cut => true
  | concl_l => false
  end.
(* TODO correct faible et fort = faible et non vide *)

(* TOTHINK connected subgraph for splitting tens ?? *)

(* TODO admettre lemme tenseur scindant puis sequantialisation directement *)
(* Lemma splitting_tens (G : graph_data) : [exists v, (vlabel v == ⊗) && (terminal_node v) &&
exists G0 : proof_net, exists G1 : proof_net, (#|G0| < #|G|) && (#|G1| < #|G|) && (sequent G == elabel (ccl v)
:: sequent G0 ++ sequent G1)].
Admitted. (* TODO hyp : non terminal ax, parr, cut *) *)

Definition sequentialisation (G : proof_net) : ll (sequent G).
Proof.
  revert G.
  enough (Hm : forall n (G : proof_structure), #|G| = n -> ll (sequent G))
    by (intro G; by apply (Hm #|G|)).
  intro n; induction n as [n IH] using lt_wf_rect; intros G Hc.
Abort.
(* TODO voir derniere quest exam et focalisation *)


(** ** Sequentialization *)
(* many things to do: spliting tens / cut, blocking parr, always a
  terminal parr or a splitting *)
(* function to turn a ps into a sequential proof *)


(***************** UNUSED LEMMA ********************************)
Ltac case_if0 := repeat (let Hif := fresh "Hif" in let Hif' := fresh "Hif" in
  case: ifP; cbn; move => /eqP Hif; rewrite // 1?Hif //).

Definition pick_unique2 := fun {T : finType} (H : #|T| = 1) => sval (fintype1 H).

(** Removing an element of a set decrease cardinality by 1 *)
Lemma cardsR1_set : forall (T : finType) (a : T) , #|setT :\ a| = #|T| - 1.
Proof. intros T a. rewrite -cardsT (cardsD1 a [set: T]) in_setT. lia. Qed.

Lemma cardsR1 {T : finType} (a : T) (A : {set T}) : #|A :\ a| = #|A| - (a \in A).
Proof. rewrite (cardsD1 a A). lia. Qed.

(** Both visions of a set as set or subset have the same cardinal *)
Lemma card_set_subset {T : finType} (P : pred T) :
  #|[finType of {e : T | P e}]| = #|[set e | P e]|.
Proof. by rewrite card_sig cardsE. Qed.

(* Switching Graph *)
Definition switching_graph (G : geos) (phi : G -> bool) : base_graph :=
  remove_edges (setT :\: [set match phi v with
  | false => left v | true => right v end | v in G & vlabel v == ⅋]).

End Atoms.
(* TODO _ plus souvent*)
(* TODO transitivity plus souvent, à la place de assert *)
(* TODO toujours utiliser = or == partout le même !!! *)
(* TODO use _spec pour casser des cas *)
(* TOTHINK fonction disant si formule atomique existe dans yalla, ajout possible pour expansion atome *)
(* TODO check if every lemma proved is useful / interesting *)
(* TODO check all names given not already used, from beginning *)
(* TODO check at the end if all import are used *)
(* TODO see file bug_report.v *)
(* TODO separer le fichier en plusieurs *)
(* TODO => de move apres vue *)
(* TODO refine (iso_correct _ _). a la place de prouver les hyp tout de suite *)
(* TODO voir wlog *)
(* TODO cbn qui simplifie avec eqP que si ça marche, pour éviter apply /eqP; cbn; apply /eqP. *)
