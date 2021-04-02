(* Unit-free MLL following Yalla schemas *)


From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
From mathcomp Require Import all_ssreflect zify.
From GraphTheory Require Import preliminaries mgraph.
(* TODO check at the end if all are used *)
(* TODO see file bug_report.v *)

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
Infix "⊗" := tens (at level 40).
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
(** Tactic to make cases on if _ == _ *)
(* Make all cases, try to rewrite the equality condition and conserve the condition
  under the form _ = _ or _ <> _, folding trivial cases *)
Ltac case_if := repeat (let Hif := fresh "Hif" in
  case: ifP; cbn; move => /eqP Hif; rewrite // ?Hif //).


(** Tactic to split both /\ and &&, folding trivial cases *)
Ltac splitb := repeat (split || apply /andP); trivial.


(** Tactic solving trivial \/ and || *)
Ltac caseb :=
  try done;
  try ((by left; caseb) || (by right; caseb));
  try (apply /orP; (by left; caseb) || (by right; caseb));
  try (apply /nandP; (by left; rewrite ?negb_involutive //; caseb)
                  || (by right; rewrite ?negb_involutive //; caseb)).


(** * Some results on 'I_n *)
(** The function inord is injective on integers <= n *)
Lemma inord_inj : forall n i j : nat, i <= n -> j <= n -> @inord n i = @inord n j -> i = j.
Proof.
  intros n i j ? ? H.
  assert (Hn : forall k : nat, k <= n -> nat_of_ord (@inord n k) = k) by apply inordK.
  by rewrite -(Hn i) // -(Hn j) // H.
Qed.

(** 'I_0 has the empty enumeration *)
Lemma enum_I0 : enum 'I_0 = [::].
Proof. rewrite -enum0. apply eq_enum, card0_eq, card_ord. Qed.

(** Tactic to distinguish cases in 'I_2 *)
Lemma case_I2 : forall n : 'I_2, (n == ord0) || (n == ord1) : bool.
Proof.
  intros [n Hn].
  repeat (destruct n as [ | n]; trivial).
Qed.

Lemma case_I2bis : forall n : 'I_2, n = ord0 \/ n = ord1.
Proof.
  intro n.
  assert (H := case_I2 n); revert H; move => /orP[/eqP H | /eqP H];
  [by left | by right].
Qed.

Ltac destruct_I2 n H := destruct (case_I2bis n) as [H | H].

(** Tactic to distinguish cases in 'I_3 *)
Lemma case_I3 : forall n : 'I_3, (n == ord0) || (n == ord1) || (n == ord2) : bool.
Proof.
  intros [n Hn].
  repeat (destruct n as [ | n]; trivial).
Qed.

Lemma case_I3bis : forall n : 'I_3, n = ord0 \/ n = ord1 \/ n = ord2.
Proof.
  intro n.
  assert (H := case_I3 n); revert H; move => /orP[/orP[/eqP H | /eqP H] | /eqP H];
  caseb.
Qed.

Ltac destruct_I3 n H := destruct (case_I3bis n) as [H | [H | H]].

(* TOTHINK possible case_nter avec des set {_}+{_}+...*)


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
  | ax, ax => true
  | ⊗, ⊗ => true
  | ⅋, ⅋ => true
  | cut, cut => true
  | concl_l, concl_l => true
  | _, _ => false
  end.

Lemma eqb_eq_rule : forall A B, eqb_rule A B = true <-> A = B.
Proof. intros A B; destruct A, B; split; intro H; trivial; by contradict H. Qed.

Definition rules_dectype := {|
  car := rule;
  dectype.eqb := eqb_rule;
  eqb_eq := eqb_eq_rule |}.


(** * A DecType is an eqType *)
Definition decType_eqMixin (X : DecType) := EqMixin (eq_dt_reflect (X := X)).

(* [formula] as an eqType *)
Canonical formula_eqType := EqType formula (decType_eqMixin (formulas_dectype)).

(* [rule] as an eqType *)
Canonical rule_eqType := EqType rule (decType_eqMixin (rules_dectype)).


(** * Removing an element of a 2-elements set yields the set with the other element *)
Lemma set2D1 {T : finType} (a b : T) : b != a -> [set a; b] :\ a = [set b].
Proof.
  intro H. apply /setP; intro e.
  rewrite !in_set andb_orb_distrib_r andNb; cbn.
  destruct (eq_comparable e b) as [Heq | Hneq].
  - by rewrite Heq H.
  - replace (e == b) with false by (symmetry; by apply /eqP).
    by rewrite andb_false_r.
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
    destruct (other_in_neq Hs Hin) as [? H]; by rewrite H.
  - replace (pred_of_set S) with (pred_of_set (S :|: S)) by (f_equal; apply setUid).
    apply setUSS;
    rewrite sub1set //.
    apply other_in_neq.
Qed.

Lemma other_setD {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :
  S :\ x = [set other Hs Hin].
Proof.
  apply setP; unfold "=i"; intros.
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
Proof. by move => A; elim: A. Qed.

Lemma no_selftens_l : forall A B, tens A B <> A.
Proof. intro A; induction A as [ | | ? H1 A2 ? | ]; intros B Hc; inversion Hc. by apply (H1 A2). Qed.

Lemma no_selftens_r : forall A B, tens B A <> A.
Proof. intro A; induction A as [ | | A1 ? ? H2 | ]; intros B Hc; inversion Hc. by apply (H2 A1). Qed.

Lemma no_selfparr_l : forall A B, parr A B <> A.
Proof. intro A; induction A as [ | | | ? H1 A2 ? ]; intros B Hc; inversion Hc. by apply (H1 A2). Qed.

Lemma no_selfparr_r : forall A B, parr B A <> A.
Proof. intro A; induction A as [ | | | A1 ? ? H2 ]; intros B Hc; inversion Hc. by apply (H2 A1). Qed.

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
  destruct (eq_comparable x y) as [Heq | Hneq].
  - contradict Hx; apply /negP.
    by rewrite Heq.
  - by apply /eqP.
Qed.

Lemma inr_seq_inl_filter {L R : eqType} (l: seq L) (P : pred L) :
  forall (b : R), (inr b : L + R) \notin [seq (inl a : L + R) | a <- l & P a].
Proof.
  intros.
  induction l as [ | a ? ?]; cbn; trivial.
  by case: (P a).
Qed.

Lemma in_seq_sig {T : eqType} {P : pred T} : forall (a : {x : T | P x}) (l : seq ({x : T | P x})),
  (a \in l) = (sval a \in [seq sval v | v <- l]).
Proof.
  intros ? l.
  induction l as [ | ? ? H]; trivial.
  by rewrite !in_cons H.
Qed.

Lemma uniq_seq_sig {T : eqType} {P : pred T} : forall (l : seq ({x : T | P x})),
  (uniq l) = (uniq [seq sval v | v <- l]).
Proof.
  intro l; induction l as [ | ? ? H]; trivial.
  by rewrite map_cons !cons_uniq -H in_seq_sig.
Qed.


(** * Image of a set of cardinal 2 *)
Lemma imset_set2 : forall (aT rT : finType) (f : aT -> rT) (x y : aT),
  [set f x | x in [set x; y]] = [set f x; f y].
Proof.
  intros ? ? f x y.
  apply /setP; intros ?.
  rewrite Imset.imsetE !in_set.
  apply /imageP.
  case: ifP.
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
    move => /eqP ?; by subst.
  - intro Hc; specialize (Hc t).
    by rewrite in_set1 eq_refl in Hc.
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
Proof.
  unfold perm_of.
  induction sigma as [ | ? ? ? sigma H | ? ? ? | ? ? ? sigma H sigma' H'];
  by rewrite ?H ?H' //.
Qed.

Lemma perm_of_map {A B S : Type}  {l1 l2 : seq S} (sigma : Permutation_Type l1 l2)
  (l : seq A) (f : A -> B) :
  perm_of sigma [seq f i | i <- l] = [seq f i | i <- perm_of sigma l].
Proof.
  revert A B l f.
  induction sigma as [ | ? ? ? sigma H | ? ? ? | ? ? ? sigma H sigma' H']; cbn;
  intros A B l f.
  - by [].
  - destruct l; trivial; cbn; by rewrite H.
  - by destruct l as [ | ? [ | ? ?]].
  - by rewrite H H'.
Qed.

Lemma perm_of_in {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) :
  forall {B : finType} (l : seq B) (b : B), (b \in perm_of sigma l) = (b \in l).
Proof.
  induction sigma as [ | ? ? ? sigma H | ? ? ? | ? ? ? sigma H sigma' H']; cbn;
  intros B l b.
  - by [].
  - destruct l; trivial; by rewrite !in_cons H.
  - destruct l as [ | a [ | a' l]]; trivial.
    rewrite !in_cons !orb_assoc.
    by replace ((b == a') || (b == a)) with ((b == a) || (b == a')) by by rewrite orb_comm.
  - by rewrite H' H.
Qed.

Lemma perm_of_uniq {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) {B : finType}
  (l : seq B) : uniq (perm_of sigma l) = uniq l.
Proof.
  revert B l.
  induction sigma as [ | ? ? ? sigma H | ? ? ? | ? ? ? sigma H sigma' H']; cbn;
  intros B l.
  - by [].
  - destruct l; trivial; cbn; by rewrite perm_of_in H.
  - destruct l as [ | ? [ | ? ?]]; trivial; cbn.
    rewrite !in_cons.
    rewrite !negb_or !andb_assoc; apply andb_id2r; intros _.
    rewrite andb_comm andb_assoc; apply andb_id2r; intros _.
    rewrite andb_comm; apply andb_id2r; intros _.
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



(** ** Stratum 1: Multigraphs with some more data *)
(** * Definition of [graph_data] *)
(* Multigraph with vertex label = rule and arrow label = formula
   [left] giving for a node its left in-edge (if relevant)
   [order] giving an ordering of its conclusion node *)
Set Primitive Projections.
Record graph_data : Type :=
  Graph_data {
    graph_of :> graph rule formula;
    left : vertex graph_of -> edge graph_of;
    order : list (vertex graph_of);
  }.
Unset Primitive Projections.


(** * Derivated functions, useful at the level geometric structure *)
(** Nonsensical values for total functions on vertices but where only some vertices matters *)
Definition bogus {G : graph_data} : G -> edge G := fun v => left v.
Opaque bogus.

(** Function [right] returning another in-edge than left *)
Definition right {G : graph_data} : G -> edge G :=
  fun v => match [pick x in edges_in_at_subset v :\ left v] with
  | Some e => e
  | None => bogus v
  end.

(** Function [ccl] returning an out-edge *)
Definition ccl {G : graph_data} : G -> edge G :=
  fun v => match [pick x in edges_out_at_subset v] with
  | Some e => e
  | None => bogus v
  end.

(** Function [edge_of_concl] returning an in-edge *)
Definition edge_of_concl {G : graph_data} : G -> edge G :=
  fun v => match [pick x in edges_in_at_subset v] with
  | Some e => e
  | None => bogus v
  end.


(** Sequent of the graph *)
Definition sequent (G : graph_data) : list formula :=
  [seq elabel (edge_of_concl i) | i <- order G].


(* Picking an out or in edge if it exists *)
Definition pick_edge_at : forall (G : graph_data), G -> edge G :=
  fun (G : graph_data) (v : G) =>
  match [pick x in edges_out_at_subset v :|: edges_in_at_subset v] with
  | Some e => e
  | None => bogus v
  end.



(** ** Stratum 2: Geometric Structure *)
(** * Conditions on the neighborhood of a node according to its rule *)
(** Out/In-degree of a node according to its rule *)
Definition deg (b : bool) := match b with
  | false => fun (r : rule) => match r with
    | ax => 2
    | ⊗ => 1
    | ⅋ => 1
    | cut => 0
    | concl_l => 0
    end
  | true => fun (r : rule) => match r with
    | ax => 0
    | ⊗ => 2
    | ⅋ => 2
    | cut => 2
    | concl_l => 1
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
  rewrite set2D1 ?pick1 //; by apply other_in_neq.
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
  { assert (#|edges_out_at_subset v| <= 0 /\ #|edges_in_at_subset v| <= 0).
    2:{ lia. }
    assert (Hu : #|edges_out_at_subset v :|: edges_in_at_subset v| = 0) by by apply eq_card0.
    rewrite -!Hu.
    apply cardsUmax. }
  assert (Hfout := p_deg_out v); rewrite Hcout in Hfout;
  assert (Hfin := p_deg_in v); rewrite Hcin in Hfin.
  by destruct (vlabel v).
Qed.



(** ** Stratum 3: Proof Structure *)
(** * The rule of a node gives conditions on the formulae of its arrows *)
Definition proper_ax_cut (G : geos) := (*TODO with prop instead of bool ? *)
  forall (b : bool),
  let rule := if b then cut else ax in
  forall (v : G), vlabel v = rule -> exists el, exists er,
  (el \in edges_at_subset b v) && (er \in edges_at_subset b v) &&
  (elabel el == dual (elabel er)).

Definition proper_tens_parr (G : geos) :=
  forall (b : bool), (* TODO replace this bool with a new type ?*)
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
    contradict Hf'; by rewrite in_set0. }
  destruct (vlabel ((source e))) eqn:Hl; try done;
  [assert (Hd := p_tens Hl) | assert (Hd := p_parr Hl)]; cbn in Hd.
  all: contradict Hd.
  all: assert (e = ccl (source e)) as <- by (apply ccl_eq; caseb).
  all: assert (Hdir : e \in edges_in_at_subset (source e)) by by rewrite in_set Hf.
  all: revert Hdir; rewrite right_set ?in_set; [ | caseb]; move => /orP[/eqP Hdir | /eqP Hdir].
  all: rewrite -Hdir.
  all: apply nesym; no_selfform.
Qed.



(** ** Operations on proof structures, at each strata *)
(** * Base case: proof structure of an axiom *)
Definition ax_graph (x : atom) : graph rule formula := {|
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

Definition ax_left (x : atom) : vertex (ax_graph x) -> edge (ax_graph x) := fun _ => ord0.
(* No vertex tens nor parr: nonsensical value *)

Definition ax_order (x : atom) : list (vertex (ax_graph x)) := ord1 :: ord2 :: nil.

Definition ax_graph_data (x : atom) : graph_data := {|
  graph_of := ax_graph x;
  left := @ax_left x;
  order := ax_order x;
  |}.


Lemma ax_p_deg (x : atom) : proper_degree (ax_graph_data x).
Proof.
  unfold proper_degree.
  intros [ | ] v;
  destruct_I3 v H;
  rewrite H.
  all: compute_card_subIn.
Qed.

Lemma ax_p_left (x : atom) : proper_left (ax_graph_data x).
Proof.
  unfold proper_left.
  intros v [Hl | Hl];
  destruct_I3 v H;
  contradict Hl;
  by rewrite H.
Qed.

Lemma ax_p_order (x : atom) : proper_order (ax_graph_data x).
Proof.
  unfold proper_order.
  split; trivial.
  intro v;
  destruct_I3 v H;
  by rewrite H.
Qed.

Definition ax_geos (x : atom) : geos := {|
  graph_data_of := ax_graph_data x;
  p_deg := @ax_p_deg x;
  p_left := @ax_p_left x;
  p_order := ax_p_order x;
  |}.


Lemma ax_p_ax_cut (x : atom) : proper_ax_cut (ax_geos x).
Proof.
  unfold proper_ax_cut.
  intros b v Hl.
  destruct b;
  destruct_I3 v Hv;
  try (contradict Hl; by rewrite Hv).
  exists ord0, ord1.
  by rewrite /edges_out_at_subset Hv !in_set !eq_refl.
Qed.

Lemma ax_p_tens_parr (x : atom) : proper_tens_parr (ax_geos x).
Proof.
  unfold proper_tens_parr.
  intros b v Hl.
  destruct b;
  destruct_I3 v Hv;
  contradict Hl;
  by rewrite Hv.
Qed.

Definition ax_ps (x : atom) : proof_structure := {|
  geos_of := ax_geos x;
  p_ax_cut := @ax_p_ax_cut x;
  p_tens_parr := @ax_p_tens_parr x;
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
  graph_of := G;
  left := @left G;
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
  p_deg := @p_deg G;
  p_left := @p_left G;
  p_order := perm_p_order G sigma;
  |}.

Definition perm_ps (G : proof_structure) (l l' : list formula) (sigma : Permutation_Type l l') :
  proof_structure := {|
  geos_of := perm_geos G sigma;
  p_ax_cut := @p_ax_cut G;
  p_tens_parr := @p_tens_parr G;
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
Definition union_left (G0 G1 : graph_data) : G0 ⊎ G1 -> edge (G0 ⊎ G1) :=
  fun v => match v with
  | inl u => inl (left u)
  | inr u => inr (left u)
  end.

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
  graph_of := G0 ⊎ G1;
  left := @union_left G0 G1;
  order := union_order G0 G1;
  |}.

(** Useful lemmas on a disjoint union *)
Lemma union_edges_at (G0 G1 : graph_data) (i : bool) (b : bool) :
  let Gi (j : bool) := match j with
  | false => G0 | true => G1 end in
  let fv := match i return Gi i -> G0 ⊎ G1 with
  | false => inl | true => inr end in
  let fe := match i return edge (Gi i) -> edge (G0 ⊎ G1) with
  | false => inl | true => inr end in
  forall v : Gi i,
  edges_at_subset b (fv v) =i [set fe e | e in edges_at_subset b v].
Proof.
  intros Gi fv fe v.
  unfold "=i".
  destruct i;
  intros [e | e].
  all: assert (injective fe) by (apply inl_inj || apply inr_inj).
  all: rewrite ?inj_imset // !in_set; cbn; trivial.
  all: apply /eqP /memPn; move => y /imsetP [? _] Hl.
  all: by rewrite Hl.
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
  all: destruct (eq_comparable v vt) as [Heq | Hneq];
       [by rewrite Heq eq_refl | ].
  all: revert Hneq; move => /eqP /negPf Hneq.
  all: assert (Hf : (fv v \in [seq fvn i | i <- ot]) = false)
        by (clear; by induction ot).
  all: by rewrite Hneq Hf ?orb_false_r.
Qed.
Notation union_order_inl := (union_order_in (i := false)).
Notation union_order_inr := (union_order_in (i := true)).


Lemma union_p_deg (G0 G1 : geos) : proper_degree (union_graph_data G0 G1).
Proof.
  unfold proper_degree.
  intros b [v | v]; cbn;
  [set fe := inl : edge G0 -> edge (G0 ⊎ G1) | set fe := inr : edge G1 -> edge (G0 ⊎ G1)].
  all: assert (injective fe) by (apply inl_inj || apply inr_inj).
  all: rewrite -(p_deg b v) -(card_imset (f := fe)) //.
  all: apply eq_card.
  - apply union_edges_at_inl.
  - apply union_edges_at_inr.
Qed.

Lemma union_p_left (G0 G1 : geos) : proper_left (union_graph_data G0 G1).
Proof.
  unfold proper_left.
  intros [v | v] Hv;
  [set fe := inl : edge G0 -> edge (G0 ⊎ G1) | set fe := inr : edge G1 -> edge (G0 ⊎ G1)].
  all: assert (injective fe) by (apply inl_inj || apply inr_inj).
  1: rewrite union_edges_at_inl. 2: rewrite union_edges_at_inr.
  all: rewrite (inj_imset (f:= fe)) //.
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
  p_deg := @union_p_deg G0 G1;
  p_left := @union_p_left G0 G1;
  p_order := union_p_order G0 G1;
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
  intros b [v | v] Hl; cbn; cbn in Hl.
  all: destruct (p_ax_cut Hl) as [el [er He]].
  1: exists (inl el), (inl er); rewrite !union_edges_at_inl.
  2: exists (inr el), (inr er); rewrite !union_edges_at_inr.
  all: rewrite !inj_imset //; by cbn.
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
  p_ax_cut := @union_p_ax_cut G0 G1;
  p_tens_parr := @union_p_tens_parr G0 G1;
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
  all: apply eq_in_map; intros e He.
  all: rewrite union_edge_of_concl //.
  all: apply p_order; cbn; rewrite /union_order ?H0 ?H1 !in_cons ?mem_cat.
  all: rewrite map_f; caseb.
Qed.



(** * Adding a tens/parr/cut node to a proof structure, replacing 2 conclusions *)
(* Add a tens/parr/cut node, without removing conclusions *)
Definition add_node_graph_1 (t : trilean) {G : graph_data} (e0 e1 : edge G) :=
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
Definition add_node_graph (t : trilean) {G : graph_data} (e0 e1 : edge G) :=
  induced ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)).

(** Function left for the graph with a new node *)
(* Function left for the intermediary graph *)
Definition add_node_left_1 (t : trilean) {G : graph_data} (e0 e1 : edge G) :=
  let G' := add_node_graph_1 t e0 e1 in
  fun (v : G') => match v return edge G' with
  | inl u => if target (left u) == target e0 then Some None
             else if target (left u) == target e1 then Some None
             else Some (Some (inl (left u)))
(* artefact for when the value of left is nonsensical: if we remove left v, give it a new value *)
  | inr _ => Some None
  end.
(* TODO mettre grosse cond add_node_hyp en if : si oui comme là, sinon ne fait rien
-> voir si pas trop d'ennui de type dépendant *)
(* TODO opacifier les intermediaires apres avoir prouvé les lemmes utiles dessus 
+ faire ça aussi dans les autres def similaires *)

(* Necessary hypothesis : the nodes we remove have no input edges *)
Lemma add_node_consistent_left (t : trilean) {G : graph_data} (e0 e1 : edge G) :
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
Definition add_node_left (t : trilean) {G : graph_data} (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  add_node_graph t e0 e1 -> edge (add_node_graph t e0 e1) :=
  fun v => Sub (add_node_left_1 (val v)) (add_node_consistent_left H (val v)).

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
  graph_of := add_node_graph t e0 e1;
  left := add_node_left H;
  order := add_node_order t e0 e1;
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
  fun e => if (e == e1) then None
           else if (e == e0) then Some None
           else Some (Some (inl e)).

Lemma add_node_transport_1_inj (t : trilean) (G : graph_data) (e0 e1 : edge G) :
  injective (add_node_transport_1 t e0 e1).
Proof.
  intros e e'.
  unfold add_node_transport_1; case_if.
  by move => /eqP Heqbis; apply /eqP.
Qed.

Lemma add_node_transport_1_edges (t : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  forall (v : G), (v != v0) /\ (v != v1) ->
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
      assert (Hr : (target e == v) = false) by by apply /negP /negP.
      rewrite Hr; clear Hr; symmetry; apply /negP /negP.
      apply /imageP; intros [x Hx Hxx].
      contradict Hxx.
      case_if.
      apply /eqP; cbn; apply /eqP.
      intro Hc. contradict Hx.
      rewrite -Hc in_set; by apply /negP.
  - symmetry; apply /negP /negP.
    apply /imageP; intros [x Hx Hxx].
    contradict Hxx.
    case_if.
  - destruct t; cbn.
    all: symmetry; apply /negP /negP.
    all: apply /imageP; intros [x Hx Hxx].
    all: contradict Hxx.
    all: case_if.
    all: contradict Hx; apply /negP.
    all: subst; rewrite in_set concl_e //.
    all: apply /eqP; apply nesym; by apply /eqP.
  - destruct t; cbn.
    all: symmetry; apply /negP /negP.
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
  assert (v0 != v1).
  { elim (p_order G).
    rewrite H cons_uniq in_cons negb_or.
    by move => _ /andP[/andP[? _] _]. }
  assert (Hneqe : e0 == e1 = false).
  { apply negbTE, (contra_neq (z1 := target e0) (z2 := target e1)).
    - apply f_equal.
    - by rewrite !concl_e. }
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
      case_if.
      contradict Hneqe. rewrite not_false_iff_true. by apply /eqP. }
    rewrite Heq inj_imset // in_set.
    by destruct b, t.
  - assert (Heq : Sub None He = g e1) by
      (apply /eqP; rewrite /g /add_node_transport sub_val_eq SubK /add_node_transport_1; case_if).
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

(* We add the node if it respect the rules, do nothing if it is inadequate *)
Definition add_node_graph_data_bis : trilean -> geos -> graph_data :=
  fun (t : trilean) (G : geos) =>
  match order G as o return order G = o -> graph_data with
  | v0 :: v1 :: _ => match t with
    | cut_t => if (elabel (edge_of_concl v0) == dual (elabel (edge_of_concl v1)))
      then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun _ => G
    | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
    end
  | _ => fun _ => G
  end Logic.eq_refl.


Lemma add_node_p_deg (t : trilean) (G : geos) : proper_degree (add_node_graph_data_bis t G).
Proof.
  unfold add_node_graph_data_bis.
  generalize (erefl (order G));
  destruct (order G) as [ | v0 [ | v1 l]] at 2 3;
  intro H; try (apply p_deg).
  revert t.
  assert (forall (t : trilean), proper_degree (add_node_graph_data t (add_node_hyp H))).
  2:{ intros [ | | ]; trivial.
      case_if.
      apply p_deg. }
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
  assert (forall (t : trilean), proper_left (add_node_graph_data t (add_node_hyp H))).
  2:{ intros [ | | ]; trivial.
      case_if.
      apply p_left. }
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
  assert (forall (t : trilean), proper_order (add_node_graph_data t (add_node_hyp H))).
  2:{ intros [ | | ]; trivial.
      case_if.
      apply p_order. }
  intro t.
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  unfold proper_order, add_node_order.
  destruct (p_order G) as [Hv U].
  split; cbn.
  - intros [[v | v] Hin]; cbn;
    rewrite in_seq_sig SubK -(proj2_sig (all_sigP _)) /add_node_order_2.
    + apply (iff_stepl (A := v \in order G)). 2:{ by apply iff_sym. }
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
  p_deg := @add_node_p_deg t G;
  p_left := @add_node_p_left t G;
  p_order := @add_node_p_order t G;
  |}.


Lemma add_node_p_ax_cut (t : trilean) (G : proof_structure) : proper_ax_cut (add_node_geos t G).
Proof.
  remember (order G) as l eqn:H; symmetry in H.
  unfold add_node_geos, add_node_graph_data_bis, proper_ax_cut; cbn.
  assert (Hdone : forall (b : bool) (v : match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match t with
      | cut_t => if (elabel (edge_of_concl v0)) == (elabel (edge_of_concl v1)^)
        then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> G
      | _ => fun Heq  => add_node_graph_data t (add_node_hyp Heq)
      end
    | _ => fun=> G
    end H), vlabel v = (if b then cut else ax) ->
    exists (el er : edge (match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match t with
      | cut_t => if (elabel (edge_of_concl v0)) == (elabel (edge_of_concl v1)^)
        then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> G
      | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
      end
    | _ => fun=> G
    end H)), (el \in edges_at_subset b v) && (er \in edges_at_subset b v) &&
    (elabel el == dual (elabel er))).
  2:{ by rewrite <-!H in Hdone. }
  destruct l as [ | v0 [ | v1 l]];
  try (apply p_ax_cut).
  assert (Hdone : t <> cut_t \/ elabel (edge_of_concl v0) = dual (elabel (edge_of_concl v1)) ->
    forall b (v : add_node_graph_data t (add_node_hyp H)),
    vlabel v = (if b then cut else ax) ->
    exists el er : edge (add_node_graph_data t (add_node_hyp H)),
    (el \in edges_at_subset b v) && (er \in edges_at_subset b v) && (elabel el == elabel er^)).
  2:{ case_if; destruct t; try (apply Hdone; caseb).
      apply p_ax_cut. }
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
  assert (Hdone : forall (v : match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match t with
      | cut_t => if (elabel (edge_of_concl v0)) == (elabel (edge_of_concl v1)^)
        then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> G
      | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
      end
    | _ => fun=> G
    end H), vlabel v = r -> elabel (ccl v) = f (elabel (left v)) (elabel (right v))).
  2:{ by rewrite <-!H in Hdone. }
  destruct l as [ | v0 [ | v1 l]];
  intros v Hv;
  assert (Hor : vlabel v = ⊗ \/ vlabel v = ⅋) by (destruct b; caseb);
  try by apply p_tens_parr.
  revert t v Hv Hor.
  assert (Hdone : forall t (v : add_node_graph_data t (add_node_hyp H)),
    vlabel v = r -> vlabel v = ⊗ \/ vlabel v = ⅋ ->
    elabel (ccl v) = f (elabel (left v)) (elabel (right v))).
  2:{ intros [ | | ];
      try apply Hdone.
      specialize (Hdone cut_t).
      case_if.
      intros. by apply p_tens_parr. }
  intros t [[v | v] Hin] Hv Hor.
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
  p_ax_cut := @add_node_p_ax_cut t G;
  p_tens_parr := @add_node_p_tens_parr t G;
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
              else sequent G
      | _ => behead (behead (sequent G))
      end
    | _ => sequent G
    end in
  sequent (add_node_geos t G) = new ++ old.
Proof.
  remember (order G) as l eqn:H; symmetry in H; cbn.
  assert ([seq elabel (edge_of_concl i) | i <- order (add_node_graph_data_bis t G)] =
    [seq elabel (edge_of_concl i) | i <- order (match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match t with
      | cut_t => if elabel (edge_of_concl v0) == elabel (edge_of_concl v1)^
        then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> G
      | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
    end
    | _ => fun=> G
    end H)]) as -> by by rewrite <-!H.
  destruct l as [ | v0 [ | v1 l]]; trivial.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [? ?]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  assert (match t with
    | cut_t => if elabel (edge_of_concl v0) == elabel (edge_of_concl v1)^
      then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> G
    | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
    end H = match t with
    | cut_t => if elabel (edge_of_concl v0) == elabel (edge_of_concl v1)^
      then add_node_graph_data t (add_node_hyp H) else G
    | _ => add_node_graph_data t (add_node_hyp H)
    end) as -> by (destruct t; trivial; case_if).
  rewrite /sequent H; cbn.
  assert ([seq elabel (edge_of_concl i) | i <- order (add_node_graph_data t (add_node_hyp H))] =
    match t with
    | tens_t => [:: elabel (edge_of_concl v0) ⊗ elabel (edge_of_concl v1)]
    | parr_t => [:: elabel (edge_of_concl v0) ⅋ elabel (edge_of_concl v1)]
    | cut_t => [::]
    end ++ [seq elabel (edge_of_concl i) | i <- l]).
  2:{ destruct t; trivial. case_if. by rewrite H. }
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
Fixpoint ps {l : list formula} (pi : ll l) : proof_structure := match pi with
  | ax_r x => ax_ps x
  | ex_r _ _ pi0 sigma => perm_ps (ps pi0) sigma
  | tens_r _ _ _ _ pi0 pi1 => add_node_ps tens_t (union_ps (ps pi0) (ps pi1))
  | parr_r _ _ _ pi0 => add_node_ps parr_t (ps pi0)
  | cut_r _ _ _ pi0 pi1 => add_node_ps cut_t (union_ps (ps pi0) (ps pi1))
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
    move => /eqP; cbn; move => /andP [/eqP H0 _];
    move => /eqP; cbn; move => /andP [/eqP H1 _].
    by rewrite H0 H1.
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



(** ** Correctness Criteria: Danos-Regnier *)
(* Switching Graph *)
Definition switching_graph (G : geos) (phi : G -> bool) : graph rule formula :=
  remove_edges (setT :\: [set match phi v with
  | false => left v | true => right v end | v in G & vlabel v == ⅋]).
(* convention: left=false, right=true, or make a new 2 elements induced ?
same choice as bool of proper_tens_parr *)
(* From GraphTheory Require Import digraph sgraph. Check digraph_of. *)
(* TOTHINK add node conclusion (with edges) to replace the arrows ? seems complicated *)
(* TOTHINK nouveau graphe : sommets du graph + 1 sommet / arete; arete = image des aretes du depart *)
(* Definir chemin directement sur mgraph (pointe sur sa source, type dependant) : sequence d'arete coherente, ignore direction, unicité arete *)
(* Definir acyclique (sur cycle minimal ?) + connexe (non orienté) *)
(* TOTHINK dédoubler arete pour symmetriser, + unicité arete de cycle : pas l'arete ou son double en 2 fois *)
(* TODO refaire preuves sur papier pour voir quelle représentation est mieux *)
(* TOTHINK cycle dans graphe : un qui ne passe pas par les 2 aretes d'un même parr [et qui ne passe pas 2 fois par la meme arete]*)
(* TODO chemin oriente avec identite sur mgraph *)
(* voir walk de mgraph, mapping de chemins de mgraph vers graph correction *)
(* TOTHINK chemins dans des mgraphs non orientés: ajouter une fonction disant quelles aretes considerées comme egales,
puis chemins simples : n'a pas 2 aretes ayant la meme image *)

(* Criteria: acyclic and connected *)
(* need def for acyclic + connected, or just for tree (tree in the lib) ?
  -> considering trees may change the proofs *)

(*
Definition is_correct PS :=
  forall phi, acyclic SG (PS) (phi) /\ connected SG (PS) (phi).
or with is_tree (already in the lib) ???
  forall phi, is_tree SG (PS) (phi).
*)

(* Soundness of correctness *)
(*
Lemma sound l (pi : ll l) : is_correct ps (pi).
*)

(** ** Cut Elimination *) (* possible avant la sequentialisation et le critere de correction *)
(** * Axiom - cut reduction *)
Definition red_ax_graph_1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : graph rule formula :=
  G ∔ [source (other_cut Hcut) , dual (elabel e) , target (other_ax Hax)].

Definition red_ax_graph (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : graph rule formula :=
  induced ([set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)).

Lemma red_ax_degenerate (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  source e = source (other_cut Hcut) <-> other_cut Hcut = other_ax Hax.
Proof.
  split; intro H.
  - apply other_ax_eq.
    rewrite H.
    splitb.
    apply /eqP; apply other_cut_in_neq.
  - destruct (other_ax_in_neq Hax) as [Hf _].
    by rewrite H Hf.
Qed.

Definition red_ax_left_1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : red_ax_graph_1 Hcut Hax -> edge (red_ax_graph_1 Hcut Hax) :=
  fun (v : red_ax_graph_1 Hcut Hax) =>
    if left v == e then
      if source e == source (other_cut Hcut) then Some (pick_edge_at v)
      else None
    else if left v == other_cut Hcut then
      if source e == source (other_cut Hcut) then Some (pick_edge_at v)
      else None
    else if left v == other_ax Hax then
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
    all: contradict Hf'; by rewrite in_set0. }
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
    assert (Hdone : other_cut Hcut = other_ax Hax).
    2:{ by rewrite Hdone Hsa in Hs. }
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
    apply /norP; split; by apply /eqP.
  - apply /eqP; intro Hc.
    assert (Hf : left v \in edges_in_at_subset (target e)) by by rewrite in_set Hc.
    contradict Hf; apply /negP.
    rewrite other_cut_set !in_set.
    apply /norP; split; by apply /eqP.
Qed. (* TODO essayer de simplifier (ça et les autres preuves de cette partie red) *)

Definition red_ax_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : red_ax_graph Hcut Hax -> edge (red_ax_graph Hcut Hax) :=
  fun v => Sub (red_ax_left_1 (val v)) (red_ax_consistent_left v).
Arguments red_ax_left {G} {e} Hcut Hax.

Lemma red_ax_consistent_order (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  let S := [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e) in
  all (pred_of_set S) (order G).
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
  graph_of := red_ax_graph Hcut Hax;
  left := red_ax_left Hcut Hax;
  order := red_ax_order Hcut Hax;
  |}.

Definition red_ax_transport (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : red_ax_graph_data Hcut Hax) :=
  fun (a : edge (red_ax_graph_data Hcut Hax)) => match val a with
  | None => if b then if val v == target (other_ax Hax) then other_ax Hax else other_cut Hcut
            else if val v == source (other_cut Hcut) then other_cut Hcut else other_ax Hax
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
  all: rewrite ?Ha ?Ha' eq_refl in Heq; subst.
  all: rewrite !in_set; cbn.
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
    all: contradict Hdone; by rewrite in_set0. }
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
      1:{ contradict Hvt; apply /negP; rewrite negb_involutive; apply /eqP.
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
        1:{ contradict Hin; apply /eqP.
          apply other_ax_in_neq. }
        contradict Hvs; apply /negP; rewrite negb_involutive; apply /eqP.
        by rewrite -Hin Ha0. }
      subst.
      exists (Sub None Hn).
      * rewrite !in_set sub_val_eq !SubK; by apply /eqP.
      * by rewrite /red_ax_transport !SubK eq_refl.
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
        1:{ contradict Hin; by apply /eqP. }
        by rewrite Hin in Hneqc. }
      subst.
      exists (Sub None Hn).
      * rewrite !in_set sub_val_eq !SubK; by apply /eqP.
      * by rewrite /red_ax_transport SubK eq_refl.
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
      destruct b.
      all: intro Hc.
      all: rewrite Hc eq_refl in Hxx.
      all: by rewrite -Hxx in Hc.
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
    assert (H := left_e Hl); contradict H.
    destruct (other_cut_in_neq Hcut) as [Hc0 _].
    rewrite Hf Hc0.
    intro Hc.
    clear - Hl Hc Hcut; contradict Hcut.
    destruct Hl as [Hl | Hl];
    by rewrite Hc Hl. }
  case_if.
  - destruct (red_ax_degenerate Hcut Hax) as [Ho _].
    assert (left v = other_cut Hcut).
    { replace (left v) with (other_ax Hax); symmetry.
      by apply Ho. }
    by [].
  - assert (Hf := left_e Hl); contradict Hf.
    replace (left v) with (other_ax Hax).
    by apply nesym.
Qed.


Lemma red_ax_p_deg (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_degree (red_ax_graph_data Hcut Hax).
Proof.
  unfold proper_degree, red_ax_graph_data.
  intros b [v Hv]; cbn.
  rewrite -(p_deg b v) (red_ax_transport_edges _ Hv) card_in_imset //.
  apply red_ax_transport_inj.
Qed.
Arguments red_ax_p_deg {G} {e} Hcut Hax.

Lemma red_ax_p_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_left (red_ax_graph_data Hcut Hax).
Proof.
  unfold proper_left, red_ax_graph_data.
  intros [v Hv] Hl; cbn; cbn in Hl.
  assert (H := p_left Hl).
  revert H; rewrite (red_ax_transport_edges_in Hv) Imset.imsetE in_set; move => /imageP [a Ha Heq].
  assert (Hdone : red_ax_left Hcut Hax (Sub v Hv) = a).
  2:{ by rewrite Hdone. }
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
Arguments red_ax_p_left {G} {e} Hcut Hax.

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
Arguments red_ax_p_order {G} {e} Hcut Hax.

Definition red_ax_geos (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : geos := {|
  graph_data_of := red_ax_graph_data Hcut Hax;
  p_deg := red_ax_p_deg Hcut Hax;
  p_left := red_ax_p_left Hcut Hax;
  p_order := red_ax_p_order Hcut Hax;
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
Arguments red_ax_p_ax_cut {G} {e} Hcut Hax.

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
Arguments red_ax_p_tens_parr {G} {e} Hcut Hax.

Definition red_ax_ps (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proof_structure := {|
  geos_of := red_ax_geos Hcut Hax;
  p_ax_cut := red_ax_p_ax_cut Hcut Hax;
  p_tens_parr := red_ax_p_tens_parr Hcut Hax;
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
(* TODO poster sur zulip : pourquoi apply eq_in_map echoue mais pas apply (@eq_in_map _) *)
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
Definition red_tens_graph_1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut) :
  graph rule formula :=
  let ntens := source e in
  let nparr := source (other_cut Hcut) in
  let ltens := left ntens in
  let rtens := right ntens in
  let lparr := left nparr in
  let rparr := right nparr in
  G ∔ cut ∔ cut
    ∔ [inl (inl (source ltens)) , elabel (ltens) , inl (inr tt)]
    ∔ [inl (inl (source rtens)) , elabel (rtens) , inr tt]
    ∔ [inl (inl (source lparr)) , elabel (lparr) , inr tt]
    ∔ [inl (inl (source rparr)) , elabel (rparr) , inl (inr tt)].

(* TODO se debarasser de other_cut -> necessite d'avoir hyp pour dire target eparr = target etens
-> casse symmetrie : Hcut *)
Definition red_tens_graph (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut) : graph rule formula :=
  let S := [set: red_tens_graph_1 Hcut] :\ (inl (inl (source e))) :\
    (inl (inl (source (other_cut Hcut)))) :\ (inl (inl (target e))) in
  induced S.

Lemma red_tens_ineq_in (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  (forall a, source a != target e) /\
  source (left (source e)) != source e /\
  source (right (source e)) != source e /\
  source (left (source e)) != source (other_cut Hcut) /\
  source (right (source e)) != source (other_cut Hcut) /\
  source (left (source (other_cut Hcut))) != source e /\
  source (right (source (other_cut Hcut))) != source e /\
  source (left (source (other_cut Hcut))) != source (other_cut Hcut) /\
  source (right (source (other_cut Hcut))) != source (other_cut Hcut).
Proof.
  assert (forall a, source a != target e).
  { intro a; apply /eqP; intro Ha.
    assert (Hf := p_deg_out (target e)).
    rewrite Hcut in Hf; cbn in Hf.
    assert (Hdone : a \in set0) by by rewrite -(cards0_eq Hf) in_set Ha.
    contradict Hdone; by rewrite in_set0. }
  assert (source (left (source e)) != source (other_cut Hcut) /\
    source (right (source e)) != source (other_cut Hcut)) as [? ?].
  { split; apply /eqP; intro Hc.
    1: assert (Hc0 : left (source e) = ccl (source (other_cut Hcut))) by (apply ccl_eq; caseb).
    2: assert (Hc0 : right (source e) = ccl (source (other_cut Hcut))) by (apply ccl_eq; caseb).
    all: assert (Hc1 : other_cut Hcut = ccl (source (other_cut Hcut))) by (apply ccl_eq; caseb).
    all: assert (Hc2 : source e = target e) by
      (destruct (other_cut_in_neq Hcut) as [Hc2 _]; rewrite Hc1 -Hc0 ?left_e ?right_e in Hc2; caseb).
    all: clear - Htens Hc2 Hcut; contradict Htens; by rewrite Hc2 Hcut. }
  assert (source (left (source e)) != source e /\ source (right (source e)) != source e) as [? ?].
  { split; apply /eqP; intro Hc.
    1: assert (Hc0 : left (source e) = ccl (source e)) by (apply ccl_eq; caseb).
    2: assert (Hc0 : right (source e) = ccl (source e)) by (apply ccl_eq; caseb).
    all: assert (Hc1 : e = ccl (source e)) by (apply ccl_eq; caseb).
    all: assert (Hc2 : source e = target e) by (rewrite {2}Hc1 -Hc0 ?left_e ?right_e; caseb).
    all: clear - Htens Hc2 Hcut; contradict Htens; by rewrite Hc2 Hcut. }
  assert (source (left (source (other_cut Hcut))) != source (other_cut Hcut) /\
    source (right (source (other_cut Hcut))) != source (other_cut Hcut)) as [? ?].
  { split; apply /eqP; intro Hc.
    1: assert (Hc0 : left (source (other_cut Hcut)) = ccl (source (other_cut Hcut))) by (apply ccl_eq; caseb).
    2: assert (Hc0 : right (source (other_cut Hcut)) = ccl (source (other_cut Hcut))) by (apply ccl_eq; caseb).
    all: assert (Hc1 : other_cut Hcut = ccl (source (other_cut Hcut))) by (apply ccl_eq; caseb).
    all: assert (Hc2 : source (other_cut Hcut) = target e) by
      (destruct (other_cut_in_neq Hcut) as [Hc2 _]; rewrite Hc1 -Hc0 ?left_e ?right_e in Hc2; caseb).
    all: clear - Hparr Hc2 Hcut; contradict Hparr; by rewrite Hc2 Hcut. }
  assert (source (left (source (other_cut Hcut))) != source e /\
    source (right (source (other_cut Hcut))) != source e) as [? ?].
  { split; apply /eqP; intro Hc.
    1: assert (Hc0 : left (source (other_cut Hcut)) = ccl (source e)) by (apply ccl_eq; caseb).
    2: assert (Hc0 : right (source (other_cut Hcut)) = ccl (source e)) by (apply ccl_eq; caseb).
    all: assert (Hc1 : e = ccl (source e)) by (apply ccl_eq; caseb).
    all: assert (Hc2 : source (other_cut Hcut) = target e) by (rewrite {2}Hc1 -Hc0 ?left_e ?right_e; caseb).
    all: clear - Hparr Hc2 Hcut; contradict Hparr; by rewrite Hc2 Hcut. }
  splitb.
Qed.

Lemma red_tens_ineq_if (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  left (source e) <> right (source e) /\
  left (source (other_cut Hcut)) <> right (source (other_cut Hcut)) /\
  left (source e) <> left (source (other_cut Hcut)) /\
  left (source e) <> right (source (other_cut Hcut)) /\
  left (source (other_cut Hcut)) <> right (source e) /\
  right (source e) <> right (source (other_cut Hcut)) /\
  right (source e) <> left (source (other_cut Hcut)) /\
  right (source e) <> left (source e) /\
  left (source (other_cut Hcut)) <> left (source e) /\
  right (source (other_cut Hcut)) <> left (source e) /\
  right (source (other_cut Hcut)) <> left (source (other_cut Hcut)) /\
  right (source (other_cut Hcut)) <> right (source e).
Proof.
  assert (left (source e) <> right (source e) /\
    left (source (other_cut Hcut)) <> right (source (other_cut Hcut))) as [? ?].
  { elim: (@p_right _ (source e)); [ | caseb]; move => _ /eqP ?;
    elim: (@p_right _ (source (other_cut Hcut))); [ | caseb]; move => _ /eqP ?.
    split; by apply nesym. }
  assert (Hf : source e <> source (other_cut Hcut)) by
    (intro Hf; clear - Htens Hf Hparr; contradict Htens; by rewrite Hf Hparr).
  assert (left (source e) <> left (source (other_cut Hcut))
    /\ left (source e) <> right (source (other_cut Hcut))
    /\ left (source (other_cut Hcut)) <> right (source e)
    /\ right (source e) <> right (source (other_cut Hcut))) as [? [? [? ?]]].
  { splitb; intro Hc; contradict Hf.
    1: rewrite -(@left_e _ (source e)) -1?(@left_e _ (source (other_cut Hcut))); caseb.
    2: rewrite -(@left_e _ (source e)) -1?(@right_e _ (source (other_cut Hcut))); caseb.
    3: rewrite -(@right_e _ (source e)) -1?(@left_e _ (source (other_cut Hcut))); caseb.
    4: rewrite -(@right_e _ (source e)) -1?(@right_e _ (source (other_cut Hcut))); caseb.
    all: by rewrite Hc. }
  assert (right (source e) <> left (source (other_cut Hcut))
    /\ right (source e) <> left (source e)
    /\ left (source (other_cut Hcut)) <> left (source e)
    /\ right (source (other_cut Hcut)) <> left (source e)
    /\ right (source (other_cut Hcut)) <> left (source (other_cut Hcut))
    /\ right (source (other_cut Hcut)) <> right (source e))
    as [? [? [? [? [? ?]]]]] by (splitb; by apply nesym).
  splitb.
Qed.

Lemma red_tens_new_edges_in (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  let S := [set: red_tens_graph_1 Hcut] :\ (inl (inl (source e))) :\
    (inl (inl (source (other_cut Hcut)))) :\ (inl (inl (target e))) in
  Some (Some (Some None)) \in edge_set S /\ Some (Some None) \in edge_set S /\
  Some None \in edge_set S /\ None \in edge_set S.
Proof.
  destruct (red_tens_ineq_in Htens Hparr) as [? [? [? [? [? [? [? [? ?]]]]]]]].
  intro S. rewrite !in_set; cbn. splitb.
Qed.

Definition red_tens_left_1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut) :
  red_tens_graph_1 Hcut -> edge (red_tens_graph_1 Hcut) :=
  fun v => match v with
  | inl (inl v) =>
    if left v == left (source e) then Some (Some (Some None))
    else if left v == right (source e) then Some (Some None)
    else if left v == left (source (other_cut Hcut)) then Some None
    else if left v == right (source (other_cut Hcut)) then None
    else if left v == e then None
    else if left v == other_cut Hcut then None
    else Some (Some (Some (Some (inl (inl (left v))))))
  | _ => None
  end.

Lemma red_tens_consistent_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  let S := [set: red_tens_graph_1 Hcut] :\ (inl (inl (source e))) :\ (inl (inl (source (other_cut Hcut))))
    :\ (inl (inl (target e))) in
  forall (v : red_tens_graph Hcut), red_tens_left_1 (val v) \in edge_set S.
Proof.
  intros S [v Hv].
  destruct (red_tens_ineq_in Htens Hparr) as [? [? [? [? [? [? [? [? ?]]]]]]]].
  destruct (red_tens_new_edges_in Htens Hparr) as [? [? [? ?]]].
  rewrite !in_set /red_tens_left_1 !SubK.
  destruct v as [[v | ] | ]; cbn;
  case_if; splitb.
  all: apply /eqP; intro Hc.
  - assert (Heq : other_cut Hcut = ccl (source (other_cut Hcut))) by (apply ccl_eq; caseb).
    assert (Heq2: left v = ccl (source (other_cut Hcut))) by (apply ccl_eq; caseb).
    by rewrite -Heq in Heq2.
  - assert (Heq : e = ccl (source e)) by (apply ccl_eq; caseb).
    assert (Heq2: left v = ccl (source e)) by (apply ccl_eq; caseb).
    by rewrite -Heq in Heq2.
  - assert (Hin : left v \in edges_in_at_subset (target e)) by by rewrite in_set Hc.
    revert Hin. rewrite other_cut_set !in_set. by move => /orP[/eqP ? | /eqP ?].
  - assert (Hin : left v \in edges_in_at_subset (source (other_cut Hcut))) by by rewrite in_set Hc.
    revert Hin. rewrite right_set ?in_set; caseb; by move => /orP[/eqP ? | /eqP ?].
  - assert (Hin : left v \in edges_in_at_subset (source e)) by by rewrite in_set Hc.
    revert Hin. rewrite right_set ?in_set; caseb; by move => /orP[/eqP ? | /eqP ?].
Qed.

Definition red_tens_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  red_tens_graph Hcut -> edge (red_tens_graph Hcut) :=
  fun v => Sub (red_tens_left_1 (val v)) (red_tens_consistent_left Htens Hparr v).

Definition red_tens_order_1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut) :
  list (red_tens_graph_1 Hcut) := [seq (inl (inl v)) | v <- order G].

Lemma red_tens_consistent_order (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  let S := [set: red_tens_graph_1 Hcut] :\ (inl (inl (source e))) :\
    (inl (inl (source (other_cut Hcut)))) :\ (inl (inl (target e))) in
  all (pred_of_set S) (red_tens_order_1 Hcut).
Proof.
  rewrite /red_tens_order_1 all_map.
  apply /allP; intros v Hv; cbn.
  assert (Hl : vlabel v = concl_l) by by apply p_order.
  repeat (apply /setD1P; split); trivial; cbn.
  all: apply /eqP; intro Hc; contradict Hl; by rewrite Hc ?Hcut ?Htens ?Hparr.
Qed.

Definition red_tens_order (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  seq (red_tens_graph Hcut) := sval (all_sigP (red_tens_consistent_order Htens Hparr)).

Definition red_tens_graph_data (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) : graph_data := {|
  graph_of := red_tens_graph Hcut;
  left := red_tens_left Htens Hparr;
  order := red_tens_order Htens Hparr;
  |}.

Definition red_tens_transport (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :=
  fun (a : edge (red_tens_graph_data Htens Hparr)) => match val a with
  | None => right (source (other_cut Hcut))
  | Some None => left (source (other_cut Hcut))
  | Some (Some None) => right (source e)
  | Some (Some (Some None)) => left (source e)
  | Some (Some (Some (Some (inl (inl a))))) => a
  | _ => e (* Never happens *)
  end.

Lemma red_tens_transport_inj (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  injective (@red_tens_transport _ _ _ Htens Hparr).
Proof.
  intros [a Ha] [b Hb].
  rewrite /red_tens_transport !SubK.
  intro H.
  apply /eqP; rewrite sub_val_eq SubK; apply /eqP.
  revert Ha Hb.
  rewrite !in_set.
  destruct (red_tens_ineq_if Htens Hparr) as [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]].
  destruct a as [[[[[[a | []] | []] | ] | ] | ] | ], b as [[[[[[b | []] | []] | ] | ] | ] | ];
  subst; cbn; try by [].
  all: rewrite ?left_e ?right_e; caseb.
  all: try (by move => /andP[_ /andP[_ /andP[/eqP ? /andP[/eqP ? _]]]] _);
       try (by move => _ /andP[_ /andP[_ /andP[/eqP ? /andP[/eqP ? _]]]]).
Qed.

Lemma red_tens_transport_edges (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  forall (b : bool) (v : G) (Hv : inl (inl v) \in
  (setT :\ (inl (inl (source e))) :\ (inl (inl (source (other_cut Hcut)))) :\ (inl (inl (target e))))),
  edges_at_subset b v =
  [set red_tens_transport a | a in edges_at_subset b (Sub (inl (inl v)) Hv : red_tens_graph_data Htens Hparr)].
Proof.
  set S := [set: red_tens_graph_1 Hcut] :\ (inl (inl (source e))) :\
    (inl (inl (source (other_cut Hcut)))) :\ (inl (inl (target e))).
  intros b v Hv; apply /setP; intro a.
  rewrite Imset.imsetE !in_set.
  symmetry; apply /imageP; case_if.
  - destruct (red_tens_ineq_in Htens Hparr) as [? [? [? [? [? [? [? [? ?]]]]]]]].
    destruct (red_tens_new_edges_in Htens Hparr) as [Insssn [Inssn [Insn Inn]]].
    assert (a <> e /\ a <> other_cut Hcut) as [? ?].
    { split; intro Hc; contradict Hv; apply /negP; subst.
      all: rewrite !in_set; cbn.
      all: destruct b; caseb.
     destruct (other_cut_in_neq Hcut) as [-> _]; caseb. }
    destruct (eq_comparable a (left (source e))) as [Hsssn | Hsssn];
    [ | destruct (eq_comparable a (left (source (other_cut Hcut)))) as [Hssn | Hssn]];
    [ | | destruct (eq_comparable a (right (source e))) as [Hsn | Hsn]];
    [ | | | destruct (eq_comparable a (right (source (other_cut Hcut)))) as [Hn | Hn]];
    subst.
    5:{ assert (Ina : Some (Some (Some (Some (inl (inl a))))) \in edge_set S).
        { rewrite !in_set; cbn. splitb.
          all: apply /eqP; intro Hf.
          - assert (a = ccl (source (other_cut Hcut)) /\ other_cut Hcut = ccl (source (other_cut Hcut)))
            as [? ?] by (split; apply ccl_eq; caseb).
            by assert (a = other_cut Hcut) by by subst.
          - assert (a = ccl (source e) /\ e = ccl (source e))
            as [? ?] by (split; apply ccl_eq; caseb).
            by assert (a = e) by by subst.
          - assert (Hin : a \in edges_in_at_subset (target e)) by by rewrite in_set Hf.
            revert Hin; rewrite other_cut_set !in_set; by move => /orP[/eqP ? | /eqP ?].
          - assert (Hin : a \in edges_in_at_subset (source (other_cut Hcut))) by by rewrite in_set Hf.
            revert Hin; rewrite right_set ?in_set; [ | caseb]; by move => /orP[/eqP ? | /eqP ?].
          - assert (Hin : a \in edges_in_at_subset (source e)) by by rewrite in_set Hf.
            revert Hin; rewrite right_set ?in_set; [ | caseb]; by move => /orP[/eqP ? | /eqP ?]. }
        exists (Sub (Some (Some (Some (Some (inl (inl a)))))) Ina).
        - rewrite !in_set; cbn; rewrite !SubK; by cbn.
        - by rewrite /red_tens_transport SubK. }
    all: destruct b;
      [contradict Hv; apply /negP; rewrite !in_set ?left_e ?right_e; caseb | ].
    4: exists (Sub None Inn).
    3: exists (Sub (Some (Some None)) Inssn).
    2: exists (Sub (Some None) Insn).
    1: exists (Sub (Some (Some (Some None))) Insssn).
    1,3,5,7: rewrite !in_set; cbn; rewrite !SubK; by cbn.
    all: by rewrite /red_tens_transport SubK.
  - intros [[[[[[[[d | []] | []] | ] | ] | ] | ] Hdin] Hd Hdd].
    all: rewrite /red_tens_transport !SubK in Hdd.
    all: revert Hd; rewrite !in_set; cbn; rewrite !SubK -Hdd; cbn; move => /eqP Hd; try by [].
    all: destruct b; contradict Hd; try by [].
    all: apply /eqP; cbn; by apply /eqP.
Qed.

Lemma red_tens_transport_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  forall (v : G) (Hv : inl (inl v) \in [set: red_tens_graph_1 Hcut] :\ (inl (inl (source e))) :\
    (inl (inl (source (other_cut Hcut)))) :\ (inl (inl (target e)))),
  vlabel v = ⊗ \/ vlabel v = ⅋ ->
  red_tens_transport (left (Sub (inl (inl (v))) Hv : red_tens_graph_data Htens Hparr)) = left v.
Proof.
  intros v Hv Hl.
  cbn; rewrite /red_tens_transport /red_tens_left /red_tens_left_1 !SubK.
  revert Hv.
  rewrite !in_set; cbn.
  move => /andP[/eqP H0 /andP[/eqP ? /andP[/eqP ? _]]].
  case_if; subst.
  - contradict H0.
    rewrite left_e; caseb.
  - contradict H0.
    destruct (other_cut_in_neq Hcut) as [<- _].
    replace (other_cut Hcut) with (left v).
    rewrite left_e; caseb.
Qed.


Lemma red_tens_p_deg (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  proper_degree (red_tens_graph_data Htens Hparr).
Proof.
  unfold proper_degree, red_tens_graph_data.
  destruct (red_tens_new_edges_in Htens Hparr) as [Insssn [Inssn [Insn Inn]]].
  set n := Sub None Inn : edge (red_tens_graph_data Htens Hparr);
  set sn := Sub (Some None) Insn : edge (red_tens_graph_data Htens Hparr);
  set ssn := Sub (Some (Some None)) Inssn : edge (red_tens_graph_data Htens Hparr);
  set sssn := Sub (Some (Some (Some None))) Insssn : edge (red_tens_graph_data Htens Hparr).
  intros b [[[v | []] | []] Hv]; cbn.
  - rewrite -(p_deg b v) (red_tens_transport_edges _ _ _ Hv) card_imset //.
    apply red_tens_transport_inj.
  - assert (edges_in_at_subset (Sub (inl (inr tt)) Hv : red_tens_graph_data Htens Hparr) = [set sssn; n]
      /\ edges_out_at_subset (Sub (inl (inr tt)) Hv : red_tens_graph_data Htens Hparr) = set0) as [Hin Hout].
    { split; apply /setP; intro a; rewrite !in_set.
      all: by destruct a as [[[[[[[a | []] | []] | ] | ] | ] | ] ?]. }
    destruct b;
    by rewrite ?Hin ?Hout ?cards2 ?cards0.
  - assert (edges_in_at_subset (Sub (inr tt) Hv : red_tens_graph_data Htens Hparr) = [set ssn; sn]
      /\ edges_out_at_subset (Sub (inr tt) Hv : red_tens_graph_data Htens Hparr) = set0) as [Hin Hout].
    { split; apply /setP; intro a; rewrite !in_set.
      all: by destruct a as [[[[[[[a | []] | []] | ] | ] | ] | ] ?]. }
    destruct b;
    by rewrite ?Hin ?Hout ?cards2 ?cards0.
Qed.
Arguments red_tens_p_deg {G} {e} {Hcut} Htens Hparr.

Lemma red_tens_p_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  proper_left (red_tens_graph_data Htens Hparr).
Proof.
  unfold proper_left.
  intros [[[v | []] | []] Hv] Hl; cbn; cbn in Hl;
  try (destruct Hl as [Hl | Hl]; by contradict Hl).
  assert (H := p_left Hl).
  revert H; rewrite (red_tens_transport_edges _ _ true Hv) Imset.imsetE in_set;
  move => /imageP [[a Hain] Ha Heq].
  assert (Hdone : red_tens_left Htens Hparr (Sub (inl (inl v)) Hv) = Sub a Hain).
  2:{ by rewrite Hdone. }
  rewrite -(red_tens_transport_left _ _ Hv Hl) in Heq.
  apply (red_tens_transport_inj Heq).
Qed.
Arguments red_tens_p_left {G} {e} {Hcut} Htens Hparr.

Lemma red_tens_p_order (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  proper_order (red_tens_graph_data Htens Hparr).
Proof.
  unfold proper_order, red_tens_graph_data, red_tens_order; cbn.
  split.
  - intros [[[v | ] | ] ?]; cbn;
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

Definition red_tens_geos (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) : geos := {|
  graph_data_of := red_tens_graph_data Htens Hparr;
  p_deg := red_tens_p_deg Htens Hparr;
  p_left := red_tens_p_left Htens Hparr;
  p_order := red_tens_p_order Htens Hparr;
  |}.

Lemma red_tens_transport_right (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  forall (v : G) (Hv : inl (inl v) \in [set: red_tens_graph_1 Hcut] :\ (inl (inl (source e))) :\
    (inl (inl (source (other_cut Hcut)))) :\ (inl (inl (target e)))),
  vlabel v = ⊗ \/ vlabel v = ⅋ ->
  red_tens_transport (right (Sub (inl (inl (v))) Hv : red_tens_geos Htens Hparr)) = right v.
Proof.
  intros v Hv Hl.
  set w : red_tens_geos Htens Hparr := Sub (inl (inl v)) Hv.
  apply right_eq; trivial.
  assert (Hdone : red_tens_transport (right w) \in edges_in_at_subset (v : G)).
  { rewrite (red_tens_transport_edges _ _ true Hv).
    by apply imset_f, (@p_right _ w). }
  revert Hdone; rewrite in_set; move => /eqP Hdone.
  splitb.
  rewrite -(red_tens_transport_left _ _ Hv) // -/w.
  intro Hf.
  assert (Hl' : vlabel w = ⊗ \/ vlabel w = ⅋) by (cbn; by rewrite SubK).
  destruct (p_right Hl') as [_ Hc].
  contradict Hc; apply /negP; rewrite negb_involutive; apply /eqP.
  by apply red_tens_transport_inj.
Qed.

Lemma red_tens_transport_ccl (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  forall (v : G) (Hv : inl (inl v) \in [set: red_tens_graph_1 Hcut] :\ (inl (inl (source e))) :\
    (inl (inl (source (other_cut Hcut)))) :\ (inl (inl (target e)))),
  vlabel v = ⊗ \/ vlabel v = ⅋ ->
  red_tens_transport (ccl (Sub (inl (inl (v))) Hv : red_tens_geos Htens Hparr)) = ccl v.
Proof.
  intros v Hv Hl.
  set w : red_tens_geos Htens Hparr := Sub (inl (inl v)) Hv.
  apply ccl_eq; trivial.
  assert (Hdone : red_tens_transport (ccl w) \in edges_out_at_subset (v : G)).
  { rewrite (red_tens_transport_edges _ _ false Hv).
    by apply imset_f, (@p_ccl _ w). }
  revert Hdone; rewrite in_set; by move => /eqP Hdone.
Qed.

Lemma red_tens_transport_edge_of_concl (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  forall (v : G) (Hv : inl (inl v) \in [set: red_tens_graph_1 Hcut] :\ (inl (inl (source e))) :\
    (inl (inl (source (other_cut Hcut)))) :\ (inl (inl (target e)))),
  vlabel v = c ->
  red_tens_transport (edge_of_concl (Sub (inl (inl (v))) Hv : red_tens_geos Htens Hparr)) = edge_of_concl v.
Proof.
  intros v Hv Hl.
  set w : red_tens_geos Htens Hparr := Sub (inl (inl v)) Hv.
  apply concl_eq; trivial.
  assert (Hdone : red_tens_transport (edge_of_concl w) \in edges_in_at_subset (v : G)).
  { rewrite (red_tens_transport_edges _ _ true Hv).
    by apply imset_f, (@p_concl _ w). }
  revert Hdone; rewrite in_set; by move => /eqP Hdone.
Qed.

Lemma red_tens_transport_label (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  forall (a : edge (red_tens_geos Htens Hparr)), elabel a = elabel (red_tens_transport a).
Proof. by intros [[[[[[[a | []] | []] | ] | ] | ] | ] Ha]. Qed.


Lemma red_tens_p_ax_cut (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  proper_ax_cut (red_tens_geos Htens Hparr).
Proof.
  unfold proper_ax_cut.
  destruct (red_tens_new_edges_in Htens Hparr) as [Insssn [Inssn [Insn Inn]]].
  set n := Sub None Inn : edge (red_tens_graph_data Htens Hparr);
  set sn := Sub (Some None) Insn : edge (red_tens_graph_data Htens Hparr);
  set ssn := Sub (Some (Some None)) Inssn : edge (red_tens_graph_data Htens Hparr);
  set sssn := Sub (Some (Some (Some None))) Insssn : edge (red_tens_graph_data Htens Hparr).
  destruct (proper_ax_cut_bis G) as [_ Hpcut].
  specialize (Hpcut (target e) Hcut e (target_in_edges_in e)).
  unfold is_dual_f, is_dual in Hpcut.
  revert Hpcut; move => /eqP Hpcut.
  assert (Ht := p_tens Htens); cbn in Ht.
  assert (Hp := p_parr Hparr); cbn in Hp.
  assert (e = ccl (source e) /\ other_cut Hcut = ccl (source (other_cut Hcut))) as [Hct Hcp]
    by (split; apply ccl_eq; caseb).
  rewrite -Hct in Ht;
  rewrite -Hcp in Hp.
  rewrite Ht Hp in Hpcut; cbn in Hpcut; clear Hct Hcp Ht Hp.
  inversion Hpcut as [[H0 H1]]; clear Hpcut.
  intros b [[[v | []] | []] Hv] Hl; cbn in Hl.
  { destruct (p_ax_cut Hl) as [el [er H]].
    revert H.
    rewrite (red_tens_transport_edges _ _ b Hv).
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

Lemma red_tens_p_tens_parr (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  proper_tens_parr (red_tens_geos Htens Hparr).
Proof.
  unfold proper_tens_parr.
  intros b [[[v | []] | []] Hv] Hl; cbn in Hl.
  all: try (destruct b; by contradict Hl).
  rewrite !red_tens_transport_label red_tens_transport_left ?red_tens_transport_right ?red_tens_transport_ccl;
  try (destruct b; by caseb).
  by apply p_tens_parr.
Qed.

Definition red_tens_ps (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) : proof_structure := {|
  geos_of := @red_tens_geos _ _ _ Htens Hparr;
  p_ax_cut := @red_tens_p_ax_cut _ _ _ _ _;
  p_tens_parr := @red_tens_p_tens_parr _ _ _ _ _;
  |}.


(** Sequent of an tensor - cut reduction *)
Lemma red_tens_sequent (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  sequent (red_tens_ps Htens Hparr) = sequent G.
Proof.
  transitivity ([seq elabel (@red_tens_transport _ _ _ Htens Hparr (edge_of_concl v)) |
    v <- red_tens_order Htens Hparr]).
  { apply eq_map; intros [? ?].
    apply red_tens_transport_label. }
  destruct (red_tens_new_edges_in Htens Hparr) as [_ [_ [_ Inn]]].
  set n := Sub None Inn : edge (red_tens_graph_data Htens Hparr).
  assert ([seq elabel (red_tens_transport (edge_of_concl v)) | v <- red_tens_order Htens Hparr] =
    [seq (match v with | inl (inl v) => elabel (edge_of_concl v) | _ => elabel n end)
    | v <- [seq val v | v <- red_tens_order Htens Hparr]]) as ->.
  { rewrite -map_comp.
    apply (@eq_in_map _); intros [a Ha].
    rewrite /red_tens_order in_seq_sig !SubK -(proj2_sig (all_sigP _)) /red_tens_order_1.
    move => /mapP [x Hx Hax].
    assert (Hxx : inl (inl x) \in [set: red_tens_graph_1 Hcut] :\ inl (inl (source e))
      :\ inl (inl (source (other_cut Hcut))):\ inl (inl (target e))) by by rewrite -Hax.
    assert (Sub a Ha = Sub (inl (inl x)) Hxx) as -> by (apply /eqP; by rewrite sub_val_eq SubK Hax).
    rewrite red_tens_transport_edge_of_concl /comp ?SubK //; by apply p_order. }
  rewrite -(proj2_sig (all_sigP _)) /red_tens_order_1 -map_comp.
  by apply eq_map.
Qed.

(** Decreasing number of vertices *)
Lemma red_tens_nb (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⊗) (Hparr : vlabel (source (other_cut Hcut)) = ⅋) :
  #|red_tens_graph Hcut| = #|G| - 1.
Proof.
  set f := fun (v : red_tens_graph Hcut) => match val v with
  | inl (inl v) => v
  | inl (inr _) => source e
  | inr _ => source (other_cut Hcut)
  end.
  assert (injective f).
  { assert (source e <> source (other_cut Hcut)).
    { intro Hc. contradict Htens.
      by rewrite Hc Hparr. }
    assert (source (other_cut Hcut) <> source e) by by apply nesym.
    intros [[[v | []] | []] Hv] [[[u | []] | []] Hu];
    rewrite /f !SubK;
    intro H.
    all: apply /eqP; rewrite // sub_val_eq SubK ?H //; cbn.
    all: revert Hv Hu.
    all: rewrite !in_set H; cbn.
    all: (try by move => /andP[/eqP ? /andP[/eqP ? /andP[/eqP ? _]]] _);
      try by move => _ /andP[/eqP ? /andP[/eqP ? /andP[/eqP ? _]]]. }
  rewrite -(card_imset (f := f)) //.
  assert (#|setT :\ (target e)| = #|G| - 1) as <-.
  { replace (#|G|) with ((target e \in [set: G]) + #|[set: G] :\ target e|)
      by by rewrite -(cardsD1 (target e)) cardsT.
    rewrite in_set.
    lia. }
  apply eq_card; intro v.
  rewrite Imset.imsetE !in_set andb_true_r.
  destruct (eq_comparable v (target e)) as [Heq | Hneq].
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
    set S := [set: red_tens_graph_1 Hcut] :\ inl (inl (source e))
      :\ inl (inl (source (other_cut Hcut))):\ inl (inl (target e)).
    destruct (eq_comparable v (source e));
    [ | destruct (eq_comparable v (source (other_cut Hcut)))].
    + assert (Hin : inl (inr tt) \in S) by by rewrite !in_set.
      by exists (Sub (inl (inr tt)) Hin).
    + assert (Hin : inr tt \in S) by by rewrite !in_set.
      by exists (Sub (inr tt) Hin).
    + assert (Hin : inl (inl v) \in S) by
        (rewrite !in_set; cbn; splitb; by apply /eqP).
      by exists (Sub (inl (inl v)) Hin).
Qed.

(* TODO remove Arguments red_ax_p_tens_parr {G} {e} Hcut Hax. and replace with @ _ _ _ ? or inverse *)
(* TODO transitivity plus souvent, à la place de assert *)


Lemma cut_parr (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Htens : vlabel (source e) = ⅋) :
  vlabel (source (other_cut Hcut)) <> ax -> vlabel (source (other_cut Hcut)) = ⊗.
Proof.
  intro Hax.
  set e' := other_cut Hcut.
  destruct (proper_ax_cut_bis G) as [_ H].
  unfold proper_cut_bis in H. specialize (H (target e) Hcut).
  unfold true_on2 in H. specialize (H e (endpoint_in_edges_at_subset true e)).
  rewrite -/e' /is_dual_f /is_dual in H. revert H; move => /eqP H.
  assert (Heqe : e = ccl (source e)) by (apply ccl_eq; trivial; caseb).
  assert (Hel : elabel e = parr (elabel (left (source e))) (elabel (right (source e))))
    by (rewrite {1}Heqe; by apply p_parr).
  rewrite Hel in H; cbn in H.
  assert (Hout := p_deg_out (source e')).
  assert (Hc : #|edges_out_at_subset (source e')| <> 0).
  { intro Hc.
    assert (Hf : e' \in set0) by by rewrite -(cards0_eq Hc) in_set.
    contradict Hf. by rewrite in_set0. }
  destruct (vlabel (source e')) eqn:Hv;
  try done; exfalso.
  assert (Hf := p_parr Hv); contradict Hf.
  assert (e' = ccl (source e')) as <- by (apply ccl_eq; trivial; caseb).
  by rewrite -H.
Qed.

Lemma cut_tens (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut) :
  vlabel (source e) = ⊗ -> vlabel (source (other_cut Hcut)) <> ax -> vlabel (source (other_cut Hcut)) = ⅋.
Proof.
  intros Htens Hax.
  set e' := other_cut Hcut.
  destruct (proper_ax_cut_bis G) as [_ H].
  unfold proper_cut_bis in H. specialize (H (target e) Hcut).
  unfold true_on2 in H. specialize (H e (endpoint_in_edges_at_subset true e)).
  rewrite -/e' /is_dual_f /is_dual in H. revert H; move => /eqP H.
  assert (Heqe : e = ccl (source e)) by (apply ccl_eq; trivial; caseb).
  assert (Hel : elabel e = tens (elabel (left (source e))) (elabel (right (source e))))
    by (rewrite {1}Heqe; by apply p_tens).
  rewrite Hel in H; cbn in H.
  assert (Hout := p_deg_out (source e')).
  assert (#|edges_out_at_subset (source e')| <> 0).
  { intro Hc.
    assert (Hf : e' \in set0) by by rewrite -(cards0_eq Hc) in_set.
    contradict Hf. by rewrite in_set0. }
  destruct (vlabel (source e')) eqn:Hv;
  try done; exfalso.
  assert (Hf := p_tens Hv); contradict Hf.
  assert (e' = ccl (source e')) as <- by (apply ccl_eq; trivial; caseb).
  by rewrite -H.
Qed. (* if used, fuse with lemma cut_parr, they are copied-pasted *)


(* TOTHINK Inductive red with both cases ? *)

(* lemma: in ps, there is a cut node <-> red_ax or red_tens possible *)
Lemma red_term (G : proof_structure) (v : G) (H : vlabel v = cut) :
  exists (e : edge G), target e = v /\ (vlabel (source e) = ax \/ (vlabel (source e) = ⊗ /\ vlabel (source e) <> ax)).
Proof.
  destruct (p_cut H) as [e [e' H']];
  revert H'; rewrite !in_set; move => /andP[/andP[/eqP Hin /eqP Hin'] /eqP Heq].
  rewrite -Hin in H.
  assert (Ho : e' = other_cut H).
  { unfold other_cut.
    apply other_eq.
    - by rewrite in_set Hin Hin'.
    - intro Hc; contradict Heq.
      rewrite Hc.
      apply nesym, no_selfdual. }
  assert (Hout := p_deg_out (source e)).
  assert (Hc : #|edges_out_at_subset (source e)| <> 0).
  { intro Hc.
    assert (Hf : e \in set0) by by rewrite -(cards0_eq Hc) in_set.
    contradict Hf. by rewrite in_set0. }
  destruct (vlabel (source e)) eqn:Hle; try done.
  - exists e; splitb; caseb.
  - exists e; splitb.
    destruct (eq_comparable (vlabel (source e)) ax); caseb.
  - exists e'; splitb.
    destruct (eq_comparable (vlabel (source e')) ax) as [? | Hneq]; caseb.
    right; splitb.
    rewrite Ho; rewrite Ho in Hneq.
    apply (cut_parr Hle Hneq).
Qed.

(* TODO faire un fixpoint reduisant tant qu'il y a une coupure *)
(* lemma: sub-confluence + convergence *)
(* lemma: if R is correct and R reduces to R', then R' is correct *)


(** ** Sequentialization *)
(* many things to do: spliting tens / cut, blocking parr, always a
  terminal parr or a splitting *)
(* function to turn a ps into a sequential proof *)
(* TODO voir quelle notion de chemin est utilisée + en discuter (RDV) *)


(***************** UNUSED LEMMA ********************************)
Definition pick_unique2 := fun {T : finType}
  (H : #|T| = 1) => sval (fintype1 H).

(** Removing an element of a set decrease cardinality by 1 *)
Lemma cardsR1_set : forall (T : finType) (a : T) , #|setT :\ a| = #|T| - 1.
Proof. intros T a. rewrite -cardsT (cardsD1 a [set: T]) in_setT. lia. Qed.

Lemma cardsR1 {T : finType} (a : T) (A : {set T}) : #|A :\ a| = #|A| - (a \in A).
Proof. rewrite (cardsD1 a A). lia. Qed.

(** Both visions of a set as set or subset have the same cardinal *)
Lemma card_set_subset {T : finType} (P : pred T) :
  #|[finType of {e : T | P e}]| = #|[set e | P e]|.
Proof. by rewrite card_sig cardsE. Qed.

End Atoms.
(* TODO toujours utiliser = or == partout le même !!! *)
(* TODO use _spec pour casser des cas *)
(* TOTHINK fonction qui dit si formule atomique existe dans yalla, possible de l'ajouter pour
expansion atome *)
(* TODO check if every lemma proved is useful / interesting *)
