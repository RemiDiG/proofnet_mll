(* Unit-free MLL following Yalla schemas *)


From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype funtheory List_more List_Type Permutation_Type_more.
From mathcomp Require Import all_ssreflect zify.
From GraphTheory Require Import preliminaries mgraph.
(* TODO check at the end if all are used *)
(* TODO see file bug_report.v *)

Import EqNotations.

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
induction A; destruct B; (split; intros Heq); inversion Heq; auto.
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
Proof. now induction A; cbn; rewrite ? IHA1 ? IHA2 ? IHA. Qed.

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
Proof. induction A; cbn; by []. Qed.

Lemma fsize_dual A : fsize (dual A) = fsize A.
Proof. induction A; cbn; rewrite ? IHA1 ? IHA2; lia. Qed.


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
Proof. destruct pi; cbn; by []. Qed.

Lemma psize_rew l l' (pi : ll l) (Heq : l = l') : psize (rew Heq in pi) = psize pi.
Proof. now subst. Qed.

(* TODO cleaning above -> psize useless ? *)
(*********************************************************************************************)
(** ** Preliminaries *)

(** * Some results on 'I_n *)
(** The function inord is injective on integers <= n *)
Lemma inord_inj : forall n i j : nat, i <= n -> j <= n -> @inord n i = @inord n j -> i = j.
Proof.
  intros n i j ? ? H.
  assert (Hn : forall k : nat, k <= n -> nat_of_ord (@inord n k) = k).
  { intros. apply inordK. lia. }
  by rewrite -(Hn i) // -(Hn j) // H.
Qed.

(** 'I_0 has the empty enumeration *)
Lemma enum_I0 : enum 'I_0 = [::].
Proof. rewrite -enum0. apply eq_enum, card0_eq, card_ord. Qed.

(** Tactic to distinguish cases in 'I_2 *)
Lemma case_I2 : forall n : 'I_2, (n == ord0) || (n == ord1) : bool.
Proof.
  destruct n as [n Hn].
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
  destruct n as [n Hn].
  repeat (destruct n as [ | n]; trivial).
Qed.

Lemma case_I3bis : forall n : 'I_3, n = ord0 \/ n = ord1 \/ n = ord2.
Proof.
  intro n.
  assert (H := case_I3 n); revert H; move => /orP[/orP[/eqP H | /eqP H] | /eqP H];
  [by left | by right; left | by right; right].
Qed.

Ltac destruct_I3 n H := destruct (case_I3bis n) as [H | [H | H]].

(* TOTHINK possible case_nter avec des set {_}+{_}+...*)


(** Tactic to make cases on if _ == _ *)
(* Make all cases, try to rewrite the equality condition and conserve the condition
  under the form _ = _ or _ <> _, folding trivial cases *)
Ltac case_if := repeat (let Hif := fresh "Hif" in
  case: ifP; cbn; move => /eqP Hif; rewrite ?Hif //).


(** Tactic to split both /\ and && *)
Ltac splitb := repeat (split || apply /andP); trivial.


(** Tactic solving trivial \/ and || *)
Ltac caseb := try done; try (apply /orP); ((left; caseb) || (right; caseb)).


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
  | ax_l, ax_l => true
  | tens_l, tens_l => true
  | parr_l, parr_l => true
  | cut_l, cut_l => true
  | concl_l, concl_l => true
  | _, _ => false
  end.

Lemma eqb_eq_rule : forall A B, eqb_rule A B = true <-> A = B.
Proof.
  destruct A, B; split; cbn; intro H; trivial; now contradict H.
Qed.

Definition rules_dectype := {|
  car := rule;
  dectype.eqb := eqb_rule;
  eqb_eq := eqb_eq_rule |}.
(* TOTHINK rule as a finType ? possible if necessary *)


(** * A DecType is an eqType *)
Definition decType_eqMixin (X : DecType) := EqMixin (eq_dt_reflect (X:=X)).

(* [formula] as an eqType *)
Canonical formula_eqType := EqType formula (decType_eqMixin (formulas_dectype)).

(* [rule] as an eqType *)
Canonical rule_eqType := EqType rule (decType_eqMixin (rules_dectype)).


(** * Some results on cardinality *)
(** Both visions of a set as set or subset have the same cardinal *)
Lemma card_set_subset (T : finType) (P : pred T) :
  #|[finType of {e : T | P e}]| = #|[set e | P e]|.
Proof. by rewrite card_sig cardsE. Qed.

(** Removing an element of a set decrease cardinality by 1 *)
Lemma cardsR1_set : forall (T : finType) (a : T) , #|setT :\ a| = #|T| - 1.
Proof.
  intros ? a.
  replace (#|T|) with ((a \in setT) + #|setT :\ a|)
    by (symmetry; rewrite -cardsT; apply cardsD1).
  rewrite in_setT. lia.
Qed.

Lemma cardsR1_subset : forall (T : finType) (a : T) (A : {set T}),
  #|A :\ a| = #|A| - (a \in A).
Proof.
  intros ? a A.
  replace (#|A|) with ((a \in A) + #|A :\ a|)
    by (symmetry; apply cardsD1).
  lia.
Qed.


Lemma set2R1 : forall (T : finType) (a b : T), b != a -> [set a; b] :\ a = [set b].
Proof.
  intros ? a b H.
  apply /setP; intro e.
  rewrite in_setD1 !in_set.
  rewrite andb_orb_distrib_r andNb; cbn.
  destruct (eq_comparable e b) as [Heq | Hneq].
  - by rewrite Heq H.
  - replace (e == b) with false by (symmetry; by apply /eqP).
    by rewrite andb_false_r.
Qed.

(** Lemma helping computing the cardinal of a subset *)
Lemma enum_subset {T : finType} P : enum [set x | P x] = filter P (enum T).
Proof.
  rewrite enumT.
  apply eq_filter. hnf.
  apply in_set.
Qed.

(** Tactic computing cardinals of subsets of 'I_n, with n fixed to a known nat *)
Ltac compute_card_subIn := rewrite cardE enum_subset; cbn;
                           repeat (rewrite enum_ordS; cbn);
                           now rewrite enum_I0.

(** Function picking the only element of a singleton *)
Definition pick_unique_subset := fun {T : finType} {S : {set T}}
  (H : #|S| = 1) => sval (mem_card1 H).
Definition pick_unique_set := fun {T : finType}
  (H : #|T| = 1) => sval (fintype1 H).

Lemma pick_unique_subset_in {T : finType} {S : {set T}} (H : #|S| = 1) :
  pick_unique_subset H \in S.
Proof.
  replace (pick_unique_subset H \in pred_of_set S)
    with (pred1 (pick_unique_subset H) \subset pred_of_set S)
    by apply subset_pred1.
  apply eq_subxx.
  unfold pick_unique_subset.
  by destruct (mem_card1 H).
Qed.

Lemma p_pick_unique {T : finType} {S : {set T}} (Hs : #|S| = 1) :
  S = [set pick_unique_subset Hs].
Proof.
  symmetry; apply /setP /subset_cardP.
  - by rewrite cards1 Hs.
  - by rewrite sub1set pick_unique_subset_in.
Qed.
(* see which pick_unique is simpler to use, idem lemma card *)

(** Function taking the 2nd element of a 2-elements set *)
Definition unique_other :
  forall (T : finType) (S : {set T}) (x : T),
  #|S| = 2 -> x \in S -> #|S :\ x| = 1.
Proof. intros. rewrite cardsR1_subset. lia. Qed.

Definition other {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :=
  pick_unique_subset (unique_other Hs Hin).

Lemma p_other {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :
  other Hs Hin \in S /\ other Hs Hin != x.
Proof.
  unfold other.
  by destruct (setD1P (pick_unique_subset_in (unique_other Hs Hin))).
Qed.

Lemma p_other2 {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :
  S = [set x; other Hs Hin].
Proof.
  symmetry; apply /setP /subset_cardP.
  - rewrite cards2 Hs.
    assert (x != other Hs Hin) by (rewrite eq_sym ; by destruct (p_other Hs Hin)).
    lia.
  - replace (pred_of_set S) with (pred_of_set (S :|: S)) by (f_equal; apply setUid).
    apply setUSS;
    rewrite sub1set;
    [assumption | apply p_other].
Qed.

Lemma p_other3 {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :
  S :\ x = [set other Hs Hin].
Proof.
  assert (H : S :\ x =i pred1 (other Hs Hin))
    by apply (proj2_sig (mem_card1 (unique_other Hs Hin))).
  apply setP; unfold "=i"; intros.
  by rewrite H in_set unfold_in.
Qed.

Lemma p_other4 {T : finType} {S : {set T}} {x y : T} (Hs : #|S| = 2) (Hx : x \in S)
  (Hy : y \in S) (Hneq : y <> x) : other Hs Hx = y.
Proof.
  symmetry.
  apply /set1P.
  rewrite -p_other3.
  apply /setD1P.
  split;
  [by apply /eqP | by []].
Qed.


(** Symmetric property on set with 2 elements *)
Definition true_on2 {T : finType} {S : {set T}} (P : rel T) (HS : #|S| = 2) :=
  forall (t : T) (Ht : t \in S), P t (other HS Ht).

(* Proving a symmetric property on one suffices to prove it on all *)
Lemma simpl_sym {T : finType} {S : {set T}} (HS : #|S| = 2) (P : rel T)
  (HP : symmetric P) (t : T) (Ht : t \in S) : P t (other HS Ht) -> true_on2 P HS.
Proof.
  intros H s.
  destruct (eq_comparable t s) as [Heq | Hneq].
  - rewrite -Heq.
    intro Hs.
    by replace Hs with Ht by apply eq_irrelevance.
  - intro Hs.
    by rewrite (p_other4 HS Hs Ht Hneq) HP -(p_other4 HS Ht Hs (nesym Hneq)).
Qed.

(* Equality with dual is a symmetric property *)
Definition is_dual := fun A B => dual A == B.

Lemma dual_sym : symmetric is_dual.
Proof.
  unfold symmetric, is_dual.
  intros A B.
  apply /eqP; case_if.
  - by apply codual.
  - apply /eqP; apply (contra (b := dual B == A)).
    + move => /eqP H; apply /eqP. by apply codual.
    + by apply /eqP.
Qed.

Definition is_dual_f {T : Type} (f : T -> formula) :=
  fun (a b : T) => is_dual (f a) (f b).

Lemma dual_sym_f {T : Type} (f : T -> formula) : symmetric (is_dual_f f).
Proof. unfold symmetric, is_dual_f. intros. apply dual_sym. Qed.

Lemma no_selfdual : forall (A : formula), dual A <> A.
Proof. by move => A; elim: A. Qed.


(** Some specific lemmas about seq *)
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
  induction l as [ | ? l H].
  - by [].
  - by rewrite !in_cons H.
Qed.

Lemma uniq_seq_sig {T : eqType} {P : pred T} : forall (l : seq ({x : T | P x})),
  (uniq l) = (uniq [seq sval v | v <- l]).
Proof.
  induction l as [ | b l H].
  - by [].
  - by rewrite map_cons !cons_uniq -H in_seq_sig.
Qed.


(** Image of a set of cardinal 2 *)
Lemma imset_set2 : forall (aT rT : finType) (f : aT -> rT) (x y : aT),
  [set f x | x in [set x; y]] = [set f x; f y].
Proof.
  intros ? ? f x y.
  apply /setP; intro a.
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


(** Lemma about pick *)
Lemma p_pick_some (T : finType) (S : {set T}) (s : T) : [pick x in S] = Some s -> s \in S.
Proof.
  destruct (picksP S); try by [].
  move => /eqP H; revert H; cbn; move => /eqP H; by rewrite -H.
Qed.

Lemma p_pick_none (T : finType) (S : {set T}) : [pick x in S] = None -> #|S| = 0.
Proof.
  destruct (picksP S); try by [].
  subst; by rewrite cards0.
Qed.

Lemma p_pick1 (T : finType) (t : T) : [pick x in [set t]] = Some t.
Proof.
  destruct ([pick x in [set t]]) as [e | ] eqn:He.
  - assert (Hin := p_pick_some He).
    rewrite in_set in Hin.
    by apply /eqP.
  - assert (Hin := p_pick_none He).
    contradict Hin.
    by rewrite cards1.
Qed.


(** Set with 3 elements for case tens, parr and cut *)
Inductive trilean :=
  | tens_t
  | parr_t
  | cut_t.



(** ** Level 0: Multigraphs from the library GraphTheory *)
(** * Notations from the library *)
Open Scope graph_scope.
(* G0 ⊎ G1 = disjoint union
   G ∔ v = add a vertex labelled v
   G ∔ [ x , u , y ] = add an arrow from x to y labelled u *)

(** * Out & In edges of a vertex *)
Definition edges_at_subset (b : bool) {Lv : Type} {Le : Type} {G : graph Lv Le} (v : G) :
  {set edge G} :=
  [set e | endpoint b e == v].
Notation edges_out_at_subset := (edges_at_subset false).
Notation edges_in_at_subset := (edges_at_subset true).



(** ** Level 1: Multigraphs with some more data *)
(** * Definition of [graph_data] *)
Set Primitive Projections.
Record graph_data : Type :=
  Graph_data {
    graph_of :> graph rule formula; (* Vertex label: rule ; Arrow label: formula *)
    left : vertex graph_of -> edge graph_of;
    order : list (vertex graph_of);
  }.
Unset Primitive Projections.

(* TOTHINK
  - direction : bool -> vertex graph_of -> edge graph_of; Notation left := (direction false).
  - fonctions depuis les ensembles totaux vers option _ puis lemma pour label ok <-> Some _
    ex: direction : bool -> graph_of -> option_finType (edge graph_of);
        direction_ok : forall b v, direction b v = Some _ <-> (vlabel c = tens_l \/ 
          vlabel c = parr_l);
  - see sig_finType, used for the function sub_edge in the graph lib : sig [eta mem S] avec
    S : {set G}
  - sum type pour avoir toutes les informations et contraintes selon le type de noeuds
  - mettre direction et ordre plutot dans proof_structure ? (ie cette couche est inutile ?)
  - something else ?
*)
(* TOTHINK fonction qui dit si formule atomique existe dans yalla, possible de l'ajouter pour
expansion atome *)

(** * Functions to weaken a proof *)
Lemma tens_to_tensparr : forall (l : rule), l = tens_l -> l = tens_l \/ l = parr_l.
Proof. intros; by left. Qed.

Lemma parr_to_tensparr : forall (l : rule), l = parr_l -> l = tens_l \/ l = parr_l.
Proof. intros; by right. Qed.


(** * Base case: graph_data of an axiom *)
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
  | 0 => ax_l
  | _ => concl_l
  end;
  elabel := fun e => match val e with
  | 0 => covar x
  | _ => var x
  end;
  |}.
(* conc_l   covar x   ax_l   var x   concl_l
     O     <--------    O   ------->   O
    ord1      ord0    ord0    ord1    ord2   *)

Definition ax_left (x : atom) : vertex (ax_graph x) -> edge (ax_graph x) := fun _ => ord0.
(* No vertex tens nor parr: nonsensical value *)
Arguments ax_left : clear implicits.

Definition ax_order (x : atom) : list (vertex (ax_graph x)) := ord1 :: ord2 :: nil.

Definition ax_graph_data (x : atom) : graph_data := {|
  graph_of := ax_graph x;
  left := ax_left x;
  order := ax_order x;
  |}.


(** * Disjoint union of graph_data *)
(** G0 ⊎ G1 is the disjoint union of G0 and G1 *)

(** Function left for a disjoint union *)
Definition union_left (G0 G1 : graph_data) : G0 ⊎ G1 -> edge (G0 ⊎ G1) :=
  fun v => match v with
  | inl u => inl (left u)
  | inr u => inr (left u)
  end.
Arguments union_left : clear implicits.

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
  left := union_left G0 G1;
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
  all: assert (Hfe: injective fe) by (apply inl_inj || apply inr_inj).
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
  all: assert (Hfv : injective fv) by (apply inl_inj || apply inr_inj).
  all: rewrite !in_cons ?mem_cat ?mem_map //; cbn.
  1: by destruct o0.
  2: by destruct o1.
  1: set vt := v1; set ot := o0; set fvn := inl.
  2: set vt := v0; set ot := o1; set fvn := inr.
  all: destruct (eq_comparable v vt) as [Heq | Hneq];
       [by rewrite Heq eq_refl | ].
  all: revert Hneq; move => /eqP /negPf Hneq.
  all: assert (H' : (fv v \in [seq fvn i | i <- ot]) = false)
        by (clear; by induction ot).
  all: by rewrite Hneq H' ?orb_false_r.
Qed.
Notation union_order_inl := (union_order_in (i := false)).
Notation union_order_inr := (union_order_in (i := true)).


(** * Adding a node to a graph_data *)
(** Add a tens/parr/cut node to a graph_data, replacing 2 conclusions *)
(* Add a tens/parr/cut node, without removing conclusions *)
Definition add_node_graph_1 (c : trilean) {G : graph_data} (e0 e1 : edge G) :=
  (* subgraph to add *)
  let graph_node (b : trilean) := match b with
  | tens_t => edge_graph tens_l (tens (elabel e0) (elabel e1)) concl_l
  | parr_t => edge_graph parr_l (parr (elabel e0) (elabel e1)) concl_l
  | cut_t => unit_graph cut_l
  end in
  let G1 (b : trilean) := G ⊎ graph_node b in
  (* node of the graph receving edges *)
  let target_node := match c return G1 c with
  | tens_t => inr (inl tt)
  | parr_t => inr (inl tt)
  | cut_t => inr tt
  end in
  (* duplicate edges *)
  G1 c ∔ [ inl (source e0) , elabel e0 , target_node ]
       ∔ [ inl (source e1) , elabel e1 , target_node ].

(* Remove the conclusions *)
Definition add_node_graph (c : trilean) {G : graph_data} (e0 e1 : edge G) :=
  let G' := add_node_graph_1 c e0 e1 in
  let S : {set G'} := setT :\ inl (target e0) :\ inl (target e1) in
  induced S.

(** Function left for the graph with a new node *)
(* Function left for the intermediary graph *)
Definition add_node_left_1 (c : trilean) {G : graph_data} (e0 e1 : edge G) :=
  let G' := add_node_graph_1 c e0 e1 in
  fun (v : G') => match v return edge G' with
  | inl u => if target (left u) == target e0 then Some None
             else if target (left u) == target e1 then Some None
             else Some (Some (inl (left u)))
(* artefact for when the value of left is nonsensical: if target (left v) is the node we remove,
we have to give a new (nonsensial) value for the new left *)
  | inr _ => Some None
  end.
(* TOTHINK Damien Pous possible de simplifier ce if / faire autrement ?
ajouter conditions (source (left u) != target e0 && source (left u) != target e1) dans le if ? *)
(* TOTEST left avec option, pour eviter ce if + ajouter un invariant dans geos pour
target (left v) = Some v si v est un tens / parr *)

(* Necessary hypothesis : the nodes we remove have no input edges *)
Lemma add_node_consistent_left (c : trilean) {G : graph_data} (e0 e1 : edge G) :
  let G' := add_node_graph_1 c e0 e1 in
  let S : {set G'} := setT :\ inl (target e0) :\ inl (target e1) in
  (forall e, source e != target e0) /\ (forall e, source e != target e1) ->
  forall v : G', add_node_left_1 v \in edge_set S.
Proof.
  destruct c; cbn;
  intros [H0 H1] [v | v];
  rewrite !in_set; cbn.
  all: splitb; case_if; by apply/eqP.
Qed.

(* Function left for the graph with a new node *)
Definition add_node_left (c : trilean) {G : graph_data} (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  add_node_graph c e0 e1 -> edge (add_node_graph c e0 e1) :=
  fun v => Sub (add_node_left_1 (val v)) (add_node_consistent_left H (val v)).

(** Function order for the graph with a new node *)
(* Remove the 2 nodes from order *)
Definition add_node_order_1 {G : graph_data} (e0 e1 : edge G) :=
  [seq x <- order G | (x != target e0) && (x != target e1)].

(* Give order the type of the intermediary graph *)
Definition add_node_type_order (c : trilean) {G : graph_data} (e0 e1 : edge G) (l : list G) :
  list (add_node_graph_1 c e0 e1) := [seq (inl v) | v <- l].

(* Add the new conclusion if it exists *)
Definition add_node_order_2 (c : trilean) {G : graph_data} (e0 e1 : edge G) :=
  match c return list (add_node_graph_1 c e0 e1) with
  | tens_t | parr_t => [:: inr (inr tt)] | cut_t => nil end
  ++  add_node_type_order c e0 e1 (add_node_order_1 e0 e1).

Lemma add_node_consistent_order (c : trilean) {G : graph_data} (e0 e1 : edge G) :
  let G' := add_node_graph_1 c e0 e1 in
  let S : {set G'} := setT :\ inl (target e0) :\ inl (target e1) in
  all (pred_of_set S) (add_node_order_2 c e0 e1).
Proof.
  apply /allP.
  intros x Hx.
  assert (inl (target e0) \notin (add_node_order_2 c e0 e1) /\
          inl (target e1) \notin (add_node_order_2 c e0 e1)) as [H0 H1].
  { rewrite -2!has_pred1 /add_node_order_2 /add_node_type_order /add_node_order_1.
    destruct c; cbn;
    rewrite 2!has_map /preim 2!has_pred1 2!mem_filter.
    all: by split; apply /negP; move => /andP[/andP[/eqP H0 /eqP H1] _]. }
  repeat (apply /setD1P; split); trivial;
  by apply (in_notin (l := add_node_order_2 c e0 e1)).
Qed.

Definition add_node_order (c : trilean) {G : graph_data} (e0 e1 : edge G) :
  list (vertex (add_node_graph c e0 e1)) :=
  sval (all_sigP (add_node_consistent_order c e0 e1)).

(** Graph data for adding a node *)
Definition add_node_graph_data (c : trilean) {G : graph_data} (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  graph_data := {|
  graph_of := add_node_graph c e0 e1;
  left := add_node_left H;
  order := add_node_order c e0 e1;
  |}.



(** ** Level 2: Geometric Structure *)
(** * Conditions on the neighborhood of a node according to its rule *)
(** Out/In-degree of a node according to its rule *)
Definition deg (b : bool) := match b with
  | false => fun (r : rule) => match r with
    | ax_l => 2
    | tens_l => 1
    | parr_l => 1
    | cut_l => 0
    | concl_l => 0
    end
  | true => fun (r : rule) => match r with
    | ax_l => 0
    | tens_l => 2
    | parr_l => 2
    | cut_l => 2
    | concl_l => 1
    end
  end.
Notation deg_out := (deg false).
Notation deg_in := (deg true).

(* TODO see if proper in bool needed later on *)
(** Property of a geometric structure *)
Definition proper_degree (G : graph_data) :=
  forall (b : bool) (v : G), #|edges_at_subset b v| = deg b (vlabel v).

Definition proper_left (G : graph_data) :=
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
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
(* Nonsensical values for total functions on vertices but where only some vertices matters *)
Definition bogus {G : graph_data} : G -> edge G := fun v => left v.

Lemma p_left3 (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  target (left v) = v.
Proof.
  intros v Hv.
  assert (H := p_left Hv).
  rewrite in_set in H; by apply /eqP.
Qed.

(** Function right for the right premisse of a tens / parr *)
Lemma unique_right (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l -> #|edges_in_at_subset v| = 2.
Proof. intros v [Hl | Hl]; by rewrite p_deg Hl. Qed.

Definition right : forall G : geos, G -> edge G :=
  fun (G : geos) (v : G) =>
  match vlabel v as l return vlabel v = l -> edge G with
  | tens_l => fun Heq => let H' := tens_to_tensparr Heq in
    other (unique_right H') (p_left H')
  | parr_l => fun Heq => let H' := parr_to_tensparr Heq in
    other (unique_right H') (p_left H')
  | _ => fun _ => bogus v
  end Logic.eq_refl.
(* TODO better name for these properties *)
Lemma p_right (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  right v \in edges_in_at_subset v /\ right v != left v.
Proof.
  intros v Hl.
  unfold right.
  split;
  generalize (erefl (vlabel v));
  destruct (vlabel v) at 2 3;
  intro H.
  all: try(
    contradict H;
    destruct Hl as [Hl | Hl];
    by rewrite Hl).
  all: apply p_other.
Qed.

Lemma p_right2 (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  edges_in_at_subset v = [set left v; right v].
Proof.
  intros v Hv.
  unfold right.
  generalize (erefl (vlabel v));
  destruct (vlabel v) at 2 3;
  intro H.
  all: try (
    contradict H;
    destruct Hv as [Hv | Hv];
    by rewrite Hv).
  all: apply p_other2.
Qed.

Lemma p_right3 (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  target (right v) = v.
Proof.
  intros v Hv.
  assert (H := p_right Hv).
  revert H; rewrite in_set; by move => [/eqP H _].
Qed.

Lemma p_right4 (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  forall (e : edge G), target e = v /\ e <> left v -> e = right v.
Proof.
  intros v Hv e [He He'].
  assert (H : e \in edges_in_at_subset v) by by rewrite in_set He.
  revert H.
  rewrite p_right2 // !in_set.
  move => /orP [/eqP H | /eqP H] //.
Qed.

(* General right *)
Definition right' : forall G : graph_data, G -> edge G :=
  fun (G : graph_data) (v : G) => 
  match [pick x in (edges_in_at_subset v) :\ left v] with
  | Some e => e
  | None => bogus v
  end.

Lemma right_eq (G : geos) : forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  right v = right' v.
Proof.
  intros v Hv.
  unfold right'.
  rewrite p_right2 // set2R1. 2:{ by apply p_right. }
  by rewrite p_pick1.
Qed.


(** Function ccl for the conclusion of a tens / parr *)
Lemma unique_ccl (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  #|edges_out_at_subset v| = 1.
Proof. intros v [Hl | Hl]; by rewrite p_deg Hl. Qed.

Definition ccl : forall G : geos, G -> edge G :=
  fun (G : geos) (v : G) =>
  match vlabel v as l return vlabel v = l -> edge G with
  | tens_l => fun Heq => pick_unique_subset (unique_ccl (tens_to_tensparr Heq))
  | parr_l => fun Heq => pick_unique_subset (unique_ccl (parr_to_tensparr Heq))
  | _ => fun _ => bogus v
  end Logic.eq_refl.

Lemma p_ccl (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  ccl v \in edges_out_at_subset v.
Proof.
  intros v Hv.
  unfold ccl.
  generalize (erefl (vlabel v));
  destruct (vlabel v) at 2 3;
  intro H.
  all: try (
    contradict H;
    destruct Hv as [Hv | Hv];
    by rewrite Hv).
  all: apply pick_unique_subset_in.
Qed.

Lemma p_ccl2 (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  edges_out_at_subset v = [set ccl v].
Proof.
  intros v Hv.
  unfold ccl.
  generalize (erefl (vlabel v));
  destruct (vlabel v) at 2 3;
  intro H.
  all: try (
    contradict H;
    destruct Hv as [Hv | Hv];
    by rewrite Hv).
  all: apply p_pick_unique.
Qed.

Lemma p_ccl3 (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  source (ccl v) = v.
Proof.
  intros v Hv.
  assert (H := p_ccl Hv).
  rewrite in_set in H; by apply /eqP.
Qed.

Lemma p_ccl4 (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  forall (e : edge G), source e = v -> e = ccl v.
Proof.
  intros v Hv e He.
  assert (H : e \in edges_out_at_subset v) by by rewrite in_set He.
  revert H.
  rewrite p_ccl2 // in_set.
  by move => /eqP H.
Qed.

(* General ccl *)
Definition ccl' : forall G : graph_data, G -> edge G :=
  fun (G : graph_data) (v : G) =>
  match [pick x in (edges_out_at_subset v)] with
  | Some e => e
  | None => bogus v
  end.

Lemma ccl_eq (G : geos) : forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  ccl v = ccl' v.
Proof.
  intros v Hv.
  unfold ccl'.
  by rewrite p_ccl2 // p_pick1.
Qed.


(** Function returning the unique (input) edge of a conclusion *)
Lemma unique_concl (G : geos) :
  forall (v : G), vlabel v = concl_l ->
  #|edges_in_at_subset v| = 1.
Proof. intros v Hl; by rewrite p_deg Hl. Qed.

Definition edge_of_concl : forall G : geos, G -> edge G :=
  fun (G : geos) (v : G) =>
  match vlabel v as l return vlabel v = l -> edge G with
  | concl_l => fun Heq => pick_unique_subset (unique_concl Heq)
  | _ => fun _ => bogus v
  end Logic.eq_refl.

Lemma p_concl (G : geos) :
  forall (v : G), vlabel v = concl_l -> edge_of_concl v \in edges_in_at_subset v.
Proof.
  intros v Hv.
  unfold edge_of_concl.
  generalize (erefl (vlabel v));
  destruct (vlabel v) at 2 3;
  intro H.
  all: try (
    contradict H;
    by rewrite Hv).
  apply pick_unique_subset_in.
Qed.

Lemma p_concl2 (G : geos) :
  forall (v : G), vlabel v = concl_l -> edges_in_at_subset v = [set edge_of_concl v].
Proof.
  intros v Hv.
  unfold edge_of_concl.
  generalize (erefl (vlabel v));
  destruct (vlabel v) at 2 3;
  intro H.
  all: try (
    contradict H;
    by rewrite Hv).
  apply p_pick_unique.
Qed.

Lemma p_concl3 (G : geos) :
  forall (v : G), vlabel v = concl_l -> target (edge_of_concl v) = v.
Proof.
  intros v Hv.
  assert (H := p_concl Hv).
  rewrite in_set in H; by apply /eqP.
Qed.

Lemma p_concl4 (G : geos) :
  forall (v : G), vlabel v = concl_l ->
  forall (e : edge G), target e = v -> e = edge_of_concl v.
Proof.
  intros v Hv e He.
  assert (H : e \in edges_in_at_subset v) by by rewrite in_set He.
  revert H.
  rewrite p_concl2 // in_set.
  by move => /eqP H.
Qed.

(* General edge_of_concl *)
Definition edge_of_concl' : forall G : graph_data, G -> edge G :=
  fun G (v : G) => 
  match [pick x in (edges_in_at_subset v)] with
  | Some e => e
  | None => bogus v
  end.

Lemma edge_of_concl_eq (G : geos) : forall (v : G), vlabel v = concl_l ->
  edge_of_concl v = edge_of_concl' v.
Proof.
  intros v Hv.
  unfold edge_of_concl'.
  by rewrite p_concl2 // p_pick1.
Qed.


(** Sequent proved by the proof structure *)
Definition sequent (G : geos) : list formula :=
  [seq elabel (edge_of_concl i) | i <- order G].

(* Order is not empty if there is a conclusion *)
Lemma order_neq_nil {G : geos} :
  forall (v : G), vlabel v = concl_l -> order G <> [::].
Proof.
  intros v Hv Hc.
  destruct (p_order G) as [Ho _].
  rewrite Hc in Ho.
  by apply notF, (Ho v).
Qed.


(** * The graph of an axiom is a geometric structure *)
Lemma ax_p_deg (x : atom) : proper_degree (ax_graph_data x).
Proof.
  unfold proper_degree.
  intros [ | ] v;
  destruct_I3 v H;
  rewrite H.
  all: compute_card_subIn.
Qed.
Arguments ax_p_deg : clear implicits.

Lemma ax_p_left (x : atom) : proper_left (ax_graph_data x).
Proof.
  unfold proper_left.
  intros v [Hl | Hl];
  destruct_I3 v H;
  contradict Hl;
  by rewrite H.
Qed.
Arguments ax_p_left : clear implicits.

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
  p_deg := ax_p_deg x;
  p_left := ax_p_left x;
  p_order := ax_p_order x;
  |}.


(** * A disjoint union of geos is a geos *)
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
Arguments union_p_deg : clear implicits.

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
Arguments union_p_left : clear implicits.

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
  p_deg := union_p_deg G0 G1;
  p_left := union_p_left G0 G1;
  p_order := union_p_order G0 G1;
  |}.

(** Useful lemmas on union_geos *)
Lemma union_right (G0 G1 : geos) :
  forall (v : union_geos G0 G1), right v = match v with
  | inl u => inl (right u)
  | inr u => inr (right u)
  end.
Proof.
  intro v;
  destruct (vlabel v) eqn:Hl.
  2: destruct (p_right (tens_to_tensparr Hl)) as [_ Hneq].
  3: destruct (p_right (parr_to_tensparr Hl)) as [_ Hneq].
  2,3: symmetry; apply p_right4; try caseb.
  2,3: destruct v as [v | v]; cbn;
    rewrite p_right3;
    auto; splitb; apply /eqP; apply p_right; auto.
  all:
    destruct v as [v | v];
    unfold right; cbn;
    generalize (erefl (vlabel v));
    destruct (vlabel v) at 2 3 14;
    trivial.
  all:
    intro Hl'; contradict Hl';
    cbn in Hl; by rewrite Hl.
Qed.

Lemma union_ccl (G0 G1 : geos) :
  forall (v : union_geos G0 G1), ccl v = match v with
  | inl u => inl (ccl u)
  | inr u => inr (ccl u)
  end.
Proof.
  intro v;
  destruct (vlabel v) eqn:Hl.
  2,3: symmetry; apply p_ccl4; try caseb.
  2,3: destruct v as [v | v]; cbn;
    rewrite p_ccl3 //; caseb.
  all:
    destruct v as [v | v];
    unfold ccl; cbn;
    generalize (erefl (vlabel v));
    destruct (vlabel v) at 2 3 12;
    trivial.
  all:
    intro Hl'; contradict Hl';
    cbn in Hl; by rewrite Hl.
Qed.

Lemma union_edge_of_concl (G0 G1 : geos) :
  forall (v : union_geos G0 G1), edge_of_concl v = match v with
  | inl u => inl (edge_of_concl u)
  | inr u => inr (edge_of_concl u)
  end.
Proof.
  intro v;
  destruct (vlabel v) eqn:Hl.
  5:{ symmetry; apply p_concl4; trivial.
    destruct v as [v | v]; cbn;
    by rewrite p_concl3. }
  all:
    destruct v as [v | v];
    unfold edge_of_concl; cbn;
    generalize (erefl (vlabel v));
    destruct (vlabel v) at 2 3 10;
    trivial.
  all:
    intro Hl'; contradict Hl';
    cbn in Hl; by rewrite Hl.
Qed.


(** * Adding a node to a geos yields a geos *)
(** Helpers for add_node *)
Lemma add_node_hyp (G : geos) (v0 v1 : G) (l : seq G) (H : order G = v0 :: v1 :: l) :
  (forall e : edge G, source e != target (edge_of_concl v0)) /\
  (forall e : edge G, source e != target (edge_of_concl v1)).
Proof.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  rewrite !p_concl3 //.
  split; [set v := v0; set Hv := Hv0 | set v := v1; set Hv := Hv1];
  intro e.
  all: apply /negP; intro; apply notF.
  all: assert (Hout : edges_out_at_subset v = set0)
    by (apply cards0_eq; by rewrite (p_deg_out v) Hv).
  all: by rewrite -(in_set0 e) -Hout in_set.
Qed.

Lemma add_node_new_edges_in (c : trilean) (G : graph_data) (e0 e1 : edge G)
  (H : (forall e : edge G, source e != target e0) /\ (forall e : edge G, source e != target e1)) :
  let S := setT :\ inl (target e0) :\ inl (target e1) : {set add_node_graph_1 c e0 e1} in
  None \in edge_set S /\ Some None \in edge_set S.
Proof. intros. rewrite !in_set. splitb; try apply H; by destruct c. Qed.

Definition add_node_transport_1 (c : trilean) (G : graph_data) (e0 e1 : edge G) :
  edge G -> edge (add_node_graph_1 c e0 e1) :=
  fun e => if (e == e1) then None
           else if (e == e0) then Some None
           else Some (Some (inl e)).

Lemma add_node_transport_1_inj (c : trilean) (G : graph_data) (e0 e1 : edge G) :
  injective (add_node_transport_1 c e0 e1).
Proof.
  intros e e'.
  unfold add_node_transport_1; case_if.
  by move => /eqP Heqbis; apply /eqP.
Qed.

Lemma add_node_transport_1_edges (c : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  forall (v : G), (v != v0) /\ (v != v1) ->
  edges_in_at_subset (inl v : add_node_graph_1 c (edge_of_concl v0) (edge_of_concl v1)) =
  [set add_node_transport_1 c (edge_of_concl v0) (edge_of_concl v1) e | e in edges_in_at_subset v].
Proof.
  set e0 := edge_of_concl v0;
  set e1 := edge_of_concl v1.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  intros v [Hvv0 Hvv1]; apply /setP; intro e.
  rewrite Imset.imsetE !in_set /add_node_transport_1.
  destruct e as [[[e | e] | ] | ]; cbn.
  - destruct (eq_comparable (target e) v) as [Heq | Hneq].
    + rewrite Heq eq_refl.
      symmetry; apply /imageP.
      exists e.
      * by rewrite in_set Heq.
      * case_if;
        contradict Heq;
        rewrite ?Hif ?Hif0 p_concl3 //;
        apply nesym; by apply /eqP.
    + revert Hneq; move => /eqP Hneq.
      assert (Hr : (target e == v) = false) by by apply /negP /negP.
      rewrite Hr; symmetry; apply /negP /negP.
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
  - destruct c; cbn.
    all: symmetry; apply /negP /negP.
    all: apply /imageP; intros [x Hx Hxx].
    all: contradict Hxx.
    all: case_if.
    all: contradict Hx; apply /negP.
    all: rewrite Hif0 in_set p_concl3 //.
    all: apply /eqP; apply nesym; by apply /eqP.
  - destruct c; cbn.
    all: symmetry; apply /negP /negP.
    all: apply /imageP; intros [x Hx Hxx].
    all: contradict Hxx.
    all: case_if.
    all: contradict Hx; apply /negP.
    all: rewrite Hif in_set p_concl3 //.
    all: apply /eqP; apply nesym; by apply /eqP.
Qed.

Lemma add_node_transport_1_label (c : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) : forall e,
  elabel (add_node_transport_1 c (edge_of_concl v0) (edge_of_concl v1) e) = elabel e.
Proof. intro e. unfold add_node_transport_1; case_if. Qed.

Lemma add_node_transport_consistent (c : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  forall e, add_node_transport_1 c (edge_of_concl v0) (edge_of_concl v1) e \in
  edge_set (setT :\ inl (target (edge_of_concl v0)) :\ inl (target (edge_of_concl v1)) :
  {set add_node_graph_1 c (edge_of_concl v0) (edge_of_concl v1)}).
Proof.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  set S := setT :\ inl (target e0) :\ inl (target e1) : {set add_node_graph_1 c e0 e1}.
  destruct (add_node_new_edges_in c (add_node_hyp H)) as [Hn Hsn].
  intro e.
  unfold add_node_transport_1; case_if.
  rewrite !in_set.
  splitb.
  1,2: apply (add_node_hyp H).
  all: rewrite p_concl3 //; cbn.
  all: apply /negP; move => /eqP ?.
  1: set et := e1. 2: set et := e0.
  all: assert (Hc : e = et) by by apply p_concl4.
  all: by contradict Hc.
Qed.

Definition add_node_transport (c : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  edge G -> edge (add_node_graph_data c (add_node_hyp H)) :=
  fun e => Sub (add_node_transport_1 c (edge_of_concl v0) (edge_of_concl v1) e)
    (add_node_transport_consistent c H e).

Lemma add_node_transport_inj (c : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  injective (add_node_transport c H).
Proof.
  intros e e' Heq.
  apply (add_node_transport_1_inj (EqdepFacts.eq_sig_fst Heq)).
Qed.

Lemma add_node_transport_edges (c : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  forall (v : G) (Hv : inl v \in
  (setT :\ inl (target (edge_of_concl v0)) :\ inl (target (edge_of_concl v1)) :
  {set add_node_graph_1 c (edge_of_concl v0) (edge_of_concl v1)})) (b : bool),
  edges_at_subset b (Sub (inl v) Hv : add_node_graph_data c _)
  = [set add_node_transport c H e | e in edges_at_subset b v].
Proof.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  assert (Hneqv : v0 != v1).
  { elim (p_order G).
    rewrite H cons_uniq in_cons negb_or.
    by move => _ /andP[/andP[? _] _]. }
  assert (Hneqe : e0 == e1 = false).
  { apply negbTE, (contra_neq (z1 := target e0) (z2 := target e1)).
    - apply f_equal.
    - by rewrite !p_concl3. }
  intros v Hv b; apply /setP; intro e.
  assert ((target e0 == v) = false /\ (target e1 == v) = false) as [? ?].
    { split; apply /eqP; intro Hc.
      all: contradict Hv.
      all: rewrite -Hc !in_set eq_refl.
      all: by move => /andP[? /andP[? _]]. }
  set w := Sub (inl v) Hv : add_node_graph_data c (add_node_hyp H).
  set g := add_node_transport c H.
  set g_1 := add_node_transport_1 c e0 e1.
  set g_inj := add_node_transport_inj (c:=c) (H:=H).
  destruct e as [[[[e | e] | ] | ] He];
 rewrite in_set; cbn; rewrite !SubK ; cbn.
  - assert (Heq : Sub (Some (Some (inl e))) He = g e).
    { apply /eqP; rewrite /g /add_node_transport sub_val_eq SubK /add_node_transport_1.
      case_if.
      all: contradict He.
      all: rewrite ?Hif ?Hif0 !in_set eq_refl.
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
      contradict Hneqe; by rewrite Hif eq_refl. }
    rewrite Heq inj_imset // in_set.
    by destruct b, c.
  - assert (Heq : Sub None He = g e1) by
      (apply /eqP; rewrite /g /add_node_transport sub_val_eq SubK /add_node_transport_1; case_if).
    rewrite Heq inj_imset // in_set.
    by destruct b, c.
Qed.

Lemma add_node_transport_label (c : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) : forall e,
  elabel (add_node_transport c H e) = elabel e.
Proof. apply (add_node_transport_1_label _ H). Qed.

Lemma add_node_transport_sequent (c : trilean) (G : geos) (v0 v1 : G) (l : seq G)
  (H : order G = v0 :: v1 :: l) :
  [seq elabel (edge_of_concl' i) | i <- order (add_node_graph_data c (add_node_hyp H))] =
  [seq elabel (match [pick x in edges_in_at_subset i] with
  | Some e => e | None => add_node_left_1 i end) | i <-
  [seq val i | i <- order (add_node_graph_data c (add_node_hyp H))]].
Proof.
  set e0 := edge_of_concl v0;
  set e1 := edge_of_concl v1.
  rewrite /add_node_graph_data /add_node_order /add_node_type_order /add_node_order_1
    /edge_of_concl'.
  set l0 := sval (all_sigP (add_node_consistent_order c e0 e1)).
  assert (Hlv : forall v, v \in l0 -> vlabel (val v) = concl_l).
  { intros [[v | v] Hv] Hl;
    revert Hl;
    rewrite in_seq_sig -(proj2_sig (all_sigP (add_node_consistent_order c e0 e1)))
      /add_node_order_2; cbn.
    - destruct c.
      all: rewrite ?in_cons /add_node_type_order /add_node_order_1 mem_map ?mem_filter;
        [ | apply inl_inj]; cbn.
      all: move => /andP[_ ?].
      all: by apply p_order.
    - destruct c;
      [destruct v as [[] | []] |destruct v as [[] | []] | destruct v as []].
      all: rewrite ?in_cons /add_node_type_order // /add_node_order_1; cbn.
      all: intro Hc; contradict Hc; apply /negP.
      all: apply inr_seq_inl_filter. }
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  induction l0 as [ | [v Hv] l0 IH]; trivial.
  rewrite !map_cons IH; clear IH.
  2:{ intros u Hu. apply Hlv. rewrite in_cons Hu. caseb. }
  f_equal.
  assert (Hl : vlabel v = concl_l).
  { specialize (Hlv (Sub v Hv)).
    rewrite in_seq_sig SubK in_cons eq_refl in Hlv; cbn in Hlv.
    by rewrite -Hlv. }
  assert (v != inl v0 /\ v != inl v1) as [Hvv0 Hvv1].
  { assert (Hv' : v \in (setT :\ inl (target e0) :\ inl (target e1))) by apply Hv.
    rewrite !in_set !p_concl3 // in Hv'.
    revert Hv'; by move => /andP[Hvv1 /andP[Hvv0 _]]. }
  destruct v as [v | v].
  - by rewrite (add_node_transport_edges H) SubK (add_node_transport_1_edges _ H) //
        p_concl2 // !imset_set1 !p_pick1.
  - destruct c; [set c := tens_t | set c := parr_t | set c := cut_t];
    [destruct v as [[] | []] | destruct v as [[] | []] | destruct v as []];
    try by contradict Hl.
    all: assert (Hout_1 : edges_in_at_subset (inr (inr tt) : add_node_graph_1 c e0 e1)
      = [set Some (Some (inr None))])
      by (apply /setP; intro e; rewrite !in_set; by destruct e as [[[e | [[[] | []] | ]] | ] | ]).
    all: assert (Hss: Some (Some (inr None)) \in edge_set ([set: add_node_graph_1 c e0 e1]
      :\ inl (target e0) :\ inl (target e1))) by (rewrite !in_set; splitb; apply (add_node_hyp H)).
    all: set ss := Sub (Some (Some (inr None))) Hss : edge (add_node_graph_data c (add_node_hyp H)).
    all: assert (Hout : edges_in_at_subset (Sub (inr (inr tt)) Hv : add_node_graph_data c
      (add_node_hyp H)) = [set ss]) by
      (apply /setP; intro e; rewrite !in_set; by destruct e as [[[[e | [[[] | []] | ]] | ] | ] ?]).
    all: by rewrite !SubK Hout_1 Hout !p_pick1.
Qed.

(* We add the node if it respect the rules, do nothing if it is inadequate *)
Definition add_node_graph_data_bis : trilean -> geos -> graph_data :=
  fun (c : trilean) (G : geos) =>
  match order G as o return order G = o -> graph_data with
  | v0 :: v1 :: _ => match c with
    | cut_t => if (elabel (edge_of_concl v0) == dual (elabel (edge_of_concl v1)))
      then fun Heq => add_node_graph_data c (add_node_hyp Heq) else fun _ => G
    | _ => fun Heq => add_node_graph_data c (add_node_hyp Heq)
    end
  | _ => fun _ => G
  end Logic.eq_refl.


Lemma add_node_p_deg (c : trilean) (G : geos) : proper_degree (add_node_graph_data_bis c G).
Proof.
  unfold add_node_graph_data_bis.
  generalize (erefl (order G));
  destruct (order G) as [ | v0 [ | v1 l]] at 2 3;
  intro H; try (apply p_deg).
  revert c.
  assert (forall c, proper_degree (add_node_graph_data c (add_node_hyp H))).
  2:{ intros [ | | ]; trivial.
      case_if.
      apply p_deg. }
  intro c.
  unfold proper_degree.
  intros b [[v | v] Hv]; cbn.
  - by rewrite (add_node_transport_edges H) -(p_deg b v)
      -(card_imset (edges_at_subset b v) (add_node_transport_inj (c := c) (H := H))).
  - set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
    set S := setT :\ inl (target e0) :\ inl (target e1) : {set add_node_graph_1 c e0 e1}.
    destruct (add_node_new_edges_in c (add_node_hyp H)) as [Hn Hsn].
    set n := Sub None Hn : edge (add_node_graph_data c (add_node_hyp H));
    set sn := Sub (Some None) Hsn : edge (add_node_graph_data c (add_node_hyp H)).
    destruct c;
    [set c := tens_t | set c := parr_t | set c := cut_t].
    1,2: assert (Some (Some (inr None)) \in edge_set S /\ inr (inl tt) \in S /\ inr (inr tt) \in S)
          as [Hss [Htn Hcn]] by (rewrite !in_set; splitb).
    1,2: set ss := Sub (Some (Some (inr None))) Hss : edge (add_node_graph_data c (add_node_hyp H));
         set tn := Sub (inr (inl tt)) Htn : add_node_graph_data c (add_node_hyp H);
         set cn := Sub (inr (inr tt)) Hcn : add_node_graph_data c (add_node_hyp H).
    1,2: assert (edges_in_at_subset tn = [set n; sn] /\ edges_out_at_subset tn = [set ss] /\
                 edges_in_at_subset cn = [set ss] /\ edges_out_at_subset cn = set0)
          as [Htn_in [Htn_out [Hcn_in Hcn_out]]]
          by (splitb; apply /setP; intro e; rewrite !in_set;
            by destruct e as [[[[e | [[[] | []] | ]] | ] | ] ?]).
    3: assert (Htn : inr tt \in S) by (rewrite !in_set; apply /andP; by split).
    3: set tn := (Sub (inr tt) Htn : add_node_graph_data c (add_node_hyp H)).
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
Arguments add_node_p_deg : clear implicits.

Lemma add_node_p_left (c : trilean) (G : geos) : proper_left (add_node_graph_data_bis c G).
Proof.
  unfold add_node_graph_data_bis.
  generalize (erefl (order G));
  destruct (order G) as [ | v0 [ | v1 l]] at 2 3;
  intro H; try (apply p_left).
  revert c.
  assert (forall c, proper_left (add_node_graph_data c (add_node_hyp H))).
  2:{ intros [ | | ]; trivial.
      case_if.
      apply p_left. }
  intro c.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  unfold proper_left.
  destruct (add_node_hyp H).
  intros [[v | v] Hv]; cbn;
  intro Hl; unfold add_node_left.
  - rewrite in_set; cbn.
    rewrite !SubK !p_concl3 // p_left3 //.
    case_if; apply /eqP; rewrite ?p_left3 //;
    destruct Hl as [Hl | Hl];
    contradict Hl; by rewrite ?Hif ?Hif0 ?Hv0 ?Hv1.
  - destruct c;
    [destruct v as [[] | []] | destruct v as [[] | []] | destruct v as []].
    all: try (destruct Hl as [Hl | Hl]; by contradict Hl).
    all: by rewrite in_set !SubK.
Qed.
Arguments add_node_p_left : clear implicits.

Lemma add_node_p_order (c : trilean) (G : geos) : proper_order (add_node_graph_data_bis c G).
Proof.
  unfold add_node_graph_data_bis.
  generalize (erefl (order G));
  destruct (order G) as [ | v0 [ | v1 l]] at 2 3;
  intro H; try (apply p_order).
  revert c.
  assert (forall c, proper_order (add_node_graph_data c (add_node_hyp H))).
  2:{ intros [ | | ]; trivial.
      case_if.
      apply p_order. }
  intro c.
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  unfold proper_order.
  destruct (p_order G) as [Hv U].
  split; cbn.
  - intros [[v | v] Hin]; cbn;
    rewrite /add_node_order in_seq_sig SubK
        -(proj2_sig (all_sigP (add_node_consistent_order c e0 e1))) /add_node_order_2.
    + apply (iff_stepl (A := v \in order G)). 2:{ by apply iff_sym. }
        assert (v != target e0 /\ v != target e1) as [Hv0 Hv1].
        { split;
          apply /negP; move => /eqP Hc;
          contradict Hin; apply /negP;
          rewrite Hc !in_set;
          [apply /nandP; right | ];
          apply /nandP; left;
          by rewrite negb_involutive. }
          destruct c;
          rewrite ?in_cons /add_node_type_order/ add_node_order_1 mem_map //; cbn; trivial.
          all: by rewrite mem_filter Hv0 Hv1.
    + destruct c;
      [destruct v as [[] | []] | destruct v as [[] | []] | destruct v as []].
      all: cbn; split; trivial; intro Hl; contradict Hl.
      all: rewrite // ?in_cons /add_node_order_2 /add_node_type_order /add_node_order_1;
           cbn; apply /negP.
      all: apply inr_seq_inl_filter.
  - rewrite /add_node_order uniq_seq_sig
      -(proj2_sig (all_sigP (add_node_consistent_order c e0 e1))) /add_node_order_2.
    destruct c;
    rewrite ?cons_uniq /add_node_type_order /add_node_order_1.
    1,2: apply /andP; split; [apply (inr_seq_inl_filter (order G) _ (inr tt)) | ].
    all: rewrite map_inj_uniq //; cbn; trivial; by apply filter_uniq.
Qed.
Arguments add_node_p_order : clear implicits.

Definition add_node_geos (c : trilean) (G : geos) : geos := {|
  graph_data_of := add_node_graph_data_bis c G;
  p_deg := add_node_p_deg c G;
  p_left := add_node_p_left c G;
  p_order := add_node_p_order c G;
  |}.



(** ** Level 3: Proof Structure *)
(** * The rule of a node gives conditions on the formulae of its arrows *)
Definition proper_ax_cut (G : geos) :=
  forall (b : bool),
  let rule := if b then cut_l else ax_l in
  forall (v : G), vlabel v = rule -> exists el, exists er,
  (el \in edges_at_subset b v) && (er \in edges_at_subset b v) &&
  (elabel el == dual (elabel er)).
Lemma pre_proper_ax (G : geos) (v : G) (Hl : vlabel v = ax_l) :
  #|edges_out_at_subset v| = 2.
Proof. by rewrite p_deg Hl. Qed.
Definition proper_ax3 (G : geos) :=
  forall (v : G) (Hl : vlabel v = ax_l),
  true_on2 (is_dual_f (elabel (g := G))) (pre_proper_ax Hl).
Lemma equiv_ax (G : geos) : proper_ax_cut G -> proper_ax3 G.
Proof.
  unfold proper_ax_cut, proper_ax3.
  intros H v Hl.
  elim: (H false v Hl) => [el [er /andP[/andP[Hel Her] /eqP Heq]]].
  assert (Ho : other (pre_proper_ax Hl) Hel = er).
  { apply p_other4; trivial.
    intro Hc.
    rewrite Hc in Heq; symmetry in Heq.
    contradict Heq; apply no_selfdual. }
  apply (simpl_sym (dual_sym_f (elabel (g := G))) (Ht := Hel)).
  by rewrite /is_dual_f /is_dual Ho Heq bidual.
Qed.
Lemma pre_proper_cut (G : geos) (v : G) (Hl : vlabel v = cut_l) :
  #|edges_in_at_subset v| = 2.
Proof. by rewrite p_deg Hl. Qed.
Definition proper_cut3 (G : geos) :=
  forall (v : G) (Hl : vlabel v = cut_l),
  true_on2 (is_dual_f (elabel (g := G))) (pre_proper_cut Hl).
Lemma equiv_cut (G : geos) : proper_ax_cut G -> proper_cut3 G.
Proof.
  unfold proper_ax_cut, proper_cut3.
  intros H v Hl.
  elim: (H true v Hl) => [el [er /andP[/andP[Hel Her] /eqP Heq]]].
  assert (Ho : other (pre_proper_cut Hl) Hel = er).
  { apply p_other4; trivial.
    intro Hc.
    rewrite Hc in Heq; symmetry in Heq.
    contradict Heq.
    apply no_selfdual. }
  apply (simpl_sym (dual_sym_f (elabel (g := G))) (Ht := Hel)).
  by rewrite /is_dual_f /is_dual Ho Heq bidual.
Qed.

Definition proper_tens_parr (G : geos) :=
  forall (b : bool),
  let rule := if b then parr_l else tens_l in
  let form := if b then parr else tens in
  forall (v : G), vlabel v = rule ->
  elabel (ccl v) = form (elabel (left v)) (elabel (right v)).
(* TODO modif bool dans proper_tens parr ?*)

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


(** * The axiom graph is a proof_structure *)
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
Arguments ax_p_ax_cut : clear implicits.

Lemma ax_p_tens_parr (x : atom) : proper_tens_parr (ax_geos x).
Proof.
  unfold proper_tens_parr.
  intros b v Hl.
  destruct b;
  destruct_I3 v Hv;
  contradict Hl;
  by rewrite Hv.
Qed.
Arguments ax_p_tens_parr : clear implicits.

Lemma ax_p_ax3 (x : atom) : proper_ax3 (ax_geos x).
Proof.
  unfold proper_ax3.
  intros v Hl.
  destruct_I3 v Hv;
  try (contradict Hl; by rewrite Hv).
  assert (ord0 \in edges_out_at_subset v /\ ord1 \in edges_out_at_subset v) as [H0 H1]
    by by rewrite /edges_out_at_subset Hv !in_set.
  apply (simpl_sym (dual_sym_f (elabel (g:=ax_geos x))) (Ht := H0)).
  by rewrite /is_dual_f /is_dual (p_other4 (y := ord1)).
Qed.

Definition ax_ps (x : atom) : proof_structure := {|
  geos_of := ax_geos x;
  p_ax_cut := ax_p_ax_cut x;
  p_tens_parr := ax_p_tens_parr x;
  |}.


(** * A disjoint union of proof_structure is a proof_structure *)
Lemma union_p_ax_cut (G0 G1 : proof_structure) : proper_ax_cut (union_geos G0 G1).
Proof.
  unfold proper_ax_cut.
  intros b [v | v] Hl; cbn; cbn in Hl.
  all: destruct (p_ax_cut Hl) as [el [er He]].
  1: exists (inl el), (inl er); rewrite !union_edges_at_inl.
  2: exists (inr el), (inr er); rewrite !union_edges_at_inr.
  all: rewrite !inj_imset //; by cbn.
Qed.
Arguments union_p_ax_cut : clear implicits.

Lemma union_p_tens_parr (G0 G1 : proof_structure) : proper_tens_parr (union_geos G0 G1).
Proof.
  unfold proper_tens_parr.
  intros b [v | v] Hl;
  rewrite union_right union_ccl;
  by apply p_tens_parr.
Qed.
Arguments union_p_tens_parr : clear implicits.

Lemma union_p_ax3 (G0 G1 : proof_structure) : proper_ax3 (union_geos G0 G1).
Proof.
  assert (proper_ax3 G0 /\ proper_ax3 G1) as [H0 H1] by (split; apply equiv_ax, p_ax_cut).
  (* TODO change the previous line when proper_ax chosen *)
  unfold proper_ax3.
  intros v Hl e He.
  set o := other (pre_proper_ax Hl) He.
  destruct v as [v | v]; cbn in Hl;
  destruct e as [e | e].
  2,3: unfold o; clear o; contradict He; apply /negP.
  2,3: rewrite ?union_edges_at_inl ?union_edges_at_inr Imset.imsetE in_set.
  2,3: apply /imageP; move => [? _ A].
  2,3: by contradict A.
  1: set fe := inl : edge G0 -> edge (union_geos G0 G1); set fv := inl : G0 -> union_geos G0 G1.
  2: set fe := inr : edge G1 -> edge (union_geos G0 G1); set fv := inr : G1 -> union_geos G0 G1.
  all: assert (injective fe) by (apply inl_inj || apply inr_inj).
  all: assert (Hin : fe e \in edges_out_at_subset (fv v)) by by [].
  all: rewrite ?union_edges_at_inl ?union_edges_at_inr inj_imset // in Hin.
  all: assert (Hd : dual (elabel e) = elabel (other (pre_proper_ax Hl) Hin))
        by by apply /eqP; (apply H0 || apply H1).
  all: assert (Ho : o = fe (other (pre_proper_ax Hl) Hin)) by
        (unfold o;
        case: (p_other (pre_proper_ax Hl) Hin) => [? ?];
        apply p_other4;
        rewrite ?union_edges_at_inl ?union_edges_at_inr ?inj_imset //;
        by apply /eqP).
  all: rewrite /is_dual_f /is_dual Hd Ho; by apply /eqP.
Qed.

Lemma union_p_cut3 (G0 G1 : proof_structure) : proper_cut3 (union_geos G0 G1).
Proof.
  assert (proper_cut3 G0 /\ proper_cut3 G1) as [H0 H1] by (split; apply equiv_cut, p_ax_cut).
  (* TODO change the previous line when proper_cut chosen *)
  unfold proper_cut3.
  intros v Hl e He.
  set o := other (pre_proper_cut Hl) He.
  destruct v as [v | v]; cbn in Hl;
  destruct e as [e | e].
  2,3: unfold o; clear o; contradict He; apply /negP.
  2,3: rewrite ?union_edges_at_inl ?union_edges_at_inr Imset.imsetE in_set.
  2,3: apply /imageP; move => [? _ A].
  2,3: by contradict A.
  1: set fe := inl : edge G0 -> edge (union_geos G0 G1); set fv := inl : G0 -> union_geos G0 G1.
  2: set fe := inr : edge G1 -> edge (union_geos G0 G1); set fv := inr : G1 -> union_geos G0 G1.
  all: assert (injective fe) by (apply inl_inj || apply inr_inj).
  all: assert (Hin : fe e \in edges_in_at_subset (fv v)) by by [].
  all: rewrite ?union_edges_at_inl ?union_edges_at_inr inj_imset // in Hin.
  all: assert (Hd : dual (elabel e) = elabel (other (pre_proper_cut Hl) Hin))
        by by apply /eqP; (apply H0 || apply H1).
  all: assert (Ho : o = fe (other (pre_proper_cut Hl) Hin)) by
        (unfold o;
        case: (p_other (pre_proper_cut Hl) Hin) => [? ?];
        apply p_other4;
        rewrite ?union_edges_at_inl ?union_edges_at_inr ?inj_imset //;
        by apply /eqP).
  all: rewrite /is_dual_f /is_dual Hd Ho; by apply /eqP.
Qed.

Definition union_ps (G0 G1 : proof_structure) : proof_structure := {|
  geos_of := union_geos G0 G1;
  p_ax_cut := union_p_ax_cut G0 G1;
  p_tens_parr := union_p_tens_parr G0 G1;
  |}.


(** * Adding a node to a proof_structure yields a proof_structure *)
Lemma add_node_p_ax_cut (c : trilean) (G : proof_structure) : proper_ax_cut (add_node_geos c G).
Proof.
  remember (order G) as l eqn:H; symmetry in H.
  unfold add_node_geos, add_node_graph_data_bis, proper_ax_cut; cbn.
  assert (Hdone : forall (b : bool) (v : match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match c with
      | cut_t => if (elabel (edge_of_concl v0)) == (elabel (edge_of_concl v1)^)
        then fun Heq => add_node_graph_data c (add_node_hyp Heq) else fun=> G
      | _ => fun Heq  => add_node_graph_data c (add_node_hyp Heq)
      end
    | _ => fun=> G
    end H), vlabel v = (if b then cut else ax) ->
    exists (el er : edge (match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match c with
      | cut_t => if (elabel (edge_of_concl v0)) == (elabel (edge_of_concl v1)^)
        then fun Heq => add_node_graph_data c (add_node_hyp Heq) else fun=> G
      | _ => fun Heq => add_node_graph_data c (add_node_hyp Heq)
      end
    | _ => fun=> G
    end H)), (el \in edges_at_subset b v) && (er \in edges_at_subset b v) &&
    (elabel el == dual (elabel er))).
  2:{ by rewrite <-!H in Hdone. }
  destruct l as [ | v0 [ | v1 l]];
  try (apply p_ax_cut).
  assert (Hdone : c <> cut_t \/ elabel (edge_of_concl v0) = dual (elabel (edge_of_concl v1)) ->
    forall b (v : add_node_graph_data c (add_node_hyp H)),
    vlabel v = (if b then cut else ax) ->
    exists el er : edge (add_node_graph_data c (add_node_hyp H)),
    (el \in edges_at_subset b v) && (er \in edges_at_subset b v) && (elabel el == elabel er^)).
  2:{ case_if.
      - replace (match c with | tens_t | _ => fun Heq => add_node_graph_data c (add_node_hyp Heq)
          end H) with (add_node_graph_data c (add_node_hyp H)) by by destruct c.
        apply Hdone; by right.
      - destruct c;
        [apply Hdone; by left | apply Hdone; by left | apply p_ax_cut]. }
  intros Hor b [[v | v] Hv] Hl; cbn in Hl; cbn.
  - elim (p_ax_cut Hl) => el [er /andP[/andP[Hel Her] /eqP Helr]].
    exists (add_node_transport c H el), (add_node_transport c H er).
    rewrite !(add_node_transport_edges H) !inj_imset ?Hel ?Her;
    [ | apply add_node_transport_inj | apply add_node_transport_inj]; cbn.
    rewrite /add_node_transport !SubK /add_node_transport_1.
    case_if; apply /eqP.
    all: try by rewrite -?Hif -?Hif0 -?Hif1 -?Hif2.
    all: contradict Helr;
      rewrite ?Hif ?Hif0 ?Hif1 ?Hif2;
      apply nesym, no_selfdual.
  - destruct b, c, v;
    try (by contradict Hl).
    set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
    set S := setT :\ inl (target e0) :\ inl (target e1) : {set add_node_graph_1 cut_t e0 e1}.
    destruct (add_node_new_edges_in cut_t (add_node_hyp H)) as [Hn Hsn].
    set n := Sub None Hn : edge (add_node_graph_data cut_t (add_node_hyp H));
    set sn := Sub (Some None) Hsn : edge (add_node_graph_data cut_t (add_node_hyp H)).
    exists n, sn.
    assert (elabel e1 == dual (elabel e0))
      by (destruct Hor as [Hc | Heq]; by rewrite // Heq bidual).
    rewrite !in_set; cbn; by rewrite !SubK.
Qed.
Arguments add_node_p_ax_cut : clear implicits.

Lemma add_node_p_tens_parr (c : trilean) (G : proof_structure) :
  proper_tens_parr (add_node_geos c G).
Proof.
  remember (order G) as l eqn:H; symmetry in H.
  unfold add_node_geos, add_node_graph_data_bis.
  intros b r f v Hv; rewrite ccl_eq ?right_eq;
  [ | destruct b; caseb | destruct b; caseb];
  revert v Hv; cbn.
  assert (Hdone : forall (v : match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match c with
      | cut_t => if (elabel (edge_of_concl v0)) == (elabel (edge_of_concl v1)^)
        then fun Heq => add_node_graph_data c (add_node_hyp Heq) else fun=> G
      | _ => fun Heq => add_node_graph_data c (add_node_hyp Heq)
      end
    | _ => fun=> G
    end H), vlabel v = r -> elabel (ccl' v) = f (elabel (left v)) (elabel (right' v))).
  2:{ by rewrite <-!H in Hdone. }
  destruct l as [ | v0 [ | v1 l]];
  intros v Hv;
  assert (Hor : vlabel v = tens_l \/ vlabel v = parr_l) by (destruct b; [by right | by left]);
  try (rewrite -ccl_eq // -right_eq //; by apply p_tens_parr).
  revert c v Hv Hor.
  assert (Hdone : forall c (v : add_node_graph_data c (add_node_hyp H)),
    vlabel v = r -> vlabel v = ⊗ \/ vlabel v = ⅋ ->
    elabel (ccl' v) = f (elabel (left v)) (elabel (right' v))).
  2:{ intros [ | | ];
      [specialize (Hdone tens_t) | specialize (Hdone parr_t) | specialize (Hdone cut_t)]; trivial.
      case_if; rewrite -?Hif //.
      intros; rewrite -ccl_eq // -right_eq //; by apply p_tens_parr. }
  intros c [[v | v] Hin] Hv Hor.
  - cbn in Hv; cbn in Hor.
    set w := Sub (inl v) Hin : add_node_graph_data c (add_node_hyp H).
    assert (Hneq := Hin); rewrite !in_set in Hneq; cbn in Hneq;
    revert Hneq; move => /andP[/eqP Hneq1 /andP[/eqP Hneq0 _]].
    assert (left v <> edge_of_concl v0) by (intro Hc; by rewrite -Hc p_left3 in Hneq0);
    assert (left v <> edge_of_concl v1) by (intro Hc; by rewrite -Hc p_left3 in Hneq1).
    assert (Hvw : left w = add_node_transport c H (left v)).
    { apply /eqP;  rewrite /add_node_transport /add_node_left sub_val_eq SubK
        /add_node_transport_1 /add_node_left_1; apply /eqP.
      case_if.
      - by rewrite p_left3 // p_concl3 in Hif.
      - by rewrite p_left3 // p_concl3 in Hif0. }
    rewrite Hvw add_node_transport_label.
    assert (ccl' w \in edges_out_at_subset w /\ right' w \in edges_in_at_subset w :\ left w)
      as [Hccl Hright].
    { rewrite /ccl' /right' !add_node_transport_edges !p_ccl2 // !p_right2 // !imset_set1 Hvw.
      replace ([set add_node_transport c H e | e in [set left v; right v]]
      :\ add_node_transport c H (left v)) with [set add_node_transport c H (right v)].
      2:{ rewrite imset_set2 set2R1 // inj_eq; [ | apply add_node_transport_inj].
        by apply p_right. }
      by rewrite !p_pick1 !in_set. }
    rewrite add_node_transport_edges Imset.imsetE in_set p_ccl2 // in Hccl.
    revert Hccl; move => /imageP [eccl Heccl_in Heccl_eq].
    revert Heccl_in; rewrite in_set; move => /eqP Heccl_in.
    rewrite Heccl_eq add_node_transport_label Heccl_in.
    rewrite add_node_transport_edges Imset.imsetE !in_set in Hright.
    revert Hright; move => /andP[Heright_neq /imageP [eright Heright_in Heright_eq]].
    rewrite Heright_eq add_node_transport_label.
    replace eright with (right v).
    2:{ revert Heright_in;
      rewrite p_right2 // !in_set; move => /orP[/eqP Heright_in | /eqP Heright_in //].
      contradict Heright_neq; apply /negP;
      rewrite negb_involutive Heright_eq Heright_in.
      cbn; rewrite !SubK /add_node_left_1 /add_node_transport_1.
      assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1]
        by (split; apply p_order; rewrite H !in_cons; caseb).
      assert (Hneqv : v0 <> v1).
      { elim (p_order G).
        rewrite H cons_uniq in_cons negb_or.
        by move => _ /andP[/andP[/eqP ? _] _]. }
       assert (target (left v) <> target (edge_of_concl v0) /\
        target (left v) <> target (edge_of_concl v1)) as [Hc0 Hc1]
        by rewrite p_left3 //.
      case_if. }
    by apply p_tens_parr.
  - destruct c;
    [set c := tens_t | set c := parr_t | set c := cut_t];
    [destruct v as [[] | []] | destruct v as [[] | []] | destruct v as []];
    destruct b;
    try (by contradict Hv).
    all: set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
    all: set S := setT :\ inl (target e0) :\ inl (target e1) : {set add_node_graph_1 c e0 e1}.
    all: destruct (add_node_new_edges_in c (add_node_hyp H)) as [Hn Hsn].
    all: assert (Hss : Some (Some (inr None)) \in edge_set S) by
      (rewrite !in_set; splitb; try (apply (add_node_hyp H)); by destruct c).
    all: set n := Sub None Hn : edge (add_node_graph_data c (add_node_hyp H));
      set sn := Sub (Some None) Hsn : edge (add_node_graph_data c (add_node_hyp H));
      set ss := Sub (Some (Some (inr None))) Hss : edge (add_node_graph_data c (add_node_hyp H));
      set tn := Sub (inr (inl tt)) Hin : add_node_graph_data c (add_node_hyp H).
    all: assert (edges_in_at_subset tn = [set n; sn] /\ edges_out_at_subset tn = [set ss])
      as [Htn_in Htn_out] by (split; apply /setP; intro e; rewrite !in_set;
      by destruct e as [[[[e | [[[] | []] | ]] | ] | ] ?]).
    all: assert (Hleft : left tn = sn) by (apply /eqP; by rewrite sub_val_eq !SubK).
    all: assert (ccl' tn = ss /\ right' tn = n) as [Hccl Hright]
      by by rewrite /ccl' /right' Htn_in Htn_out set2C set2R1 // !p_pick1.
    all: by rewrite Hleft Hccl Hright.
Qed.
Arguments add_node_p_tens_parr : clear implicits.

Definition add_node_ps (c : trilean) (G : proof_structure) : proof_structure := {|
  geos_of := add_node_geos c G;
  p_ax_cut := add_node_p_ax_cut c G;
  p_tens_parr := add_node_p_tens_parr c G;
  |}.



(** ** Proof Structure of a Proof Sequent *)
(* TOTHINK mettre les ax, union, add_node ici ? *)

(** * Permuting the conclusions of a geos *)
(** Function taking two lists l1 l2 permutations of one another, and returning a
polymorphic permutation sending l1 to l2 *)
Fixpoint perm_of {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) {struct sigma} :
  forall {B : Type}, seq B -> seq B :=
  match sigma with
  | Permutation_Type_nil_nil => fun _ => id
  | Permutation_Type_skip x l l' tau => fun _ b => match b with
    | d :: e => d :: (perm_of tau e)
    | [::] => [::]
    end
  | Permutation_Type_swap x y l => fun _ b => match b with
    | f :: d :: e => d :: f :: e
    | _ => b
    end
  | Permutation_Type_trans l l' l'' tau1 tau2 => fun _ b => perm_of tau2 (perm_of tau1 b)
  end.

Lemma perm_of_consistent {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) :
  perm_of sigma l1 = l2.
Proof.
  unfold perm_of.
  induction sigma as [ | x l l' sigma H | x y l | l l' l'' sigma H sigma' H'];
  by rewrite ?H ?H' //.
Qed.

Lemma perm_of_map : forall {A B S : Type} (l : seq A) (f : A -> B) (l1 l2 : seq S)
  (sigma : Permutation_Type l1 l2), perm_of sigma [seq f i | i <- l]
  = [seq f i | i <- perm_of sigma l].
Proof.
  intros A B S l0 f l1 l2 sigma.
  revert A B l0 f.
  induction sigma as [ | x l l' sigma H | x y l | l l' l'' sigma H sigma' H']; cbn;
  intros A B l0 f.
  - by [].
  - destruct l0; cbn; by rewrite // H.
  - by destruct l0 as [ | a [ | b l0]].
  - by rewrite H H'.
Qed.

Lemma perm_of_in {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) :
  forall {B : finType} (l : seq B) (b : B), (b \in perm_of sigma l) = (b \in l).
Proof.
  induction sigma as [ | x l l' sigma H | x y l | l l' l'' sigma H sigma' H']; cbn;
  intros B l0 b.
  - by [].
  - destruct l0 as [ | a l0]; trivial.
    by rewrite !in_cons H.
  - destruct l0 as [ | a [ | a' l0]]; trivial.
    rewrite !in_cons. rewrite !orb_assoc.
    by replace ((b == a') || (b == a)) with ((b == a) || (b == a')) by by rewrite orb_comm. 
  - by rewrite H' H.
Qed.

Lemma perm_of_uniq {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) {B : finType}
  (l : seq B) : uniq (perm_of sigma l) = uniq l.
Proof.
  revert B l.
  induction sigma as [ | x l l' sigma H | x y l | l l' l'' sigma H sigma' H']; cbn;
  intros B l0.
  - by [].
  - destruct l0 as [ | a l0]; trivial.
    cbn; by rewrite perm_of_in H.
  - destruct l0 as [ | a [ | b l0]]; trivial.
    cbn; rewrite !in_cons.
    rewrite !negb_or !andb_assoc; apply andb_id2r; intros _.
    rewrite andb_comm andb_assoc; apply andb_id2r; intros _.
    rewrite andb_comm; apply andb_id2r; intros _.
    apply /eqP; case_if.
    by apply nesym.
  - by rewrite H' H.
Qed.

Definition perm_graph_data (G : geos) (l l' : list formula) (sigma : Permutation_Type l l') :
  graph_data := {|
  graph_of := G;
  left := left (g := G);
  order := perm_of sigma (order G);
  |}.

Lemma perm_p_deg (G : geos) (l l' : list formula) (sigma : Permutation_Type l l') :
  proper_degree (perm_graph_data G sigma).
Proof. apply p_deg. Qed.
Arguments perm_p_deg {G} {l l'} (sigma).

Lemma perm_p_left (G : geos) (l l' : list formula) (sigma : Permutation_Type l l') :
  proper_left (perm_graph_data G sigma).
Proof. apply p_left. Qed.
Arguments perm_p_left {G} {l l'} (sigma).

Lemma perm_p_order (G : geos) (l l' : list formula) (sigma : Permutation_Type l l') :
  proper_order (perm_graph_data G sigma).
Proof.
  unfold proper_order, perm_graph_data; cbn.
  split.
  - intro v.
    rewrite perm_of_in.
    apply p_order.
  - rewrite perm_of_uniq.
    apply p_order.
Qed.

Definition perm_geos (G : geos) (l l' : list formula) (sigma : Permutation_Type l l') :
  geos := {|
  graph_data_of := perm_graph_data G sigma;
  p_deg := perm_p_deg sigma;
  p_left := perm_p_left sigma;
  p_order := perm_p_order G sigma;
  |}.

Lemma perm_simpl (G : geos) (l l' : list formula) (sigma : Permutation_Type l l') :
  @right G =1 @right (perm_geos G sigma) /\ @ccl G =1 @ccl (perm_geos G sigma) /\
  @edge_of_concl G =1 @edge_of_concl (perm_geos G sigma).
Proof.
  splitb;
  intro v;
  unfold right, ccl, edge_of_concl.
  all: generalize (erefl (vlabel v));
    destruct (vlabel v) at 2 3; cbn;
    intro H;
    symmetry;
    generalize (erefl (vlabel v));
    destruct (vlabel v) at 2 3; cbn;
    intro H';
    trivial.
  all: try (contradict H; by rewrite H').
  all: replace H' with H by apply eq_irrelevance.
  all: try set to := tens_to_tensparr H;
       try set to := parr_to_tensparr H.
  all: try replace (perm_p_left sigma v to) with (p_left to) by apply eq_irrelevance.
  all: try by replace (@unique_right (perm_geos G sigma) v to) with (@unique_right G v to)
    by apply eq_irrelevance.
  all: try by replace (@unique_ccl (perm_geos G sigma) v to) with (@unique_ccl G v to)
    by apply eq_irrelevance.
  all: try by replace (@unique_concl (perm_geos G sigma) v H) with (@unique_concl G v H)
    by apply eq_irrelevance.
Qed.

Lemma perm_p_ax_cut (G : proof_structure) (l l' : list formula) (sigma : Permutation_Type l l') :
  proper_ax_cut (perm_geos G sigma).
Proof. apply p_ax_cut. Qed.
Arguments perm_p_ax_cut {G} {l l'} (sigma).

Lemma perm_p_tens_parr (G : proof_structure) (l l' : list formula) (sigma : Permutation_Type l l') :
  proper_tens_parr (perm_geos G sigma).
Proof.
  unfold proper_tens_parr, perm_geos, perm_graph_data; cbn.
  intros.
  destruct (perm_simpl G sigma) as [Hr [Hc _]].
  rewrite -Hr -Hc.
  by apply p_tens_parr.
Qed.
Arguments perm_p_tens_parr {G} {l l'} (sigma).

Definition perm_ps (G : proof_structure) (l l' : list formula) (sigma : Permutation_Type l l') :
  proof_structure := {|
  geos_of := perm_geos G sigma;
  p_ax_cut := perm_p_ax_cut sigma;
  p_tens_parr := perm_p_tens_parr sigma;
  |}.

Lemma ax_sequent (x : atom) : sequent (ax_geos x) = covar x :: var x :: nil.
Proof.
  unfold sequent.
  replace ([seq elabel (edge_of_concl i) | i <- order (ax_geos x)]) with ([:: elabel 
    (edge_of_concl (ord1 : ax_geos x)); elabel (edge_of_concl (ord2 : ax_geos x))]) by by [].
  assert (edge_of_concl (ord1 : ax_geos x) = ord0 /\ edge_of_concl (ord2 : ax_geos x) = ord1)
    as [H1 H2] by (split; symmetry; by apply p_concl4).
  by rewrite H1 H2.
Qed.

Lemma perm_sequent (G : proof_structure) (l l' : list formula) (sigma : Permutation_Type l l')
  (Heq : (sequent G) = l) : sequent (perm_geos G sigma) = l'.
Proof.
  revert sigma; rewrite <-!Heq; intro sigma; cbn.
  rewrite -perm_of_map.
  destruct (perm_simpl G sigma) as [_ [_ He]].
  replace (map (fun i : G => @elabel _ _ G (@edge_of_concl (@perm_geos G (sequent G) l' sigma) i))
    (order G)) with (map (fun i : G => @elabel _ _ G (edge_of_concl i)) (order G))
    by (apply eq_map; intros ?; by rewrite He).
  apply perm_of_consistent.
Qed.

Lemma union_sequent (G0 G1 : geos) : sequent (union_geos G0 G1) =
  match sequent G0, sequent G1 with
  | f0 :: s0, f1 :: s1 => f0 :: f1 :: s1 ++ s0
  | _, [::] => sequent G0
  | [::], _ => sequent G1
  end.
Proof.
  cbn; unfold union_order, sequent.
  destruct (order G0) as [ | v0 o0];
  destruct (order G1) as [ | v1 o1];
  trivial; cbn.
  all: rewrite !union_edge_of_concl.
  all: apply /eqP; cbn; splitb; apply /eqP; trivial.
  all: rewrite ?map_cat -!map_comp /comp.
  all:
    try replace ([seq match edge_of_concl (inl x : union_geos G0 G1) with
      | inl e => elabel e | inr e => elabel e end | x <- o0])
      with ([seq elabel (edge_of_concl i) | i <- o0])
      by (apply eq_map; intros ?; by rewrite union_edge_of_concl);
    try replace ([seq match edge_of_concl (inr x : union_geos G0 G1) with
      | inl e => elabel e | inr e => elabel e end | x <- o1])
      with ([seq elabel (edge_of_concl i) | i <- o1])
      by (apply eq_map; intros ?; by rewrite union_edge_of_concl);
    trivial.
Qed.

Lemma add_node_sequent (c : trilean) (G : geos) :
  let new := match order G with
    | v0 :: v1 :: _ => match c with
      | tens_t => [:: tens (elabel (edge_of_concl v0)) (elabel (edge_of_concl v1))]
      | parr_t => [:: parr (elabel (edge_of_concl v0)) (elabel (edge_of_concl v1))]
      | cut_t => nil
      end
    | _ => nil
    end in
  let old := match order G with
    | v0 :: v1 :: _ => match c with 
      | cut_t => if (elabel (edge_of_concl v0)) == (elabel (edge_of_concl v1)^)
              then behead (behead (sequent G))
              else sequent G
      | _ => behead (behead (sequent G))
      end
    | _ => sequent G
    end in
  sequent (add_node_geos c G) = new ++ old.
Proof.
  remember (order G) as l eqn:H; symmetry in H; cbn.
  assert (Hr : [seq elabel (edge_of_concl i) | i <- order (add_node_geos c G)]
    = [seq elabel (edge_of_concl' i) | i <- order (add_node_graph_data_bis c G)]).
  { apply eq_in_map; intros v Hv.
    rewrite edge_of_concl_eq //.
    by apply p_order. }
  rewrite Hr; clear Hr.
  assert (Hr : [seq elabel (edge_of_concl' i) | i <- order (add_node_graph_data_bis c G)] =
    [seq elabel (edge_of_concl' i) | i <- order (match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match c with
      | cut_t => if elabel (edge_of_concl v0) == elabel (edge_of_concl v1)^
        then fun Heq => add_node_graph_data c (add_node_hyp Heq) else fun=> G
      | _ => fun Heq => add_node_graph_data c (add_node_hyp Heq)
    end
    | _ => fun=> G
    end H)]) by by rewrite <-!H.
  rewrite Hr; clear Hr.
  destruct l as [ | v0 [ | v1 l]].
  1,2: apply eq_in_map; intros v Hv.
  1,2: rewrite edge_of_concl_eq //.
  1,2: by apply p_order.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  assert (Hr : match c with
    | cut_t => if elabel (edge_of_concl v0) == elabel (edge_of_concl v1)^
      then fun Heq => add_node_graph_data c (add_node_hyp Heq) else fun=> G
    | _ => fun Heq => add_node_graph_data c (add_node_hyp Heq)
    end H = match c with
    | cut_t => if elabel (edge_of_concl v0) == elabel (edge_of_concl v1)^
      then add_node_graph_data c (add_node_hyp H) else G
    | _ => add_node_graph_data c (add_node_hyp H)
    end).
  { destruct c; trivial. case_if. }
  rewrite Hr; clear Hr.
(* TODO check if edge_of_concl' after here really needed *)
  assert ([seq elabel (edge_of_concl' i) | i <- order
    (match c with
    | cut_t => if elabel (edge_of_concl v0) == elabel (edge_of_concl v1)^
      then add_node_graph_data c (add_node_hyp H) else G
    | _ => add_node_graph_data c (add_node_hyp H)
    end)] = [seq elabel (edge_of_concl' i) | i <- order
    (match c with
    | cut_t => if elabel (edge_of_concl' v0) == elabel (edge_of_concl' v1)^
      then add_node_graph_data c (add_node_hyp H) else G
    | _ => add_node_graph_data c (add_node_hyp H)
    end)] /\ match c with
    | tens_t => [:: elabel (edge_of_concl v0) ⊗ elabel (edge_of_concl v1)]
    | parr_t => [:: elabel (edge_of_concl v0) ⅋ elabel (edge_of_concl v1)]
    | cut_t => [::]
    end ++ match c with
    | cut_t => if elabel (edge_of_concl v0) == elabel (edge_of_concl v1)^
      then behead (behead (sequent G)) else sequent G
    | _ => behead (behead (sequent G))
    end = match c with
    | tens_t => [:: elabel (edge_of_concl' v0) ⊗ elabel (edge_of_concl' v1)]
    | parr_t => [:: elabel (edge_of_concl' v0) ⅋ elabel (edge_of_concl' v1)]
    | cut_t => [::]
    end ++ match c with
    | cut_t => if elabel (edge_of_concl' v0) == elabel (edge_of_concl' v1)^
      then [seq elabel (edge_of_concl i) | i <- l]
      else [:: elabel (edge_of_concl' v0), elabel (edge_of_concl' v1) &
      [seq elabel (edge_of_concl i) | i <- l]]
    | _ => [seq elabel (edge_of_concl i) | i <- l]
    end) as [Hr Hr'] by by rewrite /sequent H -!edge_of_concl_eq.
  rewrite Hr Hr'; clear Hr Hr'; cbn.
  assert (Hr : [seq elabel (edge_of_concl i) | i <- l] = [seq elabel (edge_of_concl' i) | i <- l]).
  { apply eq_in_map; intros v Hv.
    rewrite -edge_of_concl_eq //.
    apply p_order.
    rewrite H !in_cons; caseb. }
  rewrite Hr; clear Hr.
  assert ([seq elabel (edge_of_concl' i) | i <- order (add_node_graph_data c (add_node_hyp H))] =
    match c with
    | tens_t => [:: elabel (edge_of_concl' v0) ⊗ elabel (edge_of_concl' v1)]
    | parr_t => [:: elabel (edge_of_concl' v0) ⅋ elabel (edge_of_concl' v1)]
    | cut_t => [::]
    end ++ [seq elabel (edge_of_concl' i) | i <- l]).
  2:{ destruct c; trivial. case_if. by rewrite H. }
  set e0 := edge_of_concl v0;
  set e1 := edge_of_concl v1.
  assert (Hneqv : v0 != v1).
  { elim (p_order G).
    rewrite H cons_uniq in_cons negb_or.
    by move => _ /andP[/andP[? _] _]. }
  rewrite add_node_transport_sequent -!edge_of_concl_eq // -/e0 -/e1 /add_node_order
    -(proj2_sig (all_sigP (add_node_consistent_order c e0 e1))) /edge_of_concl'
    /add_node_order_2 /add_node_type_order /add_node_order_1.
  assert (Hr : [seq inl v | v <- order G & (v != target e0) && (v != target e1)]
    = ([seq inl v | v <- l] : seq (add_node_graph_1 c e0 e1))).
  { f_equal.
    rewrite H; cbn; rewrite !p_concl3 //.
    replace (v0 != v0) with false by (symmetry; by apply /negP /negP);
    replace (v1 != v1) with false by (symmetry; by apply /negP /negP);
    replace (v1 != v0) with true by (symmetry; apply /eqP; apply nesym; by apply /eqP); cbn.
    elim (p_order G).
    rewrite H !cons_uniq !in_cons !negb_or; clear.
    move => _ /andP[/andP[_ H0] /andP[H1 _]].
    rewrite -{2}(filter_predT l); apply eq_in_filter; intros v Hv.
    by rewrite !(in_notin (l := l)). }
  rewrite Hr map_cat -!map_comp /comp; clear Hr.
  assert (Hr : [seq elabel (match [pick x in edges_in_at_subset i] with
    | Some e => e | None => add_node_left_1 i end) | i <- match c return
    (seq (add_node_graph_1 c e0 e1)) with | cut_t => [::] | _ => [:: inr (inr tt)] end] =
    match c with | tens_t => [:: elabel e0 ⊗ elabel e1]
    | parr_t => [:: elabel e0 ⅋ elabel e1] | cut_t => [::] end).
  { destruct c; [set c := tens_t | set c := parr_t | set c := cut_t]; cbn; trivial.
    all: assert (Hr : edges_in_at_subset (inr (inr tt) : add_node_graph_1 c e0 e1) =
      [set Some (Some (inr None))]) by
      (apply /setP; intro e; rewrite !in_set; by destruct e as [[[e | [[[] | []] | ]] | ] | ]).
    all: by rewrite Hr p_pick1. }
  rewrite Hr; clear Hr.
  apply f_equal, eq_in_map; intros v Hv.
  assert (Hl : vlabel v = concl_l) by
    (apply p_order; rewrite H !in_cons; caseb).
  assert (v != v0 /\ v != v1) as [Hvv0 Hvv1].
  { elim (p_order G).
    rewrite H !cons_uniq !in_cons.
    move => _ /andP[/norP[_ Hn0] /andP[Hn1 _]].
    by rewrite !(in_notin (l := l)). }
  rewrite (add_node_transport_1_edges _ H) //  p_concl2 // imset_set1 !p_pick1.
  apply (add_node_transport_1_label _ H).
Qed.


(** * Traduction of a sequent proof into a proof structure *)
Fixpoint ps {l : list formula} (pi : ll l) : proof_structure := match pi with
  | ax_r x => ax_ps x
  | ex_r _ _ pi0 sigma => perm_ps (ps pi0) sigma
  | tens_r _ _ _ _ pi0 pi1 => add_node_ps tens_t (union_ps (ps pi0) (ps pi1))
  | parr_r _ _ _ pi0 => add_node_ps parr_t (ps pi0)
  | cut_r _ _ _ pi0 pi1 => add_node_ps cut_t (union_ps (ps pi0) (ps pi1))
  end.

Lemma ps_consistent {l : list formula} (pi : ll l) : sequent (ps pi) = l.
Proof.
  induction pi as [x | l l' pi0 H0 sigma | A B l0 l1 pi0 H0 pi1 H1 | A B l0 pi0 H0 | A l0 l1 pi0 H0 pi1 H1].
  - apply ax_sequent.
  - by apply perm_sequent.
  - rewrite add_node_sequent union_sequent H0 H1; cbn.
    revert H0 H1.
    unfold union_order, sequent.
    destruct (order (ps pi0)) as [ | v0 o0] eqn:Ho0; try by [].
    destruct (order (ps pi1)) as [ | v1 o1] eqn:Ho1; try by [].
    rewrite Ho0 Ho1 !union_edge_of_concl.
    move => /eqP; cbn; move => /andP [/eqP H0 _];
    move => /eqP; cbn; move => /andP [/eqP H1 _].
    by rewrite H0 H1.
  - rewrite add_node_sequent H0.
    revert H0.
    unfold sequent.
    destruct (order (ps pi0)) as [ | v0 [ | v1 o]] eqn:Ho; try by [].
    rewrite Ho.
    move => /eqP; cbn; move => /andP [/eqP H0 /andP[/eqP H1 _]].
    by rewrite H0 H1.
  - rewrite add_node_sequent union_sequent H0 H1; cbn.
    revert H0 H1.
    unfold union_order, sequent.
    destruct (order (ps pi0)) as [ | v0 o0] eqn:Ho0; try by [].
    destruct (order (ps pi1)) as [ | v1 o1] eqn:Ho1; try by [].
    rewrite Ho0 Ho1 !union_edge_of_concl.
    move => /eqP; cbn; move => /andP [/eqP H0 _];
    move => /eqP; cbn; move => /andP [/eqP H1 _].
    rewrite H0 H1 bidual.
    case_if.
Qed.



(** ** Correctness Criteria: Danos-Regnier *)
(* Switching Graph *)
(* SG (PS):
for a proof structure PS, get P the nodes labelled parr, then a s.g. is given by:
phi: P -> B, G_phi = G where on node v\in P, arrow ?->v(A,phi(v)) is deleted,
  add node c_v, edge ?->c_v(A)
    then remove direction
*)

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

(** ** Cut Elimination *)
(* possible avant la sequentialisation et le critere de correction *)
(*
Inductive red : 
| ax->cut: merge the 2 nodes, then merge the final node with the node above,
    keep label of above
| tens->cut<-parr: merge the 3 nodes into the cut one, then split it
    with the good edges, give label cut to both
=> need procedure merge, where a parent node absorb another, keeping its own label
  (may be used before instead of removing edge then adding edge ???)
*)
(* lemma: if R is correct and R reduces to R', then R' is correct *)
(* lemma: applying red while we can yields a cut-free ps:
    there is a cut node => one of the two subgraphs (*2 by symmetry) =>
  reduction to another graph *)
(* lemma: sub-confluence + convergence *)

(** ** Sequentialization *)
(* many things to do: spliting tens / cut, blocking parr, always a
  terminal parr or a splitting *)
(* function to turn a ps into a sequential proof *)

(* TODO check if every lemma proved is useful / interesting *)
*)
End Atoms.
