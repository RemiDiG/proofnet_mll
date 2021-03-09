(* Unit-free MLL following Yalla schemas *)


From Coq Require Import Bool Wf_nat Lia.
From OLlibs Require Import dectype funtheory List_more List_Type Permutation_Type_more.
From mathcomp Require Import all_ssreflect zify.
From GraphTheory Require Import preliminaries mgraph.
(* check at the end if all are used *)

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
| tens_r _ _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
| parr_r _ _ _ pi0 => S (psize pi0)
| cut_r _ _ _ pi0 pi1 => S (psize pi0 + psize pi1)
end.

Lemma psize_pos l (pi : ll l) : 0 < psize pi.
Proof. destruct pi; cbn; by []. Qed.

Lemma psize_rew l l' (pi : ll l) (Heq : l = l') : psize (rew Heq in pi) = psize pi.
Proof. now subst. Qed.


(*********************************************************************************************)
(** ** Preliminaries *)

(** * Some results on 'I_n *)
(** The function inord is injective on integers <= n *)
Lemma inord_inj : forall n i j : nat, i <= n -> j <= n -> @inord n i = @inord n j -> i = j.
Proof.
  intros n i j ? ? H.
  assert (Hn : forall k : nat, k <= n -> nat_of_ord (@inord n k) = k).
  { intros. apply inordK. lia. }
  by rewrite <-(Hn i), <-(Hn j), H.
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
  destruct (orP (case_I2 n)) as [H | H];
  [left | right]; by apply /eqP.
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
  destruct (orP (case_I3 n)) as [H2 | H];
  [destruct (orP H2) as [H | H]; clear H2| ];
  [left | right; left | right; right]; by apply /eqP.
Qed.

Ltac destruct_I3 n H := destruct (case_I3bis n) as [H | [H | H]].

(* TOTHINK possible case_nter avec des set {_}+{_}+...*)


(** Tactic to make cases on if _ == _ *)
(* Make all cases, try to rewrite the equality condition and conserve the condition
  under the form _ = _ or _ <> _, folding trivial cases *)
Ltac case_if := repeat (let Hif := fresh "Hif" in
  case: ifP; cbn; move => /eqP Hif; rewrite ?Hif //).


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
Definition eqb_rule (A : rule) (B : rule) : bool :=
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

(** Tactic to distinguish cases in rule *)
Lemma case_rule (r : rule) : {r = ax_l} + {r = tens_l} + {r = parr_l} + {r = cut_l} + {r = concl_l}.
Proof.
  destruct r.
  - by apply inleft, inleft, inleft, Specif.left.
  - by apply inleft, inleft, inleft, Specif.right.
  - by apply inleft, inleft, inright.
  - by apply inleft, inright.
  - by apply inright.
Qed.

Ltac destruct_rule r H := destruct (case_rule r) as [[[[H | H] | H] | H] | H].
(* now useless ? *)
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
    rewrite !in_set; apply /orP;
    [by left | by right].
  - move => /norP [/eqP H' /eqP H''] [z Hz] Hc;
    revert Hz; rewrite !in_set; move => /orP [/eqP Hz | /eqP Hz];
    by rewrite Hz in Hc.
Qed. (* TODO see if using it can simplify proof *)



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

Definition edges_out_at_set {Lv : Type} {Le : Type} {G : graph Lv Le} (v : G) : finType :=
  [finType of {e : edge G | source e == v}].
Definition edges_in_at_set {Lv : Type} {Le : Type} {G : graph Lv Le} (v : G) : finType :=
  [finType of {e : edge G | target e == v}].



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

(* sig [eta mem S] avec S : {set G} *)
(* idées:
- direction avec type totaux (directement sur vertex -> edges)
- sum type pour avoir toutes les informations et contraintes selon le type de noeuds,
  codé en tant que 
- ajouter une donnée n et order = fonction de I_n vers des neouds/aretes ;
    ou une liste de noeuds/aretes, sans le n
- definir juste left, en deduire right apres
- curryfier les sigma input

TOTHINK other possibilities for the functions:
    order : [concl_l node] -> 'I_#|concl_l node]|;
avec    order_inj : injective order;

    order : {perm {v : graph_of | vlabel v == concl_l}};
  -     direction : bool -> vertex graph_of -> edge graph_of; avec
Notation left := (direction false).
Notation right := (direction true).
  -> {v : graph_of | (vlabel v == tens_l) || (vlabel v == parr_l)}
  - faire des fonctions depuis les ensembles totaux vers option _ puis lemma
    pour label ok <-> Some _
    ex:
      order : graph_of -> option nat;
      order_ok : forall v, exists n, order v = Some n <-> vlabel v = concl_l /\
            order v <= nb nodes concl;
          en fait si injectif, pas necessaire d'avoir la dernière condition,
          qui semble etre la plus difficile comme #|_| est dur à calculer
      direction : bool -> graph_of -> option_finType (edge graph_of);
      direction_ok : forall b v, direction b v = Some _ <->
          (vlabel c = tens_l \/ vlabel c = parr_l);
  - see sig_finType, used for the function sub_edge in the graph lib
  - other way to define bijections for order: surj instead of inj, from I_n -> vertices, ...
  - something else ?
  - define order as a permutation of the finset as finset = seq = list, easier to manipulate
      --> NON
  - dans direction, restreindre edge to edge_in_at_set v ?
  - mettre direction et ordre plutot dans proof_structure ? (ie cette couche est inutile ?)
*)

(* fonction qui dit si formule atomique existe dans yalla,
  possible de l'ajouter pour expansion atome *)
(* /!\ faire lemma (admitted dependant des defs), pour utiliser
  independamment de la def choisie *)

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

Definition ax_left (x : atom) : vertex (ax_graph x) -> edge (ax_graph x) :=
  fun _ => ord0. (* no vertex tens nor parr: we put a nonsensical value *)
Arguments ax_left : clear implicits.

Definition ax_order (x : atom) : list (vertex (ax_graph x)) :=
  ord1 :: ord2 :: nil.

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
(* Put the two first premises at the beginning, then the tail of order G1,
   finally the tail of order G0 *)
Definition union_order (G0 G1 : graph_data) : list (G0 ⊎ G1) :=
  match order G0, order G1 with
  | v0 :: o0, v1 :: o1 => inl v0 :: inr v1 :: map inr o1 ++ map inl o0
(* but order will never be nil, so other cases not encountered *)
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
    | false => G0
    | true => G1
    end in
  let fv := match i return Gi i -> G0 ⊎ G1 with
    | false => inl
    | true => inr
    end in
  let fe := match i return edge (Gi i) -> edge (G0 ⊎ G1) with
    | false => inl
    | true => inr
    end in
  forall v : Gi i,
  edges_at_subset b (fv v) =i [set fe e | e in edges_at_subset b v].
Proof.
  intros Gi fv fe v.
  unfold "=i".
  destruct i;
  intros [e | e].
  all: assert (Hfe: injective fe) by (apply inl_inj || apply inr_inj).
  all: rewrite ?inj_imset // !in_set; cbn; trivial.
  all: apply /eqP /memPn.
  all: move => y /imsetP [? _] Hl.
  all: by rewrite Hl.
Qed.
Notation union_edges_at_inl := (union_edges_at (i := false)).
Notation union_edges_at_inr := (union_edges_at (i := true)).

Lemma union_order_in (G0 G1 : graph_data) (i : bool) :
  let Gi (j : bool) := match j with
    | false => G0
    | true => G1
    end in
  let fv := match i return Gi i -> G0 ⊎ G1 with
    | false => inl
    | true => inr
    end in
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

(* BUG REPORT
(* c'est bien long à compiler ... mais ça ne l'est pas sans les let des noms de sommets !? *)
(* isoler le probleme, montrer exponentiel en temps selon le nombre de inl,
   puis faire un bug report *)
Definition add_parr_quick {G : graph_data} (e0 e1 : edge G) :=
  (* add new vertices parr and concl *)
  let G1 := (G ∔ parr_l) ∔ concl_l in
  (* duplicate edges e0 and e1 to parr, from s0 and s1, and add an edge from parr to concl *)
  let G2 := G1 ∔ [ inl (inl (source e0)) , elabel e0 , inl (inr tt) ]
    ∔ [ inl (inl (source e1)) , elabel e1 , inl (inr tt) ]
    ∔ [ inl (inr tt) , parr (elabel e0) (elabel e1) , inr tt ] in
  (* remove t0 and t1 *)
  let S : {set G2} := setT :\ inl (inl (target e0)) :\ inl (inl (target e1)) in
  induced S.
Definition add_parr_slow {G : graph_data} (e0 e1 : edge G) :=
  (* add new vertices parr and concl *)
  let G1 := (G ∔ parr_l) ∔ concl_l in
  let s0 := inl (inl (source e0)) : G1 in
  let t0 := inl (inl (target e0)) : G1 in
  let s1 := inl (inl (source e1)) : G1 in
  let t1 := inl (inl (target e1)) : G1 in
  let v_parr := inl (inr tt) : G1 in
  let v_concl := inr tt : G1 in
  (* duplicate edges e0 and e1 to parr, from s0 and s1, and add an edge from parr to concl *)
  let G2 := G1 ∔ [ s0 , elabel e0 , v_parr ]
    ∔ [ s1 , elabel e1 , v_parr ]
    ∔ [ v_parr , parr (elabel e0) (elabel e1) , v_concl ] in
  (* remove t0 and t1 *)
  let S : {set G2} := [set x | (x != t0) && (x != t1)] in
  induced S.
*)

(** * Adding a node to a graph_data *)
(** Add a tens/parr/cut node to a graph_data, replacing 2 conclusions *)
(* Add a tens/parr/cut node, without removing conclusions *)
Definition add_node_graph_1 (c : comparison) {G : graph_data} (e0 e1 : edge G) :=
  (* subgraph to add *)
  let graph_node (b : comparison) := match b with
    | Eq => edge_graph tens_l (tens (elabel e0) (elabel e1)) concl_l
    | Lt => edge_graph parr_l (parr (elabel e0) (elabel e1)) concl_l
    | Gt => unit_graph cut_l
  end in
  let G1 (b : comparison) := G ⊎ graph_node b in
  (* node of the graph receving edges *)
  let target_node := match c return G1 c with
    | Eq => inr (inl tt)
    | Lt => inr (inl tt)
    | Gt => inr tt
  end in
  (* duplicate edges *)
  G1 c ∔ [ inl (source e0) , elabel e0 , target_node ]
       ∔ [ inl (source e1) , elabel e1 , target_node ].

(* Remove the conclusions *)
Definition add_node_graph (c : comparison) {G : graph_data} (e0 e1 : edge G) :=
  let G' := add_node_graph_1 c e0 e1 in
  let S : {set G'} := setT :\ inl (target e0) :\ inl (target e1) in
  induced S.

(** Function left for the graph with a new node *)
(* Function left for the intermediary graph *)
Definition add_node_left_1 (c : comparison) {G : graph_data} (e0 e1 : edge G) :=
  let G' := add_node_graph_1 c e0 e1 in
  fun (v : G') => match v return edge G' with
  | inl u => (* if (target (left u) != target e1) && (target (left u) != target e0)
    then Some (Some (inl (left u)))
    else Some None *)
            if target (left u) == target e0 then Some None
            else if target (left u) == target e1 then Some None
            else Some (Some (inl (left u)))
(* artefact for when the value of left is nonsensical:
if target left v is the c node we remove (ie if we remove the edge left v),
we have to give it a new value in the updated left;
in this case, left v is the (unique input) edge of a c node,
so not the input edge of a tens or a parr, we can give it any value *)
  | inr _ => Some None
  end.
(* TOTHINK Damien Pous possible de simplifier ce if / faire autrement ? *)
(* ajouter conditions (source (left u) != target e0 &&
  source (left u) != target e1) dans le if ? *)
(* TOTEST left avec option, pour eviter ce if + ajouter un invariant dans geos
pour target (left v) = Some v si v est un tens / parr *)

(* Necessary hypothesis : the nodes we remove have no input edges *)
Lemma add_node_consistent_left (c : comparison) {G : graph_data} (e0 e1 : edge G) :
  let G' := add_node_graph_1 c e0 e1 in
  let S : {set G'} := setT :\ inl (target e0) :\ inl (target e1) in
  (forall e, source e != target e0) -> (forall e, source e != target e1) ->
  forall v : G', add_node_left_1 v \in edge_set S.
Proof.
  destruct c; cbn;
  intros H0 H1 [v | v];
  rewrite !in_set; cbn;
  repeat (apply /andP; split); trivial.
  all: case_if; by apply/eqP.
Qed.

(* Function left for the graph with a new node *)
Definition add_node_left (c : comparison) {G : graph_data} (e0 e1 : edge G)
  (H0 : forall e : edge G, source e != target e0)
  (H1 : forall e : edge G, source e != target e1) :
  add_node_graph c e0 e1 -> edge (add_node_graph c e0 e1) :=
  fun v => Sub (add_node_left_1 (val v)) (add_node_consistent_left H0 H1 (val v)).

(** Function order for the graph with a new node *)
(* Remove the 2 nodes from order *)
Definition add_node_order_1 {G : graph_data} (e0 e1 : edge G) :=
  [seq x <- order G | (x != target e0) && (x != target e1)].
(* TODO lemma que ca revient à retirer les 2 premiers de la liste dans le cas concret *)

(* Give order the type of the intermediary graph *)
Definition add_node_type_order (c : comparison) {G : graph_data} (e0 e1 : edge G)
  (l : list G) : list (add_node_graph_1 c e0 e1) :=
  [seq (inl v) | v <- l].

(* Add the new conclusion if it exists *)
Definition add_node_order_2 (c : comparison) {G : graph_data} (e0 e1 : edge G) :=
  match c return list (add_node_graph_1 c e0 e1) with
  | Eq as c | Lt as c => inr (inr tt) :: add_node_type_order c e0 e1 (add_node_order_1 e0 e1)
  | Gt as c => add_node_type_order c e0 e1 (add_node_order_1 e0 e1)
  end.

Lemma add_node_consistent_order (c : comparison) {G : graph_data} (e0 e1 : edge G) :
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

Definition add_node_order (c : comparison) {G : graph_data} (e0 e1 : edge G) :
  list (vertex (add_node_graph c e0 e1)) :=
  [seq v | v <- sval (all_sigP (add_node_consistent_order c e0 e1))].

(** Graph data for adding a node *)
Definition add_node_graph_data (c : comparison) {G : graph_data} (e0 e1 : edge G)
  (H0 : forall e : edge G, source e != target e0)
  (H1 : forall e : edge G, source e != target e1) : graph_data := {|
  graph_of := add_node_graph c e0 e1;
  left := add_node_left H0 H1;
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

(* TODO see if proper in bool needed later on and
if edeges_in_at_subset or edges_in_at_set better *)
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
Definition bogus {G : geos} (v : G) : edge G := left v.

(** Function right for the right premisse of a tens / parr *)
Lemma unique_right (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l -> #|edges_in_at_subset v| = 2.
Proof. intros v [Hl | Hl]; by rewrite (p_deg_in v) Hl. Qed.

Definition right : forall G : geos, G -> edge G :=
  fun (G : geos) (v : G) =>
  match vlabel v as l return vlabel v = l -> edge G with
  | tens_l => fun Heq =>
    let H' := tens_to_tensparr Heq in
    other (unique_right H') (p_left H')
  | parr_l => fun Heq =>
    let H' := parr_to_tensparr Heq in
    other (unique_right H') (p_left H')
  | _ => fun _ => bogus v
  end Logic.eq_refl.

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


(** Function ccl for the conclusion of a tens / parr *)
Lemma unique_ccl (G : geos) :
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l ->
  #|edges_out_at_subset v| = 1.
Proof. intros v [Hl | Hl]; by rewrite (p_deg_out v) Hl. Qed.

Definition ccl : forall G : geos, G -> edge G :=
  fun (G : geos) (v : G) =>
  match vlabel v as l return vlabel v = l -> edge G with
  | tens_l => fun Heq =>
    pick_unique_subset (unique_ccl (tens_to_tensparr Heq))
  | parr_l => fun Heq =>
    pick_unique_subset (unique_ccl (parr_to_tensparr Heq))
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


(** Function returning the unique (input) edge of a conclusion *)
Lemma unique_concl (G : geos) :
  forall (v : G), vlabel v = concl_l ->
  #|edges_in_at_subset v| = 1.
Proof. intros v Hl; by rewrite (p_deg_in v) Hl. Qed.

Definition edge_of_concl : forall G : geos, G -> edge G :=
  fun (G : geos) (v : G) =>
  match vlabel v as l return vlabel v = l -> edge G with
  | concl_l => fun Heq =>
    pick_unique_subset (unique_concl Heq)
  | _ => fun _ => bogus v
  end Logic.eq_refl.

Lemma p_concl (G : geos) :
  forall (v : G), vlabel v = concl_l ->
  edge_of_concl v \in edges_in_at_subset v.
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
  forall (v : G), vlabel v = concl_l ->
  edges_in_at_subset v = [set edge_of_concl v].
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
  forall (v : G), vlabel v = concl_l ->
  target (edge_of_concl v) = v.
Proof.
  intros v Hv.
  assert (H : edge_of_concl v \in edges_in_at_subset v) by by apply p_concl.
  rewrite in_set in H.
  by apply /eqP.
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
Lemma p_deg_ax (x : atom) : proper_degree (ax_graph_data x).
Proof.
  unfold proper_degree.
  intros [ | ] v;
  destruct_I3 v H;
  rewrite H.
  all: compute_card_subIn.
Qed.
Arguments p_deg_ax : clear implicits.

Lemma p_left_ax (x : atom) : proper_left (ax_graph_data x).
Proof.
  unfold proper_left.
  intros v [Hl | Hl];
  destruct_I3 v H;
  contradict Hl;
  by rewrite H.
Qed.
Arguments p_left_ax : clear implicits.

Lemma p_order_ax (x : atom) : proper_order (ax_graph_data x).
Proof.
  unfold proper_order.
  split; trivial.
  intro v;
  destruct_I3 v H;
  by rewrite H.
Qed.

Definition ax_geos (x : atom) : geos := {|
  graph_data_of := ax_graph_data x;
  p_deg := p_deg_ax x;
  p_left := p_left_ax x;
  p_order := p_order_ax x;
  |}.

Lemma ax_nb_concl (x : atom) : #|[set v : ax_graph_data x | vlabel v == concl_l]| = 2.
Proof. compute_card_subIn. Qed. (* useless ? *)


(** * A disjoint union of geos is a geos *)
Lemma p_deg_union (G0 G1 : geos) : proper_degree (union_graph_data G0 G1).
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
Arguments p_deg_union : clear implicits.

Lemma p_left_union (G0 G1 : geos) : proper_left (union_graph_data G0 G1).
Proof.
  unfold proper_left.
  intros [v | v] Hv;
  [set fe := inl : edge G0 -> edge (G0 ⊎ G1) | set fe := inr : edge G1 -> edge (G0 ⊎ G1)].
  all: assert (injective fe) by (apply inl_inj || apply inr_inj).
  1: rewrite union_edges_at_inl. 2: rewrite union_edges_at_inr.
  all: rewrite (inj_imset (f:= fe)) //.
  all: by apply p_left.
Qed.
Arguments p_left_union : clear implicits.

Lemma p_order_union (G0 G1 : geos) : proper_order (union_graph_data G0 G1).
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
    repeat (apply /andP; split); trivial; clear.
    + by induction o1.
    + by induction o0.
    + induction o0; trivial.
      rewrite negb_or.
      apply /andP; split; trivial.
      by clear; induction o1.
Qed.

Definition union_geos (G0 G1 : geos) : geos := {|
  graph_data_of := union_graph_data G0 G1;
  p_deg := p_deg_union G0 G1;
  p_left := p_left_union G0 G1;
  p_order := p_order_union G0 G1;
  |}.

(** Useful lemmas on union_geos *)
Lemma union_right (G0 G1 : geos) :
  forall (v : union_geos G0 G1), vlabel v = tens_l \/ vlabel v = parr_l -> right v = match v with
    | inl u => inl (right u)
    | inr u => inr (right u)
  end.
Proof.
  intros v Hl.
  destruct (p_right Hl) as [_ Hneq].
  assert (H : right v \in edges_in_at_subset v) by by apply p_right.
  destruct v as [v | v];
  rewrite ?union_edges_at_inl ?union_edges_at_inr p_right2 // imset_set2 !in_set in H;
  revert H; move => /orP [/eqP H | /eqP H] //;
  by contradict Hneq; apply /negP; rewrite negb_involutive; apply /eqP.
Qed.

Lemma union_ccl (G0 G1 : geos) :
  forall (v : union_geos G0 G1), vlabel v = tens_l \/ vlabel v = parr_l -> ccl v = match v with
    | inl u => inl (ccl u)
    | inr u => inr (ccl u)
  end.
Proof.
  intros v Hl.
  assert (H : ccl v \in edges_out_at_subset v) by by apply p_ccl.
  destruct v as [v | v];
  rewrite ?union_edges_at_inl ?union_edges_at_inr p_ccl2 // imset_set1 in_set in H;
  by apply /eqP.
Qed.


(** * Adding a node to a geos yields a geos *)
Lemma add_node_hyp (G : geos) (v0 v1 : G) (l : seq G) (H : order G = v0 :: v1 :: l) :
  (forall e : edge G, source e != target (edge_of_concl v0)) /\
  (forall e : edge G, source e != target (edge_of_concl v1)).
Proof.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [H0  H1].
  { destruct (p_order G) as [O _].
    split; [apply (O v0) | apply (O v1)];
    rewrite H !in_cons eq_refl //.
    apply /orP; by right. }
  rewrite !p_concl3 //.
  split; [set v := v0; set Hv := H0 | set v := v1; set Hv := H1];
  intro e.
  all: apply /negP; intro; apply notF.
  all: assert (Hout : edges_out_at_subset v = set0) by (apply cards0_eq; by rewrite (p_deg_out v) Hv).
  all: by rewrite -(in_set0 e) -Hout in_set.
Qed.

Definition add_node_graph_data_bis : comparison -> geos -> graph_data :=
  fun (c : comparison) (G : geos) =>
  match order G as o return order G = o -> graph_data with
  | v0 :: v1 :: _ => fun Heq =>
    let (H0, H1) := add_node_hyp Heq in
    add_node_graph_data c H0 H1
  | _ => fun _ => G (* do nothing if there is not at least 2 nodes conclusion *)
end Logic.eq_refl.

(***********begin f********************)
Definition f_1 (c : comparison) (G : graph_data) (e0 e1 : edge G) :
  edge G -> edge (add_node_graph_1 c e0 e1) :=
  fun e => if (e == e1) then None
           else if (e == e0) then Some None
           else Some (Some (inl e)).
Lemma Hf (c : comparison) (G : geos) (v0 v1 : G) (l : seq G) (H : order G = v0 :: v1 :: l) :
  forall e, f_1 c (edge_of_concl v0) (edge_of_concl v1) e \in
  edge_set (setT :\ inl (target (edge_of_concl v0)) :\ inl (target (edge_of_concl v1)) :
  {set add_node_graph_1 c (edge_of_concl v0) (edge_of_concl v1)}).
Proof.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1].
  { destruct (p_order G) as [O _].
    split; [apply (O v0) | apply (O v1)];
    rewrite H !in_cons eq_refl //.
    apply /orP; by right. }
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  destruct (add_node_hyp H) as [H0 H1].
  set S := setT :\ inl (target e0) :\ inl (target e1) : {set add_node_graph_1 c e0 e1}.
  assert (None \in edge_set S /\ Some None \in edge_set S) as [Hn Hsn].
  { rewrite !in_set.
    split; repeat (apply /andP; split); trivial;
    try (apply H0 || apply H1);
    rewrite p_concl3 //; by destruct c. }
  intro e.
  unfold f_1; case_if.
  rewrite !in_set.
  repeat (apply /andP; split); trivial.
  1:{ apply H1. } 1:{ apply H0. }
  all: rewrite p_concl3 //.
  all: apply /negP; intro.
  1: set et := e1. 2: set et := e0.
  all: assert (Hc : e = et) by (apply /eqP; by rewrite -in_set1 -p_concl2 // in_set).
  all: by contradict Hc.
Qed.
Definition f (c : comparison) (G : geos) (v0 v1 : G) (l : seq G) (H : order G = v0 :: v1 :: l)
  (H0 : forall e : edge G, source e != target (edge_of_concl v0))
  (H1 : forall e : edge G, source e != target (edge_of_concl v1)) :
  edge G -> edge (add_node_graph_data c H0 H1) :=
  fun e => Sub (f_1 c (edge_of_concl v0) (edge_of_concl v1) e) (Hf c H e).
(* beaucoup de bruit ... mais je n'y arrive pas sans : *)
(* Definition f (c : comparison) (G : geos) : edge G -> edge (add_node_graph_data_bis c G) :=
  match order G with
  | v0 :: v1 :: _ => fun Heq =>
    let (H0, H1) := add_node_hyp Heq in
    f_2 c Heq H0 H1
  | _ => fun _ => id
end Logic.eq_refl. *) (* TODO donner un vrai nom à ces fonctions *)
Lemma f_inj (c : comparison) (G : geos) (v0 v1 : G) (l : seq G) (H : order G = v0 :: v1 :: l)
  (H0 : forall e : edge G, source e != target (edge_of_concl v0))
  (H1 : forall e : edge G, source e != target (edge_of_concl v1)) :
  injective (f c H H0 H1).
Proof.
  intros e e' Heq.
  assert (Heqbis : f_1 c (edge_of_concl v0) (edge_of_concl v1) e = f_1 c (edge_of_concl v0) (edge_of_concl v1) e').
      { replace (f_1 c (edge_of_concl v0) (edge_of_concl v1) e) with (sval (Sub (f_1 c (edge_of_concl v0) (edge_of_concl v1) e) (Hf c H e))) by apply SubK.
        replace (f_1 c (edge_of_concl v0) (edge_of_concl v1) e') with (sval (Sub (f_1 c (edge_of_concl v0) (edge_of_concl v1) e') (Hf c H e'))) by apply SubK.
        by f_equal. }
  revert Heqbis.
  unfold f_1; case_if.
  move => /eqP Heqbis; apply /eqP; revert Heqbis.
  by rewrite 2!Some_eqE inl_eqE.
Qed.
Lemma f_ugly (c : comparison) (G : geos) : edge G -> edge (add_node_graph_data_bis c G).
  unfold add_node_graph_data_bis.
  generalize (erefl (order G));
  destruct (order G) as [ | v0 [ | v1 l]] at 2 3;
  intro H; try (apply id).
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1].
  { destruct (p_order G) as [O _].
    split; [apply (O v0) | apply (O v1)];
    rewrite H !in_cons eq_refl //.
    apply /orP; by right. }
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  destruct (add_node_hyp H) as [H0 H1].
  set S := setT :\ inl (target e0) :\ inl (target e1) : {set add_node_graph_1 c e0 e1}.
  assert (None \in edge_set S /\ Some None \in edge_set S) as [Hn Hsn].
  { rewrite !in_set.
    split; repeat (apply /andP; split); trivial;
    try (apply H0 || apply H1);
    rewrite p_concl3 //; by destruct c. }
  set n := Sub None Hn : edge (add_node_graph_data c H0 H1);
  set sn := Sub (Some None) Hsn : edge (add_node_graph_data c H0 H1).
  set f_1 := (fun e => if (e == e1) then None
                         else if (e == e0) then Some None
                         else Some (Some (inl e))) : edge G -> edge (add_node_graph_1 c e0 e1).
  assert (Hf : forall e, f_1 e \in edge_set S).
  { intro e.
    unfold f_1; case_if.
    rewrite !in_set.
    repeat (apply /andP; split); trivial.
    1:{ apply H1. } 1:{ apply H0. }
    all: rewrite p_concl3 //.
    all: apply /negP; intro.
    1: set et := e1. 2: set et := e0.
    all: assert (Hc : e = et) by (apply /eqP; by rewrite -in_set1 -p_concl2 // in_set).
    all: by contradict Hc. }
  set f := fun (e : edge G) => Sub (f_1 e) (Hf e) : edge (add_node_graph_data c H0 H1).
  apply f.
Defined.
(* Print f_ugly. *)
(*************** end f ********************)

Lemma p_deg_add_node (c : comparison) (G : geos) : proper_degree (add_node_graph_data_bis c G).
Proof.
  unfold add_node_graph_data_bis.
  generalize (erefl (order G));
  destruct (order G) as [ | v0 [ | v1 l]] at 2 3;
  intro H; try (apply p_deg).
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1].
  { destruct (p_order G) as [O _].
    split; [apply (O v0) | apply (O v1)];
    rewrite H !in_cons eq_refl //.
    apply /orP; by right. }
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  assert (Hneqv : v0 != v1).
  { destruct (p_order G) as [_ U].
    rewrite H cons_uniq in_cons negb_or in U.
    revert U; by move => /andP[/andP[? _] _]. }
  assert (Hneqe : e0 == e1 = false).
  { apply negbTE, (contra_neq (z1 := target e0) (z2 := target e1)).
    intros; by f_equal.
    by rewrite !p_concl3. }
  destruct (add_node_hyp H) as [H0 H1].
  set S := setT :\ inl (target e0) :\ inl (target e1) : {set add_node_graph_1 c e0 e1}.
  assert (None \in edge_set S /\ Some None \in edge_set S) as [Hn Hsn].
  { rewrite !in_set.
    split; repeat (apply /andP; split); trivial;
    try (apply H0 || apply H1);
    by destruct c. }
  set n := Sub None Hn : edge (add_node_graph_data c H0 H1);
  set sn := Sub (Some None) Hsn : edge (add_node_graph_data c H0 H1).
  unfold proper_degree.
  intros b [[v | v] Hv]; fold S in Hv; fold S; cbn.
  - set w := Sub (inl v) Hv : add_node_graph_data c H0 H1.
    rewrite -(p_deg b v).
Check f_inj.
set g := f c H H0 H1.
Check f_1.
set g_1 := f_1 c e0 e1.
set g_inj := f_inj (c:=c) (H:=H) (H0:=H0) (H1:=H1).
rewrite -(card_imset (edges_at_subset b v) g_inj) -/g.
    apply eq_card.
    intros [[[[e | e] | ] | ] He];
    rewrite in_set; cbn; rewrite !SubK; cbn.
    + assert (Heq : Sub (Some (Some (inl e))) He = g e).
      { apply /eqP; rewrite /g /f sub_val_eq SubK /f_1; apply /eqP.
        case_if.
        all: contradict He.
        all: rewrite ?Hif ?Hif0 !in_set.
        1: move => /andP[_ /andP[He _]].
        2: move => /andP[_ /andP[_ /andP[He _]]].
        all: contradict He; apply /negP; cbn.
        all: by rewrite negb_involutive p_concl3. }
      by rewrite Heq inj_imset // in_set.
    + symmetry; apply /negbTE.
      rewrite Imset.imsetE in_set.
      apply /imageP; move => [a _ A].
      assert (Hc : Some (Some (inr e)) = g_1 a) by apply (EqdepFacts.eq_sig_fst A).
      contradict Hc.
      unfold g_1, f_1; case_if.
    + assert (Heq : Sub (Some None) He = g e0).
      { apply /eqP; rewrite /g /f /eqP sub_val_eq SubK /f_1; apply /eqP.
        case_if.
        contradict Hneqe. by rewrite Hif eq_refl. }
      rewrite Heq inj_imset // in_set.
      assert ((target (e0) == v) = false).
      { apply /eqP; intro Hc.
        clear w; contradict Hv.
        rewrite -Hc !in_set.
        move => /andP[_ /andP[Hv _]];
        contradict Hv; apply /negP.
        by rewrite negb_involutive. }
      by destruct b, c.
    + assert (Heq : Sub None He = g e1)
        by (apply /eqP; rewrite /g/f sub_val_eq SubK /f_1; case_if).
      rewrite Heq inj_imset // in_set.
      assert ((target (e1) == v) = false).
      { apply /eqP; intro Hc.
        clear w; contradict Hv.
        rewrite -Hc !in_set.
        move => /andP[Hv _];
        contradict Hv; apply /negP.
        by rewrite negb_involutive. }
      by destruct b, c.
(* TODO generaliser la fonction f + ses propriétés + simplifier cette preuve + retirer les g *)
  - destruct c;
    [set c := Eq | set c := Lt | set c := Gt].
    1,2: assert (Some (Some (inr None)) \in edge_set S /\ inr (inl tt) \in S /\ inr (inr tt) \in S)
          as [Hss [Htn Hcn]] by (rewrite !in_set; by repeat (split || apply /andP)).
    1,2: set ss := Sub (Some (Some (inr None))) Hss : edge (add_node_graph_data c H0 H1);
         set tn := Sub (inr (inl tt)) Htn : add_node_graph_data c H0 H1;
         set cn := Sub (inr (inr tt)) Hcn : add_node_graph_data c H0 H1.
    1,2: assert (edges_in_at_subset tn = [set n; sn] /\ edges_out_at_subset tn = [set ss] /\
                 edges_in_at_subset cn = [set ss] /\ edges_out_at_subset cn = set0)
          as [Htn_in [Htn_out [Hcn_in Hcn_out]]]
          by (repeat (split); apply /setP; intro e; rewrite !in_set;
            by destruct e as [[[[e | [[[] | []] | ]] | ] | ] ?]).
    3: assert (Htn : inr tt \in S) by (rewrite !in_set; apply /andP; by split).
    3: set tn := (Sub (inr tt) Htn : add_node_graph_data c H0 H1).
    3: assert (edges_in_at_subset tn = [set n; sn] /\ edges_out_at_subset tn = set0) as [Htn_in Htn_out]
          by (split; apply /setP; intro e; rewrite !in_set; by destruct e as [[[[e | []] | ] | ] ?]).
    3: destruct v as [];
      replace Hv with Htn by apply eq_irrelevance.
    1,2: destruct v as [[] | []];
      [replace Hv with Htn by apply eq_irrelevance | replace Hv with Hcn by apply eq_irrelevance].
    all: destruct b; cbn.
    all: by rewrite ?Htn_in ?Htn_out ?Hcn_in ?Hcn_out ?cards2 ?cards1 ?cards0.
Qed.
Arguments p_deg_add_node : clear implicits.

Lemma p_left_add_node (c : comparison) (G : geos) : proper_left (add_node_graph_data_bis c G).
Proof.
  unfold add_node_graph_data_bis.
  generalize (erefl (order G));
  destruct (order G) as [ | v0 [ | v1 l]] at 2 3;
  intro H; try (apply p_left).
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1].
  { destruct (p_order G) as [O _].
    split; [apply (O v0) | apply (O v1)];
    rewrite H !in_cons eq_refl //.
    apply /orP; by right. }
  unfold proper_left.
  destruct (add_node_hyp H).
  intros [[v | v] Hv]; cbn;
  intro Hl; unfold add_node_left.
  - rewrite in_set; cbn.
    rewrite !SubK !p_concl3 //.
    assert (Hc : target (left v) = v).
    { assert (Hcc : left v \in edges_in_at_subset v) by apply (p_left Hl).
      apply /eqP; by rewrite in_set in Hcc. }
    rewrite Hc.
    case_if;
    rewrite ?Hc //;
    destruct Hl as [Hl | Hl]; contradict Hl; by rewrite ?Hif ?Hif0 ?Hv0 ?Hv1.
  - destruct c;
    [destruct v as [[] | []] | destruct v as [[] | []] | destruct v as []].
    all: try (destruct Hl as [Hl | Hl]; by contradict Hl).
    all: by rewrite in_set !SubK.
Qed.
Arguments p_left_add_node : clear implicits.

Lemma p_order_add_node (c : comparison) (G : geos) : proper_order (add_node_graph_data_bis c G).
Proof.
  unfold add_node_graph_data_bis.
  generalize (erefl (order G));
  destruct (order G) as [ | v0 [ | v1 l]] at 2 3;
  intro H; try (apply p_order).
  destruct (add_node_hyp H) as [H0 H1].
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  unfold proper_order.
  destruct (p_order G) as [Hv U].
  split; cbn.
  - intros [[v | v] Hin]; cbn.
    + apply (iff_stepl (A := v \in order G)). 2:{ by apply iff_sym. }
      rewrite /add_node_order map_id in_seq_sig SubK
        -(proj2_sig (all_sigP (add_node_consistent_order c e0 e1))) /add_node_order_2.
      split.
      * intro Hl.
        assert (v != target e0 /\ v != target e1) as [? ?].
        { split;
          apply /negP; move => /eqP Hc;
          contradict Hin; apply /negP;
          rewrite Hc !in_set;
          [apply /nandP; right | ];
          apply /nandP; left;
          by rewrite negb_involutive. }
        destruct c;
        rewrite ?in_cons /add_node_type_order/ add_node_order_1 map_f // mem_filter;
        by repeat (apply /andP; split).
      * destruct c.
        all: rewrite ?in_cons mem_map ?mem_filter; cbn; trivial.
        all: by move => /andP[_ ?].
    + rewrite /add_node_order map_id in_seq_sig SubK
        -(proj2_sig (all_sigP (add_node_consistent_order c e0 e1))) /add_node_order_2.
      destruct c.
      3: destruct v as [].
      1,2: destruct v as [[] | []].
      all: cbn; split; trivial; intro Hl; contradict Hl; try by [].
      all: rewrite ?in_cons /add_node_order_2 /add_node_type_order /add_node_order_1;
           cbn; apply /negP.
      all: apply inr_seq_inl_filter.
  - rewrite /add_node_order map_id uniq_seq_sig
      -(proj2_sig (all_sigP (add_node_consistent_order c e0 e1))) /add_node_order_2.
    assert (injective (inl : G -> (add_node_graph_1 c e0 e1))) by apply inl_inj.
    destruct c.
    all: rewrite ?cons_uniq /add_node_type_order /add_node_order_1.
    1,2: apply /andP; split.
    2,4,5: rewrite map_inj_uniq //; by apply filter_uniq.
    all: apply (inr_seq_inl_filter (order G) _ (inr tt)).
Qed.

Definition add_node_geos (c : comparison) (G : geos) : geos := {|
  graph_data_of := add_node_graph_data_bis c G;
  p_deg := p_deg_add_node c G;
  p_left := p_left_add_node c G;
  p_order := p_order_add_node c G;
  |}.



(** ** Level 3: Proof Structure *)
(** * The rule of a node gives conditions on the formulae of its arrows *)
Definition proper_ax (G : geos) :=
  forall (v : G), vlabel v = ax_l -> exists el, exists er,
  (el \in edges_out_at_subset v) && (er \in edges_out_at_subset v) &&
  (elabel el == dual (elabel er)).
Lemma pre_proper_ax (G : geos) (v : G) (Hl : vlabel v = ax_l) :
  #|edges_out_at_subset v| = 2.
Proof. by rewrite (p_deg_out v) Hl. Qed.
Definition proper_ax3 (G : geos) :=
  forall (v : G) (Hl : vlabel v = ax_l),
  true_on2 (is_dual_f (elabel (g := G))) (pre_proper_ax Hl).
Lemma equiv_ax (G : geos) : proper_ax G -> proper_ax3 G.
Proof.
  unfold proper_ax, proper_ax3.
  intros H v Hl.
  elim: (H v Hl) => [el [er /andP[/andP[Hel Her] /eqP Heq]]].
  assert (Ho : other (pre_proper_ax Hl) Hel = er).
  { apply p_other4.
    - by [].
    - intro Hc.
      rewrite Hc in Heq; symmetry in Heq.
      contradict Heq.
      apply no_selfdual. }
  apply (simpl_sym (dual_sym_f (elabel (g := G))) (Ht := Hel)).
  by rewrite /is_dual_f /is_dual Ho Heq bidual.
Qed.

Definition proper_tens (G : geos) :=
  forall (v : G), vlabel v = tens_l ->
  elabel (ccl v) = tens (elabel (left v)) (elabel (right v)).

Definition proper_parr (G : geos) :=
  forall (v : G), vlabel v = parr_l ->
  elabel (ccl v) = parr (elabel (left v)) (elabel (right v)).

Definition proper_cut (G : geos) :=
  forall (v : G), vlabel v = cut_l -> exists el, exists er,
  (el \in edges_in_at_subset v) && (er \in edges_in_at_subset v) &&
  (elabel el == dual (elabel er)).
Lemma pre_proper_cut (G : geos) (v : G) (Hl : vlabel v = cut_l) :
  #|edges_in_at_subset v| = 2.
Proof. by rewrite (p_deg_in v) Hl. Qed.
Definition proper_cut3 (G : geos) :=
  forall (v : G) (Hl : vlabel v = cut_l),
  true_on2 (is_dual_f (elabel (g := G))) (pre_proper_cut Hl).
Lemma equiv_cut (G : geos) : proper_cut G -> proper_cut3 G.
Proof.
  unfold proper_cut, proper_cut3.
  intros H v Hl.
  elim: (H v Hl) => [el [er /andP[/andP[Hel Her] /eqP Heq]]].
  assert (Ho : other (pre_proper_cut Hl) Hel = er).
  { apply p_other4.
    - by [].
    - intro Hc.
      rewrite Hc in Heq; symmetry in Heq.
      contradict Heq.
      apply no_selfdual. }
  apply (simpl_sym (dual_sym_f (elabel (g := G))) (Ht := Hel)).
  by rewrite /is_dual_f /is_dual Ho Heq bidual.
Qed.

Set Primitive Projections.
Record proof_structure : Type :=
  Proof_structure {
    geos_of :> geos;
    p_ax : proper_ax geos_of;
    p_tens : proper_tens geos_of;
    p_parr : proper_parr geos_of;
    p_cut : proper_cut geos_of;
  }.
Unset Primitive Projections.


(** * The axiom graph is a proof_structure *)
Lemma p_ax_ax (x : atom) : proper_ax (ax_geos x).
Proof.
  unfold proper_ax.
  intros v Hl.
  destruct_I3 v Hv;
  try (contradict Hl; by rewrite Hv).
  exists ord0, ord1.
  unfold edges_out_at_subset.
  rewrite Hv 2!in_set. cbn.
  apply eqb_refl.
Qed.
Lemma p_ax_ax3 (x : atom) : proper_ax3 (ax_geos x).
Proof.
  unfold proper_ax3.
  intros v Hl.
  destruct_I3 v Hv;
  try (contradict Hl; by rewrite Hv).
  assert (ord0 \in edges_out_at_subset v /\ ord1 \in edges_out_at_subset v) as [H0 H1]
    by by rewrite /edges_out_at_subset Hv 2!in_set.
  apply (simpl_sym (dual_sym_f (elabel (g:=ax_geos x))) (Ht := H0)).
  unfold is_dual_f, is_dual.
  by rewrite (p_other4 (y := ord1)).
Qed.
Arguments p_ax_ax : clear implicits.

Lemma p_tens_ax (x : atom) : proper_tens (ax_geos x).
Proof.
  unfold proper_tens.
  intros v Hl.
  destruct_I3 v Hv;
  contradict Hl;
  by rewrite Hv.
Qed.
Arguments p_tens_ax : clear implicits.

Lemma p_parr_ax (x : atom) : proper_parr (ax_geos x).
Proof.
  unfold proper_parr.
  intros v Hl.
  destruct_I3 v Hv;
  contradict Hl;
  by rewrite Hv.
Qed.
Arguments p_parr_ax : clear implicits.

Lemma p_cut_ax (x : atom) : proper_cut (ax_geos x).
Proof.
  unfold proper_cut.
  intros v Hl.
  destruct_I3 v Hv;
  contradict Hl;
  by rewrite Hv.
Qed.
Arguments p_cut_ax : clear implicits.

Definition ax_ps (x : atom) : proof_structure := {|
  geos_of := ax_geos x;
  p_ax := p_ax_ax x;
  p_tens := p_tens_ax x;
  p_parr := p_parr_ax x;
  p_cut := p_cut_ax x;
  |}.


(** * A disjoint union of proof_structure is a proof_structure *)
Lemma p_ax_union (G0 G1 : proof_structure) : proper_ax (union_geos G0 G1).
Proof.
  unfold proper_ax.
  intros [v | v] Hl; cbn; cbn in Hl.
  all: destruct (p_ax Hl) as [el [er He]].
  1: exists (inl el), (inl er); rewrite 2!union_edges_at_inl.
  2: exists (inr el), (inr er); rewrite 2!union_edges_at_inr.
  all: rewrite !inj_imset //; (apply inl_inj || apply inr_inj).
Qed.
Lemma p_ax_union3 (G0 G1 : proof_structure) : proper_ax3 (union_geos G0 G1).
Proof.
  assert (proper_ax3 G0 /\ proper_ax3 G1) as [H0 H1] by (split; apply equiv_ax, p_ax).
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
Arguments p_ax_union : clear implicits.

Lemma p_tens_union (G0 G1 : proof_structure) : proper_tens (union_geos G0 G1).
Proof.
  unfold proper_tens.
  intros [v | v] Hl;
  assert (vlabel v = tens_l \/ vlabel v = parr_l) by (by apply tens_to_tensparr);
  rewrite union_right // union_ccl //;
  by apply p_tens.
Qed.
Arguments p_tens_union : clear implicits.

Lemma p_parr_union (G0 G1 : proof_structure) : proper_parr (union_geos G0 G1).
Proof.
  unfold proper_parr.
  intros [v | v] Hl;
  assert (vlabel v = tens_l \/ vlabel v = parr_l) by (by apply parr_to_tensparr);
  rewrite union_right // union_ccl //;
  by apply p_parr.
Qed.
Arguments p_parr_union : clear implicits.

Lemma p_cut_union (G0 G1 : proof_structure) : proper_cut (union_geos G0 G1).
Proof.
  unfold proper_cut.
  intros [v | v] Hl; cbn; cbn in Hl.
  all: destruct (p_cut Hl) as [el [er He]].
  1: exists (inl el), (inl er); rewrite 2!union_edges_at_inl.
  2: exists (inr el), (inr er); rewrite 2!union_edges_at_inr.
  all: rewrite !inj_imset //; (apply inl_inj || apply inr_inj).
Qed.
Lemma p_cut_union3 (G0 G1 : proof_structure) : proper_cut3 (union_geos G0 G1).
Proof.
  assert (proper_cut3 G0 /\ proper_cut3 G1) as [H0 H1] by (split; apply equiv_cut, p_cut).
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
Arguments p_cut_union : clear implicits.

Definition union_ps (G0 G1 : proof_structure) : proof_structure := {|
  geos_of := union_geos G0 G1;
  p_ax := p_ax_union G0 G1;
  p_tens := p_tens_union G0 G1;
  p_parr := p_parr_union G0 G1;
  p_cut := p_cut_union G0 G1;
  |}.


(** * Adding a node to a proof_structure yields a proof_structure *)
Lemma p_ax_add_node (c : comparison) (G : proof_structure) : proper_ax (add_node_geos c G).
Proof.
(* TODO il devrait y avoir plus simple, mais je n'ai pas réussi avec un
"destruct (order G) as [ | v0 [ | v1 l]] at 2 3 7." ... *)
(* pour référence, dans geos:
  unfold add_node_graph_data_bis.
  generalize (erefl (order G));
  destruct (order G) as [ | v0 [ | v1 l]] at 2 3;
  intro H; try (apply p_order).
  destruct (add_node_hyp H) as [H0 H1].
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  unfold proper_order.
*)
  destruct (order G) as [ | v0 [ | v1 l]] eqn:H;
  unfold add_node_geos, add_node_graph_data_bis, proper_ax; cbn.
  1,2: assert (Heq : match order G as o return (order G = o -> graph_data) with
            | [::] => fun=> G
            | v0 :: l0 =>
                match
                  l0 as l1 return (order G = v0 :: l1 -> graph_data)
                with
                | [::] => fun=> G
                | v1 :: l =>
                    fun Heq : order G = [:: v0, v1 & l] =>
                    let (H0, H1) := add_node_hyp Heq in
                    add_node_graph_data c H0 H1
                end
            end (erefl (order G)) = G) by
  (generalize (erefl (order G));
  destruct (order G) as [ | ? [ | ? ?]] at 2 3; trivial; intro Hc; contradict Hc; by rewrite H).
  1,2: rewrite !Heq -/(proper_ax G); by apply p_ax.
  assert (Heq : match order G as o return (order G = o -> graph_data) with
        | [::] => fun=> G
        | v0 :: l0 =>
            match
              l0 as l1 return (order G = v0 :: l1 -> graph_data)
            with
            | [::] => fun=> G
            | v1 :: l =>
                fun Heq : order G = [:: v0, v1 & l] =>
                let (H0, H1) := add_node_hyp Heq in
                add_node_graph_data c H0 H1
            end
        end (erefl (order G)) = let (H0, H1) := add_node_hyp H in
                add_node_graph_data c H0 H1).
  { generalize (erefl (order G)).
    destruct (order G) as [ | ? [ | ? ?]] at 2 3; intro Hc;
    [contradict Hc; by rewrite H | contradict Hc; by rewrite H | ].
    assert (v0 = s /\ v1 = s0 /\ l = l0) as [H0 [H1 H2]] by
      (revert Hc; move => /eqP Hc; revert Hc; rewrite H !eqseq_cons;
      by move => /andP[/eqP ? /andP[/eqP ? /eqP ?]]).
    revert H.
    rewrite H0 H1 H2.
    intro H; by replace H with Hc by apply eq_irrelevance. }
  rewrite Heq; clear Heq.
  (* copié-collé de geos *)
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [Hv0  Hv1].
  { destruct (p_order G) as [O _].
    split; [apply (O v0) | apply (O v1)];
    rewrite H !in_cons eq_refl //.
    apply /orP; by right. }
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  assert (Hneqv : v0 != v1).
  { destruct (p_order G) as [_ U].
    rewrite H cons_uniq in_cons negb_or in U.
    revert U; by move => /andP[/andP[? _] _]. }
  assert (Hneqe : e0 == e1 = false).
  { apply negbTE, (contra_neq (z1 := target e0) (z2 := target e1)).
    intros; by f_equal.
    by rewrite !p_concl3. }
  destruct (add_node_hyp H) as [H0 H1].
  set S := setT :\ inl (target e0) :\ inl (target e1) : {set add_node_graph_1 c e0 e1}.
  assert (None \in edge_set S /\ Some None \in edge_set S) as [Hn Hsn].
  { rewrite !in_set.
    split; repeat (apply /andP; split); trivial;
    try (apply H0 || apply H1);
    rewrite p_concl3 //; by destruct c. }
  set n := Sub None Hn : edge (add_node_graph_data c H0 H1);
  set sn := Sub (Some None) Hsn : edge (add_node_graph_data c H0 H1).
  (* fin du copié-collé *)
  intros [[v | v] Hv] Hl; fold S in Hv; cbn in Hl; fold S; cbn.
  - destruct (p_ax Hl) as [el [er Helr]].
    revert Helr; move => /andP[/andP[Hel Her] /eqP Helr].
      (* TODO utiliser f, puis exists (f e) *)
      (* pas réussi à faire f ... en attendant, copié-collé de geos : *)
    set w := Sub (inl v) Hv : add_node_graph_data c H0 H1.
    set f_1 := (fun e => if (e == e1) then None
                         else if (e == e0) then Some None
                         else Some (Some (inl e))) : edge G -> edge (add_node_graph_1 c e0 e1).
    assert (Hf : forall e, f_1 e \in edge_set S).
    { intro e.
      unfold f_1; case_if.
      rewrite !in_set.
      repeat (apply /andP; split); trivial.
      1:{ apply H1. } 1:{ apply H0. }
      all: rewrite p_concl3 //.
      all: apply /negP; intro.
      1: set et := e1. 2: set et := e0.
      all: assert (Hc : e = et) by (apply /eqP; by rewrite -in_set1 -p_concl2 // in_set).
      all: by contradict Hc. }
    set f := fun (e : edge G) => Sub (f_1 e) (Hf e) : edge (add_node_graph_data c H0 H1).
    assert (Hinj : injective f).
    { intros e e' Heq.
      assert (Heqbis : f_1 e = f_1 e').
      { replace (f_1 e) with (sval (Sub (f_1 e) (Hf e))) by apply SubK.
        replace (f_1 e') with (sval (Sub (f_1 e') (Hf e'))) by apply SubK.
        by f_equal. }
      revert Heqbis.
      unfold f_1; case_if.
      move => /eqP Heqbis; apply /eqP; revert Heqbis.
      by rewrite 2!Some_eqE inl_eqE. }
    (* fin du copié-collé *)
    (* TODO lemma pour ce assert (apres avoir defini f) *)
      assert (Hlem : forall b, edges_at_subset b (Sub (inl v) Hv : add_node_graph_data c H0 H1)
        = [set f e | e in edges_at_subset b v]).
      { intro b; apply /setP; intro e.
(* copie colle de geos -> utiliser ce lemma aussi dans geos *)
        destruct e as [[[[e | e] | ] | ] He];
        rewrite in_set; cbn; rewrite !SubK; cbn.
    + assert (Heq : Sub (Some (Some (inl e))) He = f e).
      { apply /eqP; rewrite /f sub_val_eq SubK /f_1; apply /eqP.
        case_if.
        all: contradict He.
        all: rewrite ?Hif ?Hif0 !in_set.
        1: move => /andP[_ /andP[He _]].
        2: move => /andP[_ /andP[_ /andP[He _]]].
        all: contradict He; apply /negP; cbn.
        all: by rewrite negb_involutive p_concl3. }
      by rewrite Heq inj_imset // in_set.
    + symmetry; apply /negbTE.
      rewrite Imset.imsetE in_set.
      apply /imageP; move => [a _ A].
      assert (Hc : Some (Some (inr e)) = f_1 a) by apply (EqdepFacts.eq_sig_fst A).
      contradict Hc.
      unfold f_1; case_if.
    + assert (Heq : Sub (Some None) He = f e0).
      { apply /eqP; rewrite /f /eqP sub_val_eq SubK /f_1; apply /eqP.
        case_if.
        contradict Hneqe. by rewrite Hif eq_refl. }
      rewrite Heq inj_imset // in_set.
      assert ((target (e0) == v) = false).
      { apply /eqP; intro Hc.
        clear w; contradict Hv.
        rewrite -Hc !in_set.
        move => /andP[_ /andP[Hv _]];
        contradict Hv; apply /negP.
        by rewrite negb_involutive. }
      by destruct b, c.
    + assert (Heq : Sub None He = f e1)
        by (apply /eqP; rewrite /f sub_val_eq SubK /f_1; case_if).
      rewrite Heq inj_imset // in_set.
      assert ((target (e1) == v) = false).
      { apply /eqP; intro Hc.
        clear w; contradict Hv.
        rewrite -Hc !in_set.
        move => /andP[Hv _];
        contradict Hv; apply /negP.
        by rewrite negb_involutive. }
      by destruct b, c. }
(* fin du copié collé du assert *)
    exists (f el), (f er).
    repeat (apply /andP; split).
    + rewrite Hlem inj_imset //.
    + rewrite Hlem inj_imset //.
    + rewrite /f !SubK.
      unfold f_1; case_if;
      apply /eqP.
      all: try by rewrite -?Hif -?Hif0 -?Hif1 -?Hif2.
      all: contradict Helr;
        rewrite ?Hif ?Hif0 ?Hif1 ?Hif2;
        apply nesym, no_selfdual.
  - contradict Hl; by destruct c, v.
Qed.
(* TODO destruct -> elim *)



(** ** Proof Structure of a Proof Sequent *)
(* Function at each level *)
(*
Fixpoint graph_proof {l : list formula} (pi : ll l) : graph_data := match pi with
| ax_r x => ax_graph_data x
| ex_r _ _ pi0 sigma => graph_proof pi0
| tens_r _ _ _ _ pi0 pi1 => let gd0 := graph_proof pi0 in let gd1 := graph_proof pi1 in
    let gd := gd0 ⊎ gd1 in gd0
(* take 1st concl *)
| parr_r _ _ _ pi0 => 
| cut_r _ _ _ pi0 pi1 => 
end.
*)

(*
+inductive proof that ps(pi) is a proof_structure
+inductive proof that order list of l (pi : ll l) corresponds to order c_i of the graph
*)


(*
Fixpoint ps {l : list formula} (pi : ll l) : proof_structure :=
match pi with
| ax_r X => graph with a node labelled ax, two nodes c_1 and c_2, 
    an edge ax->c_1 labelled covar X, another ax->c_2 labelled var X

| ex_r pi0 sigma => take ps (pi_0), re-label the c_i into c_sigma(i):
About Permutation_Type.

| tens_r pi0 pi1 => take G0=ps (pi0) and G1=ps (pi1)
    In G0: turn c_i into c_n+i-1 for i\neq0, for c_0 turn into c_inf, with n =#conc in G1
    make a disjoint union of G0 and G1
    find edges on c_0 and c_n, and their endpoints (char. proof str. -> unicity)
    remove edges ?1->c_0 (B), ?0->c_inf(A)
    remove nodes c0 c_inf
    add nodes t(tens) c0
    add edges ?0->t (A,0), ?1->t (B,1), t->c_0 (tens A B)

| parr_r pi0 => take G0=ps (pi0)
    find edges on c_0 and c_1, and their endpoints (char. proof str. -> unicity)
    remove edges ?0->c_0 (A), ?1->c_1(B)
    remove nodes c0 c_1
    re-label c_i into c_i-1
    add nodes p(parr) c0
    add edges ?0->p (A,0), ?1->p (B,1), p->c_0 (parr A B)

| cut_r A l1 l2 pi0 pi1 => take G0=ps (pi0) and G1=ps (pi1)
    make a disjoint union of G0 and G1
    find edges on c_inf0 and c_inf1, and their endpoints (char. proof str. -> unicity)
    remove edges ?0->c_inf0 (var A), ?1->c_inf1(covar A)
    remove nodes cinf0 c_inf1
    add nodes c(cut)
    add edges ?0->c (var A,0), ?1->c (covar A,1)
*)


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

(* TODO check if every lemma proved is useful *)


(**************************************************************************************************)
(** ** PREVIOUS CONTENT of the file mll.v *)

(** * Cut Elimination *)

Ltac destruct_eqrefl H :=
list_simpl in H;
match goal with
| H : ?x = ?x |- _ => assert (H = eq_refl) as ->
                        by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                      cbn
end.

(** Symmetric induction principle *)
Lemma sym_induction_ll (P : forall [A B l1 l2 l3 l4], ll (l1 ++ A :: l2) -> ll (l3 ++ B :: l4)
                          -> Type) :
  (forall A B l1 l2 l3 l4 (pi1 : ll (l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)),
     P pi2 pi1 -> P pi1 pi2) ->
  (forall X B l3 l4 (pi2 : ll (l3 ++ B :: l4)),
     P (ax_r X : ll (nil ++ covar X :: var X :: nil)) pi2) ->
  (forall X B l3 l4 (pi2 : ll (l3 ++ B :: l4)),
     P (ax_r X : ll ((covar X :: nil) ++ var X :: nil)) pi2) ->
  (forall A B l1 l2 l3 l4 l' (pi1 : ll l') (pi2 : ll (l3 ++ B :: l4))
     (HP : Permutation_Type l' (l1 ++ A :: l2)),
     P (rew (rew (surjective_pairing (proj1_sig (Permutation_Type_vs_elt_inv _ _ _ HP)))
              in proj2_sig (Permutation_Type_vs_elt_inv _ _ _ HP)) in pi1) pi2 ->
     P (ex_r pi1 HP) pi2) ->
  (forall A B C D l0 l1 l2 l3 l4 (pi0 : ll (C :: l0))
     (pi1 : ll (D :: l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)),
     P (pi1 : ll ((D :: l1) ++ A :: l2)) pi2 ->
     P (rew <- (app_assoc (tens C D :: l1) (A :: l2) _) in tens_r pi0 pi1) pi2) ->
  (forall A B C D l0 l1 l2 l3 l4 (pi0 : ll (D :: l0))
     (pi1 : ll (C :: l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)),
     P (pi1 : ll ((C :: l1) ++ A :: l2)) pi2 ->
     P (rew (app_assoc (tens C D :: l0) _ (A :: l2)) in tens_r pi1 pi0 ) pi2) ->
  (forall A B C D l1 l2 l3 l4 (pi1 : ll (C :: D :: l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)),
     P (pi1 : ll ((C :: D :: l1) ++ A :: l2)) pi2 ->
     P (parr_r pi1 : ll ((parr C D :: l1) ++ A :: l2)) pi2) ->
  (forall C D C' D' l2' l2'' (pi1' : ll (C :: l2')) (pi1'' : ll (D :: l2'')),
     (forall l3 l4 (pi2 : ll (l3 ++ C' :: l4)), P (pi1' : ll (nil ++ _)) pi2) ->
     (forall l3 l4 (pi2 : ll (l3 ++ D' :: l4)), P (pi1'' : ll (nil ++ _)) pi2) ->
     forall l4' l4'' (pi2' : ll (C' :: l4')) (pi2'' : ll (D' :: l4'')),
       P (tens_r pi1' pi1'' : ll (nil ++ _)) (tens_r pi2' pi2'' : ll (nil ++ _))) ->
  (forall C D C' D' l2 (pi1 : ll (C :: D :: l2)),
     (forall l3 l4 (pi2 : ll (l3 ++ C' :: l4)), P (pi1 : ll (nil ++ _)) pi2) ->
      forall l4 (pi2 : ll (C' :: D' :: l4)),
       P (parr_r pi1 : ll (nil ++ _)) (parr_r pi2 : ll (nil ++ _))) ->
  (forall C D C' D' l1' l1'' (pi1' : ll (C :: l1')) (pi1'' : ll (D :: l1'')),
     (forall l3 l4 (pi2 : ll (l3 ++ C' :: l4)), P (pi1' : ll (nil ++ _)) pi2) ->
     (forall l3 l4 (pi2 : ll (l3 ++ D' :: l4)), P (pi1'' : ll (nil ++ _)) pi2) ->
     forall l4 (pi2 : ll (D' :: C' :: l4)),
       P (tens_r pi1' pi1'' : ll (nil ++ _)) (parr_r pi2 : ll (nil ++ _))) ->
  forall A B l1 l2 l3 l4 (pi1 : ll (l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)), P pi1 pi2.
Proof.
intros Hsym Hax1 Hax2 Hex Htens1 Htens2 Hparr Htt Hpp Htp.
enough (forall c s A B s1 s2 (pi1 : ll s1) (pi2 : ll s2),
          s = psize pi1 + psize pi2 -> fsize A <= c -> fsize B <= c ->
          forall l1 l2 l3 l4 (Heq1 : s1 = l1 ++ A :: l2) (Heq2 : s2 = l3 ++ B :: l4),
          P A B l1 l2 l3 l4 (rew Heq1 in pi1) (rew Heq2 in pi2)) as IH
  by (now intros A B l1 l2 l3 l4 pi1 pi2;
          refine (IH (max (fsize A) (fsize B)) _ _ _ _ _ pi1 pi2 _ _ _ _ _ _ _ eq_refl eq_refl);
          try lia).
induction c as [c IHf0] using lt_wf_rect.
assert (forall A B, fsize A < c -> fsize B < c ->
          forall l1 l2 l3 l4 pi1 pi2, P A B l1 l2 l3 l4 pi1 pi2) as IHf
  by (now intros A B HA HB l1 l2 l3 l4 pi1 pi2;
          refine (IHf0 (max (fsize A) (fsize B)) _ _ A _ _ _ pi1 pi2 _ _ _ _ _ _ _ eq_refl eq_refl);
          try lia); clear IHf0.
induction s as [s IHp0] using lt_wf_rect.
assert (forall A B l1 l2 l3 l4 pi1 pi2, psize pi1 + psize pi2 < s -> fsize A <= c -> fsize B <= c ->
          P A B l1 l2 l3 l4 pi1 pi2) as IHp
  by (now intros A B l1 l2 l3 l4 pi1 pi2 Hp HA HB;
          refine (IHp0 _ Hp _ _ _ _ pi1 pi2 _ _ _ _ _ _ _ eq_refl eq_refl)); clear IHp0.
intros A B s1 s2 pi1 pi2 Heqs HA HB l1 l2 l3 l4 Heq1 Heq2; rewrite_all Heqs; clear s Heqs.
destruct pi1.
- destruct l1; inversion Heq1; subst; cbn in Heq1.
  + destruct_eqrefl Heq1; apply Hax1.
  + destruct l1; inversion Heq1; subst.
    * destruct_eqrefl Heq1; apply Hax2.
    * exfalso; destruct l1; inversion Heq1.
- subst; cbn; apply Hex, IHp; cbn; rewrite ? psize_rew; lia.
- destruct l1; inversion Heq1.
  + destruct pi2; subst; cbn in HA; destruct_eqrefl Heq1.
    * repeat (destruct l3; inversion Heq2); subst; destruct_eqrefl Heq2; apply Hsym;
        [ apply Hax1 | apply Hax2 ].
    * apply Hsym, Hex, IHp; cbn; rewrite ? psize_rew; lia.
    * destruct l3; inversion Heq2; subst; cbn in HB.
      -- destruct_eqrefl Heq2.
         apply Htt; intros; apply IHf; lia.
      -- apply Hsym.
         dichot_elt_app_inf_exec H1; subst.
         ++ replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew <- (app_assoc (tens A1 B1 :: l3) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens1, IHp; cbn; try lia.
            ** rewrite <- (rew_opp_l ll (app_assoc (tens A1 B1 :: l3) (B :: l) l1)).
               f_equal; rewrite rew_compose.
               now assert (eq_trans Heq2 (app_assoc (tens A1 B1 :: l3) (B :: l) l1) = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
         ++ replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew (app_assoc (tens A1 B1 :: l6) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens2, IHp; cbn; lia.
            ** rewrite <- (rew_opp_r ll (app_assoc (tens A1 B1 :: l6) l2 (B :: l4))).
               f_equal; unfold eq_rect_r; rewrite rew_compose.
               now assert (eq_trans Heq2 (eq_sym (app_assoc (tens A1 B1 :: l6) l2 (B :: l4)))
                         = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
    * destruct l3; inversion Heq2; subst; destruct_eqrefl Heq2; cbn in HB.
      -- apply Htp; intros; apply IHf; lia.
      -- apply Hsym, Hparr, IHp; cbn; lia.
  + subst; cbn.
    dichot_elt_app_inf_exec H1; subst.
    * change ((tens A0 B0 :: l1) ++ A :: l ++ l0) with (tens A0 B0 :: l1 ++ A :: l ++ l0) in Heq1.
      replace (rew [ll] Heq1 in tens_r pi1_1 pi1_2)
         with (rew <- (app_assoc (tens A0 B0 :: l1) _ _) in tens_r pi1_1 pi1_2).
      -- apply Htens1, IHp; cbn; lia.
      -- rewrite <- (rew_opp_l ll (app_assoc (tens A0 B0 :: l1) (A :: l) l0)).
           f_equal; rewrite rew_compose.
           now assert (eq_trans Heq1 (app_assoc (tens A0 B0 :: l1) (A :: l) l0) = eq_refl)
                 as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
               cbn.
    * change ((tens A0 B0 :: l5 ++ l6) ++ A :: l2)
        with (tens A0 B0 :: (l5 ++ l6) ++ A :: l2) in Heq1.
      replace (rew [ll] Heq1 in tens_r pi1_1 pi1_2)
         with (rew (app_assoc (tens A0 B0 :: l5) _ _) in tens_r pi1_1 pi1_2).
      -- apply Htens2, IHp; cbn; lia.
      -- rewrite <- (rew_opp_r ll (app_assoc (tens A0 B0 :: l5) l6 (A :: l2))).
         f_equal; unfold eq_rect_r; rewrite rew_compose.
         now assert (eq_trans Heq1 (eq_sym (app_assoc (tens A0 B0 :: l5) l6 (A :: l2))) = eq_refl)
               as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
             cbn.
- destruct l1; inversion Heq1.
  + destruct pi2; subst; cbn in HA; destruct_eqrefl Heq1.
    * repeat (destruct l3; inversion Heq2); subst; destruct_eqrefl Heq2; apply Hsym;
        [ apply Hax1 | apply Hax2 ].
    * apply Hsym, Hex, IHp; cbn; rewrite ? psize_rew; lia.
    * destruct l3; inversion Heq2; subst; cbn in HB.
      -- destruct_eqrefl Heq2.
         apply Hsym, Htp; intros; apply IHf; lia.
      -- apply Hsym; cbn.
         dichot_elt_app_inf_exec H1; subst.
         ++ change ((tens A1 B1 :: l3) ++ B :: l ++ l1)
              with (tens A1 B1 :: l3 ++ B :: l ++ l1) in Heq2.
            replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew <- (app_assoc (tens A1 B1 :: l3) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens1, IHp; cbn; lia.
            ** rewrite <- (rew_opp_l ll (app_assoc (tens A1 B1 :: l3) (B :: l) l1)).
               f_equal; rewrite rew_compose.
               now assert (eq_trans Heq2 (app_assoc (tens A1 B1 :: l3) (B :: l) l1) = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
         ++ change ((tens A1 B1 :: l0 ++ l5) ++ B :: l4)
              with (tens A1 B1 :: (l0 ++ l5) ++ B :: l4) in Heq2.
            replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew (app_assoc (tens A1 B1 :: l0) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens2, IHp; cbn; lia.
            ** rewrite <- (rew_opp_r ll (app_assoc (tens A1 B1 :: l0) l5 (B :: l4))).
               f_equal; unfold eq_rect_r; rewrite rew_compose.
               now assert (eq_trans Heq2 (eq_sym (app_assoc (tens A1 B1 :: l0) l5 (B :: l4)))
                         = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
    * destruct l3; inversion Heq2; subst; cbn in HB; destruct_eqrefl Heq2.
      -- apply Hpp; intros; apply IHf; lia.
      -- apply Hsym, Hparr, IHp; cbn; lia.
  + subst; cbn; destruct_eqrefl Heq1.
    apply Hparr, IHp; cbn; lia.
Qed.

Theorem cut A l1 l2 l3 l4 :
  ll (l1 ++ A :: l2) -> ll (l3 ++ dual A :: l4) -> ll (l3 ++ l2 ++ l1 ++ l4).
Proof.
intros pi1 pi2; assert (Heq := eq_refl (dual A)); revert pi1 pi2 Heq.
apply (sym_induction_ll (fun A B l1 l2 l3 l4 pi1 pi2 => B = dual A -> ll (l3 ++ l2 ++ l1 ++ l4)));
  clear A l1 l2 l3 l4; cbn; try now intuition subst.
- intros A B l1 l2 l3 l4 pi1 pi2 pi ->.
  apply (ex_r (pi (eq_sym (bidual A)))).
  rewrite (app_assoc l1), (app_assoc l3); apply Permutation_Type_app_comm.
- intros A B l1 l2 l3 l4 l' pi1 pi2 HP.
  destruct (Permutation_Type_vs_elt_inv A l1 l2 HP) as [(l1', l2') ->]; cbn in pi1, HP; cbn.
  intros pi0' pi0; apply pi0' in pi0; clear - HP pi0.
  apply (ex_r pi0).
  apply Permutation_Type_app_head; rewrite ? app_assoc; apply Permutation_Type_app_tail.
  transitivity (l1' ++ l2'); [ apply Permutation_Type_app_comm | ].
  transitivity (l1 ++ l2); [ | apply Permutation_Type_app_comm ].
  apply (Permutation_Type_app_inv _ _ _ _ _ HP).
- intros A B C D l0 l1 l2 l3 l4 pi1 pi2 pi3 pi4 ->.
  change (ll (l3 ++ (l2 ++ l0) ++ tens C D :: l1 ++ l4)).
  apply ex_r with (tens C D :: ((l1 ++ l4) ++ l3 ++ l2) ++ l0); [ apply tens_r; trivial | ].
  + apply (ex_r (pi4 eq_refl)).
    rewrite app_assoc; apply Permutation_Type_app_comm.
  + list_simpl; rewrite app_comm_cons, app_assoc, ? (app_assoc l3), (app_assoc (l3 ++ l2)).
    apply Permutation_Type_app_comm.
- intros A B C D l0 l1 l2 l3 l4 pi1 pi2 pi3 pi4' pi4; apply pi4' in pi4; clear pi4'.
  apply ex_r with (tens C D :: l0 ++ (l1 ++ l4) ++ l3 ++ l2); [ apply tens_r; trivial | ].
  + apply (ex_r pi4).
    rewrite app_assoc; apply Permutation_Type_app_comm.
  + list_simpl; rewrite app_comm_cons, ? (app_assoc l3), ? app_assoc, <- app_assoc.
    apply Permutation_Type_app_comm.
- intros A B C D l1 l2 l3 l4 pi1 pi2 pi3' pi3; apply pi3' in pi3; clear pi3'.
  apply ex_r with (parr C D :: (l1 ++ l4) ++ l3 ++ l2); [ apply parr_r, (ex_r pi3) | ].
  + rewrite app_assoc; apply Permutation_Type_app_comm.
  + list_simpl; rewrite app_comm_cons, ? app_assoc, <- app_assoc.
    apply Permutation_Type_app_comm.
- intros C D C' D' l1 l2 pi1 pi2 IHC IHD l0 pi0 Heq; injection Heq as -> ->.
  rewrite <- app_assoc; apply IHC; auto.
  now rewrite <- app_nil_l; apply IHD.
Qed.
*)

End Atoms.
