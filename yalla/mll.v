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
| cut_r : forall A l1 l2 l3 l4, ll (l1 ++ A :: l2) ->
             ll (l3 ++ dual A :: l4) -> ll (l3 ++ l2 ++ l1 ++ l4).
Notation "⊢ l" := (ll l) (at level 70).



(** ** Size of proofs *)
Fixpoint psize l (pi : ll l) :=
match pi with
| ax_r _ => 1
| ex_r _ _ pi0 _ => S (psize pi0)
| tens_r _ _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
| parr_r _ _ _ pi0 => S (psize pi0)
| cut_r _ _ _ _ _ pi0 pi1 => S (psize pi0 + psize pi1)
end.

Lemma psize_pos l (pi : ll l) : 0 < psize pi.
Proof. destruct pi; cbn; by []. Qed.

Lemma psize_rew l l' (pi : ll l) (Heq : l = l') : psize (rew Heq in pi) = psize pi.
Proof. now subst. Qed.


(*******************************************************************************************************************)
(** ** Preliminaries *)

(** * Some results on 'I_n *)
(** The function inord is injective on integers <= n *)
Lemma inord_inj : forall n i j : nat, i <= n -> j <= n -> @inord n i = @inord n j -> i = j.
Proof.
  intros n i j ? ? H.
  assert(Hn : forall k : nat, k <= n -> nat_of_ord (@inord n k) = k).
    intros. apply inordK. lia.
  now rewrite <-(Hn i), <-(Hn j), H.
Qed.

(** 'I_0 has the empty enumeration *)
Lemma enum_I0 : enum 'I_0 = [::].
Proof. rewrite <-enum0. apply eq_enum, card0_eq, card_ord. Qed.

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
  [left | right]; exact (eqP H).
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
  [left | right; left | right; right]; exact (eqP H).
Qed.

Ltac destruct_I3 n H := destruct (case_I3bis n) as [H | [H | H]].

(* TOTHINK other possibility instead of the tactics:
Definition case2 {A : Type} (n : 'I_2) (a0 a1 : A) := match val n with | 0 => a0 | _ => a1 end.
*)
(* TOTHINK possible case_nter avec des set {_}+{_}+...*)

(** TO REMOVE test to see if the lemmas are good enough *)
Definition ftest2 : 'I_2 -> 'I_3 := fun n => match val n with
  | 0 => inord 1
  | _ => inord 0 end.
Goal injective ftest2.
Proof.
  unfold injective.
  intros n m Heq.
  destruct_I2 n Hn; destruct_I2 m Hm;
  rewrite Hn Hm; rewrite Hn Hm in Heq;
  try by []; unfold ftest2 in Heq; cbn in Heq.
  - now assert (C: 1 = 0) by (now apply (inord_inj (n:=2))).
  - now assert (C: 0 = 1) by (now apply (inord_inj (n:=2))).
Qed.

Definition ftest3 : 'I_3 -> 'I_3 := fun n => match val n with
  | 0 => inord 1
  | 1 => inord 0
  | _ => inord 2 end.
Goal injective ftest3.
Proof.
  unfold injective.
  intros n m Heq.
  destruct_I3 n Hn; destruct_I3 m Hm;
  rewrite Hn Hm; rewrite Hn Hm in Heq;
  try by []; unfold ftest3 in Heq; cbn in Heq.
  - now assert (C: 1 = 0) by (now apply (inord_inj (n:=2))).
  - now assert (C: 1 = 2) by (now apply (inord_inj (n:=2))).
  - now assert (C: 0 = 1) by (now apply (inord_inj (n:=2))).
  - now assert (C: 0 = 2) by (now apply (inord_inj (n:=2))).
  - now assert (C: 2 = 1) by (now apply (inord_inj (n:=2))).
  - now assert (C: 2 = 0) by (now apply (inord_inj (n:=2))).
Qed.
(** end of test *)


(** * Type [rule] for the rule of a node *)
Inductive rule : Type :=
  | ax_l
  | tens_l
  | parr_l
  | cut_l
  | concl_l.

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
  destruct A, B; split; simpl; intro H; trivial; now contradict H.
Qed.

Definition rules_dectype := {|
  car := rule;
  dectype.eqb := eqb_rule;
  eqb_eq := eqb_eq_rule |}.

(** Tactic to distinguish cases in rule *)
Lemma case_rule (r : rule) : {r = ax_l} + {r = tens_l} + {r = parr_l} + {r = cut_l} + {r = concl_l}.
Proof. (* possible de faire plus simple grace à OLlibs ? il y a de la decidabilité dedans
          ou bien avec eqType de MathComp, qui est equivalent à DecType ?
          pas sur, comme dans les 2 cas on se ramène au case {x=y} + {x <> y} *)
  destruct r.
  - by apply inleft, inleft, inleft, Specif.left.
  - by apply inleft, inleft, inleft, Specif.right.
  - by apply inleft, inleft, inright.
  - by apply inleft, inright.
  - by apply inright.
Qed.

Ltac destruct_rule r H := destruct (case_rule r) as [[[[H | H] | H] | H] | H].

(* TOTHINK rule as a finType ? possible if necessary *)


(** * A DecType is an eqType *)
Definition decType_eqMixin (X : DecType) := EqMixin (eq_dt_reflect (X:=X)).

(* [formula] as an eqType *)
Canonical formula_eqType := EqType formula (decType_eqMixin (formulas_dectype)).

(* [rule] as an eqType *)
Canonical rule_eqType := EqType rule (decType_eqMixin (rules_dectype)).


(** * Some results on cardinality *)
(** Both visions of a set as set or subset have the same cardinal *)
Lemma card_set_subset (T : finType) (P : pred T) : #|[finType of {e : T | P e}]| = #|[set e | P e]|.
Proof. by rewrite card_sig cardsE. Qed.

(** Removing an element of a set decrease cardinality by 1 *)
Lemma cardsR1_set : forall (T : finType) (a : T) , #|setT :\ a| = #|T| - 1.
Proof.
  intros ? a.
  replace (#|T|) with ((a \in setT) + #|setT :\ a|)
    by (symmetry; rewrite <-cardsT; apply cardsD1).
  rewrite in_setT. lia.
Qed.

Lemma cardsR1_subset : forall (T : finType) (a : T) (A : {set T}), #|A :\ a| = #|A| - (a \in A).
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
Definition pick_unique_subset := fun {T : finType} {S : {set T}} (H : #|S| = 1) => proj1_sig (mem_card1 H).
Definition pick_unique_set := fun {T : finType} (H : #|T| = 1) => proj1_sig (fintype1 H).

Lemma pick_unique_subset_in {T : finType} {S : {set T}} (H : #|S| = 1) :
  pick_unique_subset H \in S.
Proof.
  replace (pick_unique_subset H \in pred_of_set S)
    with (pred1 (pick_unique_subset H) \subset pred_of_set S)
    by apply subset_pred1.
  apply eq_subxx.
  unfold pick_unique_subset. cbn.
  by destruct (mem_card1 H).
Qed.
(* see which pick_unique is simpler to use, idem lemma card *)



(** ** Level 0: Multigraphs from the library GraphTheory *)
(** * Notations from the library *)
(* G0 ⊎ G1 = disjoint union
   G ∔ v = add a vertex labelled v
   G ∔ [ x , u , y ] = add an arrow from x to y labelled u *)
Open Scope graph_scope.

(** * Out & In edges of a vertex **)
Definition edges_out_at_subset {Lv : Type} {Le : Type} {G : graph Lv Le} (v : G) : {set edge G} :=
  [set e | source e == v].
Definition edges_in_at_subset {Lv : Type} {Le : Type} {G : graph Lv Le} (v : G) : {set edge G} :=
  [set e | target e == v].

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
    order : list (vertex graph_of);
    left : vertex graph_of -> edge graph_of;
  }.
Unset Primitive Projections.

(* sig [eta mem S] avec S : {set G} *)
(* idées:
- direction avec type totaux (directement sur vertex -> edges)
- sum type pour avoir toutes les informations et contraintes selon le type de noeuds, codé en tant que 
- ajouter une donnée n et order = fonction de I_n vers des neouds/aretes ;
    ou une liste de noeuds/aretes, sans le n
- definir juste left, en deduire right apres
- curryfier les sigma input

TOTHINK other possibilities for the functions:
    order : [finType of {v : graph_of | vlabel v == concl_l}] -> 'I_#|[finType of {v : graph_of | vlabel v == concl_l}]|;
avec    order_inj : injective order;

    order : {perm {v : graph_of | vlabel v == concl_l}};
  -     direction : bool -> vertex graph_of -> edge graph_of; avec
Notation left := (direction false).
Notation right := (direction true).
  - use [set v : vertex graph_of| vlabel v == concl_l], once known how to turn it into a functional domain
    ou bien avec des v \in [f @^-1: {set}] pour les conditions sur label
  -> {v : graph_of | (vlabel v == tens_l) || (vlabel v == parr_l)}
  - faire des fonctions depuis les ensembles totaux vers option _ puis lemma pour label ok <-> Some _
    ex:
      order : graph_of -> option nat;
      order_ok : forall v, exists n, order v = Some n <-> vlabel v = concl_l /\ order v <= nb nodes concl;
          en fait si injectif, pas necessaire d'avoir la dernière condition, qui semble etre la plus difficile comme #|_| est dur à calculer
      direction : bool -> graph_of -> option_finType (edge graph_of);
      direction_ok : forall b v, direction b v = Some _ <-> (vlabel c = tens_l \/ vlabel c = parr_l);
  - see sig_finType, used for the function sub_edge in the graph lib
  - other way to define bijections for order: surj instead of inj, from I_n -> vertices, ...
  - something else ?
  - define order as a permutation of the finset as finset = seq = list, easier to manipulate
  - dans direction, restreindre edge to edge_in_at_set v ?
  - mettre direction et ordre plutot dans proof_structure ? (ie cette couche est inutile ?)
*)

(* ANCIEN tests on the permutation order
(* How to get the number of a node concl thanks to order ?
  1) enum_rank is a bijection between a finset and I_n
  2) enum_rank on a conclusion node gives a number between 0 and n-1
  3) the number of the concl node v is enum_rank (order v) *)
Definition order_ax_perm (x : atom) := perm_one ([finType of {v : (graph_ax x) | vlabel v == concl_l}]).
Variable z:atom.
Lemma testz : vlabel (ord1:(graph_ax z)) == concl_l.
Proof. by []. Qed.
Definition injtest {G : graph rule formula} :=
  fun (v : G) (l : vlabel v == concl_l) => Sub v l : {v : G | vlabel v == concl_l}.
Definition inj1 : [finType of {v : graph_ax z | vlabel v == concl_l}] :=
  injtest (G:=graph_ax z) (v:=(ord1:(graph_ax z))) testz.
Check order_ax_perm z inj1.
Check enum_val. Check enum_rank.
Check enum_rank (order_ax_perm z inj1). (* must be equal to ord0 *)
Lemma testz2 : vlabel (ord2:(graph_ax z)) == concl_l.
Proof. by []. Qed.
Definition inj2 : {v : graph_ax z | vlabel v == concl_l} :=
  injtest (G:=graph_ax z) (v:=(ord2:(graph_ax z))) testz2.
Check enum_rank (order_ax_perm z inj2). (* must be equal to ord1 *)
Check ordinal_subType. (* pas forcement egal à ord0/ord1,
comme on a un sub de I_n et pas I_n -> faire en sorte d'aller vers I_n ?
faire la transition dans l'autre sens ? n'a pas l'air plus simple *)
*)

(* fonction qui dit si formule atomique existe dans yalla, possible de l'ajouter pour expansion atome *)
(* /!\ faire lemma (admitted dependant des defs), pour utiliser independamment de la def choisie *)

(** * Functions to inject a vertex into one of the particular subsets *)
Lemma tens_to_tensparr_b : forall (l : rule), (l == tens_l) -> (l == tens_l) || (l == parr_l).
Proof. intros. apply (introT orP). by left. Qed.

Lemma tens_to_tensparr : forall (l : rule), (l = tens_l) -> (l = tens_l) \/ (l = parr_l).
Proof. intros. by left. Qed.

Lemma parr_to_tensparr_b : forall (l : rule), (l == parr_l) -> (l == tens_l) || (l == parr_l).
Proof. intros. apply (introT orP). by right. Qed.

Lemma parr_to_tensparr : forall (l : rule), (l = parr_l) -> (l = tens_l) \/ (l = parr_l).
Proof. intros. by right. Qed.

Definition inj_conc {G : graph_data} :=
  fun (v : G) (l : vlabel v == concl_l) => Sub v l : {v : G | vlabel v == concl_l}.

Definition inj_tens {G : graph_data} :=
  fun (v : G) (l : vlabel v == tens_l) =>
  Sub v (tens_to_tensparr_b l) : {v : G | (vlabel v == tens_l) || (vlabel v == parr_l)}.

Definition inj_parr {G : graph_data} :=
  fun (v : G) (l : vlabel v == parr_l) =>
  Sub v (parr_to_tensparr_b l) : {v : G | (vlabel v == tens_l) || (vlabel v == parr_l)}.


(** * Base case: graph of an axiom **)
Definition graph_ax (x : atom) : graph rule formula := {|
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

Definition order_ax (x : atom) : list (vertex (graph_ax x)) := ord1 :: ord2 :: nil.

Definition left_ax (x : atom) : vertex (graph_ax x) -> edge (graph_ax x) :=
  fun _ => ord0. (* no vertex with label tens_l nor parr_l: we put a nonsensical value *)
Arguments left_ax : clear implicits.

Definition graph_data_ax (x : atom) : graph_data := {|
  graph_of := graph_ax x;
  order := order_ax x;
  left := left_ax x;
  |}.

Lemma ax_nb_concl (x : atom) : #|[set v : graph_data_ax x | vlabel v == concl_l]| = 2.
Proof. compute_card_subIn. Qed.
(* put this where proper_order is *)


(** * Operations on graph_data *)
(* c'est bien long à compiler ... mais ça ne l'est pas sans les let des noms de sommets !? *)
(* isoler le probleme, montrer exponentiel en temps selon le nombre de inl, puis faire un bug report *)
(* Add a parr node and a concl node, replacing 2 nodes *)
Definition add_parr {G : graph_data} (e0 e1 : edge G) :=
  (* add new vertices parr and concl *)
  let G1 := (G ∔ parr_l) ∔ concl_l in
  (* duplicate edges e0 and e1 to parr, from s0 and s1, and add an edge from parr to concl *)
  let G2 := G1 ∔ [ inl (inl (source e0)) , elabel e0 , inl (inr tt) ]
    ∔ [ inl (inl (source e1)) , elabel e1 , inl (inr tt) ]
    ∔ [ inl (inr tt) , parr (elabel e0) (elabel e1) , inr tt ] in
  (* remove t0 and t1 *)
  let S : {set G2} := setT :\ inl (inl (target e0)) :\ inl (inl (target e1)) in
  induced S.

(*
Definition add_parr0 {G : graph_data} (e0 e1 : edge G) :=
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

(* Add a tens node and a concl node, replacing 2 nodes in 2 graphs *)
Definition add_tens {G0 : graph_data} {G1 : graph_data} (e0 : edge G0) (e1 : edge G1) :=
  (* add new vertices tens and concl *)
  let G2 := ((G0 ⊎ G1) ∔ tens_l) ∔ concl_l in
  let s0 := inl (inl (inl (source e0))) in
  let t0 := inl (inl (inl (target e0))) in
  let s1 := inl (inl (inr (source e1))) in
  let t1 := inl (inl (inr (target e1))) in
  let v_tens := inl (inr tt) in
  let v_concl := inr tt in
  (* duplicate edges e0 and e1 to parr, from s0 and s1, and add an edge from tens to concl *)
  let G3 := G2 ∔ [ s0 , elabel e0 , v_tens ]
    ∔ [ s1 , elabel e1 , v_tens ]
    ∔ [ v_tens , tens (elabel e0) (elabel e1) , v_concl ] in
  (* remove t0 and t1 *)
  let S : {set G3} := [set x | (x != t0) && (x != t1)] in
  induced S.

(* Add a cut node, replacing 2 nodes in 2 graphs *)
Definition add_cut {G0 : graph_data} {G1 : graph_data} (e0 : edge G0) (e1 : edge G1) :=
  (* add new vertices tens and concl *)
  let G2 := (G0 ⊎ G1) ∔ cut_l in
  let s0 := inl (inl (source e0)) in
  let t0 := inl (inl (target e0)) in
  let s1 := inl (inr (source e1)) in
  let t1 := inl (inr (target e1)) in
  let v_cut := inr tt in
  (* duplicate edges e0 and e1 to cut, from s0 and s1 *)
  let G3 := G2 ∔ [ s0 , elabel e0 , v_cut ]
    ∔ [ s1 , elabel e1 , v_cut ] in
  (* remove t0 and t1 *)
  let S : {set G3} := [set x | (x != t0) && (x != t1)] in
  induced S.
*)
(* add_tens et cut sur un seul graphe pour être plus général ? *)
(*
Definition add_tens2 {G : graph_data} (e0 e1 : edge G) :=
  (* add new vertices tens and concl *)
  let G1 := (G ∔ tens_l) ∔ concl_l in
  let s0 := inl (inl (source e0)) in
  let t0 := inl (inl (target e0)) in
  let s1 := inl (inl (source e1)) in
  let t1 := inl (inl (target e1)) in
  let v_tens := inl (inr tt) in
  let v_concl := inr tt in
  (* duplicate edges e0 and e1 to parr, from s0 and s1, and add an edge from tens to concl *)
  let G2 := G1 ∔ [ s0 , elabel e0 , v_tens ]
    ∔ [ s1 , elabel e1 , v_tens ]
    ∔ [ v_tens , tens (elabel e0) (elabel e1) , v_concl ] in
  (* remove t0 and t1 *)
  let S : {set G2} := [set x | (x != t0) && (x != t1)] in
  induced S.

Definition add_cut2 {G : graph_data} (e0 e1 : edge G) :=
  (* add new vertices tens and concl *)
  let G1 := G ∔ cut_l in
  let s0 := inl (source e0) in
  let t0 := inl (target e0) in
  let s1 := inl (source e1) in
  let t1 := inl (target e1) in
  let v_cut := inr tt in
  (* duplicate edges e0 and e1 to cut, from s0 and s1 *)
  let G2 := G1 ∔ [ s0 , elabel e0 , v_cut ]
    ∔ [ s1 , elabel e1 , v_cut ] in
  (* remove t0 and t1 *)
  let S : {set G2} := [set x | (x != t0) && (x != t1)] in
  induced S.
*)

(* TODO update order & left lors des operations *)

(* ANCIEN essai de definir direction par construction
(* si direction : bool -> vertex graph_of -> edge graph_of; sinon il faut prouver vlabel u == ... *)
(* pb: see sub_edges for induced graph *)
Record quasi : Type :=
  Quasi {
    gr :> graph rule formula;
    dir : bool -> vertex gr -> edge gr;
  }.
Definition quasi_add_parr {G : quasi} (e0 e1 : edge G) :=
  (* add new vertices parr and concl *)
  let G1 := (G ∔ parr_l) ∔ concl_l in
  (* duplicate edges e0 and e1 to parr, from s0 and s1, and add an edge from parr to concl *)
  let G2 := G1 ∔ [ inl (inl (source e0)) , elabel e0 , inl (inr tt) ]
    ∔ [ inl (inl (source e1)) , elabel e1 , inl (inr tt) ]
    ∔ [ inl (inr tt) , parr (elabel e0) (elabel e1) , inr tt ] in
  (* remove t0 and t1 *)
  let S : {set G2} := [set x | (x != inl (inl (target e0))) && (x != inl (inl (target e1)))] in
  induced S.
(* need a consistent like in mgraph, but for e \in E instead of v\in V *)
Definition consistentbis {G : graph rule formula} (V : {set G}) (E : {set edge G}) :=
  forall e b, endpoint b e \in V -> e \in E.
Lemma consistentbis_induced {G : graph rule formula} (S : {set G}): consistentbis S (edge_set S).
Admitted.
Lemma quasi_add_parr_consistent {G : quasi} (e0 e1 : edge G) :
  let g := quasi_add_parr e0 e1 in consistentbis [set : g] (edge_set [set : g]).
Admitted.
(*
Variable G:quasi.
Variable e0 e1:edge G.
Definition g:=quasi_add_parr e0 e1.
Variable e : edge g.
Check valP e.
Variable v : g.
Check quasi_add_parr_consistent (e0:=e0) (e1:=e1).
Variable u:G. Variable b:bool.
Check dir b u.
Check (vertex
                 (G ∔ parr_l ∔ concl_l ∔ [inl (inl (source e0)), 
                  elabel e0, inl (inr tt)] ∔ [inl (inl (source e1)), 
                  elabel e1, inl (inr tt)] ∔ [inl (inr tt), elabel e0 ⅋ elabel e1,
                  inr tt])).
Check (vertex (quasi_add_parr e0 e1)).
Check (valP v).
Check val v.
*)
(*
Definition graph_data_parr {G : quasi} (e0 e1 : edge G) : edge G -> edge G -> quasi :=
  let g := quasi_add_parr e0 e1 in
  let dir := fun b => fun (v : vertex g) => match val v with
    | inl (inl u) => Sub (dir b u) (quasi_add_parr_consistent (e0:=e0) (e1:=e1) (valP v) b)
    | inl (inr tt) => if b then Sub e1 (quasi_add_parr_consistent (e0:=e0) (e1:=e1) (valP v) b) else Sub e0 (quasi_add_parr_consistent e0 e1)
    | inr tt => (if b then e1 else e0) (*false, not a parr/tens node*)
    end in 
  {| gr := g;
  dir := dir |}.
*)
*)







(** ** Level 2: Geometric Structure *)
(** * Conditions on the neighborhood of a node according to its rule *)

(** Out-degree of a node according to its rule *)
Definition out_deg (r : rule) := match r with
  | ax_l => 2
  | tens_l => 1
  | parr_l => 1
  | cut_l => 0
  | concl_l => 0
  end.

(** In-degree of a node according to its rule *)
Definition in_deg (r : rule) := match r with
  | ax_l => 0
  | tens_l => 2
  | parr_l => 2
  | cut_l => 2
  | concl_l => 1
  end.

(* see if proper in bool needed later on *)
(* see if edeges_in_at_subset or edges_in_at_set better *)
(** Property of a geometric structure *)
Definition proper_degree (G : graph_data) :=
  forall (v : G), #|edges_out_at_subset v| = out_deg (vlabel v)
               /\ #|edges_in_at_subset v| = in_deg (vlabel v).

Definition proper_left (G : graph_data) :=
  forall (v : G), vlabel v = tens_l \/ vlabel v = parr_l -> left v \in edges_in_at_subset v.

Definition proper_order (G : graph_data) :=
  (forall (v : G), (vlabel v = concl_l) <-> v \in order G)
  /\ NoDup (order G).
(* pas sur que ce soit la meilleure facon de dire que order G est bien *)
(* mettre proper_order ici, le mettre dans proof_structure, ou même dans sa propre couche ? *)
(* arguments:
  - le mettre ici comme pour left, comme contraintes exprimables directement depuis graphe_data
      + sequent est definit pour une geos directement
  - le mettre dans une dernière couche, comme on ne s'en sert qu'en high level *)

Set Primitive Projections.
Record geos : Type :=
  Geos {
    graph_data_of :> graph_data;
    p_deg : proper_degree graph_data_of;
    p_left : proper_left graph_data_of;
  }.
Unset Primitive Projections.


(** * Derivated results on a geometric structure *)
(* Nonsensical values for total functions on vertices but where only tens and parr matters *)
Definition bogus {G : geos} (v : G) : edge G := left v.

(** Function taking the 2nd element of a 2-elements set *)
Definition unique_other :
  forall (T : finType) (S : {set T}) (x : T),
  #|S| = 2 -> x \in S -> #|S :\ x| = 1.
Proof. intros. rewrite cardsR1_subset. lia. Qed.

Definition other {T : finType} {S : {set T}} {x : T} (CS : #|S| = 2) (Hin : x \in S) :=
  pick_unique_subset (unique_other CS Hin).

Lemma p_other {T : finType} {S : {set T}} {x : T} (CS : #|S| = 2) (Hin : x \in S) :
  other CS Hin \in S /\ other CS Hin != x.
Proof.
  unfold other.
  by destruct (setD1P (pick_unique_subset_in (unique_other CS Hin))).
Qed.
(* see if it is simpler using this *)
(* -> voir pour right et proper_ax/cut *)


(** Function right for the right premisse of a tens / parr node *)
Lemma unique_right (G : geos) :
  forall (v : G), (vlabel v = tens_l) \/ (vlabel v = parr_l) ->
  (#|edges_in_at_subset v :\ left v| = 1).
Proof.
  intro v.
  destruct (p_deg v) as [_ Hin].
  intros [Hl | Hl];
  rewrite cardsR1_subset Hin Hl;
  [set Htp := tens_to_tensparr Hl | set Htp := parr_to_tensparr Hl];
  by rewrite (p_left Htp).
Qed.

(* Help to define right: TO REMOVE if function defined from it is ok
Definition pre_right {G : geos} (v : G) : (vlabel v = tens_l) \/ (vlabel v = parr_l) -> edge G :=
  fun H => pick_unique_subset (unique_right H).
Lemma right2 {G : geos} (v : G) : edge G.
Proof.
  destruct_rule (vlabel v) H.
  - apply (bogus v).
  - apply (pre_right (tens_to_tensparr H)).
  - apply (pre_right (parr_to_tensparr H)).
  - apply (bogus v).
  - apply (bogus v).
Qed.
Print right2. (* looks like what we wanted *)
*)

Definition right : forall G : geos, G -> edge G := 
  fun (G : geos) (v : G) =>
  let s := case_rule (vlabel v) in
  match s with
  | inleft (inleft (inleft (Specif.right H))) =>
    pick_unique_subset (unique_right (tens_to_tensparr H))
  | inleft (inleft (inright H)) =>
    pick_unique_subset (unique_right (parr_to_tensparr H))
  | _ => bogus v
  end. (* si on defini right avec lemma, il devient opaque *)
(*autre solution: faire une fonction paquet d'aretes qui retourne un subset nonvide d'arete,
 = dans le cas de tens et parr à edge_in\left *)

Lemma p_right (G : geos) :
  forall (v : G), (vlabel v = tens_l) \/ (vlabel v = parr_l) ->
  right v \in edges_in_at_subset v /\ right v != left v.
Proof.
  intros v Hv.
  unfold right.
  destruct_rule (vlabel v) H;
  (* case where (vlabel v = tens_l) \/ (vlabel v = parr_l) is false *)
  try (contradict H;
       destruct Hv as [Hv | Hv];
       by rewrite Hv);
  (* case where (vlabel v = tens_l) \/ (vlabel v = parr_l) is true *)
  [set H' := tens_to_tensparr H | set H' := parr_to_tensparr H];
  by destruct (setD1P (pick_unique_subset_in (unique_right H'))).
Qed.

(* DEBUT right defined with other *)
Lemma pre_right_o (G : geos) (v : G) :
  vlabel v = tens_l \/ vlabel v = parr_l -> #|edges_in_at_subset v| = 2.
Proof.
  destruct (p_deg v) as [_ Hin].
  intros [Hl | Hl];
  by rewrite Hin Hl.
Qed.

Definition right_o (G : geos) (v : G) :=
  let s := case_rule (vlabel v) in
  match s with
  | inleft (inleft (inleft (Specif.right H))) =>
    let H' := tens_to_tensparr H in
    other (pre_right_o H') (p_left H')
  | inleft (inleft (inright H)) =>
    let H' := parr_to_tensparr H in
    other (pre_right_o H') (p_left H')
  | _ => bogus v
  end.

Lemma p_right_o (G : geos) :
  forall (v : G), (vlabel v = tens_l) \/ (vlabel v = parr_l) ->
  right_o v \in edges_in_at_subset v /\ right_o v != left v.
Proof.
  intros v Hv.
  unfold right_o.
  destruct_rule (vlabel v) H;
  (* case where (vlabel v = tens_l) \/ (vlabel v = parr_l) is false *)
  try (contradict H;
       destruct Hv as [Hv | Hv];
       by rewrite Hv);
  (* case where (vlabel v = tens_l) \/ (vlabel v = parr_l) is true *)
  [set H' := tens_to_tensparr H | set H' := parr_to_tensparr H];
  apply p_other.
Qed.
(* FIN right defined with other *)



Lemma p_direction (G : geos) :
  forall (v : G), (vlabel v = tens_l) \/ (vlabel v = parr_l) ->
  edges_in_at_subset v = [set left v; right v].
Proof.
  intros v Hv.
  assert (Hsub : [set left v; right v] \subset edges_in_at_subset v).
    rewrite <-(setUid (edges_in_at_subset v)).
    apply setUSS;
    rewrite sub1set;
    [apply (p_left Hv) | apply (p_right Hv)].
  assert (Heq : #|[set left v; right v]| = #|edges_in_at_subset v|).
    rewrite cards2.
    assert (left v != right v) by (rewrite eq_sym ; by destruct (p_right Hv)).
    destruct (p_deg v) as [_ Hin].
    rewrite Hin.
    destruct Hv as [Hv | Hv];
    rewrite Hv; cbn; lia.
  symmetry.
  apply setP, (subset_cardP Heq Hsub).
Qed.
(* ou bien juste avec p_left et p_right, pas besoin de ce lemma ? *)


(** Function ccl for the conclusion of a tens / parr node *)
Lemma unique_ccl (G : geos) :
  forall (v : G), (vlabel v = tens_l) \/ (vlabel v = parr_l) ->
  (#|edges_out_at_subset v| = 1).
Proof.
  intro v.
  destruct (p_deg v) as [Hout _].
  rewrite Hout.
  intros [Hl | Hl];
  by rewrite Hl.
Qed.

(* Help to define ccl: TO REMOVE if function defined from it is ok
Definition pre_ccl {G : geos} (v : G) : (vlabel v = tens_l) \/ (vlabel v = parr_l) -> edge G :=
  fun H => pick_unique_subset (unique_ccl H).
Lemma ccl2 {G : geos} (v : G) : edge G.
Proof.
  destruct_rule (vlabel v) H.
  - apply (bogus v).
  - apply (pre_ccl (tens_to_tensparr H)).
  - apply (pre_ccl (parr_to_tensparr H)).
  - apply (bogus v).
  - apply (bogus v).
Qed.
Print ccl2.
*)

Definition ccl : forall G : geos, G -> edge G := 
  fun (G : geos) (v : G) =>
  let s := case_rule (vlabel v) in
  match s with
  | inleft (inleft (inleft (Specif.right H))) =>
    pick_unique_subset (unique_ccl (tens_to_tensparr H))
  | inleft (inleft (inright H)) =>
    pick_unique_subset (unique_ccl (parr_to_tensparr H))
  | _ => bogus v
  end.

Lemma p_ccl (G : geos) :
  forall (v : G), (vlabel v = tens_l) \/ (vlabel v = parr_l) ->
  ccl v \in edges_out_at_subset v.
Proof.
  intros v Hv.
  unfold ccl.
  destruct_rule (vlabel v) H;
  (* case where (vlabel v = tens_l) \/ (vlabel v = parr_l) is false *)
  try (contradict H;
       destruct Hv as [Hv | Hv];
       by rewrite Hv);
  (* case where (vlabel v = tens_l) \/ (vlabel v = parr_l) is true *)
  [set H' := tens_to_tensparr H | set H' := parr_to_tensparr H];
  by exact (pick_unique_subset_in (unique_ccl H')).
Qed.


(** Function returning the unique (input) edge of a conclusion vertex *)
Lemma unique_concl (G : geos) :
  forall (v : G), (vlabel v = concl_l) ->
  (#|edges_in_at_subset v| = 1).
Proof.
  intro v.
  destruct (p_deg v) as [_ Hin].
  rewrite Hin.
  intros Hl;
  by rewrite Hl.
Qed.

(* Help to define concl: TO REMOVE if function defined from it is ok
Definition pre_concl {G : geos} (v : G) : (vlabel v = concl_l) -> edge G :=
  fun H => pick_unique_subset (unique_concl H).
Lemma concl2 {G : geos} (v : G) : edge G.
Proof.
  destruct_rule (vlabel v) H.
  - apply (bogus v).
  - apply (bogus v).
  - apply (bogus v).
  - apply (bogus v).
  - apply (pre_concl H).
Qed.
Print concl2.
*)

Definition edge_of_concl : forall G : geos, G -> edge G := 
  fun (G : geos) (v : G) =>
  let s := case_rule (vlabel v) in
  match s with
  | inright H => pick_unique_subset (unique_concl H)
  | _ => bogus v
  end.

Lemma p_concl (G : geos) :
  forall (v : G), (vlabel v = concl_l) ->
  edge_of_concl v \in edges_in_at_subset v.
Proof.
  intros v Hv.
  unfold edge_of_concl.
  destruct_rule (vlabel v) H;
  (* case where (vlabel v = concl_l) is false *)
  try (contradict H;
       by rewrite Hv).
  (* case where (vlabel v = tens_l) \/ (vlabel v = parr_l) is true *)
  by exact (pick_unique_subset_in (unique_concl H)).
Qed.

(* Sequent proved by the proof structure *)
Definition sequent (G : geos) : list formula :=
  [seq elabel (edge_of_concl i) | i <- order G].
(* return the right sequent iff proper_order *)


(** * The graph of an axiom is a geometric structure *)
Lemma p_deg_ax (x : atom) : proper_degree (graph_data_ax x).
Proof.
  unfold proper_degree.
  intro v.
  destruct_I3 v H;
  rewrite H;
  split; compute_card_subIn.
Qed.
Arguments p_deg_ax : clear implicits.

Lemma p_left_ax (x : atom) : proper_left (graph_data_ax x).
Proof.
  unfold proper_left.
  intro v.
  destruct_I3 v H;
  rewrite H;
  intros [Hl | Hl];
  by contradict Hl.
Qed.
Arguments p_left_ax : clear implicits.

Definition geos_ax (x : atom) : geos := {|
  graph_data_of := graph_data_ax x;
  p_deg := p_deg_ax x;
  p_left := p_left_ax x;
  |}.

Lemma p_order_ax (x : atom) : proper_order (graph_data_ax x).
Proof.
  unfold proper_order.
  split.
  - intro v.
    destruct_I3 v H;
    rewrite H;
    split;
    intro Hl;
    done.
  - cbn. unfold order_ax.
    repeat (apply NoDup_cons_iff; split).
    + assert (H : @ord1 1 <> @ord2 0) by by [].
      contradict H.
      by destruct (in_inv H).
    + by [].
    + apply NoDup_nil.
Qed.

(** * Operations on graphs preserve geos *)
(* TODO *)



(** ** Level 3: Proof Structure *)
(** * The rule of a node gives conditions on the formulae of its arrows **)
Definition proper_ax (G : geos) :=
  forall (v : G), vlabel v = ax_l -> exists el, exists er,
  (el \in edges_out_at_subset v) && (er \in edges_out_at_subset v) &&
  (elabel el == dual (elabel er)).
(* ax + cut : je peux remplacer exists par forall, mais pas vraiment retirer le exists... *)
Lemma pre_proper_ax2 (G : geos) (v : G) (L : vlabel v = ax_l) : #|edges_out_at_subset v| = 2.
Proof. destruct (p_deg v) as [H _]. by rewrite H L. Qed.
Definition proper_ax2 (G : geos) :=
  forall (v : G) (L : vlabel v = ax_l) (e : edge G) (E : e \in edges_out_at_subset v),
  (elabel e = dual (elabel (other (pre_proper_ax2 L) E))).
(* voir si plus facile a utiliser, idem avec cut *)


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
Lemma pre_proper_cut2 (G : geos) (v : G) (L : vlabel v = cut_l) : #|edges_in_at_subset v| = 2.
Proof. destruct (p_deg v) as [_ H]. by rewrite H L. Qed.
Definition proper_cut2 (G : geos) :=
  forall (v : G) (L : vlabel v = cut_l) (e : edge G) (E : e \in edges_in_at_subset v),
  (elabel e = dual (elabel (other (pre_proper_cut2 L) E))).

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

(* Following: NOT useful, unless we put proper as bool
(* Lemmas to use proper_degree directly *)
Lemma p_deg_at {G : proof_structure} (v : G) :
  (#|edges_out_at_subset v| == out_deg (vlabel v)) && (#|edges_in_at_subset v| == in_deg (vlabel v)).
Proof. (*revert v. rewrite/forallP. p_deg. apply p_deg.

exact (forallP (p_deg G)). Qed.*) Admitted.
(* mieux sans redupliquer les lemmes avec la syntaxe ssreflect *)

Lemma p_deg_at_out {G : proof_structure} (v : G) : #|edges_out_at_subset v| == out_deg (vlabel v).
Proof. by destruct (andP (p_deg_at v)). Qed.

Goal forall b c, b && c -> c && b.
move => b c /andP[B C]. apply/andP. now split. Qed.
(* lire tactics bouquin ssreflect *)
(* voir utilisation de proper pour savoir si bool est necessaire *)

Lemma p_deg_at_in {G : proof_structure} (v : G) : #|edges_in_at_subset v| == in_deg (vlabel v).
Proof. by destruct (andP (p_deg_at v)). Qed.


(* Same results with set instead of subset *)
Lemma p_deg_at_out_set {G : proof_structure} (v : G) :
  #|[finType of edges_out_at_set v]| = out_deg (vlabel v).
Proof. rewrite card_set_subset. exact (eqP (p_deg_at_out v)). Qed.

Lemma p_deg_at_in_set {G : proof_structure} (v : G) :
  #|[finType of edges_in_at_set v]| = in_deg (vlabel v).
Proof. rewrite card_set_subset. exact (eqP (p_deg_at_in v)). Qed.

Lemma p_deg_at_in_set_concl {G : proof_structure} (v : [finType of {v : G | vlabel v == concl_l}]) :
  #|[finType of (edges_in_at_set (val v))]| = 1.
Proof. by rewrite p_deg_at_in_set ((eqP (valP v))). Qed.
*)




(* TODO the axiom graph is a proof_structure *)
Lemma p_ax_ax (x : atom) : proper_ax (geos_ax x).
Proof.
  unfold proper_ax.
Admitted.
Arguments p_ax_ax : clear implicits. (* remove if unneeded once proved *)
Lemma p_ax_ax2 (x : atom) : proper_ax2 (geos_ax x).
Proof.
  unfold proper_ax2, other.
  intros v Hl e E.
  destruct_I3 v Hv;
  destruct_I2 e He;
  revert Hl E;
  rewrite Hv He; cbn;
  intros Hl E;
  try by [].
  - admit.
  - admit.
Admitted.

Lemma p_tens_ax (x : atom) : proper_tens (geos_ax x).
Proof.
Admitted.
Arguments p_tens_ax : clear implicits. (* remove if unneeded once proved *)

Lemma p_parr_ax (x : atom) : proper_parr (geos_ax x).
Proof.
Admitted.
Arguments p_parr_ax : clear implicits. (* remove if unneeded once proved *)

Lemma p_cut_ax (x : atom) : proper_cut (geos_ax x).
Proof.
Admitted.
Arguments p_cut_ax : clear implicits. (* remove if unneeded once proved *)

Definition ps_ax (x : atom) : proof_structure := {|
  geos_of := geos_ax x;
    p_ax := p_ax_ax x;
    p_tens := p_tens_ax x;
    p_parr := p_parr_ax x;
    p_cut := p_cut_ax x;
  |}.



(** ** Proof Structure of a Proof Sequent *)
(* Function at each level *)
(* pas au level 0: on doit savoir qui est le premier sommet conclusion pour le retirer (tens et parr)
-> faire la construction au level 1, puis lemma pour proper de la construction par induction
  ce qui donne level 2 *)

(*
Fixpoint graph_proof {l : list formula} (pi : ll l) : graph_data := match pi with
| ax_r x => graph_data_ax x
| ex_r _ _ pi0 sigma => graph_proof pi0
| tens_r _ _ _ _ pi0 pi1 => let gd0 := graph_proof pi0 in let gd1 := graph_proof pi1 in
    let gd := gd0 ⊎ gd1 in gd0
(* take 1st concl with order-1(0) -> use finv *)
| parr_r _ _ _ pi0 => 
| cut_r _ _ _ _ _ pi0 pi1 => 
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
  turn the perm on list of formulas into one on list of integers, should be easy?
About Permutation_Type. -> make the list of [c_i], apply perm on it, then re-label nodes c

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

| cut_r A l1 l2 l3 l4 pi0 pi1 => take 0=ps (pi0) and G1=ps (pi1), ni=#li for all i
    In G0: turn c_i into c_n3+n2+i for i<n1, for c_n1 turn into c_inf1, c_n3+(i-n1) otherwise
    In G1: for c_n3 turn into c_inf2,  c_n3+n2+n1+(i-n3) for i>n3
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
phi: P -> B, G_phi = G where on node v\in P, arrow ?->v(A,phi(v)) is deleted, add node c_v, edge ?->c_v(A)
    then remove direction
*)

(* Criteria: acyclic and connected *)
(* need def for acyclic + connected, or just for tree (tree in the lib) ?-> considering trees may change the proofs *)

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
| ax->cut: merge the 2 nodes, then merge the final node with the node above, keep label of above
| tens->cut<-parr: merge the 3 nodes into the cut one, then split it with the good edges, give label cut to both
=> need procedure merge, where a parent node absorb another, keeping its own label (may be used before instead of removing edge then adding edge ???)
*)
(* lemma: if R is correct and R reduces to R', then R' is correct *)
(* lemma: applying red while we can yields a cut-free ps:
    there is a cut node => one of the two subgraphs (*2 by symmetry) => reduction to another graph *)
(* lemma: sub-confluence + convergence *)

(** ** Sequentialization *)
(* many things to do: spliting tens / cut, blocking parr, always a terminal parr or a splitting *)
(* function to turn a ps into a sequential proof *)



(*******************************************************************************************************************)
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
