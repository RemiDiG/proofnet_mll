(* Unit-free MLL following Yalla schemas *)
(* Definition of proof nets and basic results *)
aa
From Coq Require Import Bool.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.
From HB Require Import structures.

From Yalla Require Export mll_prelim graph_more mgraph_dag.

Import EqNotations.

Set Mangle Names.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



(** * Type [rule] for the type of a node of a proof net *)
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

Lemma eqb_eq_rule : forall A B, eqb_rule A B <-> A = B.
Proof. by intros [] []. Qed.

Definition rules_dectype := {|
  car := rule;
  dectype.eqb := eqb_rule;
  eqb_eq := eqb_eq_rule |}.

(* [rule] as an eqType *)
Canonical rule_eqType := EqType rule (decType_eqMixin (rules_dectype)).

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
  ComMonoid_of_Setoid.Build (flat rule) rule_cm_laws.



(** * Notations from the library *)
Open Scope graph_scope.
(* G0 ⊎ G1 = disjoint union
   G ∔ v = add a vertex labelled v
   G ∔ [ x , u , y ] = add an arrow from x to y labelled u *)



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

Lemma eqb_eq_form : forall A B, eqb_form A B <-> A = B.
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

(* [formula] as an eqType *)
Canonical formula_eqType := EqType formula (decType_eqMixin (formulas_dectype)).

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


(** Equality with dual is a symmetric property *)
Definition is_dual := fun A B => dual A == B.

Lemma dual_sym : symmetric is_dual.
Proof.
  unfold symmetric, is_dual => A B.
  apply /eqP; case_if; rewrite codual //.
  by apply nesym.
Qed.

Definition is_dual_f {T : Type} (f : T -> formula) :=
  fun (a b : T) => is_dual (f a) (f b).

Lemma dual_sym_f {T : Type} (f : T -> formula) : symmetric (is_dual_f f).
Proof. unfold symmetric, is_dual_f => *. apply dual_sym. Qed.


(** * Self properties on formula *)
Lemma no_selfdual : forall (A : formula), dual A <> A.
Proof. by move => []. Qed.

Lemma no_selftens_l : forall A B, tens A B <> A.
Proof. intro A; induction A as [ | | ? H A ? | ] => ? Hc; inversion Hc. by apply (H A). Qed.

Lemma no_selftens_r : forall A B, tens B A <> A.
Proof. intro A; induction A as [ | | A ? ? H | ] => ? Hc; inversion Hc. by apply (H A). Qed.

Lemma no_selfparr_l : forall A B, parr A B <> A.
Proof. intro A; induction A as [ | | | ? H A ? ] => ? Hc; inversion Hc. by apply (H A). Qed.

Lemma no_selfparr_r : forall A B, parr B A <> A.
Proof. intro A; induction A as [ | | | A ? ? H ] => ? Hc; inversion Hc. by apply (H A). Qed.

Ltac no_selfform := try (
                      apply no_selfdual || apply nesym, no_selfdual ||
                      apply no_selftens_l || apply nesym, no_selftens_l ||
                      apply no_selftens_r || apply nesym, no_selftens_r ||
                      apply no_selfparr_l || apply nesym, no_selfparr_l ||
                      apply no_selfparr_r || apply nesym, no_selfparr_r).



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

(** ** Axiom expansion *)
Definition ax_exp : forall A, ll (dual A :: A :: nil).
Proof.
  intro A. induction A as [ | | A ? B ? | A ? B ?]; cbn.
  - apply ax_r.
  - eapply ex_r ; [ | apply Permutation_Type_swap]. apply ax_r.
  - apply parr_r.
    eapply ex_r; first last.
    { eapply Permutation_Type_trans; [apply Permutation_Type_swap | ].
    apply Permutation_Type_skip, Permutation_Type_swap. }
    change [:: tens A B; dual B; dual A] with ([:: tens A B; dual B] ++ [:: dual A]).
    apply tens_r; by eapply ex_r ; [ | apply Permutation_Type_swap].
  - eapply ex_r ; [ | apply Permutation_Type_swap]. apply parr_r.
    eapply ex_r; first last.
    { eapply Permutation_Type_trans; [apply Permutation_Type_swap | ].
    apply Permutation_Type_skip, Permutation_Type_swap. }
    change [:: tens (dual B) (dual A); A; B] with ([:: tens (dual B) (dual A); A] ++ [:: B]).
    by apply tens_r.
Defined.




(** ** Stratum 1: Multigraphs from the library GraphTheory *)
(** * Graphs that we will consider: on nodes [rule], and on edges [formula] together
      with a [bool] to identify left/right edges (convention True for left) *)
Notation base_graph := (graph (flat rule) (flat (formula * bool))). (* [flat] is used for isomorphisms *)
(** Formula of an edge *)
Definition flabel {G : base_graph} : edge G -> formula := fun e => fst (elabel e).
(** Left property of an edge *)
Definition llabel {G : base_graph} : edge G -> bool := fun e => snd (elabel e).

(* In our case, isometries are standard isometries, i.e. they do not flip edges *)
Lemma iso_noflip (F G : base_graph) (h : F ≃ G) : h.d =1 xpred0.
Proof.
  hnf => e.
  destruct h as [? ? iso_d [? ? E]]; cbn; clear - E.
  specialize (E e).
  by destruct (iso_d e).
Qed.

(* Reformulate elabel_iso on our labels on edges *)
Lemma flabel_iso (F G : base_graph) (h : F ≃ G) e :
  flabel (h.e e) = flabel e.
Proof.
  assert (Hl := elabel_iso h e).
  by revert Hl; rewrite iso_noflip => /eqP; cbn => /andP[/eqP-? _].
Qed.
Lemma llabel_iso (F G : base_graph) (h : F ≃ G) e :
  llabel (h.e e) = llabel e.
Proof.
  assert (Hl := elabel_iso h e).
  by revert Hl; rewrite iso_noflip => /eqP; cbn => /andP[_ /eqP-?].
Qed.

(** Notion of cardinality counting only rule nodes, i.e. without counting conclusion nodes,
so that operations like adding a cut increase cardinality *)
Definition rcard (G : base_graph) := #|~: [set v : G | vlabel v == c]|.
Notation "r#| G |" := (rcard G) : nat_scope.

(** Having a cut or not, for a cut reduction procedure *)
Definition has_cut (G : base_graph) := #|[set v : G | vlabel v == cut]| != 0.

Lemma has_cutP (G : base_graph) : reflect (has_cut G) [exists v : G, vlabel v == cut].
Proof.
  apply iff_reflect; split; unfold has_cut; intro H.
  - rewrite eqn0Ngt negb_involutive card_gt0 in H. revert H => /set0Pn[e H].
    rewrite in_set in H.
    apply /existsP. by exists e.
  - revert H => /existsP[v Hm].
    rewrite eqn0Ngt negb_involutive card_gt0.
    apply /set0Pn. exists v. by rewrite in_set.
Qed.



(** ** Stratum 2: Multigraphs with some more data *)
(* [order] giving an ordering on the conclusion arrows *)
(* Not giving order in stratum 1 as it does not matter for correction graphs *)
Set Primitive Projections.
Record graph_data : Type :=
  Graph_data {
    graph_of :> base_graph;
    order : seq (edge graph_of);
  }.
Unset Primitive Projections.


(** Sequent of the graph *)
Definition sequent (G : graph_data) : seq formula :=
  [seq flabel e | e <- order G].



(** ** Stratum 3: Proof Structure *)
(** * Conditions on the neighborhood of a node and formulae of its arrows according to its rule *)
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
Definition deg_out := deg false.
Definition deg_in := deg true.

Definition proper_degree (G : base_graph) :=
  forall (b : bool) (v : G), #|edges_at_outin b v| = deg b (vlabel v).

(** Duality conditions on axiom and cut nodes *)
(* edges_at_outin instead of endpoint to have the same object for all properties *)
Definition proper_ax_cut (G : base_graph) :=
  forall (b : bool),
  let rule := if b then cut else ax in
  forall (v : G), vlabel v = rule ->
  exists el er,
  el \in edges_at_outin b v /\ er \in edges_at_outin b v /\
  flabel el = dual (flabel er).

(** Applying the operation on formulae for tensor and parr nodes *)
Definition proper_tens_parr (G : base_graph) :=
  forall (b : bool),
  let rule := if b then ⅋ else ⊗ in
  let form := if b then parr else tens in
  forall (v : G), vlabel v = rule ->
  exists el er ec,
  el \in edges_at_in v /\ llabel el /\
  er \in edges_at_in v /\ ~llabel er /\
  ec \in edges_at_out v /\ flabel ec = form (flabel el) (flabel er).

(** To have a canonical representation, preventing problems with isomorphisms *)
(* All arrows pointing to a axiom, a cut or a conclusion must be left arrows by convention *)
Definition proper_noleft (G : base_graph) :=
  forall (e : edge G),
  vlabel (target e) = ax \/ vlabel (target e) = cut \/ vlabel (target e) = c ->
  llabel e.

(** Order must be an ordering of the outer arrows *)
Definition proper_order (G : graph_data) :=
  (forall e, vlabel (target e) = c <-> e \in order G) /\ uniq (order G).

Set Primitive Projections.
Record proof_structure : Type :=
  Proof_structure {
    graph_data_of :> graph_data;
    p_deg : proper_degree graph_data_of;
    p_ax_cut : proper_ax_cut graph_data_of;
    p_tens_parr : proper_tens_parr graph_data_of;
    p_noleft : proper_noleft graph_data_of;
    p_order : proper_order graph_data_of;
  }.
Unset Primitive Projections.
Definition p_deg_out (G : proof_structure) := @p_deg G false.
Definition p_deg_in (G : proof_structure) := @p_deg G true.
Definition p_ax (G : proof_structure) := @p_ax_cut G false.
Definition p_cut (G : proof_structure) := @p_ax_cut G true.
Definition p_tens (G : proof_structure) := @p_tens_parr G false.
Definition p_parr (G : proof_structure) := @p_tens_parr G true.
(* TODO étage intermediaire en retirant p_order, le seul qui est sur graph_data et pas base_graph ? *)


(** * Derivated results on a proof structure *)
(** Function left for the left premisse of a tens / parr *)
Lemma unique_left (G : proof_structure) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  #|[set e in edges_at_in v | llabel e]| = 1.
Proof.
  move => v Hl.
  assert (Hc : #|edges_at_in v| = 2)
    by by rewrite p_deg; destruct Hl as [-> | ->].
  assert (exists b, vlabel v = if b then ⅋ else ⊗) as [b Hl']
    by by destruct Hl as [-> | ->]; [exists false | exists true].
  destruct (p_tens_parr Hl') as [el [er [_ [Et [El [Rt [Rl _]]]]]]].
  assert (Hset := other_set Hc Et).
  assert (er = other Hc Et).
  { apply other_eq; trivial.
    intro; by subst er. }
  subst er; rewrite Hset -(cards1 el).
  apply eq_card => f.
  rewrite !in_set andb_orb_distrib_l.
  assert ((f == other Hc Et) && llabel f = false) as ->
    by (by cbnb; case_if; apply /negP).
  rewrite orb_false_r.
  cbnb; case_if; subst; rewrite ?eq_refl //.
  by symmetry; apply /eqP.
Qed.

Definition left {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :=
  pick_unique (unique_left H).
Definition left_tens (G : proof_structure) (v : G) (H : vlabel v = ⊗) :=
  left (or_introl H).
Definition left_parr (G : proof_structure) (v : G) (H : vlabel v = ⅋) :=
  left (or_intror H).

Lemma left_el (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  target (left H) = v /\ llabel (left H).
Proof.
  intros v H.
  assert (Hl := pick_unique_in (unique_left H)).
  by revert Hl; rewrite !in_set => /andP[/eqP ? ?].
Qed.

Lemma left_e (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  target (left H) = v.
Proof. apply left_el. Qed.

Lemma left_l (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  llabel (left H).
Proof. apply left_el. Qed.

Lemma left_eset (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  left H \in edges_at_in v.
Proof.
  intros v H.
  assert (Hl := pick_unique_in (unique_left H)).
  by revert Hl; rewrite !in_set => /andP[/eqP -> _].
Qed. (* TODO ça serait bien de se passer de ce genre de lemme redondant *)

Lemma left_eq (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  forall (e : edge G), target e = v /\ llabel e -> e = left H.
Proof.
  intros v H e [T ?].
  apply pick_unique_eq.
  rewrite !in_set T.
  splitb.
Qed.

(** Function right for the right premisse of a tens / parr *)
Lemma unique_right (G : proof_structure) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ -> #|edges_at_in v| = 2.
Proof. move => v [H | H]; by rewrite p_deg H. Qed.

Definition right {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :=
  other (unique_right H) (left_eset H).
Definition right_tens (G : proof_structure) (v : G) (H : vlabel v = ⊗) :=
  right (or_introl H).
Definition right_parr (G : proof_structure) (v : G) (H : vlabel v = ⅋) :=
  right (or_intror H).

Lemma right_e (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  target (right H) = v.
Proof.
  intros v H.
  destruct (other_in_neq (unique_right H) (left_eset H)) as [Hr _].
  by revert Hr; rewrite in_set => /eqP-->.
Qed.

Lemma left_neq_right (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  left H <> right H.
Proof.
  intros v H.
  destruct (other_in_neq (unique_right H) (left_eset H)) as [_ Hr].
  revert Hr => /eqP Hr.
  by apply nesym.
Qed.

Lemma right_set (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  edges_at_in v = [set left H; right H].
Proof.
  intros v H.
  by rewrite (other_set (unique_right H) (left_eset H)).
Qed.

Lemma right_l (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  ~~llabel (right H).
Proof.
  move => v H; apply /negP => F.
  assert (R : right H \in [set e in edges_at_in v | llabel e])
    by (rewrite !in_set right_e; splitb).
  revert R; rewrite (pick_unique_set (unique_left H)) in_set => /eqP.
  apply nesym, left_neq_right.
Qed.

Lemma right_eq (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  forall (e : edge G), target e = v /\ ~llabel e -> e = right H.
Proof.
  move => v H e [T R].
  apply pick_unique_eq.
  rewrite !in_set T.
  splitb.
  apply /eqP => ?; subst e.
  contradict R.
  apply left_l.
Qed.

Lemma right_eq2 (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  forall (e : edge G), target e = v /\ e <> left H -> e = right H.
Proof.
  move => v H e [T /eqP ?].
  apply pick_unique_eq.
  rewrite !in_set T.
  splitb.
Qed. (* TODO changer ce nom *)
(* TODO check if all these properties are useful or not *)

(** Function ccl for the conclusion of a tens / parr *)
Lemma unique_ccl (G : proof_structure) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  #|edges_at_out v| = 1.
Proof. move => v [H | H]; by rewrite p_deg H. Qed.

Definition ccl {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :=
  pick_unique (unique_ccl H).
Definition ccl_tens (G : proof_structure) (v : G) (H : vlabel v = ⊗) :=
  ccl (or_introl H).
Definition ccl_parr (G : proof_structure) (v : G) (H : vlabel v = ⅋) :=
  ccl (or_intror H).

Lemma p_ccl (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  ccl H \in edges_at_out v.
Proof. intros. apply pick_unique_in. Qed.

Lemma ccl_e (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  source (ccl H) = v.
Proof.
  intros v Hv.
  assert (H := p_ccl Hv).
  rewrite in_set in H; by apply /eqP.
Qed.

Lemma ccl_set (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  edges_at_out v = [set ccl H].
Proof. intros. apply pick_unique_set. Qed.

Lemma ccl_eq (G : proof_structure) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  forall (e : edge G), source e = v -> e = ccl H.
Proof.
  intros v Hv e He.
  assert (H : e \in edges_at_out v) by by rewrite in_set He.
  by revert H; rewrite ccl_set // in_set => /eqP ->.
Qed.

(** Unique arrow of a conclusion *)
Lemma unique_concl (G : proof_structure) :
  forall (v : G), vlabel v = c ->
  #|edges_at_in v| = 1.
Proof. move => v H; by rewrite p_deg H. Qed.

Definition edge_of_concl {G : proof_structure} {v : G} (H : vlabel v = c) :=
  pick_unique (unique_concl H).

Lemma p_concl (G : proof_structure) :
  forall (v : G) (H : vlabel v = c),
  edge_of_concl H \in edges_at_in v.
Proof. intros. apply pick_unique_in. Qed.

Lemma concl_e (G : proof_structure) :
  forall (v : G) (H : vlabel v = c),
  target (edge_of_concl H) = v.
Proof.
  intros v Hv.
  assert (H := p_concl Hv).
  rewrite in_set in H; by apply /eqP.
Qed.

Lemma concl_set (G : proof_structure) :
  forall (v : G) (H : vlabel v = c),
  edges_at_in v = [set edge_of_concl H].
Proof. intros. apply pick_unique_set. Qed.

Lemma concl_eq (G : proof_structure) :
  forall (v : G) (H : vlabel v = c),
  forall (e : edge G), target e = v -> e = edge_of_concl H.
Proof.
  intros v Hv e He.
  assert (H : e \in edges_at_in v) by by rewrite in_set He.
  revert H. by rewrite concl_set // in_set => /eqP ->.
Qed.

(** Other edge of an axiom *)
Lemma pre_proper_ax (G : proof_structure) (v : G) (Hl : vlabel v = ax) :
  #|edges_at_out v| = 2.
Proof. by rewrite p_deg Hl. Qed.

Definition other_ax (G : proof_structure) (e : edge G) (H : vlabel (source e) = ax) : edge G :=
  other (pre_proper_ax H) (source_in_edges_at_out e).

Lemma other_ax_e (G : proof_structure) :
  forall (e : edge G) (H : vlabel (source e) = ax),
  source (other_ax H) = source e.
Proof.
  intros e H.
  destruct (other_in_neq (pre_proper_ax H) (source_in_edges_at_out e)) as [Hr _].
  by revert Hr; rewrite in_set => /eqP-->.
Qed.

Lemma other_ax_neq (G : proof_structure) :
  forall (e : edge G) (H : vlabel (source e) = ax),
  other_ax H <> e.
Proof.
  intros e H.
  destruct (other_in_neq (pre_proper_ax H) (source_in_edges_at_out e)) as [_ Hr].
  by revert Hr => /eqP-?.
Qed.

Lemma other_ax_set (G : proof_structure) (e : edge G) (H : vlabel (source e) = ax) :
  edges_at_out (source e) = [set e; other_ax H].
Proof. apply other_set. Qed.

Lemma other_ax_eq (G : proof_structure) (e : edge G) (H : vlabel (source e) = ax) :
  forall (a : edge G), source a = source e /\ a <> e -> a = other_ax H.
Proof.
  intros a [Ha Ha'].
  assert (Hin : a \in edges_at_out (source e)) by by rewrite in_set Ha.
  revert Hin.
  by rewrite other_ax_set !in_set => /orP [/eqP ? | /eqP ->].
Qed.

(** Other edge of a cut *)
Lemma pre_proper_cut (G : proof_structure) (v : G) (Hl : vlabel v = cut) :
  #|edges_at_in v| = 2.
Proof. by rewrite p_deg Hl. Qed.

Definition other_cut (G : proof_structure) (e : edge G) (H : vlabel (target e) = cut) : edge G :=
  other (pre_proper_cut H) (target_in_edges_at_in e).

Lemma other_cut_e (G : proof_structure) :
  forall (e : edge G) (H : vlabel (target e) = cut),
  target (other_cut H) = target e.
Proof.
  intros e H.
  destruct (other_in_neq (pre_proper_cut H) (target_in_edges_at_in e)) as [Hr _].
  by revert Hr; rewrite in_set => /eqP-->.
Qed.

Lemma other_cut_neq (G : proof_structure) :
  forall (e : edge G) (H : vlabel (target e) = cut),
  other_cut H <> e.
Proof.
  intros e H.
  destruct (other_in_neq (pre_proper_cut H) (target_in_edges_at_in e)) as [_ Hr].
  by revert Hr => /eqP-?.
Qed.

Lemma other_cut_set (G : proof_structure) (e : edge G) (H : vlabel (target e) = cut) :
  edges_at_in (target e) = [set e; other_cut H].
Proof. apply other_set. Qed.

Lemma other_cut_eq (G : proof_structure) (e : edge G) (H : vlabel (target e) = cut) :
  forall (a : edge G), target a = target e /\ a <> e -> a = other_cut H.
Proof.
  intros a [Ha Ha'].
  assert (Hin : a \in edges_at_in (target e)) by by rewrite in_set Ha.
  revert Hin. by rewrite other_cut_set !in_set => /orP [/eqP ? | /eqP ->].
Qed.

(** Reformulation of proper_ax_cut *)
Definition proper_ax_bis (G : proof_structure) :=
  forall (v : G) (Hl : vlabel v = ax),
  true_on2 (is_dual_f (flabel (G := G))) (pre_proper_ax Hl).

Definition proper_cut_bis (G : proof_structure) :=
  forall (v : G) (Hl : vlabel v = cut),
  true_on2 (is_dual_f (flabel (G := G))) (pre_proper_cut Hl).

Lemma p_ax_cut_bis (G : proof_structure) : proper_ax_bis G /\ proper_cut_bis G.
Proof.
  assert (H := @p_ax_cut G).
  unfold proper_ax_bis, proper_cut_bis.
  split; [set b := false | set b := true];
  [set pre_proper := pre_proper_ax | set pre_proper := pre_proper_cut].
  all: intros v Hl.
  all: destruct (H b v Hl) as [el [er [Hel [Her Heq]]]].
  all: apply (simpl_sym (dual_sym_f (flabel (G := G))) (Ht := Hel)).
  all: assert (Ho : other (pre_proper G v Hl) Hel = er) by
    (symmetry; apply other_eq; trivial; intro Hc; contradict Heq; rewrite Hc; no_selfform).
  all: by rewrite /is_dual_f /is_dual Ho Heq bidual.
Qed.
Lemma p_ax_bis (G : proof_structure) : proper_ax_bis G.
Proof. apply p_ax_cut_bis. Qed.
Lemma p_cut_bis (G : proof_structure) : proper_cut_bis G.
Proof. apply p_ax_cut_bis. Qed.

(** Reformulation of proper_tens_parr *)
Definition proper_tens_bis (G : proof_structure) :=
  forall (v : G) (H : vlabel v = ⊗),
  flabel (ccl_tens H) = (flabel (left_tens H)) ⊗ (flabel (right_tens H)).

Definition proper_parr_bis (G : proof_structure) :=
  forall (v : G) (H : vlabel v = ⅋),
  flabel (ccl_parr H) = (flabel (left_parr H)) ⅋ (flabel (right_parr H)).

Lemma p_tens_parr_bis (G : proof_structure) : proper_tens_bis G /\ proper_parr_bis G.
Proof.
  split; intros v H;
  [assert (H' := p_tens H) | assert (H' := p_parr H)].
  all: destruct H' as [el [er [ec [El [Ell [Er [Erl [Ec Heq]]]]]]]].
  all: revert El; rewrite in_set => /eqP-El.
  all: revert Er; rewrite in_set => /eqP-Er.
  all: revert Ec; rewrite in_set => /eqP-Ec.
  all: by rewrite /left_tens/left_parr -(@left_eq _ _ _ el) //
                  /right_tens/right_parr -(@right_eq _ _ _ er) //
                  /ccl_tens/ccl_parr -(@ccl_eq _ _ _ ec) //.
Qed.
Lemma p_tens_bis (G : proof_structure) : proper_tens_bis G.
Proof. apply p_tens_parr_bis. Qed.
Lemma p_parr_bis (G : proof_structure) : proper_parr_bis G.
Proof. apply p_tens_parr_bis. Qed.

(** p_ax_cut and p_tens_parr in bool instead of Prop *)
Lemma p_ax_cut_bool (b : bool) (G : proof_structure) :
  let rule := if b then cut else ax in
  forall (v : G), vlabel v = rule ->
  [exists el : edge G, exists er : edge G,
  (el \in edges_at_outin b v) && (er \in edges_at_outin b v)
  && (flabel el == dual (flabel er))].
Proof.
  intros ? ? V.
  destruct (p_ax_cut V) as [el [er [El [Er F]]]].
  apply /existsP; exists el. apply /existsP; exists er.
  splitb; by apply /eqP.
Qed.
Notation p_ax_bool := (@p_ax_cut_bool false).
Notation p_cut_bool := (@p_ax_cut_bool true).

Lemma p_tens_parr_bool (b : bool) (G : proof_structure) :
  let rule := if b then ⅋ else ⊗ in
  let form := if b then parr else tens in
  forall (v : G), vlabel v = rule ->
  [exists el : edge G, exists er : edge G, exists ec : edge G,
  (el \in edges_at_in v) && llabel el &&
  (er \in edges_at_in v) && ~~llabel er &&
  (ec \in edges_at_out v) && (flabel ec == form (flabel el) (flabel er))].
Proof.
  intros ? ? ? V.
  destruct (p_tens_parr V) as [el [er [ec [El [Ll [Er [Lr [Ec Lc]]]]]]]].
  apply /existsP; exists el. apply /existsP; exists er. apply /existsP; exists ec.
  splitb; (by apply /negP) || (by apply /eqP).
Qed.
Notation p_tens_bool := (@p_tens_parr_bool false).
Notation p_parr_bool := (@p_tens_parr_bool true).

(** p_ax_cut and p_tens_parr in Type instead of Prop *)
Lemma p_ax_cut_type (b : bool) (G : proof_structure) :
  let rule := if b then cut else ax in
  forall (v : G), vlabel v = rule ->
  {'(el, er) & endpoint b el = v /\ endpoint b er = v /\ flabel el = dual (flabel er)}.
Proof.
  intros ? ? V.
  assert (H := p_ax_cut_bool V).
  revert H => /existsP/sigW[e /existsP/sigW[e' /andP[/andP[E E'] /eqP-?]]].
  revert E E'. rewrite !in_set => /eqP-E /eqP-E'.
  by exists (e, e').
Qed.
Notation p_ax_type := (@p_ax_cut_type false).
Notation p_cut_type := (@p_ax_cut_type true).

Lemma p_tens_parr_type (b : bool) (G : proof_structure) :
  let rule := if b then ⅋ else ⊗ in
  let form := if b then parr else tens in
  forall (v : G), vlabel v = rule ->
  {'(el, er, ec) & target el = v /\ llabel el /\ target er = v /\ ~~llabel er
  /\ source ec = v /\ flabel ec = form (flabel el) (flabel er)}.
Proof.
  intros ? ? ? V.
  assert (H := p_tens_parr_bool V).
  revert H => /existsP/sigW[el /existsP/sigW[er /existsP/sigW[ec
    /andP[/andP[/andP[/andP[/andP[El Ll] Er] Lr] Ec] /eqP-F]]]].
  revert El Er Ec. rewrite !in_set => /eqP-El /eqP-Er /eqP-Ec.
  by exists (el, er, ec).
Qed.
Notation p_tens_type := (@p_tens_parr_type false).
Notation p_parr_type := (@p_tens_parr_type true).

(** Some useful lemmas based on cardinality *)
Lemma no_target_ax (G : proof_structure) (v : G) :
  vlabel v = ax -> forall e, target e <> v.
Proof.
  intros H e ?; subst v.
  assert (F : edges_at_in (target e) = set0).
  { apply cards0_eq. by rewrite p_deg H. }
  assert (F' : e \in set0) by by rewrite -F in_set.
  by rewrite in_set in F'.
Qed.

Lemma no_source_cut (G : proof_structure) (v : G) :
  vlabel v = cut -> forall e, source e <> v.
Proof.
  intros H e ?; subst v.
  assert (F : edges_at_out (source e) = set0).
  { apply cards0_eq. by rewrite p_deg H. }
  assert (F' : e \in set0) by by rewrite -F in_set.
  by rewrite in_set in F'.
Qed.

Lemma no_source_c (G : proof_structure) (v : G) :
  vlabel v = c -> forall e, source e <> v.
Proof.
  intros H e ?; subst v.
  assert (F : edges_at_out (source e) = set0).
  { apply cards0_eq. by rewrite p_deg H. }
  assert (F' : e \in set0) by by rewrite -F in_set.
  by rewrite in_set in F'.
Qed.

Lemma one_target_c (G : proof_structure) :
  forall (e : edge G), vlabel (target e) = c -> forall f, target f = target e -> f = e.
Proof. intros e H ? ?. transitivity (edge_of_concl H); [ | symmetry]; by apply concl_eq. Qed.

Lemma one_source_tensparr (G : proof_structure) :
  forall (e : edge G), vlabel (source e) = ⊗ \/ vlabel (source e) = ⅋ ->
  forall f, source f = source e -> f = e.
Proof. intros e H ? ?. transitivity (ccl H); [ | symmetry]; by apply ccl_eq. Qed.
Lemma one_source_tens (G : proof_structure) :
  forall (e : edge G), vlabel (source e) = ⊗ -> forall f, source f = source e -> f = e.
Proof. intros. apply one_source_tensparr; caseb. Qed.
Lemma one_source_parr (G : proof_structure) :
  forall (e : edge G), vlabel (source e) = ⅋ -> forall f, source f = source e -> f = e.
Proof. intros. apply one_source_tensparr; caseb. Qed.

Lemma in_path (G : proof_structure) (a b : edge G) :
  target a = source b -> vlabel (source b) = ⊗ \/ vlabel (source b) = ⅋.
Proof.
  intros E.
  destruct (vlabel (source b)) eqn:V; auto.
  - contradict E. by apply no_target_ax.
  - rewrite -E in V.
    contradict E. by apply nesym, no_source_cut.
  - rewrite -E in V.
    contradict E. by apply nesym, no_source_c.
Qed.


Fixpoint sub_formula A B := (A == B) || match B with
  | var _ | covar _ => false
  | tens Bl Br | parr Bl Br => (sub_formula A Bl) || (sub_formula A Br)
  end.
Infix "⊆" := sub_formula (left associativity, at level 25).

(** The relation being a sub formula is a partial order *)
Lemma sub_formula_reflexivity :
  forall A, sub_formula A A.
Proof. intros []; caseb. Qed.

Lemma sub_formula_transitivity :
  forall A B C, sub_formula A B -> sub_formula B C -> sub_formula A C.
Proof.
  intros A B C; revert A B.
  induction C as [x | x | Cl HCl Cr HCr | Cl HCl Cr HCr] => A B.
  all: rewrite /= ?orb_false_r.
  - move => S0 /eqP-?; subst B.
    inversion S0 as [[S0']]. by rewrite orb_false_r in S0'.
  - move => S0 /eqP-?; subst B.
    inversion S0 as [[S0']]. by rewrite orb_false_r in S0'.
  - move => S0 /orP[/eqP-? | /orP[S1 | S1]]; subst.
    + revert S0 => /= /orP[/eqP-? | /orP[S0 | S0]]; subst; caseb.
    + specialize (HCl _ _ S0 S1). caseb.
    + specialize (HCr _ _ S0 S1). caseb.
  - move => S0 /orP[/eqP-? | /orP[S1 | S1]]; subst.
    + revert S0 => /= /orP[/eqP-? | /orP[S0 | S0]]; subst; caseb.
    + specialize (HCl _ _ S0 S1). caseb.
    + specialize (HCr _ _ S0 S1). caseb.
Qed.

Lemma sub_formula_antisymmetry :
  forall A B, sub_formula B A -> sub_formula A B -> A = B.
Proof.
  intro A; induction A as [a | a | Al HAl Ar HAr | Al HAl Ar HAr] => B.
  all: rewrite /= ?orb_false_r //.
  - by move => /eqP--> _.
  - by move => /eqP--> _.
  - move => /orP[/eqP-HA | /orP[HA | HA]] HB //.
    + enough (Hf : Al = Al ⊗ Ar) by by contradict Hf; no_selfform.
      apply HAl.
      * exact (sub_formula_transitivity HB HA).
      * rewrite /= sub_formula_reflexivity. caseb.
    + enough (Hf : Ar = Al ⊗ Ar) by by contradict Hf; no_selfform.
      apply HAr.
      * exact (sub_formula_transitivity HB HA).
      * rewrite /= sub_formula_reflexivity. caseb.
  - move => /orP[/eqP-HA | /orP[HA | HA]] HB //.
    + enough (Hf : Al = Al ⅋ Ar) by by contradict Hf; no_selfform.
      apply HAl.
      * exact (sub_formula_transitivity HB HA).
      * rewrite /= sub_formula_reflexivity. caseb.
    + enough (Hf : Ar = Al ⅋ Ar) by by contradict Hf; no_selfform.
      apply HAr.
      * exact (sub_formula_transitivity HB HA).
      * rewrite /= sub_formula_reflexivity. caseb.
Qed.

Lemma walk_formula (G : proof_structure) (e : edge G) (p : path) (s t : G) :
  walk s t (e :: p) -> sub_formula (flabel e) (flabel (last e p)).
Proof.
  move => /= /andP[/eqP-? W]. subst s.
  revert t W.
  apply (@last_ind (edge G) (fun p => forall t, walk (target e) t p -> flabel e ⊆ flabel (last e p)));
  rewrite {p} /=.
  - move => ? /eqP-?; subst. apply sub_formula_reflexivity.
  - intros p f H t.
    rewrite walk_rcons => /andP[W /eqP-?]; subst t.
    specialize (H _ W).
    rewrite last_rcons.
    apply (sub_formula_transitivity H). clear H.
    set a := last e p.
    assert (TS : target a = source f).
    { destruct (walk_endpoint W) as [_ A].
      by rewrite /= last_map in A. }
    assert (F := in_path TS).
    assert (F' : f = ccl F) by by apply ccl_eq.
    destruct F as [F | F].
    + destruct (llabel a) eqn:La.
      * assert (A : a = left_tens F) by by apply left_eq.
        rewrite F' A p_tens_bis /= sub_formula_reflexivity. caseb.
      * revert La => /negP-La.
        assert (A : a = right_tens F) by by apply right_eq.
        rewrite F' A p_tens_bis /= sub_formula_reflexivity. caseb.
    + destruct (llabel a) eqn:La.
      * assert (A : a = left_parr F) by by apply left_eq.
        rewrite F' A p_parr_bis /= sub_formula_reflexivity. caseb.
      * revert La => /negP-La.
        assert (A : a = right_parr F) by by apply right_eq.
        rewrite F' A p_parr_bis /= sub_formula_reflexivity. caseb.
Qed.

(** A proof structure is directed acyclic *)
Lemma ps_acyclic (G : proof_structure) : @acyclic _ _ G.
Proof.
  intros v [ | e p] W0; trivial.
  exfalso.
  assert (F0 := walk_formula W0).
  destruct (walk_endpoint W0) as [E S].
  simpl in E, S. subst v.
  rewrite last_map in S.
  assert (W1 : walk (source (last e p)) (target e) [:: last e p; e]).
  { rewrite /= S. splitb. }
  assert (F1 := walk_formula W1).
  simpl in F1.
  assert (F : flabel e = flabel (last e p)) by by apply sub_formula_antisymmetry.
  clear F0 F1 W0 W1.
  assert (Se := in_path S).
  assert (E : e = ccl Se) by by apply ccl_eq.
  rewrite [in LHS]E in F.
  destruct Se as [Se | Se].
  - assert (Fse := p_tens_bis Se). contradict Fse.
    rewrite /ccl_tens F.
    destruct (llabel (last e p)) eqn:Ll.
    + assert (last e p = left_tens Se) as -> by by apply left_eq.
      no_selfform.
    + revert Ll => /negP-Ll.
      assert (last e p = right_tens Se) as -> by by apply right_eq.
      no_selfform.
  - assert (Fse := p_parr_bis Se). contradict Fse.
    rewrite /ccl_tens F.
    destruct (llabel (last e p)) eqn:Ll.
    + assert (last e p = left_parr Se) as -> by by apply left_eq.
      no_selfform.
    + revert Ll => /negP-Ll.
      assert (last e p = right_parr Se) as -> by by apply right_eq.
      no_selfform.
Qed.

(* A proof_structure can be considered as a directed acyclic multigraph *)
Coercion dam_of_ps (G : proof_structure) := Dam (@ps_acyclic G).

(** No selfloop in a proof_structure *)
Lemma no_selfloop (G : proof_structure) : forall (e : edge G), source e <> target e.
Proof.
  intros e H.
  assert (A := @ps_acyclic G (source e) [:: e]). simpl in A.
  enough ([:: e] = [::]) by by [].
  apply A. splitb. by rewrite H.
Qed.



(** ** Stratum 4: Proof Net *)
(** ** Correctness Criteria: Danos-Regnier *)
(** Identify all premises of a ⅋ node *)
Definition switching {G : base_graph} : edge G -> option ((edge G) + G) :=
  fun e => Some (if vlabel (target e) == ⅋ then inr (target e) else inl e).

(** Paths in the switching graph without any right *)
Definition switching_left {G : base_graph} : edge G -> option (edge G) :=
  fun e => if (vlabel (target e) == ⅋) && (~~llabel e) then None else Some e.

(* All switching graphs have the same number of connected components:
   any one is connected iff the graph where we remove all lefts is connected and not empty *)
Definition correct_weak (G : base_graph) := uacyclic (@switching G) /\ uconnected (@switching_left G).
Definition correct (G : base_graph) := uacyclic (@switching G) /\ uconnected_nb (@switching_left G) = 1.

Set Primitive Projections.
Record proof_net : Type :=
  Proof_net {
    ps_of :> proof_structure;
    p_correct : correct ps_of;
  }.
Unset Primitive Projections.



(** * Properties on switching & switching_left *)
Lemma switching_eq (G : base_graph) :
  forall (a b : edge G), switching a = switching b -> target a = target b.
Proof.
  intros ? ?. unfold switching => /eqP; cbn => /eqP.
  case: ifP; case: ifP; by move => // _ _ /eqP; cbn => /eqP ->.
Qed.

Lemma switching_None (G : base_graph) :
  forall (p : @upath _ _ G), None \notin [seq switching e.1 | e <- p].
Proof. intro p. by induction p. Qed.

Lemma switching_left_sinj {G : base_graph} :
  {in ~: (@switching_left G) @^-1 None &, injective switching_left}.
Proof.
  move => a b; rewrite !in_set => A B /eqP; revert A B.
  unfold switching_left; case_if.
Qed.

Lemma swithching_to_left_eq {G : proof_structure} :
  forall (a b : edge G), switching_left a <> None -> switching_left b <> None ->
  switching a = switching b -> switching_left a = switching_left b.
Proof.
  move => a b A B S.
  assert (T := switching_eq S).
  apply /eqP; revert S A B => /eqP.
  rewrite /switching/switching_left T; cbn.
  case_if; apply /eqP.
  assert (llabel a) by (by apply /negPn);
  assert (llabel b) by by apply /negPn.
  assert (Bl : vlabel (target b) = ⅋) by by apply /eqP.
  transitivity (left_parr Bl); [ | symmetry];
  by apply left_eq.
Qed.

Lemma supath_switching_from_leftK {G : proof_structure} :
  forall (u v : G) p, supath switching_left u v p ->
  supath switching u v p.
Proof.
  move => u v p /andP[/andP[? U] N].
  splitb; last by apply switching_None.
  destruct p as [ | e p]; trivial.
  apply /(uniqP (Some (inl (e.1)))) => a f A F.
  revert U => /(uniqP (Some e.1)) /(_ a f).
  rewrite_all size_map; rewrite !(nth_map e) // => /(_ A F) U Heq.
  apply U, swithching_to_left_eq; trivial.
  - intro Hc.
    contradict N; apply /negP/negPn/mapP.
    exists (nth e (e :: p) a); try by [].
    by apply mem_nth.
  - intro Hc.
    contradict N; apply /negP/negPn/mapP.
    exists (nth e (e :: p) f); try by [].
    by apply mem_nth.
Qed.

Definition supath_switching_from_left {G : proof_structure} (s t : G) (p : Supath switching_left s t) :=
  {| upval := _ ; upvalK := supath_switching_from_leftK (upvalK p) |}.

Lemma uacyclic_swithching_left {G : proof_structure} :
  uacyclic (@switching G) -> uacyclic (@switching_left G).
Proof.
  move => A u P.
  specialize (A _ (supath_switching_from_left P)).
  cbnb. by revert A => /eqP; cbn => /eqP.
Qed.

Lemma switching_left_edges_None (G : base_graph) :
  (@switching_left G) @^-1 None = [set e | (vlabel (target e) == ⅋) && (~~llabel e)].
Proof.
  apply /setP => e.
  rewrite !in_set; symmetry.
  destruct (switching_left e \in pred1 None) eqn:E.
  all: revert E => /eqP.
  all: unfold switching_left; case_if.
Qed.

Lemma switching_left_edges_None_nb (G : proof_structure) :
  #|[set e : edge G | (vlabel (target e) == ⅋) && (~~llabel e)]| = #|[set v : G | vlabel v == ⅋]|.
Proof.
  rewrite -!card_set_subset.
  assert (Hf : forall E : [finType of {e : edge G | (vlabel (target e) == ⅋) && (~~llabel e)}],
    (vlabel (target (val E)) == ⅋)).
  { by intros [e E]; cbn; revert E => /andP[E _]. }
  set f : [finType of {e : edge G | (vlabel (target e) == ⅋) && (~~llabel e)}] ->
    [finType of {v | vlabel v == ⅋}] :=
    fun e => Sub (target (val e)) (Hf e).
  assert (Hg : forall E : [finType of {v : G | vlabel v == ⅋}],
    (vlabel (target (right_parr (eqP (valP E)))) == ⅋) && (~~llabel (right_parr (eqP (valP E))))).
  { intros [e E]; splitb.
    - by rewrite right_e.
    - apply right_l. }
  set g : [finType of {v | vlabel v == ⅋}] ->
    [finType of {e : edge G | (vlabel (target e) == ⅋) && (~~llabel e)}] :=
    fun V => Sub (right_parr (eqP (valP V))) (Hg V).
  apply (bij_card_eq (f := f)), (Bijective (g := g)).
  - move => [e E].
    rewrite /f/g; cbnb.
    symmetry; apply right_eq; simpl.
    by revert E => /andP[_ /negP-?].
  - move => [v V].
    rewrite /f/g; cbnb.
    apply right_e.
Qed.

Lemma switching_left_edges_nb (G : proof_structure) :
  #|[set v : G | vlabel v == ⅋]| + #|~: (@switching_left G) @^-1 None| = #|edge G|.
Proof. by rewrite -switching_left_edges_None_nb -switching_left_edges_None cardsC. Qed.

Lemma switching_left_uconnected_nb {G : proof_structure} :
  uacyclic (@switching G) ->
  uconnected_nb (@switching_left G) + #|edge G| = #|G| + #|[set v : G | vlabel v == ⅋]|.
Proof.
  move => *.
  rewrite -switching_left_edges_nb.
  transitivity (uconnected_nb (@switching_left G) +
    #|~: (@switching_left G) @^-1 None| + #|[set v : G | vlabel v == ⅋]|); [lia | ].
  rewrite uacyclic_uconnected_nb //.
  - apply switching_left_sinj.
  - by apply uacyclic_swithching_left.
Qed.

Lemma correct_from_weak (G : base_graph) :
  #|G| <> 0 -> correct_weak G -> correct G.
Proof.
  intros ? [? ?]. split; trivial.
  apply uconnected_to_nb1; trivial. apply switching_left_sinj.
Qed.

Lemma correct_to_weak (G : base_graph) :
  correct G -> correct_weak G.
Proof.
  intros [? ?]. split; trivial.
  apply uconnected_from_nb1; trivial. apply switching_left_sinj.
Qed.

Lemma correct_not_empty (G : base_graph) :
  correct G -> #|G| <> 0.
Proof. intros [_ C]. by apply (nb1_not_empty C). Qed.

Lemma exists_node (G : proof_net) : {v : G & vlabel v <> c}.
Proof.
  assert (N := correct_not_empty (p_correct G)).
  revert N => /eqP. rewrite -cardsT cards_eq0 => /set0Pn/sigW[v _].
  destruct (vlabel v) eqn:V;
  try by (exists v; rewrite V).
  exists (source (edge_of_concl V)).
  intros U.
  assert (F : source (edge_of_concl V) = source (edge_of_concl V)) by trivial.
  contradict F. by apply no_source_c.
Qed.



(** * Isomorphism for each strata *)
(** Correction is preserved by isomorphism on base graphs *)
Definition switching_map (F G : base_graph) (h : F ≃ G) :=
  fun e => match e with
  | Some (inl a) => Some (inl (h.e a))
  | Some (inr a) => Some (inr (h a))
  | None => None
 end.

Lemma iso_switching (F G : base_graph) (h : F ≃ G) :
  forall e, switching (h.e e) = switching_map h (switching e).
Proof.
  intro e; cbnb.
  rewrite !endpoint_iso iso_noflip vlabel_iso; cbn.
  by destruct (vlabel (target e)) eqn:Hl; rewrite Hl; case_if.
Qed.

Lemma iso_switching_left (F G : base_graph) (h : F ≃ G) :
  forall e, switching_left (h.e e) = option_map h.e (switching_left e).
Proof.
  intros.
  rewrite /switching_left endpoint_iso iso_noflip vlabel_iso llabel_iso.
  case_if.
Qed.


Lemma iso_path_switchingK (F G : base_graph) (h : F ≃ G) : forall p s t,
  supath switching s t p -> supath switching (h s) (h t) (iso_path h p).
Proof.
  move => p s t /andP[/andP[W U] N]. splitb.
  - apply iso_walk; trivial. apply iso_noflip.
  - rewrite -map_comp /comp; cbn.
    assert (map _ p = [seq switching_map h (switching x.1) | x <- p]) as ->
      by (apply eq_map; move => *; by rewrite iso_switching).
    rewrite /switching map_comp map_inj_uniq // in U.
    rewrite (map_comp (fun e => match e with | inl _1 => _ | inr _1 => _ end) _ _) map_inj_uniq //.
    move => [a | a] [b | b] /eqP; cbn => // /eqP-Eq; cbnb.
    all: by revert Eq; apply bij_injective.
  - apply switching_None.
Qed.

Definition iso_path_switching (F G : base_graph) (h : F ≃ G) (s t : F) :
  Supath switching s t -> Supath switching (h s) (h t) :=
  fun p => {| upval := _ ; upvalK := iso_path_switchingK h (upvalK p) |}.

Lemma iso_path_switching_inj (F G : base_graph) (h : F ≃ G) :
  forall s t, injective (@iso_path_switching _ _ h s t).
Proof.
  move => s t [p P] [q Q] /eqP; cbn => /eqP Heq; cbnb.
  revert Heq; apply inj_map => [[e b] [f c]] /eqP; cbn => /andP[/eqP Heq /eqP ->].
  apply /eqP; splitb; cbn; apply /eqP.
  by revert Heq; apply bij_injective.
Qed.

Lemma iso_path_nil (F G : base_graph) (h : F ≃ G) :
  forall (s : F), iso_path_switching h (supath_nil switching s) = supath_nil switching (h s).
Proof. intros. by apply /eqP. Qed.

Lemma iso_path_switching_leftK (F G : base_graph) (h : F ≃ G) : forall p s t,
  supath switching_left s t p -> supath switching_left (h s) (h t) (iso_path h p).
Proof.
  move => p s t /andP[/andP[W U] N].
  splitb.
  - apply iso_walk; trivial. apply iso_noflip.
  - rewrite -map_comp /comp; cbn.
    enough ([seq switching_left (h.e x.1) | x <- p] = [seq Some (h.e x.1) | x <- p] /\
      [seq switching_left e.1 | e <- p] = [seq Some x.1 | x <- p]) as [Hr' Hr].
    { rewrite Hr map_comp map_inj_uniq // in U.
      by rewrite Hr' map_comp map_inj_uniq // map_comp map_inj_uniq. }
    split; apply eq_in_map; intros (e, b) E.
    all: rewrite ?iso_switching_left /switching_left.
    all: case_if.
    all: contradict N; apply /negP/negPn.
    all: enough (Hn : None = switching_left (e, b).1) by
      (rewrite Hn; by apply (map_f (fun a => switching_left a.1))).
    all: rewrite /switching_left /=.
    all: by replace (vlabel (target e) == ⅋) with true; replace (~~llabel e) with true.
  - rewrite -map_comp /comp; cbn.
    apply /(nthP None); move => [n Hc] Hf.
    rewrite size_map in Hc.
    enough (nth None [seq switching_left x.1 | x <- p] n = None).
    { contradict N; apply /negP/negPn/(nthP None). rewrite size_map. by exists n. }
    revert Hf.
    destruct p as [ | (e, b) p]; try by [].
    rewrite !(nth_map (e, b) None) // iso_switching_left.
    unfold switching_left; case_if.
Qed.

Definition iso_path_switching_left (F G : base_graph) (h : F ≃ G) (s t : F) :
  Supath switching_left s t -> Supath switching_left (h s) (h t) :=
  fun p => {| upval := _ ; upvalK := iso_path_switching_leftK h (upvalK p) |}.

Lemma iso_uacyclic (F G : base_graph) :
  F ≃ G -> uacyclic switching (G := G) -> uacyclic switching (G := F).
Proof.
  intros h A ? ?.
  apply (@iso_path_switching_inj _ _ h).
  rewrite iso_path_nil.
  apply A.
Qed.

Lemma iso_uconnected (F G : base_graph) :
  F ≃ G -> uconnected switching_left (G := G) -> uconnected switching_left (G := F).
Proof.
  intros h C u v. destruct (C (h u) (h v)) as [p _].
  set h' := iso_sym h.
  rewrite -(bijK' h' u) -(bijK' h' v).
  by exists (iso_path_switching_left h' p).
Qed.

(*
Lemma iso_uconnectednb (F G : base_graph) :
  F ≃ G -> uconnected_nb switching_left (G := G) = uconnected_nb switching_left (G := F).
Proof.
Abort. (* TODO if useful, but it is stronger than what we need *)*)

Lemma iso_correct_weak (F G : base_graph) : F ≃ G -> correct_weak G -> correct_weak F.
Proof.
  intros h [? ?]; split.
  - by apply (iso_uacyclic h).
  - by apply (iso_uconnected h).
Qed.

Lemma iso_correct (F G : base_graph) : F ≃ G -> correct G -> correct F.
Proof.
  intros h C.
  apply correct_from_weak.
  - rewrite (card_iso h). by apply correct_not_empty.
  - by apply (iso_correct_weak h), correct_to_weak.
Qed.


(** * Isomorphism on graph data preserves being a proof structure *)
Set Primitive Projections.
Record iso_data (F G : graph_data) :=
  Iso_order {
    iso_of :> F ≃ G;
    order_iso : order G = [seq iso_of.e e | e <- order F]
  }.
Unset Primitive Projections.
Infix "≃d" := iso_data (at level 79).

(* Equivalence relation *)
Definition iso_data_id G : G ≃d G.
Proof. exists (iso_id (G:=G)). symmetry; apply map_id. Defined.

Definition iso_data_sym F G : F ≃d G -> G ≃d F.
Proof.
  move => f.
  exists (iso_sym f).
  rewrite -(map_id (order F)) (order_iso f) -map_comp /=.
  apply eq_map => v /=.
  symmetry; apply bijK.
Defined.

Definition iso_data_comp F G H : F ≃d G -> G ≃d H -> F ≃d H.
Proof.
  move => f g.
  exists (iso_comp f g).
  by rewrite (order_iso g) (order_iso f) -map_comp.
Defined.

Global Instance iso_data_Equivalence: CEquivalence iso_data.
Proof. constructor; [exact @iso_data_id | exact @iso_data_sym | exact @iso_data_comp]. Defined.

Lemma sequent_iso_data F G : F ≃d G -> sequent F = sequent G.
Proof.
  intros [h O].
  rewrite /sequent O -map_comp.
  apply eq_map => e /=.
  by rewrite flabel_iso.
Qed.

(* Properties making a graph a proof structure are transported *)
Lemma p_deg_iso (F G : base_graph) : F ≃ G -> proper_degree G -> proper_degree F.
Proof.
  intros h H b v.
  specialize (H b (h v)).
  rewrite ->vlabel_iso in H.
  rewrite -H edges_at_outin_iso ?card_imset //.
  apply iso_noflip.
Qed.

Lemma p_ax_cut_iso (F G : base_graph) : F ≃ G -> proper_ax_cut G -> proper_ax_cut F.
Proof.
  move => h H b r v Hl.
  rewrite <-(vlabel_iso h v) in Hl.
  revert H => /(_ b _ Hl) [el [er H]].
  exists (h.e^-1 el), (h.e^-1 er).
  rewrite -(bijK h v) (@edges_at_outin_iso _ _ _ _ (iso_sym h)) ?(bij_imset_f (iso_sym h).e)
    ?(flabel_iso (iso_sym h)) //.
  apply iso_noflip.
Qed.

Lemma p_tens_parr_iso (F G : base_graph) : F ≃ G -> proper_tens_parr G -> proper_tens_parr F.
Proof.
  move => h H b r /= v Hl.
  rewrite <-(vlabel_iso h v) in Hl.
  revert H => /(_ b _ Hl) [el [er [ec H]]].
  exists (h.e^-1 el), (h.e^-1 er), (h.e^-1 ec).
  rewrite -(bijK h v) !(@edges_at_outin_iso _ _ _ _ (iso_sym h)) ?(bij_imset_f (iso_sym h).e)
    ?(flabel_iso (iso_sym h)) ?(llabel_iso (iso_sym h)) //.
  all: apply iso_noflip.
Qed.

Lemma p_noleft_iso (F G : base_graph) : F ≃ G -> proper_noleft G -> proper_noleft F.
Proof.
  intros h H e Hl.
  assert (Hl' : vlabel (target (h.e e)) = ax \/ vlabel (target (h.e e)) = cut \/
    vlabel (target (h.e e)) = c) by by rewrite endpoint_iso iso_noflip vlabel_iso.
  specialize (H (h.e e) Hl').
  by rewrite llabel_iso in H.
Qed.

Lemma p_order_iso (F G : graph_data) : F ≃d G -> proper_order G -> proper_order F.
Proof.
  intros h [In U].
  split.
  - intro e.
    specialize (In (h.e e)). rewrite ->endpoint_iso, ->vlabel_iso, iso_noflip in In. simpl in In.
    symmetry; symmetry in In. apply (@iff_stepl _ _ _ In).
    by rewrite (order_iso h) mem_map.
  - by rewrite (order_iso h) map_inj_uniq in U.
Qed.

Lemma order_iso_weak (F G : proof_structure) : forall (h : F ≃ G),
  forall e, e \in order F <-> h.e e \in order G.
Proof.
  intros h e.
  destruct (p_order F) as [? _].
  destruct (p_order G) as [? _].
  transitivity (vlabel (target e) = c); [by symmetry | ].
  by replace (vlabel (target e)) with (vlabel (target (h.e e)))
    by by rewrite endpoint_iso iso_noflip vlabel_iso.
Qed.

Definition order_iso_perm (F G : proof_structure) : forall (h : F ≃ G),
  Permutation_Type (order G) [seq h.e e | e <- order F].
Proof.
  intro h.
  destruct (p_order F) as [_ ?].
  destruct (p_order G) as [_ ?].
  by apply Permutation_Type_bij_uniq, order_iso_weak.
Defined.

Lemma sequent_iso_weak (F G : proof_structure) :
  forall (h : F ≃ G),
  sequent F = [seq flabel e | e <- [seq h.e e | e <- order F]].
Proof.
  intro h. rewrite /sequent -map_comp. apply eq_map => ? /=. by rewrite flabel_iso.
Qed.

Definition sequent_iso_perm (F G : proof_structure) : F ≃ G ->
  Permutation_Type (sequent G) (sequent F).
Proof.
  intro h.
  rewrite (sequent_iso_weak h).
  exact (Permutation_Type_map_def _ (order_iso_perm h)).
Defined.

Lemma perm_of_sequent_iso_perm (F G : proof_structure) :
  forall (h : F ≃ G),
  perm_of (sequent_iso_perm h) (order G) = [seq h.e e | e <- order F].
Proof.
  intros. by rewrite -(perm_of_consistent (order_iso_perm _)) perm_of_rew_r
    perm_of_Permutation_Type_map.
Qed.
(* TODO lemma iso_to_isod ici ? Nécressite d'y mettre perm_graph aussi *)
(* TODO si besoin de proprietes comme left (h ) = h left, les mettre ici *)



(** * Some results about rule carninality rcard *)
Lemma rset_bij {F G : base_graph} (h : F ≃ G) :
  [set h v | v : F & vlabel v == c] = [set v | vlabel v == c].
Proof. apply setP => v. by rewrite -[in LHS](bijK' h v) bij_imset_f !in_set (vlabel_iso (iso_sym h)). Qed.

Lemma rset_bij_in {F G : base_graph} (h : F ≃ G) :
  forall (v : sig_finType (pred_of_set (~: [set v : F | vlabel v == c]))),
    h (val v) \in ~: [set v : G | vlabel v == c].
Proof. intros []. by rewrite -(rset_bij h) bij_imsetC bij_imset_f. Qed.

Lemma rcard_iso (F G : base_graph) :
  F ≃ G -> r#|F| = r#|G|.
Proof.
  intro h.
  rewrite /rcard -card_sig -[in RHS]card_sig.
  set f : sig_finType (pred_of_set (~: [set v : F | vlabel v == c])) ->
    sig_finType (pred_of_set (~: [set v : G | vlabel v == c])) :=
    fun v => Sub (h (val v)) (rset_bij_in h v).
  set g : sig_finType (pred_of_set (~: [set v : G | vlabel v == c])) ->
    sig_finType (pred_of_set (~: [set v : F | vlabel v == c])) :=
    fun v => Sub (h^-1 (val v)) (rset_bij_in (iso_sym h) v).
  apply (bij_card_eq (f := f)), (Bijective (g := g)); unfold f, g.
  - intros [v V]. cbnb. apply bijK.
  - intros [v V]. cbnb. apply bijK'.
Qed.

Lemma union_rcard (F G : base_graph) : r#|F ⊎ G| = r#|F| + r#|G|.
Proof.
  rewrite /rcard.
  assert (~: [set v : F ⊎ G | vlabel v == c] = ~: [set v : F ⊎ G | match v with | inl v => vlabel v == c | inr _ => true end]
    :|: ~: [set v : F ⊎ G | match v with | inr v => vlabel v == c | inl _ => true end]) as ->.
  { apply /setP. by intros [? | ?]; rewrite !in_set ?orb_false_r. }
  rewrite cardsU.
  assert (~: [set v : F ⊎ G | match v with | inl v => vlabel v == c | inr _ => true end]
    :&: ~: [set v : F ⊎ G | match v with | inl _ => true | inr v => vlabel v == c end] = set0) as ->.
  { apply /setP. by intros [? | ?]; rewrite !in_set ?andb_false_r. }
  rewrite cards0.
  enough ((~: [set v : F ⊎ G | match v with | inl v => vlabel v == c | inr _ => true end] =
    inl @: ~: [set v : F | vlabel v == c]) /\
    ~: [set v : F ⊎ G | match v with | inr v => vlabel v == c | inl _ => true end] =
    inr @: ~: [set v : G | vlabel v == c]) as [-> ->].
  { rewrite !card_imset; try by (apply inl_inj || apply inr_inj). lia. }
  split; apply /setP; intros [v | v].
  all: rewrite ?mem_imset ?in_set //; try by (apply inl_inj || apply inr_inj).
  all: symmetry; simpl.
  all: apply /imsetP; by move => [? _ /eqP-Hf].
Qed.

Lemma add_edge_rcard (G : base_graph) u v A :
  r#|G ∔ [u, A, v]| = r#|G|.
Proof. trivial. Qed.

Lemma unit_graph_rset R :
  R <> c -> [set v : (unit_graph R : base_graph) | vlabel v == c] = set0.
Proof.
  intros. apply /setP => v.
  rewrite !in_set. destruct v; by apply /eqP.
Qed.

Lemma unit_graph_rcard R :
  R <> c -> r#|unit_graph R| = 1.
Proof. intros. by rewrite /rcard cardsCs setCK unit_graph_rset // cards0 /= card_unit. Qed.

Lemma two_graph_rset R :
  R <> c -> [set v : (two_graph R c : base_graph) | vlabel v == c] = [set inr tt].
Proof.
  intros. apply /setP => v.
  rewrite !in_set /=. destruct v as [[] | []]; by apply /eqP.
Qed.

Lemma two_graph_rcard R :
  R <> c -> r#|two_graph R c| = 1.
Proof. intros. by rewrite /rcard cardsCs setCK /= card_sum card_unit two_graph_rset // cards1. Qed.

Lemma rem_rcard (G : base_graph) (v : G) S :
  vlabel v = c -> r#|induced (S :\ v)| = r#|induced S|.
Proof.
  intro V.
  rewrite /rcard -card_sig -[in RHS]card_sig.
  assert (Hf : forall (u : sig_finType (pred_of_set (~: [set u : induced (S :\ v) | vlabel u == c]))),
    val (val u) \in S).
  { move => [[u I] /= _]. revert I. by rewrite in_set => /andP[_ I]. }
  assert (Hf' : forall (u : sig_finType (pred_of_set (~: [set u : induced (S :\ v) | vlabel u == c]))),
    Sub (val (val u)) (Hf u) \in ~: [set u : induced S | vlabel u == c]).
  { move => [[u I] U] /=.
    rewrite !in_set /=. by rewrite -in_set finset_of_pred_of_set !in_set /= in U. }
  set f : sig_finType (pred_of_set (~: [set u : induced (S :\ v) | vlabel u == c])) ->
    sig_finType (pred_of_set (~: [set u : induced S | vlabel u == c])) :=
    fun u => Sub (Sub (val (val u)) (Hf u)) (Hf' u).
  assert (Hg : forall (u : sig_finType (pred_of_set (~: [set u : induced S | vlabel u == c]))),
    val (val u) \in S :\ v).
  { move => [[u I] U] /=.
    rewrite !in_set /=. rewrite -in_set finset_of_pred_of_set !in_set /= in U.
    splitb. apply /eqP => ?; subst u. contradict V. by apply /eqP. }
  assert (Hg' : forall (u : sig_finType (pred_of_set (~: [set u : induced S | vlabel u == c]))),
    Sub (val (val u)) (Hg u) \in ~: [set u : induced (S :\ v) | vlabel u == c]).
  { move => [[u I] U] /=.
    rewrite !in_set /=. by rewrite -in_set finset_of_pred_of_set !in_set /= in U. }
  set g : sig_finType (pred_of_set (~: [set u : induced S | vlabel u == c])) ->
    sig_finType (pred_of_set (~: [set u : induced (S :\ v) | vlabel u == c])) :=
    fun u => Sub (Sub (val (val u)) (Hg u)) (Hg' u).
  apply (bij_card_eq (f := f)), (Bijective (g := g)); intros [[u I] U]; cbnb.
Qed.


Lemma has_ax (G : proof_net) : { v : G & vlabel v == ax }.
Proof.
  apply /sigW.
  apply (well_founded_ind (R := @is_connected_strict_rev _ _ G)).
  { apply (@well_founded_dam_rev _ _ G). }
  2:{ apply exists_node. }
  intros v H.
  destruct (vlabel v) eqn:V.
  - exists v. by apply /eqP.
  - apply (H (source (left_tens V))).
    unfold is_connected_strict_rev, is_connected_strict.
    exists [:: left_tens V]. splitb; apply /eqP.
    apply left_e.
  - apply (H (source (left_parr V))).
    unfold is_connected_strict_rev, is_connected_strict.
    exists [:: left_parr V]. splitb; apply /eqP.
    apply left_e.
  - destruct (p_cut V) as [e [_ [E _]]].
    rewrite !in_set in E.
    apply (H (source e)).
    unfold is_connected_strict_rev, is_connected_strict.
    exists [:: e]. splitb.
  - apply (H (source (edge_of_concl V))).
    unfold is_connected_strict_rev, is_connected_strict.
    exists [:: edge_of_concl V]. splitb; apply /eqP.
    apply concl_e.
Qed.

Definition terminal (G : base_graph) (v : G) : bool :=
  match vlabel v with
  | c => false
  | _ => [forall e, (source e == v) ==> (vlabel (target e) == c)]
  end.

Lemma terminal_not_c (G : base_graph) (v : G) :
  vlabel v <> c ->
  terminal v = [forall e, (source e == v) ==> (vlabel (target e) == c)].
Proof. unfold terminal. by destruct (vlabel v). Qed.

Lemma not_terminal (G : base_graph) (v : G) :
  vlabel v <> c -> ~~ terminal v ->
  {e : edge G & (source e == v) && (vlabel (target e) != c)}.
Proof.
  intros V T. apply /sigW.
  rewrite terminal_not_c // in T.
  revert T => /forallPn[e]. rewrite negb_imply => /andP[/eqP-Se /eqP-E].
  exists e. splitb; by apply /eqP.
Qed.

Lemma terminal_source (G : proof_structure) (v : G) :
  terminal v -> forall e, source e = v -> vlabel (target e) = c.
Proof.
  intros T e E.
  rewrite terminal_not_c in T.
  2:{ intro F. contradict E. by apply no_source_c. }
  revert T => /forallP/(_ e) /implyP-T.
  by apply /eqP; apply T; apply /eqP.
Qed.

Lemma terminal_cut (G : proof_structure) (v : G) (H : vlabel v = cut) :
  terminal v.
Proof.
  rewrite /terminal H.
  apply /forallP => e. apply /implyP => /eqP-E.
  contradict E.
  by apply no_source_cut.
Qed.

Lemma terminal_tens_parr (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  terminal v = (vlabel (target (ccl H)) == c).
Proof.
  transitivity [forall e, (source e == v) ==> (vlabel (target e) == c)].
  { rewrite /terminal. by destruct H as [-> | ->]. }
  destruct (vlabel (target (ccl H)) == c) eqn:C.
  - apply /forallP => e. apply /implyP => /eqP-E.
    enough (e = ccl H) by by subst e.
    by apply ccl_eq.
  - apply /negP => /forallP/(_ (ccl H))/implyP-P.
    rewrite ccl_e in P.
    revert C => /eqP-C. contradict C. apply /eqP.
    by apply P.
Qed.
Unset Mangle Names.
(* lemma : si exists node pas ax c, alors en existe un terminal *)
(* puis sinon, alors exists ax term *)

Lemma has_terminal (G : proof_net) : { v : G & terminal v }.
Proof.
  apply /sigW.
  apply (well_founded_induction (@well_founded_sigma _ _
    (fun v => vlabel v <> c) (@well_founded_dam _ _ G))).
  2:{ exact (exists_node G). }
  move => [v V] /= H.
  destruct (terminal v) eqn:T.
  { by exists v. }
  revert T => /negP/negP T.
  elim: (not_terminal V T) => {T} [e /andP[/eqP-? /eqP-E]]. subst v.
  apply (H (existT _ (target e) E)).
  rewrite /is_connected_strict /=.
  exists [:: e]. splitb.
Qed.
(*
Lemma has_terminal (G : proof_net) : { v : G & terminal v }.
Proof.
  apply /sigW.
  apply (well_founded_induction_sigma (@well_founded_dam _ _ (dam_of_ps G))
    (sig := fun v => vlabel v <> c) (P := fun=> exists v : G, terminal v)).
  2:{ exact (exists_node G). }
  move => [v V] /= H.
  destruct (terminal v) eqn:T.
  { by exists v. }
  revert T => /negP/negP T.
  elim: (not_terminal V T) => {T} [e /andP[/eqP-? /eqP-E]]. subst v.
  apply (H (existT _ (target e) E)).
  rewrite /is_connected_strict /=.
  exists [:: e]. splitb.
Qed.*)

Lemma descending_path (G : proof_net) :
  forall (s : G), vlabel s <> c ->
  { p : Walk s & terminal (path_target s (wval p)) }.
Proof.
  intros s S. apply /sigW.
  apply (well_founded_induction (@well_founded_sigma _ _
    (fun v => {w : Walk s & path_target s w = v /\ vlabel v <> c})
    (@well_founded_dam _ _ G))).
  2:{ by exists s, (Walk_nil _). }
  move => [v [W [V C]]] H.
  destruct (terminal v) eqn:T.
  { exists W. by rewrite V. }
  revert T => /negP/negP T.
  elim: (not_terminal C T) => {T} [e /andP[/eqP-Se /eqP-E]].
  revert W V H. move => [w /= /existsP/sigW[t W]] V H.
  destruct (walk_endpoint W) as [_ ?]. subst t.
  assert (We : [exists t, walk s t (rcons w e)]).
  { apply /existsP. exists (target e).
    rewrite walk_rcons Se -V. splitb. }
  assert (P : {p : Walk s & path_target s p = target e /\ vlabel (target e) <> c}).
  { exists {| wval := _ ; wvalK := We |}. simpl. splitb.
    by rewrite map_rcons last_rcons. }
  apply (H (existT _ (target e) P)).
  rewrite /is_connected_strict /=.
  exists [:: e]. splitb. by apply /eqP.
Qed.

(* Terminal node below the node s *)
Definition descending_node (G : proof_net) :
  forall (s : G), vlabel s <> c -> G :=
  fun s S => path_target s (wval (projT1 (descending_path S))).

Lemma descending_node_terminal (G : proof_net) (s : G) (S : vlabel s <> c) :
  terminal (descending_node S).
Proof. unfold descending_node. by destruct (descending_path _). Qed.

Lemma descending_node_walk (G : proof_net) (s : G) (S : vlabel s <> c) :
  { p & walk s (descending_node S) p }.
Proof.
  unfold descending_node. elim: (descending_path _) => [[p /= /existsP/sigW[t W]] _].
  enough (t = last s [seq target _1 | _1 <- p]) as <- by by exists p.
  by destruct (walk_endpoint W) as [_ <-].
Qed.

End Atoms.

Notation "'ν' X" := (var X) (at level 12).
Notation "'κ' X" := (covar X) (at level 12).
Infix "⊗" := tens (left associativity, at level 25). (* TODO other way to overload notations ? *)(* zulip *)
Infix "⅋" := parr (at level 40).
Notation "A ^" := (dual A) (at level 12, format "A ^").
Notation "⊢ l" := (ll l) (at level 70).
Notation base_graph := (graph (flat rule) (flat (formula * bool))).
Notation "r#| G |" := (rcard G) : nat_scope.
Infix "≃d" := iso_data (at level 79).
Notation p_ax_bool := (@p_ax_cut_bool _ false).
Notation p_cut_bool := (@p_ax_cut_bool _ true).
Notation p_tens_bool := (@p_tens_parr_bool _ false).
Notation p_parr_bool := (@p_tens_parr_bool _ true).
Notation p_ax_type := (@p_ax_cut_type _ false).
Notation p_cut_type := (@p_ax_cut_type _ true).
Notation p_tens_type := (@p_tens_parr_type _ false).
Notation p_parr_type := (@p_tens_parr_type _ true).


(* TODO list:
- specialize qu'on peut faire en move
- _ plus souvent
- transitivity à la place de assert
- refine (iso_correct _ _): a la place de prouver les hyp tout de suite
- utiliser wlog pour cas symétriques
- cbnb a utiliser, et switching_None et uconnected_simpl
- check if every lemma proved is useful / interesting
- check all names given not already used, from beginning
- homogene notations and spaces
- utiliser turns et turn pour homogeneiser plus de cas dans correction
- check at the end if all import are used
- see files bug_report
- psize and size of formula useless ?
- TOTHINK se passer de correct_weak ?
- TOTHINK fonction disant si formule atomique existe dans yalla, ajout possible pour expansion atome
- TOTHINK faire des sections pour chaque op de correct, et ainsi de suite ?
- TOTHINK graphes avec garbage pour ne pas faire de suppression et donc de sigma type
- utiliser unl et unr pour union graph plutot que inl et inr
- TOMAJ coq (dernière fois le 29/10/21)
- zulip pour pb
- plutot que des by by [] ou des by trivial, faire des change et des refine
- se passer des exists ?, true
- utiliser Theorem, Remark, Fact, Corollary, Proposition, Property ?
*)
(* TODO idées à tester :
  faire des nodes c indexes par des formules, et demander proper pour correspondance des formules
*)
(* TODO ajouter un fichier ac resultats sur mll pour casser ce fichier en 2 *)

(* TODO clearbody x to forget def of x but not type ! pour cacher preuve dans def !
warning makefile *)
