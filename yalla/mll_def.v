(* Unit-free MLL following Yalla schemas *)
(* Definition of proof nets and immediate results *)

From Coq Require Import Bool.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.
From HB Require Import structures.

From Yalla Require Export mll_prelim graph_more upath supath mgraph_dag.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
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

Lemma eqb_eq_rule (A B : rule) : eqb_rule A B <-> A = B.
Proof. by destruct A, B. Qed.

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
  repeat split.
  - by intros ? ? -> ? ? ->.
  - by intros [] [] [].
  - by intros [].
  - by intros [] [].
Qed.

HB.instance Definition rule_commMonoid :=
  ComMonoid_of_Setoid.Build (flat rule) rule_cm_laws. (* TODO essayer _ comme nom à la place *)



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

Lemma eqb_eq_form A B : eqb_form A B <-> A = B.
Proof.
revert B. induction A as [ | | ? IHA1 ? IHA2 | ? IHA1 ? IHA2]; intros [];
(split; intros Heq); inversion Heq as [H0]; auto.
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
Proof. by destruct A. Qed.

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
Lemma no_selfdual (A : formula) : dual A <> A.
Proof. by destruct A. Qed.

Lemma no_selftens_l A B : tens A B <> A.
Proof. revert B; induction A as [ | | ? H A ? | ] => ? Hc; inversion Hc. by apply (H A). Qed.

Lemma no_selftens_r A B : tens B A <> A.
Proof. revert B; induction A as [ | | A ? ? H | ] => ? Hc; inversion Hc. by apply (H A). Qed.

Lemma no_selfparr_l A B : parr A B <> A.
Proof. revert B; induction A as [ | | | ? H A ? ] => ? Hc; inversion Hc. by apply (H A). Qed.

Lemma no_selfparr_r A B : parr B A <> A.
Proof. revert B; induction A as [ | | | A ? ? H ] => ? Hc; inversion Hc. by apply (H A). Qed.

Ltac no_selfform := try (
                      apply no_selfdual || apply nesym, no_selfdual ||
                      apply no_selftens_l || apply nesym, no_selftens_l ||
                      apply no_selftens_r || apply nesym, no_selftens_r ||
                      apply no_selfparr_l || apply nesym, no_selfparr_l ||
                      apply no_selfparr_r || apply nesym, no_selfparr_r).



(** * MLL Proofs *)
(* As opposed to Yalla, we allow general axioms.
   This allows to sequentialize proof-nets with
   general axioms. *)
Inductive ll : list formula -> Type :=
(* | ax_r : forall X, ll [:: covar X; var X] *)
| ax_r : forall A, ll [:: dual A; A]
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
(* Proof of axiom expansion when only axiom on atoms. *)
Definition ax_exp A : ll [:: dual A; A].
Proof.
  induction A as [ | | A ? B ? | A ? B ?]; cbn.
  - apply (ax_r (var _)).
  - eapply ex_r ; [ | apply Permutation_Type_swap]. apply (ax_r (var _)).
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
(* To get the rule of a vertex      -> [vlabel]
          the formula of an edge    -> [flabel]
          if an edge is a left edge -> [llabel] *)

Lemma elabel_eq {G : base_graph} (e : edge G) : elabel e = (flabel e, llabel e).
Proof. unfold flabel, llabel. by destruct (elabel e). Qed.
(* TODO surjective_pairing is less usable ... *)
(* TODO to use instead of trickery to destruct elabel *)

(* In our case, isomorphisms are standard isomorphisms, i.e. they do not flip edges *)
Lemma iso_noflip (F G : base_graph) (h : F ≃ G) : h.d =1 xpred0.
Proof.
  hnf => e.
  destruct h as [? ? iso_d [? ? E]]; simpl; clear - E.
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
so that operations like adding a cut increase cardinality *)(*
Definition rcard (G : base_graph) := #|~: [set v : G | vlabel v == c]|.
Notation "r#| G |" := (rcard G) : nat_scope.*)

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
  forall (b : bool) (v : G), vlabel v = (if b then cut else ax) ->
  exists el er,
  el \in edges_at_outin b v /\ er \in edges_at_outin b v /\
  flabel el = dual (flabel er). (* TODO tout avec endpoint plutot que edges_at_outin ? *)

(** Applying the operation on formulae for tensor and parr nodes *)
Definition proper_tens_parr (G : base_graph) :=
  forall (b : bool) (v : G), vlabel v = (if b then ⅋ else ⊗) ->
  exists el er ec,
  el \in edges_at_in v /\ llabel el /\
  er \in edges_at_in v /\ ~llabel er /\
  ec \in edges_at_out v /\ flabel ec = (if b then parr else tens) (flabel el) (flabel er).

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
Lemma unique_left (G : proof_structure) (v : G) :
  vlabel v = ⊗ \/ vlabel v = ⅋ ->
  #|[set e in edges_at_in v | llabel e]| = 1.
Proof.
  move => Hl.
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
  cbnb; case_if.
  by symmetry; apply /eqP.
Qed.

Definition left {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :=
  pick_unique (unique_left H).
Definition left_tens (G : proof_structure) (v : G) (H : vlabel v = ⊗) :=
  left (or_introl H).
Definition left_parr (G : proof_structure) (v : G) (H : vlabel v = ⅋) :=
  left (or_intror H).

Lemma left_el (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  target (left H) = v /\ llabel (left H).
Proof.
  assert (Hl := pick_unique_in (unique_left H)).
  by revert Hl; rewrite !in_set => /andP[/eqP ? ?].
Qed.

Lemma left_e (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  target (left H) = v.
Proof. apply left_el. Qed.

Lemma left_l (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  llabel (left H).
Proof. apply left_el. Qed.

Lemma left_eset (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  left H \in edges_at_in v.
Proof.
  assert (Hl := pick_unique_in (unique_left H)).
  by revert Hl; rewrite !in_set => /andP[/eqP -> _].
Qed. (* TODO ça serait bien de se passer de ce genre de lemme redondant *)

Lemma left_eq (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) (e : edge G) :
  target e = v /\ llabel e -> e = left H.
Proof.
  intros [T ?].
  apply pick_unique_eq.
  rewrite !in_set T.
  splitb.
Qed.

(** Function right for the right premisse of a tens / parr *)
Lemma unique_right (G : proof_structure) (v : G) :
  vlabel v = ⊗ \/ vlabel v = ⅋ -> #|edges_at_in v| = 2.
Proof. move => [H | H]; by rewrite p_deg H. Qed.

Definition right {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :=
  other (unique_right H) (left_eset H).
Definition right_tens (G : proof_structure) (v : G) (H : vlabel v = ⊗) :=
  right (or_introl H).
Definition right_parr (G : proof_structure) (v : G) (H : vlabel v = ⅋) :=
  right (or_intror H).

Lemma right_e (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  target (right H) = v.
Proof.
  destruct (other_in_neq (unique_right H) (left_eset H)) as [Hr _].
  by revert Hr; rewrite in_set => /eqP-->.
Qed.

Lemma left_neq_right (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  left H <> right H.
Proof.
  destruct (other_in_neq (unique_right H) (left_eset H)) as [_ Hr].
  revert Hr => /eqP Hr.
  by apply nesym.
Qed.

Lemma right_set (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  edges_at_in v = [set left H; right H].
Proof. by rewrite (other_set (unique_right H) (left_eset H)). Qed.

Lemma right_l (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  ~~llabel (right H).
Proof.
  apply /negP => F.
  assert (R : right H \in [set e in edges_at_in v | llabel e])
    by (rewrite !in_set right_e; splitb).
  revert R; rewrite (pick_unique_set (unique_left H)) in_set => /eqP.
  apply nesym, left_neq_right.
Qed.

Lemma right_eq (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) (e : edge G) :
  target e = v /\ ~llabel e -> e = right H.
Proof.
  move => [T R].
  apply pick_unique_eq.
  rewrite !in_set T.
  splitb.
  apply /eqP => ?; subst e.
  contradict R.
  apply left_l.
Qed.

Lemma right_eq2 (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) (e : edge G) :
  target e = v /\ e <> left H -> e = right H.
Proof.
  move => [T /eqP-?].
  apply pick_unique_eq.
  rewrite !in_set T.
  splitb.
Qed. (* TODO changer ce nom *)
(* TODO check if all these properties are useful or not *)

(** Function ccl for the conclusion of a tens / parr *)
Lemma unique_ccl (G : proof_structure) (v : G) :
  vlabel v = ⊗ \/ vlabel v = ⅋ -> #|edges_at_out v| = 1.
Proof. move => [H | H]; by rewrite p_deg H. Qed.

Definition ccl {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :=
  pick_unique (unique_ccl H).
Definition ccl_tens (G : proof_structure) (v : G) (H : vlabel v = ⊗) :=
  ccl (or_introl H).
Definition ccl_parr (G : proof_structure) (v : G) (H : vlabel v = ⅋) :=
  ccl (or_intror H).

Lemma p_ccl (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  ccl H \in edges_at_out v.
Proof. apply pick_unique_in. Qed.

Lemma ccl_e (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  source (ccl H) = v.
Proof.
  assert (Hv := p_ccl H).
  rewrite in_set in Hv; by apply /eqP.
Qed.

Lemma ccl_set (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  edges_at_out v = [set ccl H].
Proof. apply pick_unique_set. Qed.

Lemma ccl_eq (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) (e : edge G) :
  source e = v -> e = ccl H.
Proof.
  intros He.
  assert (Hv : e \in edges_at_out v) by by rewrite in_set He.
  by revert Hv; rewrite ccl_set // in_set => /eqP ->.
Qed.

(** Unique arrow of a conclusion *)
Lemma unique_concl (G : proof_structure) (v : G) :
  vlabel v = c -> #|edges_at_in v| = 1.
Proof. move => H; by rewrite p_deg H. Qed.

Definition edge_of_concl {G : proof_structure} {v : G} (H : vlabel v = c) :=
  pick_unique (unique_concl H).

Lemma p_concl (G : proof_structure) (v : G) (H : vlabel v = c) :
  edge_of_concl H \in edges_at_in v.
Proof. apply pick_unique_in. Qed. (* TODO use directly pick_unique for such lemmas? *)

Lemma concl_e (G : proof_structure) (v : G) (H : vlabel v = c) :
  target (edge_of_concl H) = v.
Proof.
  assert (Hv := p_concl H).
  rewrite in_set in Hv; by apply /eqP.
Qed.

Lemma concl_set (G : proof_structure) (v : G) (H : vlabel v = c) :
  edges_at_in v = [set edge_of_concl H].
Proof. apply pick_unique_set. Qed.

Lemma concl_eq (G : proof_structure) (v : G) (H : vlabel v = c) (e : edge G) :
  target e = v -> e = edge_of_concl H.
Proof.
  intros He.
  assert (Hv : e \in edges_at_in v) by by rewrite in_set He.
  revert Hv. by rewrite concl_set // in_set => /eqP ->.
Qed.

(** Other edge of an axiom *)
Lemma pre_proper_ax (G : proof_structure) (v : G) (Hl : vlabel v = ax) :
  #|edges_at_out v| = 2.
Proof. by rewrite p_deg Hl. Qed.

Definition other_ax (G : proof_structure) (e : edge G) (H : vlabel (source e) = ax) : edge G :=
  other (pre_proper_ax H) (source_in_edges_at_out e).

Lemma other_ax_e (G : proof_structure) (e : edge G) (H : vlabel (source e) = ax) :
  source (other_ax H) = source e.
Proof.
  destruct (other_in_neq (pre_proper_ax H) (source_in_edges_at_out e)) as [Hr _].
  by revert Hr; rewrite in_set => /eqP-->.
Qed.

Lemma other_ax_neq (G : proof_structure) (e : edge G) (H : vlabel (source e) = ax) :
  other_ax H <> e.
Proof.
  destruct (other_in_neq (pre_proper_ax H) (source_in_edges_at_out e)) as [_ Hr].
  by revert Hr => /eqP-?.
Qed.

Lemma other_ax_set (G : proof_structure) (e : edge G) (H : vlabel (source e) = ax) :
  edges_at_out (source e) = [set e; other_ax H].
Proof. apply other_set. Qed.

Lemma other_ax_eq (G : proof_structure) (e : edge G) (H : vlabel (source e) = ax) (a : edge G) :
  source a = source e /\ a <> e -> a = other_ax H.
Proof.
  intros [Ha Ha'].
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

Lemma other_cut_e (G : proof_structure) (e : edge G) (H : vlabel (target e) = cut) :
  target (other_cut H) = target e.
Proof.
  destruct (other_in_neq (pre_proper_cut H) (target_in_edges_at_in e)) as [Hr _].
  by revert Hr; rewrite in_set => /eqP-->.
Qed.

Lemma other_cut_neq (G : proof_structure) (e : edge G) (H : vlabel (target e) = cut) :
  other_cut H <> e.
Proof.
  destruct (other_in_neq (pre_proper_cut H) (target_in_edges_at_in e)) as [_ Hr].
  by revert Hr => /eqP-?.
Qed.

Lemma other_cut_set (G : proof_structure) (e : edge G) (H : vlabel (target e) = cut) :
  edges_at_in (target e) = [set e; other_cut H].
Proof. apply other_set. Qed.

Lemma other_cut_eq (G : proof_structure) (e : edge G) (H : vlabel (target e) = cut) (a : edge G) :
  target a = target e /\ a <> e -> a = other_cut H.
Proof.
  intros [Ha Ha'].
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

Lemma other_ax_flabel (G : proof_structure) (e : edge G) (H : vlabel (source e) = ax) :
  flabel (other_ax H) = (flabel e)^.
Proof. symmetry. apply /eqP. apply p_ax_bis. Qed.

Lemma other_cut_flabel (G : proof_structure) (e : edge G) (H : vlabel (target e) = cut) :
  flabel (other_cut H) = (flabel e)^.
Proof. symmetry. apply /eqP. apply p_cut_bis. Qed.

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
Lemma p_ax_cut_bool (G : proof_structure) (b : bool) (v : G) :
  vlabel v = (if b then cut else ax) ->
  [exists el : edge G, exists er : edge G,
  (el \in edges_at_outin b v) && (er \in edges_at_outin b v)
  && (flabel el == dual (flabel er))].
Proof.
  intro V.
  destruct (p_ax_cut V) as [el [er [El [Er F]]]].
  apply /existsP; exists el. apply /existsP; exists er.
  splitb; by apply /eqP.
Qed.
Notation p_ax_bool := (@p_ax_cut_bool _ false).
Notation p_cut_bool := (@p_ax_cut_bool _ true).

Lemma p_tens_parr_bool (G : proof_structure) (b : bool) (v : G) :
  vlabel v = (if b then ⅋ else ⊗) ->
  [exists el : edge G, exists er : edge G, exists ec : edge G,
  (el \in edges_at_in v) && llabel el &&
  (er \in edges_at_in v) && ~~llabel er &&
  (ec \in edges_at_out v) && (flabel ec == (if b then parr else tens) (flabel el) (flabel er))].
Proof.
  intro V.
  destruct (p_tens_parr V) as [el [er [ec [El [Ll [Er [Lr [Ec Lc]]]]]]]].
  apply /existsP; exists el. apply /existsP; exists er. apply /existsP; exists ec.
  splitb; (by apply /negP) || (by apply /eqP).
Qed.
Notation p_tens_bool := (@p_tens_parr_bool _ false).
Notation p_parr_bool := (@p_tens_parr_bool _ true).

(** p_ax_cut and p_tens_parr in Type instead of Prop *)
Lemma p_ax_cut_type (G : proof_structure) (b : bool) (v : G) :
  vlabel v = (if b then cut else ax) ->
  {'(el, er) & endpoint b el = v /\ endpoint b er = v /\ flabel el = dual (flabel er)}.
Proof.
  intro V.
  assert (H := p_ax_cut_bool V).
  revert H => /existsP/sigW[e /existsP/sigW[e' /andP[/andP[E E'] /eqP-?]]].
  revert E E'. rewrite !in_set => /eqP-E /eqP-E'.
  by exists (e, e').
Qed.
Notation p_ax_type := (@p_ax_cut_type _ false).
Notation p_cut_type := (@p_ax_cut_type _ true).

Lemma p_tens_parr_type (G : proof_structure) (b : bool) (v : G) :
   vlabel v = (if b then ⅋ else ⊗) ->
  {'(el, er, ec) & target el = v /\ llabel el /\ target er = v /\ ~~llabel er
  /\ source ec = v /\ flabel ec = (if b then parr else tens) (flabel el) (flabel er)}.
Proof.
  intro V.
  assert (H := p_tens_parr_bool V).
  revert H => /existsP/sigW[el /existsP/sigW[er /existsP/sigW[ec
    /andP[/andP[/andP[/andP[/andP[El Ll] Er] Lr] Ec] /eqP-F]]]].
  revert El Er Ec. rewrite !in_set => /eqP-El /eqP-Er /eqP-Ec.
  by exists (el, er, ec).
Qed.
Notation p_tens_type := (@p_tens_parr_type _ false).
Notation p_parr_type := (@p_tens_parr_type _ true).

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

Lemma one_target_c (G : proof_structure) (e : edge G) :
  vlabel (target e) = c -> forall f, target f = target e -> f = e.
Proof. intros H ? ?. transitivity (edge_of_concl H); [ | symmetry]; by apply concl_eq. Qed.

Lemma one_source_tensparr (G : proof_structure) (e : edge G) :
  vlabel (source e) = ⊗ \/ vlabel (source e) = ⅋ ->
  forall f, source f = source e -> f = e.
Proof. intros H ? ?. transitivity (ccl H); [ | symmetry]; by apply ccl_eq. Qed.
Lemma one_source_tens (G : proof_structure) (e : edge G) :
  vlabel (source e) = ⊗ -> forall f, source f = source e -> f = e.
Proof. intros. apply one_source_tensparr; caseb. Qed.
Lemma one_source_parr (G : proof_structure) (e : edge G) :
  vlabel (source e) = ⅋ -> forall f, source f = source e -> f = e.
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
Lemma sub_formula_reflexivity A:
  sub_formula A A.
Proof. destruct A; caseb. Qed.

Lemma sub_formula_transitivity A B C :
  sub_formula A B -> sub_formula B C -> sub_formula A C.
Proof.
  revert A B.
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

Lemma sub_formula_antisymmetry A B :
  sub_formula B A -> sub_formula A B -> A = B.
Proof.
  revert B; induction A as [a | a | Al HAl Ar HAr | Al HAl Ar HAr] => B.
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


(** Isomorphism between graph_data *)
Set Primitive Projections.
Record iso_data (F G : graph_data) :=
  Iso_order {
    iso_of :> F ≃ G;
    order_iso : order G = [seq iso_of.e e | e <- order F]
  }.
Unset Primitive Projections.
Infix "≃d" := iso_data (at level 79).


(* About axiom expansion in proof structures and proof nets *)
(* (Positive) Formula associated to an axiom or cut node *)
Definition ax_cut_formula_edge (G : proof_structure) :=
  fun (b : bool) (v : G) (V : vlabel v = if b then cut else ax) =>
  let (e, e') := projT1 (p_ax_cut_type V) in match flabel e with
  | var _ | tens _ _ => e
  | _ => e'
  end.

Definition ax_cut_formula (G : proof_structure) :=
  fun (b : bool) (v : G) (V : vlabel v = if b then cut else ax) =>
   flabel (ax_cut_formula_edge V).
Notation ax_formula := (@ax_cut_formula _ false).
Notation cut_formula := (@ax_cut_formula _ true).

(* A proof net is ax_atomic if all its axiom are on atomic formulae *)
Definition is_atomic (A : formula) :=
  if A is var _ then True else False.

Definition ax_atomic (G : proof_structure) :=
  forall (v : G) (V : vlabel v = ax), is_atomic (ax_formula V).

End Atoms.

Notation "'ν' X" := (var X) (at level 12).
Notation "'κ' X" := (covar X) (at level 12).
Infix "⊗" := tens (left associativity, at level 25). (* TODO other way to overload notations ? *)(* zulip *)
Infix "⅋" := parr (at level 40).
Notation "A ^" := (dual A) (at level 12, format "A ^").
Notation "⊢ l" := (ll l) (at level 70).
Notation base_graph := (graph (flat rule) (flat (formula * bool))).
(* Notation "r#| G |" := (rcard G) : nat_scope. *)
Infix "≃d" := iso_data (at level 79).
Notation p_ax_bool := (@p_ax_cut_bool _ _ false).
Notation p_cut_bool := (@p_ax_cut_bool _ _ true).
Notation p_tens_bool := (@p_tens_parr_bool _ _ false).
Notation p_parr_bool := (@p_tens_parr_bool _ _ true).
Notation p_ax_type := (@p_ax_cut_type _ _ false).
Notation p_cut_type := (@p_ax_cut_type _ _ true).
Notation p_tens_type := (@p_tens_parr_type _ _ false).
Notation p_parr_type := (@p_tens_parr_type _ _ true).
Notation ax_formula_edge := (@ax_cut_formula_edge _ _ false).
Notation cut_formula_edge := (@ax_cut_formula_edge _ _ true).
Notation ax_formula := (@ax_cut_formula _ _ false).
Notation cut_formula := (@ax_cut_formula _ _ true).

Ltac no_selfform := try (
                      apply no_selfdual || apply nesym, no_selfdual ||
                      apply no_selftens_l || apply nesym, no_selftens_l ||
                      apply no_selftens_r || apply nesym, no_selftens_r ||
                      apply no_selfparr_l || apply nesym, no_selfparr_l ||
                      apply no_selfparr_r || apply nesym, no_selfparr_r).


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
- see files bug_report, then once they are exploitable go to the zulip's channel of Graph Theory
- psize and size of formula useless ?
- TOTHINK se passer de correct_weak ?
- TOTHINK fonction `atomic` disant si formule atomique existe dans yalla
- TOTHINK faire des sections pour chaque op de correct, et ainsi de suite ?
- TOTHINK graphes avec garbage pour ne pas faire de suppression et donc de sigma type
- utiliser unl et unr pour union graph plutot que inl et inr
- TOMAJ coq (dernière fois le 07/23)
- zulip pour pb
- plutot que des by by [] ou des by trivial, faire des change et des refine
- se passer des exists ?, true
- use Theorem, Remark, Fact, Corollary, Proposition, Property?
- clearbody x to forget def of x but not type! pour cacher preuve dans def !
- utiliser walk_edge (et en faire un uwalk idem)
*)
(* TODO idées à tester :
  faire des nodes c indexes par des formules, et demander proper pour correspondance des formules
*)

(* TODO
- ax_atomic à faire avec la séquentialisation en expansant les axiomes à la volée avec
  deseq(seq(R)) = ax-exp(R) OU atomes généreaux dans séquents OU gax de Yalla
- lemmes "évidents" de ssreflect dans mll_prelim : aller sur le canal ssreflect de zulip
pour demander si cette série de lemma est déjà dans la lib, ou si je peux faire une push request pour ça
- r#|_| -> to remove? in comments for the moment
*)

