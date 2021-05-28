(* Unit-free MLL following Yalla schemas *)
(* Definition of proof nets and basic results *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
From mathcomp Require Import all_ssreflect zify.
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.
From HB Require Import structures.

From Yalla Require Export graph_more mll_prelim.

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

Lemma eqb_eq_rule : forall A B, eqb_rule A B = true <-> A = B.
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
  ComMonoid_of_Setoid.Build (flat rule) rule_cm_laws. (* TODO warning equalite avec instance de unit ? typage *)


(** * Set with 3 elements to make cases on tens, parr and cut *)
Inductive trilean :=
  | tens_t
  | parr_t
  | cut_t.



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
  apply /eqP; case_if;
  rewrite codual //.
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

Ltac no_selfform := try apply no_selfdual;
                    try apply no_selftens_l;
                    try apply no_selftens_r;
                    try apply no_selfparr_l;
                    try apply no_selfparr_r.



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
Proof. now subst. Qed. (* TODO psize useless ? *)



(** * Graph that we will consider *)
Notation base_graph := (graph (flat rule) (flat formula)). (* [flat] is used for isomorphisms *)

(* In our case, isometries are standard isometries; i.e. they do not flip edges *)
Lemma iso_noflip (F G : base_graph) (h : F ≃ G) : h.d =1 xpred0.
Proof.
  hnf => e.
  destruct h as [? ? iso_d [? ? E]]; cbn; clear - E.
  specialize (E e).
  by destruct (iso_d e).
Qed.




(** ** Stratum 0: Multigraphs from the library GraphTheory *)


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
  fun v => match [pick x in edges_at_in v :\ left v] with
  | Some e => e
  | None => bogus v
  end.

(** Function [ccl] returning an out-edge *)
Definition ccl {G : graph_left} : G -> edge G :=
  fun v => match [pick x in edges_at_out v] with
  | Some e => e
  | None => bogus v
  end.

(** Function [edge_of_concl] returning an in-edge *)
Definition edge_of_concl {G : graph_left} : G -> edge G :=
  fun v => match [pick x in edges_at_in v] with
  | Some e => e
  | None => bogus v
  end.


(* Picking an out or in edge if it exists *)
Definition pick_edge_at {G : graph_left} : G -> edge G :=
  fun (v : G) =>
  match [pick x in edges_at_out v :|: edges_at_in v] with
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
  forall (b : bool) (v : G), #|edges_at_outin b v| = deg b (vlabel v).

Definition proper_left (G : graph_data) :=
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  left v \in edges_at_in v.

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
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ -> #|edges_at_in v| = 2.
Proof. intros v [Hl | Hl]; by rewrite p_deg Hl. Qed.

Lemma right_o (G : geos) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  right v = other (unique_right H) (p_left H).
Proof.
  intros v H; unfold right.
  replace (edges_at_in v :\ left v) with
    ([set left v; other (unique_right H) (p_left H)] :\ left v)
    by by rewrite -(other_set (unique_right H) (p_left H)).
  rewrite set2D1 ?pick1 //. by apply other_in_neq.
Qed.

Lemma p_right (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  right v \in edges_at_in v /\ right v != left v.
Proof. intros. rewrite right_o. apply other_in_neq. Qed.

Lemma right_e (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  target (right v) = v.
Proof.
  intros v Hv.
  assert (H := p_right Hv).
  revert H; rewrite in_set; by move => [/eqP -> _].
Qed.

Lemma right_set (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  edges_at_in v = [set left v; right v].
Proof. intros. rewrite right_o. apply other_set. Qed.

Lemma right_eq (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  forall (e : edge G), target e = v /\ e <> left v -> e = right v.
Proof.
  intros ? ? ? [<- ?].
  rewrite right_o. apply other_eq; by rewrite // in_set.
Qed.


(** Function ccl for the conclusion of a tens / parr *)
Lemma unique_ccl (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  #|edges_at_out v| = 1.
Proof. intros v [Hl | Hl]; by rewrite p_deg Hl. Qed.

Lemma ccl_o (G : geos) :
  forall (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋),
  ccl v = pick_unique (unique_ccl H).
Proof.
  intros v H; unfold ccl.
  assert ([pick x in edges_at_out v] = [pick x in [set pick_unique (unique_ccl H)]])
    as -> by by rewrite -(pick_unique_set (unique_ccl H)).
  by rewrite pick1.
Qed.

Lemma p_ccl (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  ccl v \in edges_at_out v.
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
  edges_at_out v = [set ccl v].
Proof. intros. rewrite ccl_o. apply pick_unique_set. Qed.

Lemma ccl_eq (G : geos) :
  forall (v : G), vlabel v = ⊗ \/ vlabel v = ⅋ ->
  forall (e : edge G), source e = v -> e = ccl v.
Proof.
  intros v Hv e He.
  assert (H : e \in edges_at_out v) by by rewrite in_set He.
  revert H. by rewrite ccl_set // in_set => /eqP ->.
Qed.


(** Function returning the unique (input) edge of a conclusion *)
Lemma unique_concl (G : geos) :
  forall (v : G), vlabel v = concl_l ->
  #|edges_at_in v| = 1.
Proof. intros v Hl; by rewrite p_deg Hl. Qed.

Lemma edge_of_concl_o (G : geos) :
  forall (v : G) (H : vlabel v = concl_l),
  edge_of_concl v = pick_unique (unique_concl H).
Proof.
  intros v H; unfold edge_of_concl.
  assert ([pick x in edges_at_in v] = [pick x in [set pick_unique (unique_concl H)]])
    as -> by by rewrite -(pick_unique_set (unique_concl H)).
  by rewrite pick1.
Qed.

Lemma p_concl (G : geos) :
  forall (v : G), vlabel v = concl_l -> edge_of_concl v \in edges_at_in v.
Proof. intros. rewrite edge_of_concl_o. apply pick_unique_in. Qed.

Lemma concl_e (G : geos) :
  forall (v : G), vlabel v = concl_l -> target (edge_of_concl v) = v.
Proof.
  intros v Hv.
  assert (H := p_concl Hv).
  rewrite in_set in H; by apply /eqP.
Qed.

Lemma concl_set (G : geos) :
  forall (v : G), vlabel v = concl_l -> edges_at_in v = [set edge_of_concl v].
Proof. intros. rewrite edge_of_concl_o. apply pick_unique_set. Qed.

Lemma concl_eq (G : geos) :
  forall (v : G), vlabel v = concl_l ->
  forall (e : edge G), target e = v -> e = edge_of_concl v.
Proof.
  intros v Hv e He.
  assert (H : e \in edges_at_in v) by by rewrite in_set He.
  revert H. by rewrite concl_set // in_set => /eqP ->.
Qed.


(** Other edge of an axiom *)
Lemma pre_proper_ax (G : geos) (v : G) (Hl : vlabel v = ax) :
  #|edges_at_out v| = 2.
Proof. by rewrite p_deg Hl. Qed.

Definition other_ax (G : geos) (e : edge G) (H : vlabel (source e) = ax) : edge G :=
  other (pre_proper_ax H) (source_in_edges_at_out e).

Lemma other_ax_in_neq (G : geos) (e : edge G) (H : vlabel (source e) = ax) :
  source (other_ax H) = source e /\ other_ax H != e.
Proof.
  unfold other_ax.
  destruct (other_in_neq (pre_proper_ax H) (source_in_edges_at_out e)) as [Hd0 Hd1].
  by revert Hd0; rewrite in_set => /eqP ->.
Qed.

Lemma other_ax_set (G : geos) (e : edge G) (H : vlabel (source e) = ax) :
  edges_at_out (source e) = [set e; other_ax H].
Proof. apply other_set. Qed.

Lemma other_ax_eq (G : geos) (e : edge G) (H : vlabel (source e) = ax) :
  forall (a : edge G), source a = source e /\ a <> e -> a = other_ax H.
Proof.
  intros a [Ha Ha'].
  assert (Hin : a \in edges_at_out (source e)) by by rewrite in_set Ha.
  revert Hin.
  by rewrite other_ax_set !in_set => /orP [/eqP ? | /eqP ->].
Qed.


(** Other edge of a cut *)
Lemma pre_proper_cut (G : geos) (v : G) (Hl : vlabel v = cut) :
  #|edges_at_in v| = 2.
Proof. by rewrite p_deg Hl. Qed.

Definition other_cut (G : geos) (e : edge G) (H : vlabel (target e) = cut) : edge G :=
  other (pre_proper_cut H) (target_in_edges_at_in e).

Lemma other_cut_in_neq (G : geos) (e : edge G) (H : vlabel (target e) = cut) :
  target (other_cut H) = target e /\ other_cut H != e.
Proof.
  unfold other_cut.
  destruct (other_in_neq (pre_proper_cut H) (target_in_edges_at_in e)) as [Hd0 Hd1].
  by revert Hd0; rewrite in_set => /eqP ->.
Qed.

Lemma other_cut_set (G : geos) (e : edge G) (H : vlabel (target e) = cut) :
  edges_at_in (target e) = [set e; other_cut H].
Proof. apply other_set. Qed.

Lemma other_cut_eq (G : geos) (e : edge G) (H : vlabel (target e) = cut) :
  forall (a : edge G), target a = target e /\ a <> e -> a = other_cut H.
Proof.
  intros a [Ha Ha'].
  assert (Hin : a \in edges_at_in (target e)) by by rewrite in_set Ha.
  revert Hin. by rewrite other_cut_set !in_set => /orP [/eqP ? | /eqP ->].
Qed.


(** Always an out or in edge *)
Lemma pick_edge_at_some : forall (G : geos), forall (v : G),
  pick_edge_at v \in edges_at_out v :|: edges_at_in v.
Proof.
  intros G v.
  unfold pick_edge_at.
  case: pickP; trivial.
  intro Hc. exfalso.
  assert (#|edges_at_out v| = 0 /\ #|edges_at_in v| = 0) as [Hcout Hcin].
  { enough (#|edges_at_out v| <= 0 /\ #|edges_at_in v| <= 0) by lia.
    assert (Hu : #|edges_at_out v :|: edges_at_in v| = 0) by by apply eq_card0.
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
  (el \in edges_at_outin b v) && (er \in edges_at_outin b v) &&
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
(* TODO notations ? *)

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
  assert (#|edges_at_in (source e)| <> 0 /\ #|edges_at_out (source e)| <> 0) as [? ?].
  { split; intro Hc;
    assert (Hf' : e \in set0) by (by rewrite -(cards0_eq Hc) in_set Hf);
    contradict Hf'; by rewrite in_set. }
  destruct (vlabel (source e)) eqn:Hl; try by [];
  [assert (Hd := p_tens Hl) | assert (Hd := p_parr Hl)]; cbn in Hd.
  all: contradict Hd.
  all: assert (e = ccl (source e)) as <- by (apply ccl_eq; caseb).
  all: assert (Hdir : e \in edges_at_in (source e)) by by rewrite in_set Hf.
  all: revert Hdir; rewrite right_set ?in_set; [ | caseb] => /orP[/eqP <- | /eqP <-].
  all: apply nesym; no_selfform.
Qed.



(** ** Stratum 5: Proof Net *)
(** ** Correctness Criteria: Danos-Regnier *)
(** Identify all premises of a ⅋ node *)
Definition switching {G : graph_left} : edge G -> option (edge G) :=
  fun e => Some (if vlabel (target e) == ⅋ then left (target e) else e).

(** Paths in the left switching graph *)
Definition switching_left {G : graph_left} : edge G -> option (edge G) :=
  fun e => if vlabel (target e) == ⅋ then if e == left (target e) then None else Some e else Some e.

(* All switching graphs have the same number of connected components:
   any one is connected iff the graph where we remove all lefts is connected *)
Definition correct (G : graph_left) := uacyclic (@switching G) /\ uconnected (@switching_left G).


Set Primitive Projections.
Record proof_net : Type :=
  Proof_net {
    ps_of :> proof_structure;
    p_correct : correct ps_of;
  }.
Unset Primitive Projections.



Lemma switching_eq (G : geos) :
  forall (a b : edge G), switching a = switching b -> target a = target b.
Proof.
  intros a b. unfold switching => /eqP; cbn => /eqP.
  case_if.
  all: try assert (vlabel (target a) = ⅋) by by apply /eqP.
  all: try assert (vlabel (target b) = ⅋) by by apply /eqP.
  - rewrite -(left_e (v := target a)) -1?(left_e (v := target b)); caseb.
    by f_equal.
  - subst b.
    rewrite left_e; caseb.
  - rewrite left_e; caseb.
Qed.

Lemma switching_None (G : graph_left) :
  forall (p : @upath _ _ G), None \notin [seq switching e.1 | e <- p].
Proof. intro p. by induction p. Qed.

Lemma switching_left_sinj {G : graph_left} :
  {in ~: (@switching_left G) @^-1 None &, injective switching_left}.
Proof.
  move => x y; rewrite !in_set => /eqP X /eqP Y /eqP In; apply /eqP; revert X Y In.
  unfold switching_left; case_if.
Qed.

Lemma uconnected_simpl {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :
  {in ~: f @^-1 None &, injective f} ->
  (exists p, (uwalk s t p) && (None \notin [seq f e.1 | e <- p])) ->
  exists _ : Supath f s t, true.
Proof.
  move => F [p /andP[W N]]; revert s t W N; induction p as [ | e p IH] => s t.
  { move => /eqP <- {t}.
    by exists (supath_nil f s). }
  move => /andP[/eqP <- W] {s} /norP[n N].
  revert IH => /(_ _ _ W N) {W N p} [q _].
  assert (P : supath f (usource e) (utarget e) (e :: nil)).
  { rewrite /supath !in_cons /= orb_false_r. splitb. }
  set p := {| upval := _ ; upvalK := P |}.
  remember (upath_disjoint f p q) as b eqn:D; symmetry in D.
  destruct b.
  { by exists (supath_cat D). }
  destruct q as [q Q].
  revert D; rewrite /upath_disjoint disjoint_sym disjoint_has /p has_sym /= orb_false_r
    => /negPn /mapP [[a b] In Hea].
  assert (a = e.1).
  { assert (a \in ~: f @^-1 None /\ e.1 \in ~: f @^-1 None) as [A E].
    { rewrite !in_set -Hea.
      by revert n => /eqP n; apply nesym in n; revert n => /eqP ->. }
    by apply (F _ _ A E). }
  subst a; clear Hea.
  apply in_elt_sub in In. destruct In as [l [r ?]]; subst q.
  destruct (supath_subKK Q) as [_ R], e as [e c]; cbn in *.
  destruct (eq_comparable b c); [subst b | ].
  * by exists {| upval := _ ; upvalK := R |}.
  * assert (b = ~~c) by by destruct b, c. subst b.
    revert R. rewrite /supath map_cons in_cons /=.
    move => /andP[/andP[/andP[_ W] /andP[_ U]] /norP[_ N]].
    assert (R : supath f (endpoint (~~ c) e) t r) by splitb.
    by exists {| upval := _ ; upvalK := R |}.
Qed. (* TODO dans graph_more si on garde cette version + verif que les autres fichiers marchent tj *)

(* AVEC 
Lemma uconnected_simpl {G : graph_left} (s t : G) :
  (exists p, (uwalk s t p) && (None \notin [seq switching_left e.1 | e <- p])) ->
  exists _ : Supath switching_left s t, true.
Proof.
  move => [p /andP[W N]]; revert s t W N; induction p as [ | e p IH] => s t.
  - move => /eqP <- {t}.
    by exists (supath_nil switching_left s).
  - move => /andP[/eqP <- W] {s} /norP[n N].
    revert IH => /(_ _ _ W N) {W N p} [q _].
    assert (P : supath switching_left (usource e) (utarget e) (e :: nil)).
    { rewrite /supath !in_cons /= orb_false_r. splitb. }
    set p := {| upval := _ ; upvalK := P |}.
    remember (upath_disjoint switching_left p q) as b eqn:D; symmetry in D.
    destruct b.
    + by exists (supath_cat D).
    + destruct q as [q Q].
      revert D. rewrite /upath_disjoint disjoint_sym disjoint_has /p has_sym /= orb_false_r.
      move => /negPn /mapP [[a b] In Hea].
      assert (a = e.1).
      { revert Hea n => /eqP. unfold switching_left; case_if. }
      subst a; clear Hea.
      apply in_elt_sub in In. destruct In as [l [r ?]]; subst q.
      destruct (supath_subKK Q) as [_ R], e as [e c]; cbn in *.
      destruct (eq_comparable b c); [subst b | ].
      * by exists {| upval := _ ; upvalK := R |}.
      * assert (b = ~~c) by by destruct b, c. subst b.
        revert R. rewrite /supath map_cons in_cons /=.
        move => /andP[/andP[/andP[_ W] /andP[_ U]] /norP[_ N]].
        assert (R : supath switching_left (endpoint (~~ c) e) t r) by splitb.
        by exists {| upval := _ ; upvalK := R |}.
Qed.
*)


(** ** Isomorphism for each strata *)
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
  left_iso: forall v, vlabel v = ⊗ \/ vlabel v = ⅋ -> left (iso_of v) = iso_of.e (left v) }.
Unset Primitive Projections.
Infix "≃l" := iso_left (at level 79).

Definition iso_left_id G : G ≃l G.
Proof. by exists (@iso_id _ _ G). Defined.

Definition iso_left_sym F G : F ≃l G -> G ≃l F.
Proof.
  move => f.
  exists (iso_sym f) => *.
  apply /eqP. by rewrite -bij_eqLR -left_iso -?(vlabel_iso f) bijK'.
Defined.

Definition iso_left_comp F G H : F ≃l G -> G ≃l H -> F ≃l H.
Proof.
  move => f g.
  exists (iso_comp f g) => *.
  by rewrite !left_iso // vlabel_iso.
Defined.

Global Instance iso_left_Equivalence: CEquivalence iso_left.
Proof. constructor. exact @iso_left_id. exact @iso_left_sym. exact @iso_left_comp. Defined.


Lemma iso_switching (F G : graph_left) (h : F ≃l G) :
  forall e, switching (h.e e) = option_map h.e (switching e).
Proof.
  intro e; cbnb.
  rewrite /switching !endpoint_iso iso_noflip vlabel_iso; cbn.
  case_if.
  apply left_iso. by right; apply /eqP.
Qed.

Lemma iso_switching_left (F G : graph_left) (h : F ≃l G) :
  forall e, switching_left (h.e e) = option_map h.e (switching_left e).
Proof.
  intro e.
  rewrite /switching_left !endpoint_iso iso_noflip vlabel_iso; cbn.
  case_if.
  - enough (e = left (target e)) by by [].
    apply /eqP; rewrite -(bij_eq (f := h.e)) //; apply /eqP.
    rewrite -left_iso //. by right; apply /eqP.
  - enough (h.e (left (target e)) = left (h (target (left (target e))))) by by [].
    replace (left (target e)) with e in * at 2.
    rewrite left_iso //. by right; apply /eqP.
Qed.


Lemma iso_path_switchingK (F G : graph_left) (h : F ≃l G) : forall p s t,
  supath switching s t p -> supath switching (h s) (h t) (iso_path h p).
Proof.
  move => p s t /andP[/andP[W U] N]. splitb.
  - by apply iso_walk.
  - rewrite -map_comp /comp; cbn.
    replace [seq switching (h.e x.1) | x <- p] with [seq option_map h.e (switching x.1) | x <- p]
      by (apply eq_map; move => *; by rewrite iso_switching).
    rewrite /switching map_comp map_inj_uniq // in U.
    by rewrite /= map_comp map_inj_uniq // map_comp map_inj_uniq.
  - apply switching_None.
Qed.

Definition iso_path_switching (F G : graph_left) (h : F ≃l G) (s t : F) :
  Supath switching s t -> Supath switching (h s) (h t) :=
  fun p => {| upval := _ ; upvalK := iso_path_switchingK h (upvalK p) |}.

Lemma iso_path_switching_inj (F G : graph_left) (h : F ≃l G) :
  forall s t, injective (@iso_path_switching _ _ h s t).
Proof.
  move => s t [p P] [q Q] /eqP; cbn; move => /eqP Heq; cbnb.
  revert Heq; apply inj_map => [[e b] [f c]] /eqP; cbn => /andP[/eqP Heq /eqP ->].
  apply /eqP; splitb; cbn; apply /eqP.
  revert Heq. by apply bij_injective.
Qed.

Lemma iso_path_nil (F G : graph_left) (h : F ≃l G) :
  forall (s : F), iso_path_switching h (supath_nil switching s) = supath_nil switching (h s).
Proof. intros. by apply /eqP. Qed.

Lemma iso_path_switching_leftK (F G : graph_left) (h : F ≃l G) : forall p s t,
  supath switching_left s t p -> supath switching_left (h s) (h t) (iso_path h p).
Proof.
  move => p s t /andP[/andP[W U] N].
 splitb.
  - by apply iso_walk.
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
    all: unfold switching_left; case_if.
    all: replace (left (target e)) with e in *.
    all: by enough (Hd : vlabel (target e) == ⅋) by by contradict Hd; apply /negP.
  - rewrite -map_comp /comp; cbn.
    apply /(nthP None). move => [n Hc] Hf.
    rewrite size_map in Hc.
    enough (nth None [seq switching_left x.1 | x <- p] n = None).
    { contradict N; apply /negP/negPn/(nthP None). rewrite size_map. by exists n. }
    revert Hf.
    rewrite !(nth_map (forward (left s)) None) // iso_switching_left.
    unfold switching_left; case_if.
Qed.

Definition iso_path_switching_left (F G : graph_left) (h : F ≃l G) (s t : F) :
  Supath switching_left s t -> Supath switching_left (h s) (h t) :=
  fun p => {| upval := _ ; upvalK := iso_path_switching_leftK h (upvalK p) |}.

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
Proof. exists (@iso_left_id G). by rewrite map_id. Defined.

Definition iso_data_sym F G : F ≃d G -> G ≃d F.
Proof.
  move => f.
  exists (iso_left_sym f).
  rewrite -(map_id (order F)) (order_iso f) -map_comp /=.
  apply eq_map => v /=.
  by rewrite bijK.
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
Abort.

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



(** TEST: Equivalence classes of uconnected, so to speak about connected components *)
(* TODO mis ici car on a besoin d'hypotheses sur f : ça marche pour switching_left mais pas pour switching
-> ajouter cette hypothese (f injective sauf avec None) et mettre dans graph_more, idem pour uconnected_simpl
+ mettre des notations ici pour ne pas à avoir à donner la preuve d'injectivité *)
Section Finite.

Lemma upath_size {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  p : supath f s t p -> size p < S #|edge G|.
Proof.
  move => /andP[/andP[_ U] _].
  rewrite map_comp in U.
  apply map_uniq in U.
  revert U => /card_uniqP U.
  rewrite size_map in U.
  rewrite -U.
  exact: max_card.
Qed.

Definition Supath_tuple {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : Supath f s t) : {n : 'I_(S #|edge G|) & n.-tuple (edge G * bool)} :=
  let (p, Up) := p in existT _ (Ordinal (upath_size Up)) (in_tuple p).
Definition tuple_Supath {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (m : {n : 'I_(S #|edge G|) & n.-tuple (edge G * bool)}) : option (Supath f s t) :=
  let (_, p) := m in match boolP (supath f s t p) with
  | AltTrue P => Some (Sub (val p) P)
  | AltFalse _ => None
  end.
Lemma Supath_tupleK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :
  pcancel (@Supath_tuple _ _ _ _ f s t) (tuple_Supath f s t).
Proof.
  move => [/= p P].
  case: {-}_ / boolP; last by rewrite P.
  by move => P'; rewrite (bool_irrelevance P' P).
Qed.

Definition Supath_finMixin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in PcanFinMixin (@Supath_tupleK _ _ _ _ f s t).
Canonical Supath_finType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in FinType (Supath f s t) (Supath_finMixin f s t).

End Finite.

Definition is_uconnected {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (x y : G) :=
  [exists p : Supath f x y, true].

Definition is_uconnected_id {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (x : G) :
  is_uconnected f x x.
Proof. apply /existsP. by exists (supath_nil _ _). Defined.

Definition is_uconnected_sym {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (x y : G) :
  is_uconnected f x y -> is_uconnected f y x.
Proof. move => /existsP[P _]. apply /existsP. by exists (supath_rev P). Defined.


(* AVEC switching_left
Infix "▬" := (is_uconnected switching_left) (at level 70).
(*TODO f qui gene pour une notation propre + level mis au pif*)

Definition is_uconnected_comp {G : graph_left} (x y z : G) :
  x ▬ y -> y ▬ z -> x ▬ z.
Proof.
  move => /existsP[[pxy /andP[/andP[Wxy _] Nxy]] _] /existsP[[pyz /andP[/andP[Wyz _] Nyz]] _].
  apply /existsP; apply uconnected_simpl.
  exists (pxy ++ pyz). splitb.
  - by apply (uwalk_cat Wxy).
  - rewrite map_cat mem_cat. splitb.
Defined.

Global Instance is_uconnected_Equivalence {G : graph_left}: CEquivalence (is_uconnected (@switching_left G)).
Proof. constructor. exact (is_uconnected_id _). exact (is_uconnected_sym (f := _)). exact (@is_uconnected_comp _). Defined.

Lemma is_uconnected_equivalence {G : graph_left} :
  {in [set: G] & &, equivalence_rel (is_uconnected switching_left)}.
Proof.
  intros x y z _ _ _.
  split; [apply is_uconnected_id | ].
  intro Pxy.
  remember (y ▬ z) as b eqn:Pyz; symmetry in Pyz. destruct b.
  - by apply (is_uconnected_comp Pxy).
  - remember (x ▬ z) as c eqn:Pxz; symmetry in Pxz. destruct c; trivial.
    contradict Pyz; apply not_false_iff_true.
    exact (is_uconnected_comp (is_uconnected_sym Pxy) Pxz).
Qed.

Lemma is_uconnected_partition {G : graph_left} :
  partition (equivalence_partition (is_uconnected switching_left) [set: G]) [set: G].
Proof. exact (@equivalence_partitionP _ _ _ is_uconnected_equivalence). Qed.

Definition uconnected_nb (G : graph_left) :=
  #|equivalence_partition (is_uconnected switching_left) [set: G]|.

Definition switching_left_edges (G : graph_left) :=
  setT :\: [set left v | v in G & vlabel v == ⅋].
*)

Definition is_uconnected_comp {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} ->
  forall (x y z : G), is_uconnected f x y -> is_uconnected f y z -> is_uconnected f x z.
Proof.
  move => F x y z /existsP[[pxy /andP[/andP[Wxy _] Nxy]] _] /existsP[[pyz /andP[/andP[Wyz _] Nyz]] _].
  apply /existsP; apply uconnected_simpl; trivial.
  exists (pxy ++ pyz). splitb.
  - by apply (uwalk_cat Wxy).
  - rewrite map_cat mem_cat. splitb.
Defined.

Global Instance is_uconnected_Equivalence {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) : CEquivalence (is_uconnected f).
Proof. constructor. exact (is_uconnected_id _). exact (is_uconnected_sym (f := _)). exact (is_uconnected_comp F). Defined.

Lemma is_uconnected_equivalence {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} ->
  {in [set: G] & &, equivalence_rel (is_uconnected f)}.
Proof.
  intros F x y z _ _ _.
  split; [apply is_uconnected_id | ].
  intro Pxy.
  remember (is_uconnected f y z) as b eqn:Pyz; symmetry in Pyz. destruct b.
  - by apply (is_uconnected_comp F Pxy).
  - remember (is_uconnected f x z) as c eqn:Pxz; symmetry in Pxz. destruct c; trivial.
    contradict Pyz; apply not_false_iff_true.
    exact (is_uconnected_comp F (is_uconnected_sym Pxy) Pxz).
Qed.

Lemma is_uconnected_eq {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> forall u v w, is_uconnected f u v ->
  is_uconnected f u w = is_uconnected f v w.
Proof.
  move => F u v w UV.
  destruct (is_uconnected f v w) eqn:VW.
  - apply (is_uconnected_comp F UV VW).
  - destruct (is_uconnected f u w) eqn:UW; trivial.
    enough (is_uconnected f v w) as <- by trivial.
    apply is_uconnected_sym in UV.
    apply (is_uconnected_comp F UV UW).
Qed.

Lemma is_uconnected_partition {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} ->
  partition (equivalence_partition (is_uconnected f) [set: G]) [set: G].
Proof. intros. by refine (@equivalence_partitionP _ _ _ (is_uconnected_equivalence _)). Qed.

Definition uconnected_nb {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :=
  #|equivalence_partition (is_uconnected f) [set: G]|.

Definition switching_left_edges (G : graph_left) :=
  setT :\: [set left v | v in G & vlabel v == ⅋].

Lemma uconnected_to_nb1 {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> #|G| <> 0 -> uconnected f -> uconnected_nb f = 1.
Proof.
  move => F N C.
  destruct (set_0Vmem [set: G]) as [Hc | [v _]].
  { contradict N. by rewrite -cardsT Hc cards0. }
  unfold uconnected_nb, equivalence_partition.
  apply /eqP/cards1P.
  exists ([set u in [set: G] | is_uconnected f v u]).
  apply /eqP/eq_set1P. split.
  { apply /imsetP. by exists v. }
  move => ? /imsetP [u _ ?]; subst.
  apply eq_finset => w.
  rewrite in_setT /=.
  enough (is_uconnected f u w /\ is_uconnected f v w) as [-> ->] by trivial.
  split; apply /existsP; apply C.
Qed.

Lemma uconnected_from_nb1 {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> uconnected_nb f = 1 -> uconnected f.
Proof.
  move => F /eqP/cards1P; move => [S /eqP/eq_set1P [Sin Seq]] u v.
  assert (Suin : [set w in [set: G] | is_uconnected f u w] \in
    equivalence_partition (is_uconnected f) [set: G]).
  { apply /imsetP. by exists u. }
  assert (UW := Seq _ Suin). cbn in UW. subst S.
  assert (Svin : [set w in [set: G] | is_uconnected f v w] \in
    equivalence_partition (is_uconnected f) [set: G]).
  { apply /imsetP. by exists v. }
  assert (Heq := Seq _ Svin). cbn in Heq. clear - F Heq.
  assert (V : v \in [set w in [set: G] | is_uconnected f v w]).
  { rewrite in_set. splitb. apply is_uconnected_id. }
  rewrite Heq in_set in V.
  by revert V => /andP[_ /existsP ?].
Qed.

Unset Mangle Names.
(** Both visions of a set as set or subset have the same cardinal *)
Lemma card_set_subset {T : finType} (P : pred T) :
  #|[finType of {e : T | P e}]| = #|[set e | P e]|.
Proof. by rewrite card_sig cardsE. Qed. (* TODO dans prelim *)
Definition neighbours {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G) :=
  [set target e | e in ~: f @^-1 None :&: edges_at_out v] :|: [set source e | e in ~: f @^-1 None :&: edges_at_in v].
Lemma neighbours_nb {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G) :
  uacyclic f ->
  #|neighbours f v| = #|~: f @^-1 None :&: edges_at v|.
Proof.
 (* Début de preuve avec [set endpoint b e | b in setT, e in ~: f @^-1 None :&: edges_at v] :\ v. *)
(*   move => A.
  rewrite -!card_set_subset.
  assert (Hg : forall u : [finType of {u : G | (u \notin [set v]) &&
    (u \in [set endpoint b e | b in [set: bool_finType], e in ~: f @^-1 None :&: edges_at v])}],
    exists e, [exists b, (val u == endpoint b e) && ((e \in ~: f @^-1 None) && (e \in edges_at v))]).
  { move => [u U]. assert (U' := U).
    rewrite !in_set curry_imset2X in U'.
    revert U' => /andP[/eqP Hv /imsetP/sig2_eqW [[b e]]]; rewrite in_set in_setI /=
      => /andP[_ /andP[? ?]] /eqP ?.
    exists e; apply /existsP; exists b. splitb. }
  assert (Hh : forall (e : [finType of {e : edge G | (e \in ~: f @^-1 None) && (e \in edges_at v)}]),
    exists b, (endpoint b (val e) \notin [set v]) && (endpoint b (val e) \in
    [set endpoint c a | c in [set: bool_finType], a in ~: f @^-1 None :&: edges_at v])).
  { admit. }
  eapply bij_card_eq.
  Unshelve.
  2:{ move => u. assert (T := (Hg u)). revert T => /sigW [e /existsP/sigW [? /andP[_ He]]].
      exact (Sub e He). }
  cbn.
  eapply (Bijective).
  Unshelve.
  3:{ move => e. assert (T := Hh e). revert T => /sigW [b He].
      exact (Sub (endpoint b (val e)) He). }
  all: cbn.
  - move => [u U].
    destruct (sigW _); destruct (sigW _); destruct (sigW _); destruct (elimTF _).
    cbnb.
     *)
(* uacyclic pour contrer les selfloops *)
Admitted.

Lemma uacyclic_uconnected_nb {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  uconnected_nb f + #|~: f @^-1 None| = #|G|.
Proof.
  remember (#|G|) as n eqn:N; symmetry in N.
  revert G N f; induction n as [ | n IH] => G N f F A.
  { rewrite -cardsT in N. apply cards0_eq in N.
    rewrite /uconnected_nb N /equivalence_partition imset0 cards0.
    enough (#|~: f @^-1 None| <= 0) by lia.
    enough (#|edge G| = 0) as <- by apply max_card.
    apply eq_card0 => e.
    enough (H : source e \in set0) by by rewrite in_set in H.
    by rewrite -N. }
  destruct (set_0Vmem [set: G]) as [Hc | [v _]].
  { contradict N. by rewrite -cardsT Hc cards0. }
  set G' := induced (setT :\ v).
  set f' : edge G' -> option I := fun e => f (val e).
  assert (N' : #|G'| = n).
  { enough (#|G'| = #|G| - 1) as -> by (rewrite N; lia).
    rewrite card_set_subset cardsE -cardsT (cardsD1 v [set: G]) in_setT. lia. }
  assert (F' : {in ~: f' @^-1 None &, injective f'}).
  { move => [u U] [w W]; rewrite !in_set /f' /= => /eqP Fu /eqP Fw Eq. cbnb.
    by apply F; rewrite // !in_set; apply /eqP. }
  assert (A' : uacyclic f').
  { move => [x X] [p' P']. cbnb.
    assert (P : supath f x x [seq (val e.1, e.2) | e <- p']).
    { revert P' => /andP[/andP[W ?] ?].
      splitb.
      - enough (H : forall x y X Y, uwalk (Sub x X : G') (Sub y Y) p' ->
          uwalk x y [seq (val _0.1, _0.2) | _0 <- p']) by by apply (H _ _ _ _ W).
        clear; induction p' as [ | [[? ?] ?] ? IH];
        move => // ? ? ? ?; cbnb => /andP[? W].
        splitb. apply (IH _ _ _ _ W).
      - by rewrite -map_comp.
      - by rewrite -map_comp. }
    specialize (A _ {| upval := _ ; upvalK := P |}).
    revert A => /eqP; cbn => /eqP A.
    by destruct p'. }
  specialize (IH G' N' f' F' A').
  assert (#|~: f' @^-1 None| = #|~: f @^-1 None :\: edges_at v|).
  { rewrite -!card_set_subset.
    assert (Sube : forall e, e \notin edges_at v = (e \in edge_set ([set: G] :\ v))).
    { move => e.
      rewrite !in_set /incident.
      apply (sameP existsPn), iff_reflect; split.
      - move => *; splitb.
      - by move => /andP[/andP[? _] /andP[? _]] []. }
    assert (Ine : forall e (E : e \in edge_set ([set: G] :\ v)),
      e \in ~: f @^-1 None = (Sub e E \notin f' @^-1 None)).
    { move => *. by rewrite !in_set /f' SubK. }
    assert (Hg : forall (e : [finType of {_0 : edge G' | _0 \notin f' @^-1 None}]),
      (val (val e) \notin edges_at v) && (val (val e) \in ~: f @^-1 None)).
    { intros [[e E] He]. rewrite Sube Ine. splitb. }
    set g : [finType of {_0 : edge G' | _0 \notin f' @^-1 None}] ->
      [finType of {_0 : edge G | (_0 \notin edges_at v) && (_0 \in ~: f @^-1 None)}] :=
      fun e => Sub (val (val e)) (Hg e).
    apply (bij_card_eq (f := g)).
    assert (Hg' : forall (e : [finType of {_0 : edge G | (_0 \notin edges_at v) && (_0 \in ~: f @^-1 None)}]),
      val e \in edge_set ([set: G] :\ v)).
    { move => [e E]. rewrite SubK -Sube. by revert E => /andP[? _]. }
    assert (Hg'' : forall (e : [finType of {_0 : edge G | (_0 \notin edges_at v) && (_0 \in ~: f @^-1 None)}]),
      (Sub (val e) (Hg' e) \notin f' @^-1 None)).
    { move => [e E]. rewrite -Ine SubK. by revert E => /andP[_ ?]. }
    set g' : [finType of {_0 : edge G | (_0 \notin edges_at v) && (_0 \in ~: f @^-1 None)}] ->
      [finType of {_0 : edge G' | _0 \notin f' @^-1 None}] :=
      fun e => Sub (Sub (val e) (Hg' e)) (Hg'' e).
    apply (Bijective (g := g')); move => *; cbnb. }
  assert (uconnected_nb f' + 1 = uconnected_nb f + #|~: f @^-1 None :&: edges_at v|).
  { set S := [set w | is_uconnected f v w].
    assert (Hr : equivalence_partition (is_uconnected f) setT =
      [set [set w | is_uconnected f u w] | u : G & u \notin S] :|:
      [set [set w | is_uconnected f u w] | u : G & u \in S]).
    { rewrite /equivalence_partition -imsetU memKset setUC setUCr.
      apply eq_imset => u. apply eq_finset => w. by rewrite in_set. }
    rewrite /uconnected_nb Hr {Hr}.
    assert (Hr : equivalence_partition (is_uconnected f') setT =
      [set [set w | is_uconnected f' u w] | u : G' & val u \notin S] :|:
      [set [set w | is_uconnected f' u w] | u : G' & val u \in S]).
    { rewrite /equivalence_partition -imsetU setUC.
      replace [set u : G' | val u \notin S] with (~: [set u : G' | val u \in S])
        by by apply /setP => ?; rewrite !in_set.
      rewrite setUCr.
      apply eq_imset => u. apply eq_finset => w. by rewrite in_set. }
    rewrite Hr {Hr}.
    assert (is_uconnected_to' : forall (u w : G'), is_uconnected f' u w -> is_uconnected f (val u) (val w)).
    { move => [u U] [w W] /existsP [[q Q] _].
      rewrite !SubK. apply /existsP.
      enough (uwalk u w [seq (val e.1, e.2) | e <- q] &&
        (None \notin [seq f e.1 | e <- [seq (val e.1, e.2) | e <- q]])).
      { assert (Q' : exists q', uwalk u w q' && (None \notin [seq f e.1 | e <- q']))
          by by exists [seq (val e.1, e.2) | e <- q].
        assert (Hd := uconnected_simpl F Q').
        by revert Hd => /sigW [? _]. }
      revert Q; clear => /andP[/andP[Wq _]] Nq.
      revert u U Wq; induction q as [ | [[e E] b] q IHq] => u U.
      { move => ?. splitb. }
      move => /= /andP[wq Wq]; revert wq; cbnb => ?.
      revert Nq; rewrite /= !in_cons /f' SubK => /norP[nq Nq].
      revert IHq => /(_ Nq _ _ Wq) /andP[Wq' Nq'].
      splitb. }
    assert (is_uconnectedf' : forall (u w : G'), val u \notin S ->
      is_uconnected f' u w = is_uconnected f (val u) (val w)).
    { move => [u U] [w W]. cbnb; rewrite in_set => /existsPn /= Hu.
      destruct (is_uconnected f u w) eqn:UW.
      - revert UW => /existsP [[p P] _].
        revert u U Hu P; induction p as [ | e p IHp] => u U Hu P.
        { revert P => /andP[/andP[/eqP ? _] _]; subst w.
          rewrite (eq_irrelevance U W).
          apply /existsP. by exists (supath_nil _ _). }
        revert P => /andP[/andP[/= /andP[/eqP ? Wp] /andP[up Up]]];
        rewrite in_cons => /norP[/eqP np Np]; subst u.
        assert (P' : supath f (utarget e) w p) by splitb.
        assert (U' : utarget e \in [set: G] :\ v).
        { rewrite !in_set. splitb.
          apply /eqP => Hc.
          enough (Pc : supath f v (usource e) [:: (e.1, ~~e.2)]) by by specialize (Hu {| upval := _ ; upvalK := Pc |}).
          rewrite /supath in_cons /= negb_involutive Hc orb_false_r. splitb. by apply /eqP. }
        assert (Hu' : Supath f v (utarget e) -> false).
        { move => [q /andP[/andP[Wq _ ] Nq]].
          enough (Supath f v (usource e)) by by apply Hu.
          enough (Hd : exists _ : Supath f v (usource e), true) by by revert Hd => /sigW [? _].
          apply (uconnected_simpl F).
          exists (rcons q (e.1, ~~e.2)).
          rewrite uwalk_rcons /= negb_involutive map_rcons mem_rcons in_cons. splitb. by apply /eqP. }
        specialize (IHp _ U' Hu' P').
        revert IHp => /existsP [[q /andP[/andP[Wq _ ] Nq]] _] {Hu' P'}.
        apply /existsP. apply (uconnected_simpl F').
        assert (E : e.1 \in edge_set ([set: G] :\ v)).
        { clear - U U'. revert U U'; rewrite !in_set => /andP[? _] /andP[? _].
          destruct e as [e []]; splitb. }
        exists ((Sub e.1 E, e.2) :: q).
        cbn. rewrite !SubK.
        assert (Hr : (Sub (endpoint e.2 (sval (Sub e.1 E))) (induced_proof _ (valP (Sub e.1 E)))) =
          (Sub (utarget e) U' : G')) by cbnb.
        rewrite Hr {Hr}.
        splitb. by apply /eqP.
      - destruct (is_uconnected f' (Sub u U) (Sub w W)) eqn:UW'; trivial.
        assert (Hc := is_uconnected_to' _ _ UW').
        rewrite !SubK in Hc. by rewrite Hc in UW. }
    assert (Hr : [set [set w | is_uconnected f' u w] | u : G' & val u \notin S] =
      [set [set w | is_uconnected f (val u) (val w)] | u : G' & val u \notin S]).
    { apply eq_in_imset => u. rewrite in_set => Hu. apply eq_finset => w. by apply is_uconnectedf'. }
    rewrite Hr {Hr} !cardsU.
    assert (Hr : [set [set w | is_uconnected f (val u) (val w)] | u : G' & val u \notin S]
      :&: [set [set w | is_uconnected f' u w] | u : G' & val u \in S] = set0).
    { apply disjoint_setI0. apply /disjointP => ? /imsetP [u U] ? /imsetP [w W]; subst.
      revert U; rewrite in_set => U.
      revert W; rewrite !in_set => W.
      move => /setP /(_ u). rewrite !in_set is_uconnected_id => Hc.
      symmetry in Hc. apply is_uconnected_sym in Hc.
      rewrite is_uconnectedf' // in Hc.
      apply is_uconnected_sym in Hc.
      contradict U; apply /negP/negPn.
      rewrite !in_set.
      apply (is_uconnected_comp F W Hc). }
    rewrite Hr {Hr} cards0.
    assert (Hr : [set [set w | is_uconnected f u w] | u : G & u \notin S]
      :&: [set [set w | is_uconnected f u w] | u : G & u \in S] = set0).
    { apply disjoint_setI0. apply /disjointP => ? /imsetP [u U] ? /imsetP [w W]; subst.
      revert U W; rewrite !in_set => U W.
      move => /setP /(_ u). rewrite !in_set is_uconnected_id => Hc.
      symmetry in Hc.
      contradict U; apply /negP/negPn.
      apply (is_uconnected_comp F W Hc). }
    rewrite Hr {Hr} cards0.
    assert (Hr : #|[set [set w : G' | is_uconnected f (val u) (val w)] | u : G' & val u \notin S]| =
      #|[set [set w | is_uconnected f u w] | u : G & u \notin S]|).
    { rewrite -card_sig -[in RHS]card_sig.
      assert (Hg : forall (E : sig_finType (pred_of_set
        [set [set w : G' | is_uconnected f (val u) (val w)] | u : G' & val u \notin S])),
        [set val u | u in val E] \in [set [set w | is_uconnected f u w] | u : G & u \notin S]).
      { move => [E HE].
        assert (HE' := HE). revert HE' => /imsetP/sig2_eqW [u Hu ?]; subst E.
        rewrite in_set in Hu. rewrite SubK.
        assert ([set val u0 | u0 in [set w : G' | is_uconnected f (val u) (val w)]]
          = [set w | is_uconnected f (val u) w]) as ->.
        { transitivity [set val w | w : G' & is_uconnected f (val u) (val w)]; [by apply eq_imset | ].
          apply /setP => w.
          rewrite in_set.
          destruct (is_uconnected f (val u) w) eqn:UW; apply /imsetP.
          - assert (W : w \in [set: G] :\ v).
            { rewrite !in_set. splitb.
              apply /eqP => ?; subst w.
              contradict Hu; apply /negP/negPn.
              rewrite in_set.
              by apply is_uconnected_sym. }
            exists (Sub w W); rewrite ?in_set; cbnb.
          - move => [[w' ?]].
            rewrite in_set SubK => Hc ?; subst w'.
            by rewrite Hc in UW. }
        apply /imsetP.
        exists (val u); by rewrite // in_set. }
      set g : sig_finType (pred_of_set
        [set [set w | is_uconnected f (val u) (val w)] | u : G' & val u \notin S]) ->
        sig_finType (pred_of_set [set [set w | is_uconnected f u w] | u : G & u \notin S]) :=
        fun E => Sub [set val u | u in val E] (Hg E).
      apply (bij_card_eq (f := g)).
      assert (Hh : forall u : G, u \in [set u | u \notin S] -> [set w | is_uconnected f u (val w)] \in
        [set [set w : G' | is_uconnected f (val u0) (val w)] | u0 : G' & val u0 \notin S]).
      { move => u Hu.
        rewrite in_set in Hu.
        apply /imsetP.
        assert (U : u \in [set: G] :\ v).
        { rewrite !in_set. splitb.
          apply /eqP => ?; subst u.
          contradict Hu; apply /negP/negPn.
          rewrite in_set.
          apply is_uconnected_id. }
        exists (Sub u U); by rewrite 1?in_set SubK. }
      assert (Hh' : forall E : sig_finType (pred_of_set [set [set w | is_uconnected f u w] | u : G & u \notin S]),
        {u : G | u \in [set u | u \notin S] & val E = [set w | is_uconnected f u w]}).
      { move => [E HE].
        assert (HE' := HE).
        revert HE' => /imsetP/sig2_eqW [u ? ?].
        by exists u. }
      set h : sig_finType (pred_of_set [set [set w | is_uconnected f u w] | u : G & u \notin S])
        -> sig_finType (pred_of_set [set [set w | is_uconnected f (val u) (val w)] |
        u : G' & val u \notin S]) :=
        fun E => let (u, Hu, _) := Hh' E in Sub [set w | is_uconnected f u (val w)] (Hh u Hu).
      apply (Bijective (g := h)).
      - move => E.
        unfold h. destruct (Hh' (g E)) as [u U Hu].
        destruct E as [E HE]; cbnb.
        revert Hu. rewrite /g !SubK.
        revert HE => /imsetP[[w W] Hw ?]; subst E.
        rewrite !SubK.
        move => /setP /(_ u).
        rewrite !in_set is_uconnected_id.
        move => /imsetP [[x X]]; rewrite in_set SubK => WU ?; subst x.
        f_equal; apply /setP; move => {X} [x X].
        rewrite !in_set !SubK.
        apply is_uconnected_eq; trivial.
        by apply is_uconnected_sym.
      - move => E.
        unfold h. destruct (Hh' E) as [u U Hu].
        destruct E as [E HE]; cbnb.
        rewrite SubK in Hu; subst E.
        f_equal; apply /setP => w.
        rewrite in_set.
        destruct (is_uconnected f u w) eqn:UW.
        + apply /imsetP.
          assert (W : w \in [set: G] :\ v).
          { rewrite !in_set. splitb.
            apply /eqP => ?; subst w.
            contradict U; apply /negP.
            rewrite !in_set negb_involutive.
            by apply is_uconnected_sym. }
          exists (Sub w W); [ | cbnb].
          by rewrite in_set SubK.
        + apply /imsetP. move => [[x X]]. rewrite in_set SubK => UX ?; subst x.
          by rewrite UX in UW. }
    rewrite Hr {Hr}.
    assert ([set [set w | is_uconnected f u w] | u : G & u \in S] = [set S]) as ->.
    { apply /setP => E.
      rewrite !in_set.
      remember (E == S) as b eqn:B; symmetry in B. destruct b; revert B => /eqP B.
      - subst E.
        apply /imsetP.
        exists v; trivial.
        rewrite !in_set.
        apply is_uconnected_id.
      - apply /imsetP; move => [u].
        rewrite !in_set => VU ?.
        contradict B; subst E.
        apply /setP => w.
        rewrite !in_set.
        remember (is_uconnected f v w) as b eqn:VW; symmetry in VW. destruct b.
        + apply is_uconnected_sym in VU.
          exact (is_uconnected_comp F VU VW).
        + remember (is_uconnected f u w) as b eqn:UW; symmetry in UW. destruct b; trivial.
          enough (is_uconnected f v w) as <- by trivial.
          exact (is_uconnected_comp F VU UW). }
    rewrite cards1.
    enough (#|[set [set w | is_uconnected f' u w] | u : G' & val u \in S]| = #|neighbours f v|) as ->
      by by rewrite neighbours_nb //; lia.
    rewrite -card_sig -[in RHS]card_sig.
    assert (Hg : forall E : sig_finType (pred_of_set [set [set w | is_uconnected f' u w] | u : G' & val u \in S]),
      { u : G' | val u \in neighbours f v & val E = [set w : G' | is_uconnected f' u w]}).
    { move => [E HE]. rewrite SubK.
      revert HE => /imsetP/sig2_eqW [[u U] VU ?]; subst E.
      rewrite !in_set SubK in VU.
      revert VU => /existsP/sigW [[p /andP[/andP[Wp Up] Np]] _].
(* TODO ici, il ne faut pas prendre ce w là : il faut prendre comme e la 1ère arète sur le chemin
de u vers v touchant v *)
      destruct p as [ | e p].
      { revert Wp => /eqP ?; subst u.
        contradict U; apply /negP.
        rewrite !in_set. caseb. }
      revert Wp => /= /andP[/eqP Es Wp].
      revert Up => /= /andP[Ep Up].
      revert Np; rewrite /= in_cons => /norP[/eqP En Np].
      set w := utarget e.
      assert (P : supath f w u p) by splitb.
      clear Wp Up Np.
      assert (W : w \in [set: G] :\ v).
      { rewrite /w !in_set. splitb.
        apply /eqP => Hc.
        assert (Pe : supath f v v [:: e]).
        { rewrite /supath /= Es -Hc in_cons orb_false_r. splitb. by apply /eqP. }
        specialize (A _ {| upval := _ ; upvalK := Pe |}).
        contradict A. cbnb. }
      exists (Sub w W).
      + rewrite SubK !in_set.
        destruct e as [e []]; rewrite /w /=; apply /orP; [left | right];
        apply imset_f; rewrite !in_set Es; splitb; by apply /eqP; apply nesym.
      + apply /setP => x.
        rewrite !in_set.
        apply is_uconnected_eq; trivial. clear x.
(* TODO utiliser le fait que v ne soit pas dans e chemin, puis comme /notin S *)
(*
        revert P; induction p as [ | a p IHp] => P.
        { revert P => /andP[/andP[/eqP ? _] _]; subst u.
          rewrite (eq_irrelevance U W).
          apply /existsP. by exists (supath_nil _ _). }
        revert P => /andP[/andP[/= /andP[/eqP Ha Wp] /andP[up Up]]];
        rewrite in_cons => /norP[/eqP np Np]; subst w.
        assert (P' : supath f (utarget a) u p) by splitb.
        revert Ep; rewrite /= in_cons => /norP[/eqP ? Ep].
        assert (U' : utarget a \in [set: G] :\ v).
        { rewrite !in_set. splitb.
          apply /eqP => Hc.
          enough (Pc : supath f v v [:: e; a]).
          { specialize (A _ {| upval := _ ; upvalK := Pc |}). contradict A; cbnb. }
          rewrite /supath /= !in_cons !orb_false_r Hc Es Ha. splitb; by apply /eqP. }
        specialize (IHp Ep).
        revert IHp => /existsP [[q /andP[/andP[Wq _ ] Nq]] _] {Hu' P'}.
        apply /existsP. apply (uconnected_simpl F').
        assert (E : e.1 \in edge_set ([set: G] :\ v)).
        { clear - U U'. revert U U'; rewrite !in_set => /andP[? _] /andP[? _].
          destruct e as [e []]; splitb. }
        exists ((Sub e.1 E, e.2) :: q).
        cbn. rewrite !SubK.
        assert (Hr : (Sub (endpoint e.2 (sval (Sub e.1 E))) (induced_proof _ (valP (Sub e.1 E)))) =
          (Sub (utarget e) U' : G')) by cbnb.
        rewrite Hr {Hr}.
        splitb. by apply /eqP.

        apply /existsP.
        assert (P : supath f w u p) by splitb.
        by exists ({|upval := _ ; upvalK := P|}).
        
      assert (WU : is_uconnected f w u).
      { apply /existsP.
        by exists ({|upval := _ ; upvalK := P|}). }
        Check is_uconnected_to'.
        rewrite !SubK in Hc. by rewrite Hc in UW. }
        rewrite !is_uconnectedf' !SubK.
Search (_ _ \in (imset _ _)).
          apply map_f.
        
      
*)
admit. }
    set g : sig_finType (pred_of_set [set [set w | is_uconnected f' u w] | u : G' & val u \in S]) ->
      sig_finType (pred_of_set (neighbours f v)) := fun E => let (u, U, _) := Hg E in exist _ (val u) U.
    apply (bij_card_eq (f := g)).
    assert (Hh : forall u : sig_finType (pred_of_set (neighbours f v)), val u \in [set: G] :\ v).
    { move => [u U].
      rewrite SubK !in_set. splitb. apply /eqP => Huv.
      enough (exists (e : edge G), source e = target e /\ None <> f e) as [e [Ce Ne]].
      { assert (Pe : supath f (source e) (target e) [:: forward e]).
        { rewrite /supath /= in_cons orb_false_r. splitb. by apply /eqP. }
        rewrite Ce in Pe.
        specialize (A _ {| upval := _ ; upvalK := Pe |}).
        contradict A; cbnb. }
      assert (Hu : u \in neighbours f v) by by []. clear U.
      revert Hu; rewrite in_set => /orP [/imsetP[e] | /imsetP[e]].
      all: rewrite !in_set => /andP[/eqP Ne /eqP E] E'; apply nesym in Ne.
      all: exists e; splitb.
      all: by rewrite E -E' Huv. }
    assert (Hh' : forall u : sig_finType (pred_of_set (neighbours f v)),
      [set w | is_uconnected f' (Sub (val u) (Hh u)) w] \in [set [set w | is_uconnected f' u0 w]
      | u0 : G' & val u0 \in S]).
    { move => u.
      apply /imsetP.
      exists (Sub (val u) (Hh u)); trivial.
      destruct u as [u U].
      rewrite !in_set !SubK.
      assert (Hu : u \in neighbours f v) by by []. clear U.
      apply /existsP.
      revert Hu; rewrite in_set => /orP [/imsetP[e] | /imsetP[e]].
      all: rewrite !in_set => /andP[/eqP Ne /eqP E] E'; apply nesym in Ne.
      - assert (Pe : supath f v u [:: forward e]).
        { rewrite /supath /= in_cons orb_false_r E E'. splitb. by apply /eqP. }
        by exists {| upval := _ ; upvalK := Pe |}.
      - assert (Pe : supath f v u [:: backward e]).
        { rewrite /supath /= in_cons orb_false_r E E'. splitb. by apply /eqP. }
        by exists {| upval := _ ; upvalK := Pe |}. }
    set h : sig_finType (pred_of_set (neighbours f v)) ->
      sig_finType (pred_of_set [set [set w | is_uconnected f' u w] | u : G' & val u \in S]) :=
      fun u => Sub [set w | is_uconnected f' (Sub (val u) (Hh u)) w] (Hh' u).
    apply (Bijective (g := h)).
    - move => E.
      unfold g. destruct (Hg E) as [[u Uin] U Hu].
      unfold h.
      destruct E as [E HE]; cbnb. f_equal.
      rewrite SubK in Hu. subst E.
      revert HE => /imsetP[[w W] Hw ->].
      rewrite !in_set SubK in Hw.
      apply /setP => ?.
      rewrite !in_set.
      apply is_uconnected_eq; trivial.
(* TODO similaire au TODO d'avant : en faire un lemma dans S *)
      admit.
    - move => u.
      unfold g. destruct (Hg (h u)) as [[w Win] W Hw], u as [u U].
      cbnb. rewrite SubK in W.
      rewrite /h !SubK in Hw.
      revert Hw => /setP /(_ (Sub w Win)). rewrite !in_set is_uconnected_id => /existsP[[p P] _].
      assert (exists ew, usource ew = w /\ utarget ew = v /\ None <> f ew.1) as [ew [Sew [Tew New]]].
      { revert W; rewrite !in_set => /orP [/imsetP[e] | /imsetP[e]].
        all: rewrite !in_set => /andP[/eqP Ne /eqP E] E'; apply nesym in Ne; symmetry in E'.
        - exists (backward e). splitb.
        - exists (forward e). splitb. }
      assert (exists eu, usource eu = v /\ utarget eu = u /\ None <> f eu.1) as [eu [Seu [Teu Neu]]].
      { assert (U' : u \in neighbours f v) by by [].
        revert U'; rewrite !in_set => /orP [/imsetP[e] | /imsetP[e]].
        all: rewrite !in_set => /andP[/eqP Ne /eqP E] E'; apply nesym in Ne; symmetry in E'.
        - exists (forward e). splitb.
        - exists (backward e). splitb. }
      destruct (eq_comparable w u) as [ | Hneq]; trivial.
      assert (Heuw : eu.1 <> ew.1).
      { intro Hc. contradict Hneq.
        destruct eu as [eu []], ew as [ew []]; by rewrite -Sew -Teu Hc // -[in LHS]Hc Seu Tew. }
      enough (Pc : supath f v v (eu :: rcons [seq (val a.1, a.2) | a <- p] ew)).
      { specialize (A _ {| upval := _ ; upvalK := Pc |}).
        contradict A; cbnb. }
      assert (Pm : supath f u w [seq (val a.1, a.2) | a <- p]).
      { admit. (* should be easy, already done before *) }
      revert Pm => /andP[/andP[? ?] ?].
      rewrite /supath /= !map_rcons !mem_rcons !in_cons !mem_rcons !in_cons !rcons_uniq.
      splitb; try by apply /eqP.
      + rewrite uwalk_rcons Tew Teu Sew. splitb.
      + apply /eqP => Hc.
        contradict Heuw.
        apply F; rewrite // !in_set; apply /eqP; by apply nesym.
      + (* sinon on passait par v dans p *) admit.
      + (* sinon on passait par v dans p *) admit.
    }
  assert (#|~: f @^-1 None| = #|~: f @^-1 None :\: edges_at v| + #|~: f @^-1 None :&: edges_at v|) as ->.
  { rewrite cardsD.
    enough (#|~: f @^-1 None| >= #|~: f @^-1 None :&: edges_at v|) by lia.
    rewrite -(cardsID (edges_at v) (~: f @^-1 None)).
    lia. }
  lia.
Admitted. (* TODO puis prouver neigh_nb, lemma d'avant *)
(* TOTHINK est ce qu'on se sert reellement des proprietes de partition ? Si non, on peut refaire à la main ? *)
(* Definition is_uconnected_class {G : graph_left} (x : G) := [set y | x ▬ y]. *)
(* TODO specialiser ces lemmas dans le cas de switching eq en simplifiant les ensembles *)
(* assert (P := is_uconnected_partition F). revert P => /andP[C /andP[Cap Z]]. *)

End Atoms.

Declare Scope proofnet_scope. (* Completely Useless ?! *)
Notation "'ν' X" := (var X) (at level 12) : proofnet_scope.
Notation "'κ' X" := (covar X) (at level 12) : proofnet_scope.
Infix "⊗" := tens (left associativity, at level 25) : proofnet_scope. (* TODO other way to overload notations ? *)(* zulip *)
Infix "⅋" := parr (at level 40) : proofnet_scope.
Notation "A ^" := (dual A) (at level 12, format "A ^") : proofnet_scope.
Notation "⊢ l" := (ll l) (at level 70) : proofnet_scope.
Notation base_graph := (graph (flat rule) (flat formula)).
Notation deg_out := (deg false).
Notation deg_in := (deg true).
Notation p_deg_out := (p_deg false).
Notation p_deg_in := (p_deg true).
Infix "≃l" := iso_left (at level 79) : proofnet_scope.

(***************** UNUSED LEMMA ********************************
Ltac case_if0 := repeat (let Hif := fresh "Hif" in let Hif' := fresh "Hif" in
  case: ifP; cbn; move => /eqP Hif; rewrite // 1?Hif //).

Definition pick_unique2 := fun {T : finType} (H : #|T| = 1) => sval (fintype1 H).

(** Removing an element of a set decrease cardinality by 1 *)
Lemma cardsR1_set : forall (T : finType) (a : T) , #|setT :\ a| = #|T| - 1.
Proof. intros T a. rewrite -cardsT (cardsD1 a [set: T]) in_setT. lia. Qed.

Lemma cardsR1 {T : finType} (a : T) (A : {set T}) : #|A :\ a| = #|A| - (a \in A).
Proof. rewrite (cardsD1 a A). lia. Qed.

(* Switching Graph *)
Definition switching_graph (G : geos) (phi : G -> bool) : base_graph :=
  remove_edges (setT :\: [set match phi v with
  | false => left v | true => right v end | v in G & vlabel v == ⅋]).
*)

(* TODO list:
- warnings ssreflect
- revert; move => devient revert => + => de move apres vue
- idem pour les specialize qu'on peut faire en move
- _ plus souvent
- transitivity plus souvent, à la place de assert
- toujours utiliser = or == partout le même !!! idem != et <>
- sameP to rewrite reflect ?
- use _spec pour casser des cas
- refine (iso_correct _ _): a la place de prouver les hyp tout de suite
- utiliser wlog pour cas symétriques
- cbnb a utiliser, et switching_None et uconnected_simpl
- lemma other_cut_in_neq en 2 lemmas ?
- check if every lemma proved is useful / interesting
- check all names given not already used, from beginning
- homogene notations and spaces
- utiliser turns et turn pour homogeneiser plus de cas dans correction
- check at the end if all import are used
- uacyclic et connected dans bool ?
- see files bug_report
- ugly def: do useful lemma and then put it opaque
- eq_refl dans cbnb ?
- repeat dans case_if ?
- TOTHINK fonction disant si formule atomique existe dans yalla, ajout possible pour expansion atome
- TOTHINK faire des sections pour chaque op de correct, et ainsi de suite ?
- TOTHINK graphes avec garbage pour ne pas faire de suppression et donc de sigma type
- TOTHINK composantes connexes : relation d'equivalence "etre connexe"
*)
