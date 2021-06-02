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
Proof. now subst. Qed.




(** ** Stratum 0: Multigraphs from the library GraphTheory *)
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

(** Having a cut or not, for a cut reduction procedure *)
Definition has_cut (G : base_graph) := #|[set v : G | vlabel v == cut]| != 0.

Lemma has_cutP (G : base_graph) : reflect (has_cut G) [exists v : G, vlabel v == cut].
Proof.
  apply iff_reflect; split; unfold has_cut; intro H.
  - rewrite eqn0Ngt negb_involutive card_gt0 in H. revert H => /set0Pn [e H].
    rewrite in_set in H.
    apply /existsP. by exists e.
  - revert H => /existsP [v Hm].
    rewrite eqn0Ngt negb_involutive card_gt0.
    apply /set0Pn. exists v. by rewrite in_set.
Qed.



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

(** Paths in the switching graph without any left *)
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


(** Properties on switching & switching_left *)
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

Lemma swithching_to_left_eq {G : geos} :
  forall (a e : edge G), switching_left a <> None -> switching_left e <> None ->
  switching a = switching e -> switching_left a = switching_left e.
Proof.
  move => a e A E S.
  assert (T := switching_eq S).
  apply /eqP; revert S A E => /eqP.
  rewrite /switching /switching_left T; cbn.
  case_if; apply /eqP.
  assert (vlabel (target e) = ⅋) by by apply /eqP.
  transitivity (right (target e)); [ | symmetry];
  apply right_eq; caseb.
Qed.

Lemma supath_switching_from_leftK {G : geos} :
  forall (u v : G) p, supath switching_left u v p ->
  supath switching u v p.
Proof.
  move => u v p /andP[/andP[? U] N].
  splitb; last by apply switching_None.
  destruct p as [ | e p]; trivial.
  apply /(uniqP (Some e.1)) => a f A F.
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

Definition supath_switching_from_left {G : geos} (s t : G) (p : Supath switching_left s t) :=
  {| upval := p ; upvalK := supath_switching_from_leftK (upvalK p) |}.

Lemma uacyclic_swithching_left {G : geos} :
  uacyclic (@switching G) -> uacyclic (@switching_left G).
Proof.
  move => A u P.
  specialize (A _ (supath_switching_from_left P)).
  cbnb. by revert A => /eqP; cbn => /eqP.
Qed.

Lemma switching_left_edges_None (G : geos) :
  (@switching_left G) @^-1 None = [set left v | v : G & vlabel v == ⅋].
Proof.
  apply /setP => e.
  rewrite !in_set; symmetry.
  destruct (switching_left e \in pred1 None) eqn:E.
  - revert E => /eqP.
    unfold switching_left; case_if.
    apply imset_f.
    rewrite !in_set.
    by replace e with (left (target e)).
  - apply /imsetP. move => [v]; rewrite in_set => /eqP V ?; subst e.
    contradict E; apply /negPf/eqP.
    rewrite /switching_left left_e V; caseb.
    case_if.
Qed.

Lemma switching_left_edges_None_nb (G : geos) :
  #|[set left v | v : G & vlabel v == ⅋]| = #|[set v : G | vlabel v == ⅋]|.
Proof.
  apply card_in_imset.
  move => u v; rewrite !in_set => /eqP U /eqP V L.
  rewrite -(left_e (v := u)) -1?(left_e (v := v)) ?L; caseb.
Qed.

Lemma switching_left_edges_nb (G : geos) :
  #|[set v : G | vlabel v == ⅋]| + #|~: (@switching_left G) @^-1 None| = #|edge G|.
Proof. by rewrite -switching_left_edges_None_nb -switching_left_edges_None cardsC. Qed.

Lemma switching_left_uconnected_nb {G : geos} :
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


(** ** Isomorphism for each strata *)
Lemma edges_at_outin_iso (F G : base_graph) :
  forall (h : F ≃ G) b v, edges_at_outin b (h v) = [set h.e e | e in edges_at_outin b v].
Proof.
  move => h b v. apply /setP => e.
  by rewrite -[e](bijK' h.e) bij_mem_imset !inE endpoint_iso iso_noflip bij_eqLR bijK.
Qed.

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
Record iso_data (F G : graph_data) := Iso_order {
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
  rewrite ->vlabel_iso in H.
  by rewrite -H edges_at_outin_iso card_imset.
Qed.

Lemma p_left_iso (F G : graph_data) : F ≃l G -> proper_left G -> proper_left F.
Proof.
  intros h H v Hl.
  assert (Hl' : vlabel (h v) = ⊗ \/ vlabel (h v) = ⅋) by by rewrite vlabel_iso.
  specialize (H _ Hl').
  by rewrite edges_at_outin_iso left_iso // bij_mem_imset in H.
Qed.

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

(* TODO lemma F iso G -> F : proper_ -> G : proper_ pour ps *)


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

(* TODO list:
- warnings ssreflect
- revert; move => devient revert => + => de move apres vue
- idem pour les specialize qu'on peut faire en move
- _ plus souvent
- transitivity plus souvent, à la place de assert
- toujours utiliser = or == partout le même !!! idem != et <>
- refine (iso_correct _ _): a la place de prouver les hyp tout de suite
- utiliser wlog pour cas symétriques
- cbnb a utiliser, et switching_None et uconnected_simpl
- lemma other_cut_in_neq en 2 lemmas ?
- check if every lemma proved is useful / interesting
- check all names given not already used, from beginning
- homogene notations and spaces
- utiliser turns et turn pour homogeneiser plus de cas dans correction
- check at the end if all import are used
- see files bug_report
- psize and size of formula useless ?
- TOTHINK fonction disant si formule atomique existe dans yalla, ajout possible pour expansion atome
- TOTHINK faire des sections pour chaque op de correct, et ainsi de suite ?
- TOTHINK graphes avec garbage pour ne pas faire de suppression et donc de sigma type
*)
