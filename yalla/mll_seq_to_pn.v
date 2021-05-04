(* From a LL proof, return a Proof Net of the same sequent *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
From mathcomp Require Import all_ssreflect zify.
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export graph_more mll_prelim mll_def mll_correct.

Import EqNotations.

Set Mangle Names.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


Section Atoms.

(** A set of atoms for building formulas *)
Context { atom : DecType }.
(* TODO meilleur moyen de récupérer les notations *)
Notation formula := (@formula atom).
Notation ll := (@ll atom).
Notation base_graph := (graph (flat rule) (flat formula)).
Notation graph_left := (@graph_left atom).
Notation graph_data := (@graph_data atom).
Notation geos := (@geos atom).
Notation proof_structure := (@proof_structure atom).
Notation proof_net := (@proof_net atom).
Infix "≃l" := iso_left (at level 79).


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

Definition v_graph_data : graph_data := {|
  graph_left_of := v_graph_left;
  order := nil;
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
  by rewrite /edges_at_out !in_set !eq_refl.
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
  p_deg := p_deg (g := _);
  p_left := p_left (g := _);
  p_order := perm_p_order _ _;
  |}.

Definition perm_ps (G : proof_structure) (l l' : list formula) (sigma : Permutation_Type l l') :
  proof_structure := {|
  geos_of := perm_geos G sigma;
  p_ax_cut := p_ax_cut (p := _);
  p_tens_parr := p_tens_parr (p := _);
  |}.


(** Sequent of a permutation *)
Lemma perm_sequent (G : proof_structure) (l l' : list formula) (sigma : Permutation_Type l l')
  (H : sequent G = l) : sequent (perm_geos G sigma) = l'.
Proof.
  revert sigma; rewrite -H => *.
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
  edges_at_outin b (fv v) =i [set fe e | e in edges_at_outin b v].
Proof.
  intros Gi fv fe v; hnf.
  destruct i; intros [e | e].
  all: assert (injective fe) by (apply inl_inj || apply inr_inj).
  all: rewrite ?inj_imset // !in_set; cbn; trivial.
  all: by apply /eqP /memPn => ? /imsetP [? _] ->.
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
  all: revert Hneq => /eqP /negPf ->.
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
    revert U0 U1. rewrite 4!cons_uniq => /andP[VO0 U0] /andP[VO1 U1].
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
  all: apply p_order; cbn; rewrite /union_order ?H0 ?H1 !in_cons ?mem_cat map_f; caseb.
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
  apply /allP => x Hx.
  assert (inl (target e0) \notin (add_node_order_2 t e0 e1) /\
          inl (target e1) \notin (add_node_order_2 t e0 e1)) as [? ?].
  { rewrite -2!has_pred1 /add_node_order_2 /add_node_type_order /add_node_order_1.
    destruct t; cbn;
    rewrite 2!has_map /preim 2!has_pred1 2!mem_filter.
    all: by split; apply /negP => /andP[/andP[/eqP H0 /eqP H1] _]. }
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
  split => e; [set v := v0; set Hv := Hv0 | set v := v1; set Hv := Hv1].
  all: apply /negP => ?; apply notF.
  all: assert (Hout : edges_at_out v = set0)
    by (apply cards0_eq; by rewrite (p_deg_out v) Hv).
  all: by rewrite -(in_set0 e) -Hout in_set.
Qed.

Lemma add_node_new_edges_at_in (t : trilean) (G : graph_data) (e0 e1 : edge G)
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
  edges_at_in (inl v : add_node_graph_1 t (edge_of_concl v0) (edge_of_concl v1)) =
  [set add_node_transport_1 t (edge_of_concl v0) (edge_of_concl v1) e | e in edges_at_in v].
Proof.
  set e0 := edge_of_concl v0;
  set e1 := edge_of_concl v1.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [? ?]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  intros v [? ?]; apply /setP => e.
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
    + revert Hneq => /eqP /negPf Hneq. rewrite Hneq.
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
  destruct (add_node_new_edges_at_in t (add_node_hyp H)).
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
  edges_at_outin b (Sub (inl v) Hv : add_node_graph_data t _)
  = [set add_node_transport t H e | e in edges_at_outin b v].
Proof.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [? ?]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  set e0 := edge_of_concl v0; set e1 := edge_of_concl v1.
  assert (Hneqv : v0 <> v1).
  { elim (p_order G).
    by rewrite H cons_uniq in_cons negb_or => _ /andP[/andP[/eqP ? _] _]. }
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
  [seq elabel (match [pick x in edges_at_in i] with
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
    all: assert (Hout_1 : edges_at_in (inr (inr tt) : add_node_graph_1 t e0 e1)
      = [set Some (Some (inr None))])
      by (apply /setP; intro e; rewrite !in_set; by destruct e as [[[e | [[[] | []] | ]] | ] | ]).
    all: assert (Hss: Some (Some (inr None)) \in edge_set ([set: add_node_graph_1 t e0 e1]
      :\ inl (target e0) :\ inl (target e1))) by (rewrite !in_set; splitb; apply (add_node_hyp H)).
    all: set ss := Sub (Some (Some (inr None))) Hss : edge (add_node_graph_data t (add_node_hyp H)).
    all: assert (Hout : edges_at_in (Sub (inr (inr tt)) Hv : add_node_graph_data t
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
      -(card_imset (edges_at_outin b v) (add_node_transport_inj (t := t) (H := H))).
  - set e0 := edge_of_concl v0;
    set e1 := edge_of_concl v1;
    set S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1).
    destruct (add_node_new_edges_at_in t (add_node_hyp H)) as [Hn Hsn].
    set n := Sub None Hn : edge (add_node_graph_data t (add_node_hyp H));
    set sn := Sub (Some None) Hsn : edge (add_node_graph_data t (add_node_hyp H)).
    destruct t;
    [set t := tens_t | set t := parr_t | set t := cut_t].
    1,2: assert (Some (Some (inr None)) \in edge_set S /\ inr (inl tt) \in S /\ inr (inr tt) \in S)
          as [Hss [Htn Hcn]] by (rewrite !in_set; splitb).
    1,2: set ss := Sub (Some (Some (inr None))) Hss : edge (add_node_graph_data t (add_node_hyp H));
         set tn := Sub (inr (inl tt)) Htn : add_node_graph_data t (add_node_hyp H);
         set cn := Sub (inr (inr tt)) Hcn : add_node_graph_data t (add_node_hyp H).
    1,2: assert (edges_at_in tn = [set n; sn] /\ edges_at_out tn = [set ss] /\
                 edges_at_in cn = [set ss] /\ edges_at_out cn = set0)
          as [Htn_in [Htn_out [Hcn_in Hcn_out]]]
          by (splitb; apply /setP; intro e; rewrite !in_set;
            by destruct e as [[[[e | [[[] | []] | ]] | ] | ] ?]).
    3: assert (Htn : inr tt \in S) by (rewrite !in_set; apply /andP; by split).
    3: set tn := (Sub (inr tt) Htn : add_node_graph_data t (add_node_hyp H)).
    3: assert (edges_at_in tn = [set n; sn] /\ edges_at_out tn = set0)
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
      | cut_t => if (elabel (edge_of_concl v0)) == dual (elabel (edge_of_concl v1))
        then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> v_graph_data
      | _ => fun Heq  => add_node_graph_data t (add_node_hyp Heq)
      end
    | _ => fun=> v_graph_data
    end H), vlabel v = (if b then cut else ax) ->
    exists (el er : edge (match l return (order G = l -> graph_data) with
    | v0 :: v1 :: _ => match t with
      | cut_t => if (elabel (edge_of_concl v0)) == dual (elabel (edge_of_concl v1))
        then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> v_graph_data
      | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
      end
    | _ => fun=> v_graph_data
    end H)), (el \in edges_at_outin b v) && (er \in edges_at_outin b v) &&
    (elabel el == dual (elabel er))) by by rewrite <-!H in Hdone.
  destruct l as [ | v0 [ | v1 l]]; try by [].
  enough (Hdone : t <> cut_t \/ elabel (edge_of_concl v0) = dual (elabel (edge_of_concl v1)) ->
    forall b (v : add_node_graph_data t (add_node_hyp H)),
    vlabel v = (if b then cut else ax) ->
    exists el er : edge (add_node_graph_data t (add_node_hyp H)),
    (el \in edges_at_outin b v) && (er \in edges_at_outin b v) && (elabel el == dual (elabel er))).
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
    destruct (add_node_new_edges_at_in cut_t (add_node_hyp H)) as [Hn Hsn].
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
      | cut_t => if (elabel (edge_of_concl v0)) == dual (elabel (edge_of_concl v1))
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
    assert (ccl w \in edges_at_out w /\ right w \in edges_at_in w :\ left w)
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
      rewrite right_set // !in_set; move => /orP[/eqP Heright_in | /eqP ? //].
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
    all: destruct (add_node_new_edges_at_in t (add_node_hyp H)) as [Hn Hsn].
    all: assert (Hss : Some (Some (inr None)) \in edge_set S) by
      (rewrite !in_set; splitb; try (apply (add_node_hyp H)); by destruct t).
    all: set n := Sub None Hn : edge (add_node_graph_data t (add_node_hyp H));
      set sn := Sub (Some None) Hsn : edge (add_node_graph_data t (add_node_hyp H));
      set ss := Sub (Some (Some (inr None))) Hss : edge (add_node_graph_data t (add_node_hyp H));
      set tn := Sub (inr (inl tt)) Hin : add_node_graph_data t (add_node_hyp H).
    all: assert (edges_at_in tn = [set n; sn] /\ edges_at_out tn = [set ss])
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
      | cut_t => if (elabel (edge_of_concl v0)) == dual (elabel (edge_of_concl v1))
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
      | cut_t => if elabel (edge_of_concl v0) == dual (elabel (edge_of_concl v1))
        then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> v_graph_data
      | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
    end
    | _ => fun=> v_graph_data
    end H)]) as -> by by rewrite <-!H.
  destruct l as [ | v0 [ | v1 l]]; trivial.
  assert (vlabel v0 = concl_l /\ vlabel v1 = concl_l) as [? ?]
    by (split; apply p_order; rewrite H !in_cons; caseb).
  assert (match t with
    | cut_t => if elabel (edge_of_concl v0) == dual (elabel (edge_of_concl v1))
      then fun Heq => add_node_graph_data t (add_node_hyp Heq) else fun=> v_graph_data
    | _ => fun Heq => add_node_graph_data t (add_node_hyp Heq)
    end H = match t with
    | cut_t => if elabel (edge_of_concl v0) == dual (elabel (edge_of_concl v1))
      then add_node_graph_data t (add_node_hyp H) else v_graph_data
    | _ => add_node_graph_data t (add_node_hyp H)
    end) as -> by (destruct t; trivial; case_if).
  rewrite /sequent H; cbn.
  enough ([seq elabel (edge_of_concl i) | i <- order (add_node_graph_data t (add_node_hyp H))] =
    match t with
    | tens_t => [:: tens (elabel (edge_of_concl v0)) (elabel (edge_of_concl v1))]
    | parr_t => [:: parr (elabel (edge_of_concl v0)) (elabel (edge_of_concl v1))]
    | cut_t  => [::]
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
  assert (Hr : [seq elabel (match [pick x in edges_at_in i] with
    | Some e => e | None => add_node_left_1 i end) | i <- match t return
    (seq (add_node_graph_1 t e0 e1)) with | cut_t => [::] | _ => [:: inr (inr tt)] end] =
    match t with
    | tens_t => [:: tens (elabel e0) (elabel e1)]
    | parr_t => [:: parr (elabel e0) (elabel e1)]
    | cut_t =>  [::]
    end).
  { destruct t; [set t := tens_t | set t := parr_t | set t := cut_t]; cbn; trivial.
    all: assert (Hr : edges_at_in (inr (inr tt) : add_node_graph_1 t e0 e1) =
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
    assert (H : supath switching_left u v p) by by destruct_I3 u; destruct_I3 v.
    by exists {| upval := p; upvalK := H |}.
Qed.


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
 (@add_concl_graph_left _
    (@add_concl_graph_left _
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
  ∔ [inl (inr tt), parr (elabel e0) (elabel e1), inr tt]
  ≃ (G ⊎ (unit_graph (⅋) ⊎ unit_graph c))
  ∔ [inr (inl tt), parr (elabel e0) (elabel e1), inr (inr tt)]
  ∔ [inl (source e0), elabel e0, inr (inl tt)].
Proof.
  etransitivity. apply add_edge_C. symmetry.
  apply (add_edge_iso (add_edge_iso (union_A G (unit_graph (⅋)) (unit_graph c))
    (inr (inl tt)) (parr (elabel e0) (elabel e1)) (inr (inr tt)))).
Defined.

Definition add_node_parr_iso_1 (G : base_graph) (e0 e1 : edge G) :
  (G ⊎ unit_graph (⅋) ⊎ unit_graph c)
  ∔ [inl (inl (source e0)), elabel e0, inl (inr tt)]
  ∔ [inl (inl (source e1)), elabel e1, inl (inr tt)]
  ∔ [inl (inr tt), parr (elabel e0) (elabel e1), inr tt]
  ≃ (G ⊎ (unit_graph (⅋) ⊎ unit_graph c))
  ∔ [inr (inl tt), parr (elabel e0) (elabel e1), inr (inr tt)]
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
  (inr tt) c (parr (elabel e0) (elabel e1)).
Proof.
  unfold add_node_graph_1, add_concl_graph, add_parr_graph, edge_graph, two_graph, "∔".
  etransitivity. apply (add_edge_iso (add_edge_iso (@union_add_edge_r _ _ G _ _ _ _) _ _ _)).
  etransitivity. symmetry. apply add_node_parr_iso_1.
  apply (add_edge_iso (add_node_parr_iso_2 e0 e1)).
Defined.

Lemma add_node_parr_isol (G : geos) (e0 e1 : edge G)
  (H' : vlabel (target e0) = c /\ vlabel (target e1) = c) :
  add_node_graph_left_1 parr_t e0 e1 ≃l
  @add_concl_graph_left _ (add_parr_graph_left (source e0) (source e1) (elabel e0) (elabel e1))
  (inr tt) c (parr (elabel e0) (elabel e1)).
Proof.
  exists (add_node_parr_iso _ _).
  intros [v | [[] | []]] V; apply /eqP; cbn; try by [].
  case_if.
  all: destruct H' as [H0 H1].
  all: rewrite ->(left_e (v := v)) in *; caseb.
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
  enough (H': correct (@add_concl_graph_left _ (@add_concl_graph_left _ (add_node_graph_left parr_t (add_node_hyp Hl))
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
  ∔ [inl tt, tens (elabel e0) (elabel e1), inr tt]
  ≃
  (G0 ⊎ G1 ⊎ unit_graph (⊗) ⊎ unit_graph c)
  ∔ [inl (inr tt), tens (elabel e0) (elabel e1), inr tt].
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
  (inr (inr tt)) c (tens (elabel e0) (elabel e1)).
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
  @add_concl_graph_left _
    (@union_edge_graph_left _ G1
      (@add_concl_graph_left _ G0 (source e0) (⊗) (elabel e0))
      (source e1) (inr tt) (elabel e1))
  (inr (inr tt)) c (tens (elabel e0) (elabel e1)).
Proof.
  exists (add_node_tens_iso _ _).
  destruct H as [H0 H1].
  intros [[v | v] | [[] | []]] V; apply /eqP; cbn; try by [].
  all: case_if.
  all: rewrite ->(left_e (v := v)) in *; caseb.
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
  enough (H': correct (@add_concl_graph_left _ (@add_concl_graph_left _ (add_node_graph_left tens_t (add_node_hyp Hl))
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
  @union_edge_graph_left _ G1 (@add_concl_graph_left _ G0 (source e0) cut (elabel e0))
    (source e1) (inr tt) (elabel e1).
Proof.
  exists (add_node_cut_iso _ _).
  destruct H as [H0 H1].
  intros [[v | v] | []] V; apply /eqP; cbn; try by [].
  all: case_if.
  all: rewrite ->(left_e (v := v)) in *; caseb.
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
    | v0 :: v1 :: _ => if elabel (edge_of_concl v0) == dual (elabel (edge_of_concl v1))
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
  enough (H': correct (@add_concl_graph_left _ (@add_concl_graph_left _ (add_node_graph_left cut_t (add_node_hyp Hl))
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

End Atoms.
