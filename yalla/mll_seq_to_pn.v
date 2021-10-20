(* From a LL proof, return a Proof Net of the same sequent *)

From Coq Require Import Bool.
From OLlibs Require Import dectype Permutation_Type_more.
From mathcomp Require Import all_ssreflect.
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
Notation base_graph := (graph (flat rule) (flat (formula * bool))).
Notation graph_data := (@graph_data atom).
Notation proof_structure := (@proof_structure atom).
Notation proof_net := (@proof_net atom).


(** ** Operations on proof nets, at each strata *)
(** * Empty proof structure *)
Definition v_graph : base_graph := {|
  vertex := [finType of void];
  edge := [finType of void];
  endpoint := fun _ => vfun;
  vlabel := vfun;
  elabel := vfun;
  |}.

Definition v_graph_data : graph_data := {|
  graph_of := v_graph;
  order := nil;
  |}.

Definition v_ps : proof_structure.
Proof. by exists v_graph_data. Defined.

Lemma v_correct : correct v_graph_data.
Proof. split; intros []. Qed. (* TODO devrait etre faux avec nouvelle connexite *)



(** * Base case: proof net of an axiom *)
(** Base graph of an axiom *)
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
  | _ => c
  end;
  elabel := fun e => match val e with
  | 0 => (covar x, true)
  | _ => (var x, true)
  end;
  |}.
(*   c    covar x,left  ax  var x,left  c
     O     <--------    O   ------->   O
    ord1      ord0    ord0    ord1    ord2   *)

(** Graph data of an axiom *)
Definition ax_graph_data (x : atom) : graph_data := {|
  graph_of := ax_graph x;
  order := ord0 :: ord1 :: nil;
  |}.

(** Proof structure of an axiom *)
Lemma ax_p_deg (x : atom) : proper_degree (ax_graph_data x).
Proof. intros [] v; destruct_I3 v; compute_card_subIn. Qed.

Lemma ax_p_ax_cut (x : atom) : proper_ax_cut (ax_graph_data x).
Proof.
  unfold proper_ax_cut.
  intros [] v Hl; destruct_I3 v; try (by contradict Hl).
  exists ord0, ord1.
  by rewrite /edges_at_out !in_set /=.
Qed.

Lemma ax_p_tens_parr (x : atom) : proper_tens_parr (ax_graph_data x).
Proof. unfold proper_tens_parr. intros [] v Hl; destruct_I3 v; by contradict Hl. Qed.

Lemma ax_p_noleft (x : atom) : proper_noleft (ax_graph_data x).
Proof. move => e _. by destruct_I2 e. Qed.

Lemma ax_p_order (x : atom) : proper_order (ax_graph_data x).
Proof. split; trivial. by intro e; destruct_I2 e. Qed.

Definition ax_ps (x : atom) : proof_structure := {|
  graph_data_of := ax_graph_data x;
  p_deg := @ax_p_deg _;
  p_ax_cut := @ax_p_ax_cut _;
  p_tens_parr := @ax_p_tens_parr _;
  p_noleft := @ax_p_noleft _;
  p_order := ax_p_order _;
  |}.

(** Proof net of an axiom *)
Lemma ax_correct (x : atom) : correct (ax_graph x).
Proof.
  split.
  - intros u [p P]; destruct_I3 u; apply /eqP; cbn; apply /eqP.
    all: destruct p as [ | [a [ | ]] [ | [b [ | ]] [ | [c [ | ]] p]]];
      try (destruct_I2 a); try (destruct_I2 b); try (destruct_I2 c); try by [].
    all: contradict P; apply /negP; cbn; caseb.
  - set fp : ax_ps x -> ax_ps x -> @upath _ _ (ax_ps x) :=
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

Definition ax_pn (x : atom) : proof_net := {|
  ps_of := ax_ps x;
  p_correct := @ax_correct _;
  |}.

(** Sequent of an axiom *)
Lemma ax_sequent (x : atom) : sequent (ax_graph_data x) = covar x :: var x :: nil.
Proof. trivial. Qed.



(** * Permuting the conclusions of a proof structure *)
(** Graph data of a permutation *)
Definition perm_graph_data (G : graph_data) (l l' : list formula) (sigma : Permutation_Type l l') :
  graph_data := {|
  graph_of := G;
  order := perm_of sigma (order G);
  |}.

(** Proof structure of a permutation *)
Lemma perm_p_order (G : proof_structure) (l l' : list formula) (sigma : Permutation_Type l l') :
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

Definition perm_ps (G : proof_structure) (l l' : list formula) (sigma : Permutation_Type l l') :
  proof_structure := {|
  graph_data_of := perm_graph_data G sigma;
  p_deg := @p_deg _ _;
  p_ax_cut := @p_ax_cut _ _;
  p_tens_parr := @p_tens_parr _ _;
  p_noleft := @p_noleft _ _;
  p_order := perm_p_order _ _;
  |}.

(** Proof net of a permutation *)
Definition perm_pn (G : proof_net) (l l' : list formula) (sigma : Permutation_Type l l') :
  proof_net := {|
  ps_of := perm_ps G sigma;
  p_correct := @p_correct _ _;
  |}.

(** Sequent of a permutation *)
Lemma perm_sequent (G : graph_data) (l l' : list formula) (sigma : Permutation_Type l l')
  (H : sequent G = l) : sequent (perm_graph_data G sigma) = l'.
Proof.
  revert sigma; rewrite -H => *.
  by rewrite /sequent -perm_of_map perm_of_consistent.
Qed.



(** * Disjoint union of proof structures *)
(** G0 ⊎ G1 is the disjoint union of G0 and G1 *)

(** Graph data of a disjoint union *)
(* Put the two first premises at the beginning, then the tail of order G1, finally the tail of
order G0 *)
Definition union_order (G0 G1 : graph_data) :=
  match order G0, order G1 with
  | e0 :: o0, e1 :: o1 => inl e0 :: inr e1 :: map inr o1 ++ map inl o0
  | _, [::] => map inl (order G0)
  | [::], _ => map inr (order G1)
  end.

Definition union_graph_data (G0 G1 : graph_data) : graph_data := {|
  graph_of := G0 ⊎ G1;
  order := union_order _ _;
  |}.

(** Useful lemmas on a disjoint union *)
Lemma union_edges_at (G0 G1 : base_graph) (i : bool) (b : bool) :
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
  let fe := match i return edge (Gi i) -> edge (G0 ⊎ G1) with
  | false => inl | true => inr end in
  forall e, (fe e \in order (union_graph_data G0 G1)) = (e \in order (Gi i)).
Proof.
  intros Gi fe e.
  destruct i; cbn; unfold union_order;
  induction (order G0) as [ | e0 o0 H0];
  induction (order G1) as [ | e1 o1 H1]; cbn; trivial.
  all: assert (injective fe) by (apply inl_inj || apply inr_inj).
  all: rewrite !in_cons ?mem_cat ?mem_map //; cbn.
  1: by destruct o0.
  2: by destruct o1.
  1: set et := e1; set ot := o0; set fen := inl.
  2: set et := e0; set ot := o1; set fen := inr.
  all: destruct (eq_comparable e et) as [-> | Hneq]; [by rewrite eq_refl | ].
  all: revert Hneq => /eqP /negPf ->.
  all: assert (Hf : (fe e \in [seq fen i | i <- ot]) = false) by (clear; by induction ot).
  all: by rewrite Hf ?orb_false_r.
Qed.
Notation union_order_inl := (union_order_in (i := false)).
Notation union_order_inr := (union_order_in (i := true)).

(** Proof structure of a disjoint union *)
Lemma union_p_deg (G0 G1 : proof_structure) : proper_degree (union_graph_data G0 G1).
Proof.
  unfold proper_degree.
  intros b [v | v]; cbn;
  [set fe := inl : edge G0 -> edge (G0 ⊎ G1) | set fe := inr : edge G1 -> edge (G0 ⊎ G1)].
  all: rewrite -(p_deg b v) -(card_imset (f := fe)); [ | apply inl_inj || apply inr_inj].
  all: apply eq_card.
  - apply union_edges_at_inl.
  - apply union_edges_at_inr.
Qed.

Lemma union_p_ax_cut (G0 G1 : proof_structure) : proper_ax_cut (union_graph_data G0 G1).
Proof.
  unfold proper_ax_cut.
  intros b [v | v] Hl; cbn in *.
  all: destruct (p_ax_cut Hl) as [el [er He]].
  - exists (inl el), (inl er); by rewrite !union_edges_at_inl !inj_imset /=.
  - exists (inr el), (inr er); by rewrite !union_edges_at_inr !inj_imset /=.
Qed.

Lemma union_p_tens_parr (G0 G1 : proof_structure) : proper_tens_parr (union_graph_data G0 G1).
Proof.
  unfold proper_tens_parr.
  intros b [v | v] Hl;
  [set fe := inl : edge G0 -> edge (G0 ⊎ G1) | set fe := inr : edge G1 -> edge (G0 ⊎ G1)].
  all: destruct (p_tens_parr Hl) as [el [er [ec He]]].
  all: exists (fe el), (fe er), (fe ec).
  all: rewrite ?union_edges_at_inl ?union_edges_at_inr !inj_imset //;
  apply inl_inj || apply inr_inj.
Qed.

Lemma union_p_noleft (G0 G1 : proof_structure) : proper_noleft (union_graph_data G0 G1).
Proof. intros [e | e] Hl; apply (p_noleft Hl). Qed.

Lemma union_p_order (G0 G1 : proof_structure) : proper_order (union_graph_data G0 G1).
Proof.
  unfold proper_order.
  assert (injective (inl : edge G0 -> edge (G0 ⊎ G1)) /\ injective (inr : edge G1 -> edge (G0 ⊎ G1)))
    as [? ?] by by split => ? ? /eqP; cbn => /eqP-->.
  split.
  - destruct (p_order G0) as [? _];
    destruct (p_order G1) as [? _].
    intros [e | e];
    [rewrite union_order_inl | rewrite union_order_inr];
    by revert e.
  - destruct (p_order G0) as [_ U0];
    destruct (p_order G1) as [_ U1]; cbn.
    unfold union_order.
    destruct (order G0) as [ | e0 o0];
    destruct (order G1) as [ | e1 o1];
    rewrite ?map_inj_uniq //.
    revert U0 U1. rewrite 4!cons_uniq => /andP[? ?] /andP[? ?].
    rewrite cat_uniq in_cons !mem_cat !negb_or !map_inj_uniq ?mem_map //; cbn.
    splitb; clear.
    + by induction o1.
    + by induction o0.
    + induction o0; trivial.
      rewrite negb_or. splitb.
      by clear; induction o1.
Qed.

Definition union_ps (G0 G1 : proof_structure) : proof_structure := {|
  graph_data_of := union_graph_data G0 G1;
  p_deg := @union_p_deg _ _;
  p_ax_cut := @union_p_ax_cut _ _;
  p_tens_parr := @union_p_tens_parr _ _;
  p_noleft := @union_p_noleft _ _;
  p_order := union_p_order _ _;
  |}.

(** Sequent of a union *)
Lemma union_sequent (G0 G1 : graph_data) : sequent (union_graph_data G0 G1) =
  match sequent G0, sequent G1 with
  | f0 :: s0, f1 :: s1 => f0 :: f1 :: s1 ++ s0
  | _, [::] => sequent G0
  | [::], _ => sequent G1
  end.
Proof.
  cbn; unfold union_order, sequent.
  destruct (order G0) as [ | e0 o0];
  destruct (order G1) as [ | e1 o1]; trivial; cbn.
  all: apply /eqP; cbn; splitb; apply /eqP; trivial.
  all: by rewrite ?map_cat -!map_comp.
Qed.



(** * Adding a tens/parr/cut node to a proof structure, replacing 2 conclusions *)
(** Base graph for adding a node *)
(* Add a tens/parr/cut node, without removing conclusions *)
Definition add_node_graph_1 (t : trilean) {G : base_graph} (e0 e1 : edge G) :=
  (* subgraph to add *)
  let graph_node (t' : trilean) := match t' with
  | tens_t => edge_graph (⊗) (tens (flabel e0) (flabel e1), true) c
  | parr_t => edge_graph (⅋) (parr (flabel e0) (flabel e1), true) c
  | cut_t => unit_graph cut
  end in
  let G1 (t' : trilean) := G ⊎ graph_node t' in
  (* node of the graph receving edges *)
  let target_node := match t return G1 t with
  | tens_t => inr (inl tt)
  | parr_t => inr (inl tt)
  | cut_t => inr tt
  end in
  (* duplicate edges and modify left if a tens/parr is added *)
  G1 t ∔ [inl (source e0), (flabel e0, true), target_node]
       ∔ [inl (source e1), (flabel e1, match t with | cut_t => true | _ => false end), target_node].

(* Remove the conclusions *)
Definition add_node_graph (t : trilean) {G : base_graph} (e0 e1 : edge G) :=
  induced ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)).


(** Graph data for adding a node *)
(* Remove the inconsistent arrows from order *)
Definition add_node_order_1 {G : graph_data} (e0 e1 : edge G) :=
  [seq x <- order G | (target x != target e0) && (source x != target e0) &&
                      (target x != target e1) && (source x != target e1)].

(* Give order the type of the intermediary graph *)
Definition add_node_type_order (t : trilean) {G : graph_data} (e0 e1 : edge G) (l : seq (edge G)) :
  seq (edge (add_node_graph_1 t e0 e1)) := [seq Some (Some (inl e)) | e <- l].

(* Add the new conclusion if it exists *)
Definition add_node_order_2 (t : trilean) {G : graph_data} (e0 e1 : edge G) :=
  match t return seq (edge (add_node_graph_1 t e0 e1)) with
  | cut_t => nil | _ => [:: Some (Some (inr None))] end
  ++  add_node_type_order t e0 e1 (add_node_order_1 e0 e1).

Lemma add_node_consistent_order (t : trilean) {G : graph_data} (e0 e1 : edge G) :
  let S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1) in
  all (pred_of_set (edge_set S)) (add_node_order_2 t e0 e1).
Proof.
  apply /allP => e E.
  rewrite /edge_set. apply /setIdP.
  rewrite !in_set.
  revert E; rewrite /add_node_order_2 mem_cat => /orP[].
  - destruct t; rewrite ?in_nil // mem_seq1 => /eqP-?; subst e; splitb.
  - rewrite /add_node_order_1 /add_node_type_order.
    move => /mapP[a A ?]; subst e; cbn.
    revert A; rewrite mem_filter => /andP[/andP[/andP[/andP[? ?] ?] ?] _].
    splitb.
Qed.

Definition add_node_order (t : trilean) {G : graph_data} (e0 e1 : edge G) :
  seq (edge (add_node_graph t e0 e1)) :=
  sval (all_sigP (add_node_consistent_order t e0 e1)).

Definition add_node_graph_data (t : trilean) {G : graph_data} (e0 e1 : edge G) :
  graph_data := {|
  graph_of := add_node_graph t e0 e1;
  order := add_node_order _ _ _;
  |}.

(** Helpers for add_node *)
Lemma add_node_hyp {G : proof_structure} (e0 e1 : edge G) :
  forall l, order G = e0 :: e1 :: l ->
  forall e, source e != target e0 /\ source e != target e1.
Proof.
  intros ? O e.
  split; apply /eqP; apply no_source_c, p_order.
  all: rewrite O !in_cons; caseb.
Qed.

(* The list add_node_order_1 is just order without e0 and e1 *)
Lemma add_node_order_1_eq {G : proof_structure} (e0 e1 : edge G) :
  forall l, order G = e0 :: e1 :: l ->
  add_node_order_1 e0 e1 = [seq x <- order G | (x != e0) && (x != e1)].
Proof.
  intros ? O.
  assert (e0 \in order G /\ e1 \in order G) as [O0 O1].
  { rewrite O !in_cons. split; caseb. }
  destruct (p_order G) as [P _].
  assert (P0 := P e0). destruct P0 as [_ P0]. specialize (P0 O0).
  assert (P1 := P e1). destruct P1 as [_ P1]. specialize (P1 O1).
  rewrite /add_node_order_1.
  apply eq_in_filter => e E.
  destruct (add_node_hyp O e) as [-> ->].
  rewrite !andb_true_r.
  f_equal; [set ei := e0 | set ei := e1].
  all: destruct (eq_comparable e ei) as [ | Neq]; first by subst e; by rewrite !eq_refl.
  all: assert (e != ei) as -> by by apply /eqP.
  all: apply /eqP => Hc.
  all: contradict Neq.
  all: by apply one_target_c.
Qed.
Opaque add_node_order_1. (* To prevent Coq from unfolding the definition *)

Lemma add_node_new_edges_at_in (t : trilean) (G : proof_structure) (e0 e1 : edge G) :
  forall l, order G = e0 :: e1 :: l ->
  let S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1) in
  None \in edge_set S /\ Some None \in edge_set S.
Proof.
  intros ? O S.
  rewrite !in_set.
  destruct (add_node_hyp O e0); destruct (add_node_hyp O e1).
  splitb; by destruct t.
Qed.

Definition add_node_transport_1 (t : trilean) (G : graph_data) (e0 e1 : edge G) :
  edge G -> edge (add_node_graph_1 t e0 e1) :=
  fun e => if e == e1 then None
           else if e == e0 then Some None
           else Some (Some (inl e)).

Lemma add_node_transport_consistent (t : trilean) (G : proof_structure) (e0 e1 : edge G) :
  forall l, order G = e0 :: e1 :: l ->
  forall e, add_node_transport_1 t e0 e1 e \in
  edge_set ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)).
Proof.
  intros ? O e.
  assert (vlabel (target e0) = c /\ vlabel (target e1) = c) as [P0 P1]
    by (split; apply p_order; rewrite O !in_cons; caseb).
  set S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1).
  destruct (add_node_new_edges_at_in t O).
  unfold add_node_transport_1; case_if.
  rewrite !in_set.
  splitb; try apply (add_node_hyp O); cbn.
  all: apply /negP => /eqP ?.
  - enough (e = e1) by by [].
    by apply one_target_c.
  - enough (e = e0) by by [].
    by apply one_target_c.
Qed.

Definition add_node_transport (t : trilean) (G : proof_structure) (e0 e1 : edge G) (l : seq (edge G))
  (O : order G = e0 :: e1 :: l) :
  edge G -> edge (add_node_graph_data t e0 e1) :=
  fun e => Sub (add_node_transport_1 t e0 e1 e) (add_node_transport_consistent t O e).

Lemma add_node_transport_inj (t : trilean) (G : proof_structure) (e0 e1 : edge G) (l : seq (edge G))
  (O : order G = e0 :: e1 :: l) :
  injective (add_node_transport t O).
Proof. move => ? ? /eqP. unfold add_node_transport, add_node_transport_1. cbnb. case_if. Qed.

Lemma add_node_transport_edges (t : trilean) (G : proof_structure) (e0 e1 : edge G) (l : seq (edge G))
  (O : order G = e0 :: e1 :: l) :
  forall v V b, edges_at_outin b (Sub (inl v) V : add_node_graph_data t e0 e1) =
  [set add_node_transport t O e | e in edges_at_outin b v].
Proof.
  assert (vlabel (target e0) = c /\ vlabel (target e1) = c) as [P0 P1]
    by (split; apply p_order; rewrite O !in_cons; caseb).
  assert (Hneqv : target e0 <> target e1).
  { elim (p_order G) => _.
    rewrite O cons_uniq in_cons negb_or => /andP[/andP[/eqP Neq _] _] ?.
    contradict Neq.
    by apply one_target_c. }
  assert (Hneqe : e0 <> e1) by by intros ?; subst.
  intros v Hv b; apply /setP => e.
  assert ((target e0 == v) = false /\ (target e1 == v) = false) as [? ?].
    { split; apply /eqP; intros ?; subst; contradict Hv; apply /negP.
      all: rewrite !in_set; caseb. }
  set w := Sub (inl v) Hv : add_node_graph_data t e0 e1.
  set g := add_node_transport t O.
  set g_1 := add_node_transport_1 t e0 e1.
  set g_inj := @add_node_transport_inj t _ _ _ _ O.
  destruct e as [[[[e | e] | ] | ] He];
  rewrite in_set; cbn; rewrite !SubK; cbn.
  - enough (Heq : Sub (Some (Some (inl e))) He = g e) by by rewrite Heq inj_imset // in_set.
    apply /eqP; rewrite /g /add_node_transport sub_val_eq SubK /add_node_transport_1.
    case_if; subst.
    all: contradict He; apply /negP.
    all: rewrite !in_set; caseb.
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
      case_if. }
    rewrite Heq inj_imset // in_set.
    by destruct b, t.
Qed.

Lemma add_node_transport_flabel (t : trilean) (G : proof_structure) (e0 e1 : edge G) (l : seq (edge G))
  (O : order G = e0 :: e1 :: l) :
  forall e, flabel (add_node_transport t O e) = flabel e.
Proof. intros. unfold add_node_transport, add_node_transport_1. cbnb. case_if. Qed.

Lemma add_node_transport_llabel (t : trilean) (G : proof_structure) (e0 e1 : edge G) (l : seq (edge G))
  (O : order G = e0 :: e1 :: l) :
  forall e, e <> e1 -> llabel (add_node_transport t O e) = llabel e.
Proof.
  intros e Neq.
  unfold add_node_transport, add_node_transport_1; cbnb; case_if.
  subst e. symmetry; apply p_noleft.
  assert (vlabel (target e0) = c) as -> by (apply p_order; rewrite O !in_cons; caseb).
  caseb.
Qed.

(* We add the node if it respect the rules, otherwise we do nothing *)
Definition add_node_graph_data_bis : trilean -> graph_data -> graph_data :=
  fun (t : trilean) (G : graph_data) =>
  match order G with
  | e0 :: e1 :: _ => match t with
    | cut_t => if (flabel e1 == dual (flabel e0)) then add_node_graph_data t e0 e1 else G
    | _ => add_node_graph_data t e0 e1
    end
  | _ => G
  end.

(** Proof structure for adding a node *)
Lemma add_node_p_deg (t : trilean) (G : proof_structure) : proper_degree (add_node_graph_data_bis t G).
Proof.
  unfold add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; try apply p_deg.
  revert t.
  enough (forall t, proper_degree (add_node_graph t e0 e1)).
  { intros []; case_if; trivial. apply p_deg. }
  intros t b [[v | v] Hv]; cbn.
  - by rewrite (add_node_transport_edges O) -(p_deg b v)
      -(card_imset (edges_at_outin b v) (@add_node_transport_inj t _ _ _ _ O)).
  - set S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1).
    destruct (add_node_new_edges_at_in t O) as [Hn Hsn].
    set n := Sub None Hn : edge (add_node_graph_data t e0 e1);
    set sn := Sub (Some None) Hsn : edge (add_node_graph_data t e0 e1).
    destruct t; [set t := tens_t | set t := parr_t | set t := cut_t].
    1,2: assert (Some (Some (inr None)) \in edge_set S /\ inr (inl tt) \in S /\ inr (inr tt) \in S)
          as [Hss [Htn Hcn]] by (rewrite !in_set; splitb).
    1,2: set ss := Sub (Some (Some (inr None))) Hss : edge (add_node_graph_data t e0 e1);
         set tn := Sub (inr (inl tt)) Htn : add_node_graph_data t e0 e1;
         set cn := Sub (inr (inr tt)) Hcn : add_node_graph_data t e0 e1.
    1,2: assert (edges_at_in tn = [set n; sn] /\ edges_at_out tn = [set ss] /\
                 edges_at_in cn = [set ss] /\ edges_at_out cn = set0)
          as [Htn_in [Htn_out [Hcn_in Hcn_out]]]
          by (splitb; apply /setP => e; rewrite !in_set;
            by destruct e as [[[[e | [[[] | []] | ]] | ] | ] ?]).
    3: assert (Htn : inr tt \in S) by (rewrite !in_set; apply /andP; by split).
    3: set tn := (Sub (inr tt) Htn : add_node_graph_data t e0 e1).
    3: assert (edges_at_in tn = [set n; sn] /\ edges_at_out tn = set0)
        as [Htn_in Htn_out]
        by (split; apply /setP => e; rewrite !in_set; by destruct e as [[[[e | []] | ] | ] ?]).
    3: destruct v as [];
      replace Hv with Htn by apply eq_irrelevance.
    1,2: destruct v as [[] | []];
      [replace Hv with Htn by apply eq_irrelevance | replace Hv with Hcn by apply eq_irrelevance].
    all: destruct b; cbn.
    all: by rewrite ?Htn_in ?Htn_out ?Hcn_in ?Hcn_out ?cards2 ?cards1 ?cards0.
Qed.

Lemma add_node_p_ax_cut (t : trilean) (G : proof_structure) :
  proper_ax_cut (add_node_graph_data_bis t G).
Proof.
  unfold add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; try apply p_ax_cut.
  unfold proper_ax_cut.
  enough (Hdone : t <> cut_t \/ flabel e1 = dual (flabel e0) ->
    forall b (v : add_node_graph t e0 e1), vlabel v = (if b then cut else ax) ->
    exists el er : edge (add_node_graph t e0 e1),
    el \in edges_at_outin b v /\ er \in edges_at_outin b v /\ flabel el = dual (flabel er)).
  { case_if; destruct t; try (apply Hdone; caseb). by apply p_ax_cut. }
  intros Hor b [[v | v] Hv] Hl; cbn in Hl.
  - destruct (p_ax_cut Hl) as [el [er ?]].
    exists (add_node_transport t O el), (add_node_transport t O er).
    rewrite !(add_node_transport_edges O) !inj_imset; try apply add_node_transport_inj.
    by rewrite 2!add_node_transport_flabel /=.
  - destruct b, t, v, Hor as [? | Hf]; try by [].
    exists (add_node_transport cut_t O e1), (add_node_transport cut_t O e0).
    rewrite !add_node_transport_flabel Hf !in_set /=.
    cbn; rewrite !SubK /add_node_transport_1; case_if.
Qed.

Lemma add_node_p_tens_parr (t : trilean) (G : proof_structure) :
  proper_tens_parr (add_node_graph_data_bis t G).
Proof.
  unfold add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; try (apply p_tens_parr).
  revert t.
  enough (forall t, proper_tens_parr (add_node_graph t e0 e1)).
  { intros []; case_if; trivial. apply p_tens_parr. }
  intro t.
  unfold proper_tens_parr.
  move => b [[v | v] V] Hl; simpl in Hl.
  - destruct (p_tens_parr Hl) as [el [er [ec [El [Ell [Er [Erl [Ec Eq]]]]]]]].
    assert (el <> e1 /\ er <> e1) as [? ?].
    { split.
      all: intros ?; subst.
      1: revert El; rewrite in_set => /eqP ?; subst v.
      2: revert Er; rewrite in_set => /eqP ?; subst v.
      all: contradict V; apply /negP.
      all: rewrite !in_set; caseb. }
    exists (add_node_transport t O el), (add_node_transport t O er), (add_node_transport t O ec).
    rewrite !(add_node_transport_edges O) !inj_imset; try apply add_node_transport_inj.
    by rewrite !add_node_transport_flabel !add_node_transport_llabel.
  - destruct (add_node_new_edges_at_in t O) as [Hn Hsn].
    set n := Sub None Hn : edge (add_node_graph_data t e0 e1);
    set sn := Sub (Some None) Hsn : edge (add_node_graph_data t e0 e1).
    destruct t; [set t := tens_t | set t := parr_t | ];
    [destruct v as [[] | []] | destruct v as [[] | []] | destruct v as []];
    destruct b; try by [].
    all: assert (Hssn : Some (Some (inr None)) \in edge_set ([set: add_node_graph_1 tens_t e0 e1]
          :\ inl (target e0) :\ inl (target e1))) by (rewrite !in_set; splitb).
    all: set ssn := Sub (Some (Some (inr None))) Hssn : edge (add_node_graph_data tens_t e0 e1).
    all: exists sn, n, ssn.
    all: by rewrite !in_set /=.
Qed.

Lemma add_node_p_noleft (t : trilean) (G : proof_structure) : proper_noleft (add_node_graph_data_bis t G).
Proof.
  unfold add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; try (apply p_noleft).
  revert t.
  enough (forall t, proper_noleft (add_node_graph t e0 e1)).
  { intros []; case_if; trivial. apply p_noleft. }
  intro t.
  assert (vlabel (target e0) = c /\ vlabel (target e1) = c) as [Hv0 Hv1]
    by (split; apply p_order; rewrite O !in_cons; caseb).
  unfold proper_noleft.
  move => [[[[e | e] | ] | ] E] /= Hl //.
  - assert (e <> e0 /\ e <> e1) as [? ?].
    { split => ?; subst; contradict E; apply /negP.
       all: rewrite !in_set; caseb. }
    assert (Hr : Sub (Some (Some (inl e))) E = add_node_transport t O e).
    { apply /eqP; cbn; rewrite /= /add_node_transport_1.
      case_if. }
    by rewrite Hr add_node_transport_llabel // p_noleft.
  - by destruct t;
    [destruct e as [[[] | []] | ] | destruct e as [[[] | []] | ] | destruct e as []].
  - by destruct t;
    simpl in Hl; destruct Hl as [Hlax | [Hlcut | Hlc]].
Qed.

Lemma add_node_p_order (t : trilean) (G : proof_structure) : proper_order (add_node_graph_data_bis t G).
Proof.
  unfold add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; try (apply p_order).
  revert t.
  enough (forall (t : trilean), proper_order (add_node_graph_data t e0 e1)).
  { intros []; case_if; trivial. apply p_order. }
  intro t.
  unfold proper_order, add_node_order.
  destruct (p_order G).
  assert (Some None \notin add_node_type_order t e0 e1 (add_node_order_1 e0 e1)
    /\ None \notin add_node_type_order t e0 e1 (add_node_order_1 e0 e1)
    /\ Some (Some (inr None)) \notin add_node_type_order tens_t e0 e1 (add_node_order_1 e0 e1)
    /\ Some (Some (inr None)) \notin add_node_type_order parr_t e0 e1 (add_node_order_1 e0 e1))
    as [? [? [? ?]]].
  { splitb.
    all: rewrite /add_node_type_order (add_node_order_1_eq O).
    all: generalize (order G) as o => o.
    all: induction o as [ | a A IH]; trivial.
    all: replace (a :: A) with ([:: a] ++ A) by by [].
    all: rewrite filter_cat map_cat mem_cat negb_or IH andb_true_r /=.
    all: case_if. }
  split; cbn.
  - intros [[[[e | e] | ] | ] Hin]; cbn;
    rewrite in_seq_sig SubK -(proj2_sig (all_sigP _)) /add_node_order_2 /=.
    + apply (iff_stepl (A := e \in order G)); [ | by apply iff_sym].
      assert (e != e0 /\ e != e1) as [He0 He1].
      { split; apply /eqP => Hc;
        contradict Hin; apply /negP;
        rewrite Hc !in_set; caseb. }
      destruct t;
      rewrite ?in_cons /add_node_type_order (add_node_order_1_eq O) mem_map ?mem_filter ?He0 ?He1 //=.
      all: by move => ? ? /eqP; cbn => /eqP.
    + by destruct t;
      [destruct e as [[[] | []] | ] | destruct e as [[[] | []] | ] | destruct e as []].
    + destruct t; simpl.
      all: split => H //; contradict H; apply /negP; by rewrite ?in_cons.
    + destruct t; simpl.
      all: split => H //; contradict H; apply /negP; by rewrite ?in_cons.
  - rewrite uniq_seq_sig -(proj2_sig (all_sigP _)) /add_node_order_2.
    destruct t;
    rewrite ?cons_uniq.
    all: splitb.
    all: rewrite (add_node_order_1_eq O) map_inj_uniq //=; first by apply filter_uniq.
    all: by move => ? ? /eqP; cbn => /eqP-->.
Qed.

Definition add_node_ps (t : trilean) (G : proof_structure) : proof_structure := {|
  graph_data_of := add_node_graph_data_bis t G;
  p_deg := @add_node_p_deg _ _;
  p_ax_cut := @add_node_p_ax_cut _ _;
  p_tens_parr := @add_node_p_tens_parr _ _ ;
  p_noleft := @add_node_p_noleft _ _;
  p_order := @add_node_p_order _ _;
  |}.

(** Sequent for adding a node *)
Lemma add_node_sequent_eq (t : trilean) (G : graph_data) (e0 e1 : edge G) :
  sequent (add_node_graph_data t e0 e1) =
  [seq flabel e | e <- add_node_order_2 t e0 e1].
Proof.
  rewrite /add_node_graph_data /= /add_node_order.
  set l := sval (all_sigP _).
  rewrite (proj2_sig (all_sigP (add_node_consistent_order t e0 e1))).
  by rewrite -map_comp.
Qed.

Lemma add_node_sequent_type_order (t : trilean) (G : graph_data) (e0 e1 : edge G) :
  forall l,
  [seq flabel e | e <- add_node_type_order t e0 e1 l] = [seq flabel e | e <- l].
Proof. intros. by rewrite /add_node_type_order -map_comp. Qed.

Lemma add_node_sequent (t : trilean) (G : proof_structure) :
  let new := match order G with
    | e0 :: e1 :: _ => match t with
      | tens_t => [:: tens (flabel e0) (flabel e1)]
      | parr_t => [:: parr (flabel e0) (flabel e1)]
      | cut_t => [::]
      end
    | _ => [::]
    end in
  let old := match order G with
    | e0 :: e1 :: _ => match t with 
      | cut_t => if flabel e1 == dual (flabel e0)
              then behead (behead (sequent G))
              else sequent G
      | _ => behead (behead (sequent G))
      end
    | _ => sequent G
    end in
  sequent (add_node_graph_data_bis t G) = new ++ old.
Proof.
  unfold add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; trivial.
  enough (sequent (add_node_graph_data t e0 e1) =
    match t with
    | tens_t => [:: tens (flabel e0) (flabel e1)]
    | parr_t => [:: parr (flabel e0) (flabel e1)]
    | cut_t  => [::]
    end ++ [seq flabel i | i <- l]).
  { rewrite /sequent O.
    destruct t; try done.
    case_if.
    by rewrite O. }
  rewrite add_node_sequent_eq /add_node_order_2 map_cat add_node_sequent_type_order (add_node_order_1_eq O).
  f_equal; [by destruct t | ].
  f_equal.
  rewrite O /= !eq_refl /= andb_false_r.
  apply /all_filterP/allP => e E.
  destruct (p_order G) as [_ U].
  rewrite O /= in_cons in U.
  revert U => /andP[/norP[_ /negP-U0] /andP[/negP-U1 _]].
  by splitb; apply /eqP => ?; subst e.
Qed.



(** ** Proof Structure of a Proof Sequent *)
Definition add_node_tens (G0 G1 : proof_structure) := add_node_ps tens_t (union_ps G0 G1).
Definition add_node_cut (G0 G1 : proof_structure) := add_node_ps cut_t (union_ps G0 G1).
Definition add_node_parr (G : proof_structure) := add_node_ps parr_t G.

Fixpoint ps {l : list formula} (pi : ll l) : proof_structure := match pi with
  | ax_r x                  => ax_ps x
  | ex_r _ _ pi0 sigma      => perm_ps (ps pi0) sigma
  | tens_r _ _ _ _ pi0 pi1  => add_node_tens (ps pi0) (ps pi1)
  | parr_r _ _ _ pi0        => add_node_parr (ps pi0)
  | cut_r _ _ _ pi0 pi1     => add_node_cut (ps pi0) (ps pi1)
  end.

Lemma ps_consistent {l : list formula} (pi : ll l) : sequent (ps pi) = l.
Proof.
  induction pi as [ | | A B l0 l1 pi0 H0 pi1 H1 | A B l0 pi0 H0 | A l0 l1 pi0 H0 pi1 H1].
  - apply ax_sequent.
  - by apply perm_sequent.
  - rewrite add_node_sequent union_sequent H0 H1; cbn.
    revert H0 H1.
    unfold union_order, sequent.
    destruct (order (ps pi0)) as [ | e0 o0] eqn:Ho0; try by [].
    destruct (order (ps pi1)) as [ | e1 o1] eqn:Ho1; try by [].
    rewrite Ho0 Ho1 /=.
    move => /eqP; cbn => /andP[/eqP-E0 _].
    move => /eqP; cbn => /andP[/eqP-E1 _].
    by replace (tens A B) with (tens (flabel e0) (flabel e1)) by by rewrite E0 E1.
  - rewrite add_node_sequent H0.
    revert H0.
    unfold sequent.
    destruct (order (ps pi0)) as [ | e0 [ | e1 o]] eqn:Ho; try by [].
    rewrite Ho /=.
    by move => /eqP; cbn => /andP[/eqP--> /andP[/eqP--> _]].
  - rewrite add_node_sequent union_sequent H0 H1; cbn.
    revert H0 H1.
    unfold union_order, sequent.
    destruct (order (ps pi0)) as [ | e0 o0] eqn:Ho0; try by [].
    destruct (order (ps pi1)) as [ | e1 o1] eqn:Ho1; try by [].
    rewrite Ho0 Ho1 /=.
    move => /eqP; cbn => /andP[/eqP-E0 _].
    move => /eqP; cbn => /andP[/eqP-E1 _].
    replace (@flabel _ (_ ⊎ _) (inl e0)) with A.
    replace (@flabel _ (_ ⊎ _) (inr e1)) with (dual A).
    case_if.
Qed.



(** ** Proof Net of a Proof Sequent *)
Lemma add_node_s0 (t : trilean) (G : proof_structure) (e0 e1 : edge G) :
  forall l, order G = e0 :: e1 :: l ->
  (inl (source e0)) \in ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)).
Proof. intros ? O. destruct (add_node_hyp O e0). rewrite !in_set; cbn. splitb. Qed.

Lemma add_node_s1 (t : trilean) (G : proof_structure) (e0 e1 : edge G) :
  forall l, order G = e0 :: e1 :: l ->
  (inl (source e1)) \in ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)).
Proof. intros ? O. destruct (add_node_hyp O e1). rewrite !in_set; cbn. splitb. Qed.

Definition add_node_iso_v_bij_fwd (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  l (O : order G = e0 :: e1 :: l) :
  @add_concl_graph _
    (@add_concl_graph _
      (add_node_graph t e0 e1) (Sub (inl (source e0)) (add_node_s0 _ O)) c (flabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ O))) c (flabel e1) ->
  add_node_graph_1 t e0 e1 :=
  fun v => match v with
  | inl (inl (exist u _)) => u
  | inl (inr tt)          => inl (target e0)
  | inr tt                => inl (target e1)
  end.

Definition add_node_iso_v_bij_bwd (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  l (O : order G = e0 :: e1 :: l) :
  add_node_graph_1 t e0 e1 ->
  @add_concl_graph _
    (@add_concl_graph _
      (add_node_graph t e0 e1) (Sub (inl (source e0)) (add_node_s0 _ O)) c (flabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ O))) c (flabel e1) :=
  fun v => if @boolP (v \in [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1))
  is AltTrue p then inl (inl (Sub v p)) else if v == inl (target e0) then inl (inr tt) else inr tt.

Lemma add_node_iso_v_bijK (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  l (O : order G = e0 :: e1 :: l) :
  cancel (@add_node_iso_v_bij_fwd t _ _ _ _ O) (@add_node_iso_v_bij_bwd t _ _ _ _ O).
Proof.
  intros [[[v V] | []] | []]; cbn; unfold add_node_iso_v_bij_bwd.
  - case: {-}_ /boolP => [? | /negP ? //]; cbnb.
  - case: {-}_ /boolP => [Hc | ?].
    + contradict Hc; apply /negP.
      rewrite !in_set. caseb.
    + case_if.
  - case: {-}_ /boolP => [Hc | ?].
    + contradict Hc; apply /negP.
      rewrite !in_set. caseb.
    + case_if.
      enough (target e1 <> target e0) by by [].
      elim (p_order G) => _.
      rewrite O cons_uniq in_cons negb_or => /andP[/andP[/eqP Neq _] _] _.
      contradict Neq.
      assert (vlabel (target e1) = c) by (apply p_order; rewrite O !in_cons; caseb).
      by apply one_target_c.
Qed.

Lemma add_node_iso_v_bijK' (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  l (O : order G = e0 :: e1 :: l) :
  cancel (@add_node_iso_v_bij_bwd t _ _ _ _ O) (@add_node_iso_v_bij_fwd t _ _ _ _ O).
Proof.
  intros [v | v]; unfold add_node_iso_v_bij_bwd; case: {-}_ /boolP => [? | In]; cbnb.
  - case_if. cbnb.
    by revert In; rewrite !in_set; cbn => /nandP[/negPn /eqP -> | /nandP[/negPn /eqP ? | ]].
  - contradict In; apply /negP /negPn.
    rewrite !in_set. splitb.
Qed.

Definition add_node_iso_v (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  l (O : order G = e0 :: e1 :: l) := {|
  bij_fwd := @add_node_iso_v_bij_fwd t _ _ _ _ O;
  bij_bwd:= @add_node_iso_v_bij_bwd _ _ _ _ _ _;
  bijK:= @add_node_iso_v_bijK _ _ _ _ _ _;
  bijK':= add_node_iso_v_bijK' _;
  |}.

Definition add_node_iso_e_bij_fwd (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  l (O : order G = e0 :: e1 :: l) :
  edge (@add_concl_graph _
    (@add_concl_graph _
      (add_node_graph t e0 e1) (Sub (inl (source e0)) (add_node_s0 _ O)) c (flabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ O))) c (flabel e1)) ->
  edge (add_node_graph_1 t e0 e1) :=
  fun e => match e with
  | Some (inl (Some (inl (exist a _)))) => a
  | Some (inl (Some (inr a)))           => match a with end
  | Some (inl (None))                   => (Some (Some (inl e0)))
  | Some (inr a)                        => match a with end
  | None                                => Some (Some (inl e1))
  end.

Definition add_node_iso_e_bij_bwd (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  l (O : order G = e0 :: e1 :: l) :
  edge (add_node_graph_1 t e0 e1) ->
  edge (@add_concl_graph _
    (@add_concl_graph _
      (add_node_graph t e0 e1) (Sub (inl (source e0)) (add_node_s0 _ O)) c (flabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ O))) c (flabel e1)) :=
  fun e => if @boolP (e \in edge_set ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)))
  is AltTrue p then Some (inl (Some (inl (Sub e p))))
  else if e == Some (Some (inl e0)) then Some (inl (None)) else None.
(* TODO 30 secs pour cette definition *)

Lemma add_node_iso_e_bijK (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  l (O : order G = e0 :: e1 :: l) :
  cancel (@add_node_iso_e_bij_fwd t _ _ _ _ O) (@add_node_iso_e_bij_bwd t _ _ _ _ O).
Proof.
  intros [[[[[e E] | []] | ] | []] | ]; cbn; unfold add_node_iso_e_bij_bwd; case: {-}_ /boolP => [Hc | ?].
  - apply /eqP; cbn; rewrite SubK; destruct e as [[[? | ?] | ] | ]; by cbn.
  - by contradict E; apply /negP.
  - contradict Hc; apply /negP. rewrite !in_set. caseb.
  - case_if.
  - contradict Hc; apply /negP. rewrite !in_set. caseb.
  - case_if. subst.
    elim (p_order G) => _.
    by rewrite O cons_uniq in_cons negb_or => /andP[/andP[/eqP-Neq _] _].
Qed.

Lemma add_node_iso_e_bijK' (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  l (O : order G = e0 :: e1 :: l) :
  cancel (@add_node_iso_e_bij_bwd t _ _ _ _ O) (@add_node_iso_e_bij_fwd t _ _ _ _ O).
Proof.
  assert (vlabel (target e0) = c /\ vlabel (target e1) = c) as [P0 P1]
    by (split; apply p_order; rewrite O !in_cons; caseb).
  intros [[[e | e] | ] | ]; unfold add_node_iso_e_bij_bwd.
  - case: {-}_ /boolP => [? | In]; cbnb.
    case_if; cbnb. apply /eqP.
    revert In; rewrite !in_set; cbn =>
      /nandP[/nandP[/negPn/eqP-E | /nandP[/negPn/eqP-E | ]] | /nandP[/negPn/eqP-E | /nandP[/negPn/eqP-E | ]]] //.
    + destruct (add_node_hyp O e) as [_ He]. by rewrite E eq_refl in He.
    + destruct (add_node_hyp O e) as [He _]. by rewrite E eq_refl in He.
    + symmetry; by apply one_target_c.
    + enough (e = e0) by by [].
      by apply one_target_c.
  - case: {-}_ /boolP => [? | In]; cbnb.
    contradict In; apply /negP/negPn. by rewrite !in_set.
  - case: {-}_ /boolP => [? | In]; cbnb.
    contradict In; apply /negP/negPn.
    rewrite !in_set; cbn. splitb.
    all: (by destruct (add_node_hyp O e0)) || by destruct t.
  - case: {-}_ /boolP => [? | In]; cbnb.
    contradict In; apply /negP/negPn.
    rewrite !in_set; cbn. splitb.
    all: (by destruct (add_node_hyp O e1)) || by destruct t.
Qed.

Definition add_node_iso_e (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  l (O : order G = e0 :: e1 :: l) := {|
  bij_fwd := @add_node_iso_e_bij_fwd t _ _ _ _ O;
  bij_bwd:= @add_node_iso_e_bij_bwd _ _ _ _ _ _;
  bijK:= @add_node_iso_e_bijK _ _ _ _ _ _;
  bijK':= add_node_iso_e_bijK' _;
  |}.

Lemma add_node_iso_ihom (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  l (O : order G = e0 :: e1 :: l) :
  is_ihom (add_node_iso_v t O) (add_node_iso_e t O) pred0.
Proof.
  assert (vlabel (target e0) = c /\ vlabel (target e1) = c) as [? ?]
    by (split; apply p_order; rewrite O !in_cons; caseb).
  split.
  - by intros [[[[[? ?] | []] | ] | []] | ] [].
  - by intros [[[[? | ?] ?] | []] | []].
  - assert (llabel e0 /\ llabel e1) as [? ?] by (split; apply p_noleft; caseb).
    move => [[[[[[[[? | ?] | ] | ] ?] | []] | ] | []] | ] //; by cbnb; case_if.
Qed.

Definition add_node_iso (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  l (O : order G = e0 :: e1 :: l) := {|
  iso_v := add_node_iso_v t O;
  iso_e := add_node_iso_e _ _;
  iso_d := pred0;
  iso_ihom := add_node_iso_ihom _ _ |}.

Definition add_node_parr_iso_0 (G : base_graph) (e0 e1 : edge G) :
  (G ⊎ unit_graph (⅋) ⊎ unit_graph c)
  ∔ [inl (inl (source e0)), (flabel e0, true), inl (inr tt)]
  ∔ [inl (inr tt), (parr (flabel e0) (flabel e1), true), inr tt]
  ≃
  (G ⊎ (unit_graph (⅋) ⊎ unit_graph c))
  ∔ [inr (inl tt), (parr (flabel e0) (flabel e1), true), inr (inr tt)]
  ∔ [inl (source e0), (flabel e0, true), inr (inl tt)].
Proof.
  etransitivity. apply add_edge_C. symmetry.
  apply (add_edge_iso (add_edge_iso (union_A G (unit_graph (⅋)) (unit_graph c))
    (inr (inl tt)) (parr (flabel e0) (flabel e1), true) (inr (inr tt)))).
Defined.

Definition add_node_parr_iso_1 (G : base_graph) (e0 e1 : edge G) :
  (G ⊎ unit_graph (⅋) ⊎ unit_graph c)
  ∔ [inl (inl (source e0)), (flabel e0, true), inl (inr tt)]
  ∔ [inl (inl (source e1)), (flabel e1, false), inl (inr tt)]
  ∔ [inl (inr tt), (parr (flabel e0) (flabel e1), true), inr tt]
  ≃
  (G ⊎ (unit_graph (⅋) ⊎ unit_graph c))
  ∔ [inr (inl tt), (parr (flabel e0) (flabel e1), true), inr (inr tt)]
  ∔ [inl (source e0), (flabel e0, true), inr (inl tt)]
  ∔ [inl (source e1), (flabel e1, false), inr (inl tt)].
Proof.
  etransitivity. apply add_edge_C.
  apply (add_edge_iso (add_node_parr_iso_0 e0 e1)).
Defined.

Definition add_node_parr_iso_2 (G : base_graph) (e0 e1 : edge G) :
  (G ⊎ unit_graph (⅋) ⊎ unit_graph c)
  ∔ [inl (inl (source e0)), (flabel e0, true), inl (inr tt)]
  ∔ [inl (inl (source e1)), (flabel e1, false), inl (inr tt)]
  ≃
  ((G ⊎ unit_graph (⅋))
  ∔ [inl (source e0), (flabel e0, true), inr tt])
  ∔ [inl (source e1), (flabel e1, false), inr tt] ⊎ unit_graph c .
Proof.
  etransitivity.
  - symmetry. apply (add_edge_iso (@union_add_edge_l _ _ (G ⊎ unit_graph _) _ _ _ _)).
  - symmetry. apply union_add_edge_l.
Defined.

Definition add_node_parr_iso (G : base_graph) (e0 e1 : edge G) :
  add_node_graph_1 parr_t e0 e1 ≃
  @add_concl_graph _ (add_parr_graph (source e0) (source e1) (flabel e0) (flabel e1))
  (inr tt) c (parr (flabel e0) (flabel e1)).
Proof.
  unfold add_node_graph_1, add_concl_graph, add_parr_graph, edge_graph, two_graph, "∔".
  etransitivity. apply (add_edge_iso (add_edge_iso (@union_add_edge_r _ _ G _ _ _ _) _ _ _)).
  etransitivity. symmetry. apply add_node_parr_iso_1.
  apply (add_edge_iso (add_node_parr_iso_2 e0 e1)).
Defined.

Lemma add_node_parr_correct (G : proof_structure) : correct G -> correct (add_node_parr G).
Proof.
  intro H.
  rewrite /= /add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; trivial.
  enough (H': correct (@add_concl_graph _ (@add_concl_graph _ (add_node_graph parr_t e0 e1)
    (Sub (inl (source e0)) (add_node_s0 _ O)) c (flabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ O))) c (flabel e1)))
    by apply (rem_concl_correct (rem_concl_correct H')).
  by apply (iso_correct (add_node_iso parr_t O)),
    (iso_correct (add_node_parr_iso e0 e1)), add_concl_correct, add_parr_correct.
Qed.


Definition add_node_tens_iso_0 (G0 G1 : base_graph) (e0 : edge G0) (e1 : edge G1) :
  G0 ⊎ G1 ⊎ (unit_graph (⊗) ⊎ unit_graph c)
  ∔ [inl tt, (tens (flabel e0) (flabel e1), true), inr tt]
  ≃
  (G0 ⊎ G1 ⊎ unit_graph (⊗) ⊎ unit_graph c)
  ∔ [inl (inr tt), (tens (flabel e0) (flabel e1), true), inr tt].
Proof.
  etransitivity. apply (@union_add_edge_r _ _ (G0 ⊎ G1) (unit_graph _ ⊎ unit_graph _) _ _ _).
  apply (add_edge_iso (union_A (G0 ⊎ G1) (unit_graph _) (unit_graph _))).
Defined.

Definition add_node_tens_iso_1 (G0 G1 : base_graph) (e0 : edge G0) (e1 : edge G1) :
  ((G1 ⊎ (G0 ⊎ unit_graph (⊗))
  ∔ [inl (source e0), (flabel e0, true), inr tt])
  ∔ [inl (source e1), (flabel e1, false), inr (inr tt)]
  ⊎ unit_graph c)
  ≃
  ((G1 ⊎ (G0 ⊎ unit_graph (⊗)))
  ∔ [inr (inl (source e0)), (flabel e0, true), inr (inr tt)]
  ∔ [inl (source e1), (flabel e1, false), inr (inr tt)]
  ⊎ unit_graph c).
Proof.
  apply union_iso; [ | reflexivity].
  apply (add_edge_iso (@union_add_edge_r _ _ _ (_ ⊎ unit_graph _) _  _ _) (inl (source e1)) _ (inr (inr tt))).
Defined.

Definition add_node_tens_iso_2 (G0 G1 : base_graph) (e0 : edge G0) (e1 : edge G1) :
  ((G1 ⊎ (G0 ⊎ unit_graph (⊗)))
  ∔ [inr (inl (source e0)), (flabel e0, true), inr (inr tt)]
  ∔ [inl (source e1), (flabel e1, false), inr (inr tt)]
  ⊎ unit_graph c)
  ≃
  ((G1 ⊎ (G0 ⊎ unit_graph (⊗))) ⊎ unit_graph c)
  ∔ [inl (inr (inl (source e0))), (flabel e0, true), inl (inr (inr tt))]
  ∔ [inl (inl (source e1)), (flabel e1, false), inl (inr (inr tt))].
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
  @add_concl_graph _
    (@union_edge_graph _ G1
      (@add_concl_graph _ G0 (source e0) (⊗) (flabel e0))
      (source e1) (inr tt) (flabel e1, false))
  (inr (inr tt)) c (tens (flabel e0) (flabel e1)).
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

Lemma add_node_tens_correct (G0 G1 : proof_structure) :
  (exists v0 l0, order G0 = v0 :: l0) -> (exists v1 l1, order G1 = v1 :: l1) ->
  correct G0 -> correct G1 -> correct (add_node_tens G0 G1).
Proof.
  intros [e0 [l0 Hl0]] [e1 [l1 Hl1]] H0 H1.
  assert (exists l, order (union_ps G0 G1) = inl e0 :: inr e1 :: l) as [l Hl].
  { rewrite /= /union_order Hl0 Hl1.
    by exists ([seq inr i | i <- l1] ++ [seq inl i | i <- l0]). }
  rewrite /= /add_node_graph_data_bis /union_order Hl0 Hl1.
  enough (H': correct (@add_concl_graph _ (@add_concl_graph _ (@add_node_graph tens_t (G0 ⊎ G1) (inl e0) (inr e1))
    (Sub (_ : @add_node_graph_1 tens_t (G0 ⊎ G1) (inl e0) (inr e1)) (add_node_s0 _ Hl)) c (flabel e0))
    (inl (Sub (_ : @add_node_graph_1 tens_t (G0 ⊎ G1) (inl e0) (inr e1)) (add_node_s1 _ Hl))) c (flabel e1)))
    by apply (rem_concl_correct (rem_concl_correct H')).
  apply (iso_correct (add_node_iso tens_t Hl)),
    (iso_correct (add_node_tens_iso e0 e1)), add_concl_correct, union_edge_correct,
    add_concl_correct; caseb.
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
  @union_edge_graph _ G1 (@add_concl_graph _ G0 (source e0) cut (flabel e0))
    (source e1) (inr tt) (flabel e1, true).
Proof.
  unfold add_node_graph_1, union_edge_graph, add_concl_graph, edge_graph, two_graph, "∔"; cbn.
  symmetry.
  etransitivity. apply (add_edge_iso (@union_add_edge_r _ _ _ _ _ _ _)).
  apply (add_edge_iso (@add_edge_iso _ _ _ _ (add_node_cut_iso_0 e0 e1)
    (inr (inl (source e0))) _ (inr (inr tt)))).
Defined.

Lemma add_node_cut_correct (G0 G1 :proof_structure) :
  (exists e0 l0 e1 l1, order G0 = e0 :: l0 /\ order G1 = e1 :: l1 /\ flabel e1 = dual (flabel e0)) ->
  correct G0 -> correct G1 -> correct (add_node_cut G0 G1).
Proof.
  intros [e0 [l0 [e1 [l1 [Hl0 [Hl1 ?]]]]]] H0 H1.
  assert (exists l, order (union_ps G0 G1) = inl e0 :: inr e1 :: l) as [l Hl].
  { rewrite /= /union_order Hl0 Hl1.
    by exists ([seq inr i | i <- l1] ++ [seq inl i | i <- l0]). }
  rewrite /= /add_node_graph_data_bis /union_order Hl0 Hl1.
  case_if.
  enough (H': correct (@add_concl_graph _ (@add_concl_graph _ (@add_node_graph cut_t (G0 ⊎ G1) (inl e0) (inr e1))
    (Sub (_ : @add_node_graph_1 cut_t (G0 ⊎ G1) (inl e0) (inr e1)) (add_node_s0 _ Hl)) c (flabel e0))
    (inl (Sub (_ : @add_node_graph_1 cut_t (G0 ⊎ G1) (inl e0) (inr e1)) (add_node_s1 _ Hl))) c (flabel e1)))
    by apply (rem_concl_correct (rem_concl_correct H')).
  apply (iso_correct (add_node_iso cut_t Hl)), (iso_correct (add_node_cut_iso e0 e1)),
    union_edge_correct, add_concl_correct; caseb.
Qed.


Lemma sound l (pi : ll l) : correct (ps pi).
Proof.
  induction pi as [ | | ? ? ? ? pi0 ? pi1 ? | | A ? ? pi0 ? pi1 ?].
  - apply ax_correct.
  - trivial.
  - apply add_node_tens_correct; trivial.
    + destruct (order (ps pi0)) as [ | e O] eqn:HO.
      * assert (Hf : sequent (ps pi0) = [::]) by by rewrite /sequent HO.
        by rewrite ps_consistent in Hf.
      * by exists e, O.
    + destruct (order (ps pi1)) as [ | e O] eqn:HO.
      * assert (Hf : sequent (ps pi1) = [::]) by by rewrite /sequent HO.
        by rewrite ps_consistent in Hf.
      * by exists e, O.
  - by apply add_node_parr_correct.
  - apply add_node_cut_correct; trivial.
    destruct (order (ps pi0)) as [ | e0 O0] eqn:HO0.
    1:{ assert (Hf : sequent (ps pi0) = [::]) by by rewrite /sequent HO0.
      by rewrite ps_consistent in Hf. }
    destruct (order (ps pi1)) as [ | e1 O1] eqn:HO1.
    1:{ assert (Hf : sequent (ps pi1) = [::]) by by rewrite /sequent HO1.
      by rewrite ps_consistent in Hf. }
    exists e0, O0, e1, O1. splitb.
    assert (Hc0 := ps_consistent pi0);
    assert (Hc1 := ps_consistent pi1).
    rewrite /sequent HO0 /= in Hc0;
    rewrite /sequent HO1 /= in Hc1.
    revert Hc0 => /eqP; cbn => /andP[/eqP--> _];
    revert Hc1 => /eqP; cbn => /andP[/eqP--> _]; trivial.
Qed.

(** * Proof Net of a Proof Sequent *)
Definition pn {l : list formula} (pi : ll l) : proof_net := {|
  ps_of := ps pi;
  p_correct := sound pi;
  |}.

End Atoms.
