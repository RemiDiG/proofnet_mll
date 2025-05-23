(* From a LL proof, return a Proof Net of the same sequent *)

From Coq Require Import Bool.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export mll_prelim graph_more upath supath mll_def mll_basic mll_correct.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Section Atoms.

(** A set of atoms for building formulas *)
Context { atom : DecType }.
(* TODO meilleur moyen de récupérer les notations *)
Notation formula := (@formula atom).
Notation base_graph := (graph (flat rule) (flat (formula * bool))).
Notation graph_data := (@graph_data atom).
Notation proof_structure := (@proof_structure atom).
Notation proof_net := (@proof_net atom).


(** ** Operations on proof nets, at each strata *)
(** * Empty proof structure *)
Definition v_graph : base_graph := {|
  vertex := void;
  edge := void;
  endpoint _ := vfun;
  vlabel := vfun;
  elabel := vfun;
  |}.

Definition v_graph_data : graph_data := {|
  graph_of := v_graph;
  order := [::];
  |}.

Definition v_ps : proof_structure.
Proof. by exists v_graph_data. Defined.

Lemma v_correct_weak : correct_weak v_graph.
Proof. split; intros []. Qed.

Lemma v_notcorrect : ~ correct v_graph.
Proof. by move=> [_ /eqP/cards1P[_ /eqP/eq_set1P[/imsetP[? ? _] _]]]. Qed.



(** * Base case: proof net of an axiom *)
(** Base graph of an axiom *)
Definition ax_graph (A : formula) : base_graph := {|
  vertex := 'I_3;
  edge := 'I_2;
  endpoint b := match b with
  | true => fun e => match val e with
    | 0 => ord1
    | _ => ord2
    end
  | false => fun _ => ord0
  end;
  vlabel v := match val v with
  | 0 => ax
  | _ => c
  end;
  elabel e := match val e with
  | 0 => (dual A, true)
  | _ => (A, true)
  end;
  |}.
(*   c      A^, left   ax    A, left   c
     O     <--------    O   ------->   O
    ord1      ord0    ord0    ord1    ord2   *)

(** Graph data of an axiom *)
Definition ax_graph_data (A : formula) : graph_data := {|
  graph_of := ax_graph A;
  order := [:: ord0; ord1];
  |}.

(** Proof structure of an axiom *)
Lemma ax_p_deg (A : formula) : proper_degree (ax_graph_data A).
Proof. intros [] v; destruct_I v; compute_card_subIn. Qed.

Lemma ax_p_ax_cut (A : formula) : proper_ax_cut (ax_graph_data A).
Proof.
  unfold proper_ax_cut.
  intros [] v Hl; destruct_I v; try by contradict Hl.
  exists ord0, ord1.
  by rewrite /edges_at_out !in_set /=.
Qed.

Lemma ax_p_tens_parr (A : formula) : proper_tens_parr (ax_graph_data A).
Proof. unfold proper_tens_parr. intros [] v Hl; destruct_I v; by contradict Hl. Qed.

Lemma ax_p_noleft (A : formula) : proper_noleft (ax_graph_data A).
Proof. move=> e _. by destruct_I e. Qed.

Lemma ax_p_order_full (A : formula) : proper_order_full (ax_graph_data A).
Proof. intro e. by destruct_I e. Qed.

Lemma ax_p_order_uniq (A : formula) : proper_order_uniq (ax_graph_data A).
Proof. trivial. Qed.

Definition ax_ps (A : formula) : proof_structure := {|
  graph_data_of := ax_graph_data A;
  p_deg := @ax_p_deg _;
  p_ax_cut := @ax_p_ax_cut _;
  p_tens_parr := @ax_p_tens_parr _;
  p_noleft := @ax_p_noleft _;
  p_order_full := @ax_p_order_full _;
  p_order_uniq := ax_p_order_uniq _;
  |}.

(** Proof net of an axiom *)
(* All switching paths are of length at most 2, so we look at all 3 first edges in
  a cycle to conclude *)
Lemma ax_uacyclic (A : formula) : uacyclic (@switching _ (ax_graph A)).
Proof.
  intros u [p P]; destruct_I u; apply /eqP; cbn; apply /eqP.
  all: destruct p as [ | [a [ | ]] [ | [b [ | ]] [ | [c [ | ]] p]]];
    try (destruct_I a); try (destruct_I b); try (destruct_I c); try by [].
  all: contradict P; apply /negP; cbn; caseb.
Qed.

Lemma ax_uconnected (A : formula) : uconnected (@switching_left _ (ax_graph A)).
Proof.
  set fp : ax_ps A -> ax_ps A -> @upath _ _ (ax_ps A) :=
    fun u v => match val u, val v with
    | 0, 1 => [:: forward ord0]
    | 0, 2 => [:: forward ord1]
    | 1, 0 => [:: backward ord0]
    | 1, 2 => [:: backward ord0; forward ord1]
    | 2, 0 => [:: backward ord1]
    | 2, 1 => [:: backward ord1; forward ord0]
    | _, _ => [::]
    end.
  move=> u v.
  assert (H : well_colored_utrail switching_left u v (fp u v)) by by destruct_I u; destruct_I v.
  by exists (Sub (fp u v) H).
Qed.

Lemma ax_correct_weak (A : formula) : correct_weak (ax_graph A).
Proof.
  split.
  - apply ax_uacyclic.
  - apply ax_uconnected.
Qed.

Lemma ax_correct (A : formula) : correct (ax_graph A).
Proof.
  apply correct_from_weak, ax_correct_weak.
  apply fintype0, ord0.
Qed.

Definition ax_pn (A : formula) : proof_net := {|
  ps_of := ax_ps A;
  p_correct := @ax_correct _;
  |}.

(** Sequent of an axiom *)
Lemma ax_sequent (A : formula) : sequent (ax_graph_data A) = [:: dual A; A].
Proof. trivial. Qed.



(** * Permuting the conclusions of a proof structure *)
(** Graph data of a permutation *)
(* Typically A is a formula or an edge of G *)
Definition perm_graph_data {A : Type} {l l' : list A} (sigma : Permutation_Type l l') (G : graph_data) :
  graph_data := {|
  graph_of := G;
  order := perm_of sigma (order G);
  |}.

(** Proof structure of a permutation *)
Lemma perm_p_order_full {A : Type} {l l' : list A} (sigma : Permutation_Type l l') (G : proof_structure) :
  proper_order_full (perm_graph_data sigma G).
Proof.
  rewrite /proper_order_full /=. move=> *.
  rewrite perm_of_in. apply p_order_full.
Qed.

Lemma perm_p_order_uniq {A : Type} {l l' : list A} (sigma : Permutation_Type l l') (G : proof_structure) :
  proper_order_uniq (perm_graph_data sigma G).
Proof. rewrite /proper_order_uniq /= perm_of_uniq. apply p_order_uniq. Qed.

Definition perm_ps {A : Type} {l l' : list A} (sigma : Permutation_Type l l') (G : proof_structure) :
  proof_structure := {|
  graph_data_of := perm_graph_data sigma G;
  p_deg := @p_deg _ _;
  p_ax_cut := @p_ax_cut _ _;
  p_tens_parr := @p_tens_parr _ _;
  p_noleft := @p_noleft _ _;
  p_order_full := @perm_p_order_full _ _ _ _ _;
  p_order_uniq := perm_p_order_uniq _ _;
  |}.

(** Proof net of a permutation *)
Definition perm_pn {A : Type} {l l' : list A} (sigma : Permutation_Type l l') (G : proof_net) :
  proof_net := {|
  ps_of := perm_ps sigma G;
  p_correct := @p_correct _ _;
  |}.

(** Sequent of a permutation *)
Lemma perm_sequent {l l' : list formula} (sigma : Permutation_Type l l') (G : graph_data) :
  sequent G = l -> sequent (perm_graph_data sigma G) = l'.
Proof. move=> ?. subst l. by rewrite /sequent -perm_of_map perm_of_consistent. Qed.



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
  move=> Gi fv fe v e.
  destruct i, e as [e | e].
  all: assert (injective fe) by (apply inl_inj || apply inr_inj).
  all: rewrite ?mem_imset // !in_set; cbn; trivial.
  all: by apply /eqP/memPn => ? /imsetP[? _] ->.
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
  all: revert Hneq => /eqP/negPf-->.
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
  - exists (inl el), (inl er); by rewrite !union_edges_at_inl !mem_imset /=.
  - exists (inr el), (inr er); by rewrite !union_edges_at_inr !mem_imset /=.
Qed.

Lemma union_p_tens_parr (G0 G1 : proof_structure) : proper_tens_parr (union_graph_data G0 G1).
Proof.
  unfold proper_tens_parr.
  intros b [v | v] Hl;
  [set fe := inl : edge G0 -> edge (G0 ⊎ G1) | set fe := inr : edge G1 -> edge (G0 ⊎ G1)].
  all: destruct (p_tens_parr Hl) as [el [er [ec He]]].
  all: exists (fe el), (fe er), (fe ec).
  all: rewrite ?union_edges_at_inl ?union_edges_at_inr !mem_imset //;
    apply inl_inj || apply inr_inj.
Qed.

Lemma union_p_noleft (G0 G1 : proof_structure) : proper_noleft (union_graph_data G0 G1).
Proof. intros [? | ?]; apply p_noleft. Qed.

Lemma union_p_order_full (G0 G1 : proof_structure) : proper_order_full (union_graph_data G0 G1).
Proof.
  rewrite /proper_order_full.
  move=> [e | e]; [rewrite union_order_inl | rewrite union_order_inr];
  apply p_order_full.
Qed.

Lemma union_p_order_uniq (G0 G1 : proof_structure) : proper_order_uniq (union_graph_data G0 G1).
Proof.
  have := p_order_uniq G0.
  have := p_order_uniq G1.
  rewrite /proper_order_uniq /= /union_order.
  assert (injective (inl : edge G0 -> edge (G0 ⊎ G1)) /\ injective (inr : edge G1 -> edge (G0 ⊎ G1)))
    as [? ?] by by split => ? ? /eqP; cbn => /eqP-->.
  destruct (order G0) as [ | e0 o0], (order G1) as [ | e1 o1];
  rewrite ?map_inj_uniq // 4!cons_uniq cat_uniq in_cons !mem_cat !negb_or !map_inj_uniq
    // !mem_map // => /andP[-> ->] /andP[-> ->].
  cbn. rewrite !andb_true_r. clear.
  repeat (apply/andP; split).
  - by induction o1.
  - by induction o0.
  - induction o0; first by [].
    rewrite /= negb_or. apply/andP. split; last by assumption.
    clear. by induction o1.
Qed.

Definition union_ps (G0 G1 : proof_structure) : proof_structure := {|
  graph_data_of := union_graph_data G0 G1;
  p_deg := @union_p_deg _ _;
  p_ax_cut := @union_p_ax_cut _ _;
  p_tens_parr := @union_p_tens_parr _ _;
  p_noleft := @union_p_noleft _ _;
  p_order_full := @union_p_order_full _ _;
  p_order_uniq := union_p_order_uniq _ _;
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
(** Set with 3 elements to make cases on tens, parr and cut *)
Inductive trilean :=
  | tens_t
  | parr_t
  | cut_t.

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
(* We do it after adding nodes as in an arbitrary graph there could be only the removed nodes. *)
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
  | cut_t => [::] | _ => [:: Some (Some (inr None))] end
  ++  add_node_type_order t e0 e1 (add_node_order_1 e0 e1).

Lemma add_node_consistent_order (t : trilean) {G : graph_data} (e0 e1 : edge G) :
  let S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1) in
  all (pred_of_set (edge_set S)) (add_node_order_2 t e0 e1).
Proof.
  apply/allP => e E.
  rewrite /edge_set. apply/setIdP.
  rewrite !in_set !in_set1 !andb_true_r.
  move: E. rewrite /add_node_order_2 mem_cat => /orP[].
  - destruct t; rewrite ?in_nil // mem_seq1 => /eqP-?; subst e; splitb.
  - rewrite /add_node_order_1 /add_node_type_order.
    move=> /mapP[a A ?]. subst e. cbn.
    move: A. by rewrite mem_filter => /andP[/andP[/andP[/andP[-> ->] ->] ->] _].
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
Lemma add_node_c {G : proof_structure} (e0 e1 : edge G) l :
  order G = e0 :: e1 :: l ->
  vlabel (target e0) = c /\ vlabel (target e1) = c.
Proof. intro O. split; apply p_order_full; rewrite O !in_cons; caseb. Qed.

Lemma add_node_neq_t {G : proof_structure} (e0 e1 : edge G) l :
  order G = e0 :: e1 :: l -> target e0 <> target e1.
Proof.
  intro O.
  destruct (add_node_c O).
  have := p_order_uniq G.
  rewrite /proper_order_uniq O cons_uniq in_cons negb_or => /andP[/andP[/eqP-Neq _] _] ?.
  contradict Neq.
  by apply one_target_c.
Qed.

Lemma add_node_hyp {G : proof_structure} (e0 e1 : edge G) l :
  order G = e0 :: e1 :: l ->
  forall e, source e != target e0 /\ source e != target e1.
Proof. intros O e. split; apply /eqP; apply no_source_c, p_order_full; rewrite O !in_cons; caseb. Qed.

(* The list add_node_order_1 is just order without e0 and e1 *)
Lemma add_node_order_1_eq {G : proof_structure} (e0 e1 : edge G) l :
  order G = e0 :: e1 :: l ->
  add_node_order_1 e0 e1 = [seq x <- order G | (x != e0) && (x != e1)].
Proof.
  intro O.
  rewrite /add_node_order_1.
  apply eq_in_filter => e E.
  destruct (add_node_c O).
  destruct (add_node_hyp O e) as [-> ->]. rewrite !andb_true_r.
  f_equal; [set ei := e0 | set ei := e1].
  all: destruct (eq_comparable e ei) as [ | Neq]; first by (subst e; by rewrite !eq_refl).
  all: assert (e != ei) as -> by by apply /eqP.
  all: apply /eqP => Hc.
  all: contradict Neq.
  all: by apply one_target_c.
Qed.

Lemma add_node_new_edges_at_in (t : trilean) (G : proof_structure) (e0 e1 : edge G) l :
  order G = e0 :: e1 :: l ->
  let S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1) in
  None \in edge_set S /\ Some None \in edge_set S.
Proof.
  intros O S.
  rewrite !in_set !in_set1 !andb_true_r.
  destruct (add_node_hyp O e0); destruct (add_node_hyp O e1).
  splitb; by destruct t.
Qed.

Definition add_node_transport_1 (t : trilean) (G : graph_data) (e0 e1 : edge G) (e : edge G) :
  edge (add_node_graph_1 t e0 e1) :=
  if e == e1 then None
  else if e == e0 then Some None
  else Some (Some (inl e)).

Lemma add_node_transport_consistent (t : trilean) (G : proof_structure) (e0 e1 : edge G) l :
  order G = e0 :: e1 :: l ->
  forall e, add_node_transport_1 t e0 e1 e \in
  edge_set ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)).
Proof.
  intros O e.
  set S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1).
  destruct (add_node_c O), (add_node_new_edges_at_in t O).
  unfold add_node_transport_1; case_if.
  rewrite !in_set !in_set1 !andb_true_r /=.
  splitb; try apply (add_node_hyp O); cbn; apply /eqP => ?.
  - enough (e = e1) by by [].
    by apply one_target_c.
  - enough (e = e0) by by [].
    by apply one_target_c.
Qed.

Definition add_node_transport (t : trilean) (G : proof_structure) (e0 e1 : edge G) (l : seq (edge G))
  (O : order G = e0 :: e1 :: l) (e : edge G) :
  edge (add_node_graph_data t e0 e1) :=
  Sub (add_node_transport_1 t e0 e1 e) (add_node_transport_consistent t O e).

Lemma add_node_transport_inj (t : trilean) (G : proof_structure) (e0 e1 : edge G) (l : seq (edge G))
  (O : order G = e0 :: e1 :: l) :
  injective (add_node_transport t O).
Proof. move => ? ? /eqP. unfold add_node_transport, add_node_transport_1. cbnb. case_if. Qed.

Lemma add_node_transport_edges (t : trilean) (G : proof_structure) (e0 e1 : edge G) (l : seq (edge G))
  (O : order G = e0 :: e1 :: l) v V b :
  edges_at_outin b (Sub (inl v) V : add_node_graph_data t e0 e1) =
  [set add_node_transport t O e | e in edges_at_outin b v].
Proof.
  destruct (add_node_c O).
  assert (Hneqv := add_node_neq_t O).
  assert (Hneqe : e0 <> e1) by by intros ?; subst.
  apply /setP => e.
  assert ((target e0 == v) = false /\ (target e1 == v) = false) as [? ?].
  { split; apply /eqP; intros ?; subst; contradict V; apply /negP.
    all: by rewrite !in_set !in_set1 eq_refl !andb_true_r ?andb_false_r. }
  set w := Sub (inl v) V : add_node_graph_data t e0 e1.
  set g := add_node_transport t O.
  assert (g_inj := @add_node_transport_inj t _ _ _ _ O).
  destruct e as [[[[e | e] | ] | ] He]; rewrite in_set.
  - enough (Heq : exist _ (Some (Some (inl e))) He = g e).
    { rewrite Heq mem_imset // in_set -Heq. cbnb. }
    apply /eqP; rewrite /g /add_node_transport sub_val_eq /= /add_node_transport_1.
    case_if.
    all: contradict He; apply /negP.
    all: rewrite !in_set !in_set1; caseb.
  - symmetry; apply /negbTE.
    apply/imsetP. move=> [a _ A].
    contradict A. cbnb. case_if.
  - assert (Heq : exist _ (Some None) He = g e0).
    { apply /eqP; rewrite /g /add_node_transport /eqP sub_val_eq /= /add_node_transport_1.
      case_if. }
    rewrite Heq mem_imset // in_set -Heq.
    by destruct b, t.
  - assert (Heq : exist _ None He = g e1).
    { apply /eqP; rewrite /g /add_node_transport sub_val_eq /= /add_node_transport_1.
      case_if. }
    rewrite Heq mem_imset // in_set -Heq.
    by destruct b, t.
Qed.

Lemma add_node_transport_flabel (t : trilean) (G : proof_structure) (e0 e1 : edge G) (l : seq (edge G))
  (O : order G = e0 :: e1 :: l) e :
  flabel (add_node_transport t O e) = flabel e.
Proof. rewrite /add_node_transport /add_node_transport_1 /flabel /=. case_if. Qed.

Lemma add_node_transport_llabel (t : trilean) (G : proof_structure) (e0 e1 : edge G) (l : seq (edge G))
  (O : order G = e0 :: e1 :: l) e :
  e <> e1 -> llabel (add_node_transport t O e) = llabel e.
Proof.
  intro Neq.
  unfold add_node_transport, add_node_transport_1; cbnb; case_if.
  symmetry; apply p_noleft.
  destruct (add_node_c O). caseb.
Qed.

(* We add the node if it respect the rules, otherwise give the empty graph *)
Definition add_node_graph_data_bis (t : trilean) (G : graph_data) : graph_data :=
  match order G with
  | e0 :: e1 :: _ => match t with
    | cut_t => if (flabel e1 == dual (flabel e0)) then add_node_graph_data t e0 e1 else v_graph_data
    | _ => add_node_graph_data t e0 e1
    end
  | _ => v_graph_data
  end.

(** Proof structure for adding a node *)
Lemma add_node_p_deg (t : trilean) (G : proof_structure) : proper_degree (add_node_graph_data_bis t G).
Proof.
  unfold add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; try by [].
  revert t.
  enough (forall t, proper_degree (add_node_graph t e0 e1)).
  { intros []; case_if. }
  intros t b [[v | v] Hv]; cbn.
  - by rewrite (add_node_transport_edges O) -(p_deg b v)
      -(card_imset (edges_at_outin b v) (@add_node_transport_inj t _ _ _ _ O)).
  - set S := [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1).
    destruct (add_node_new_edges_at_in t O) as [Hn Hsn].
    set n := Sub None Hn : edge (add_node_graph_data t e0 e1);
    set sn := Sub (Some None) Hsn : edge (add_node_graph_data t e0 e1).
    destruct t; [set t := tens_t | set t := parr_t | set t := cut_t].
    1,2: assert (Some (Some (inr None)) \in edge_set S /\ inr (inl tt) \in S /\ inr (inr tt) \in S)
          as [Hss [Htn Hcn]] by (rewrite !in_set !in_set1; splitb).
    1,2: set ss := Sub (Some (Some (inr None))) Hss : edge (add_node_graph_data t e0 e1);
         set tn := Sub (inr (inl tt)) Htn : add_node_graph_data t e0 e1;
         set cn := Sub (inr (inr tt)) Hcn : add_node_graph_data t e0 e1.
    1,2: assert (edges_at_in tn = [set n; sn] /\ edges_at_out tn = [set ss] /\
                 edges_at_in cn = [set ss] /\ edges_at_out cn = set0)
          as [Htn_in [Htn_out [Hcn_in Hcn_out]]]
          by by splitb; apply /setP => e; rewrite !in_set ?in_set1;
            destruct e as [[[[e | [[[] | []] | ]] | ] | ] ?].
    3: assert (Htn : inr tt \in S) by (rewrite !in_set !in_set1; apply /andP; by split).
    3: set tn := (Sub (inr tt) Htn : add_node_graph_data t e0 e1).
    3: assert (edges_at_in tn = [set n; sn] /\ edges_at_out tn = set0)
        as [Htn_in Htn_out]
        by (split; apply /setP => e; rewrite !in_set ?in_set1; by destruct e as [[[[e | []] | ] | ] ?]).
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
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; try by [].
  unfold proper_ax_cut.
  enough (Hdone : t <> cut_t \/ flabel e1 = dual (flabel e0) ->
    forall b (v : add_node_graph t e0 e1), vlabel v = (if b then cut else ax) ->
    exists el er : edge (add_node_graph t e0 e1),
    el \in edges_at_outin b v /\ er \in edges_at_outin b v /\ flabel el = dual (flabel er)).
  { case_if; destruct t; try (apply Hdone; caseb); by []. }
  intros Hor b [[v | v] Hv] Hl; cbn in Hl.
  - destruct (p_ax_cut Hl) as [el [er ?]].
    exists (add_node_transport t O el), (add_node_transport t O er).
    rewrite !(add_node_transport_edges O) !mem_imset; try apply add_node_transport_inj.
    by rewrite 2!add_node_transport_flabel /=.
  - destruct b, t, v, Hor as [? | Hf]; try by [].
    exists (add_node_transport cut_t O e1), (add_node_transport cut_t O e0).
    rewrite !add_node_transport_flabel Hf !in_set /=.
    cbn; rewrite /= /add_node_transport_1; case_if.
Qed.

Lemma add_node_p_tens_parr (t : trilean) (G : proof_structure) :
  proper_tens_parr (add_node_graph_data_bis t G).
Proof.
  unfold add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; try by [].
  revert t.
  enough (forall t, proper_tens_parr (add_node_graph t e0 e1)).
  { intros []; case_if. }
  intro t.
  unfold proper_tens_parr.
  move => b [[v | v] V] Hl; simpl in Hl.
  - destruct (p_tens_parr Hl) as [el [er [ec [El [Ell [Er [Erl [Ec Eq]]]]]]]].
    assert (el <> e1 /\ er <> e1) as [? ?].
    { split.
      all: intros ?; subst.
      1: revert El; rewrite in_set => /eqP-?; subst v.
      2: revert Er; rewrite in_set => /eqP-?; subst v.
      all: contradict V; apply /negP.
      all: rewrite !in_set !in_set1; caseb. }
    exists (add_node_transport t O el), (add_node_transport t O er), (add_node_transport t O ec).
    rewrite !(add_node_transport_edges O) !mem_imset; try apply add_node_transport_inj.
    by rewrite !add_node_transport_flabel !add_node_transport_llabel.
  - destruct (add_node_new_edges_at_in t O) as [Hn Hsn].
    set n := Sub None Hn : edge (add_node_graph_data t e0 e1);
    set sn := Sub (Some None) Hsn : edge (add_node_graph_data t e0 e1).
    destruct t; [set t := tens_t | set t := parr_t | ];
    [destruct v as [[] | []] | destruct v as [[] | []] | destruct v as []];
    destruct b; try by [].
    all: assert (Hssn : Some (Some (inr None)) \in edge_set ([set: add_node_graph_1 tens_t e0 e1]
          :\ inl (target e0) :\ inl (target e1))) by (rewrite !in_set !in_set1; splitb).
    all: set ssn := Sub (Some (Some (inr None))) Hssn : edge (add_node_graph_data tens_t e0 e1).
    all: exists sn, n, ssn.
    all: by rewrite !in_set.
Qed.

Lemma add_node_p_noleft (t : trilean) (G : proof_structure) : proper_noleft (add_node_graph_data_bis t G).
Proof.
  unfold add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; try by [].
  revert t.
  enough (forall t, proper_noleft (add_node_graph t e0 e1)).
  { intros []; case_if. }
  intro t.
  destruct (add_node_c O).
  unfold proper_noleft.
  move => [[[[e | e] | ] | ] E] /= Hl //.
  - assert (e <> e0 /\ e <> e1) as [? ?].
    { split => ?; subst; contradict E; apply /negP.
       all: rewrite !in_set !in_set1; caseb. }
    assert (Hr : exist _ (Some (Some (inl e))) E = add_node_transport t O e).
    { apply /eqP; cbn; rewrite /= /add_node_transport_1.
      case_if. }
    by rewrite Hr add_node_transport_llabel // p_noleft.
  - by destruct t;
    [destruct e as [[[] | []] | ] | destruct e as [[[] | []] | ] | destruct e as []].
  - by destruct t;
    simpl in Hl; destruct Hl as [Hlax | [Hlcut | Hlc]].
Qed.

Lemma add_node_p_order_full (t : trilean) (G : proof_structure) :
  proper_order_full (add_node_graph_data_bis t G).
Proof.
  rewrite /add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; try by [].
  move: t.
  enough (forall (t : trilean), proper_order_full (add_node_graph_data t e0 e1)).
  { intros []; case_if. }
  move=> t.
  rewrite /proper_order_full /add_node_order.
  assert (Some None \notin add_node_type_order t e0 e1 (add_node_order_1 e0 e1)
    /\ None \notin add_node_type_order t e0 e1 (add_node_order_1 e0 e1)
    /\ Some (Some (inr None)) \notin add_node_type_order tens_t e0 e1 (add_node_order_1 e0 e1)
    /\ Some (Some (inr None)) \notin add_node_type_order parr_t e0 e1 (add_node_order_1 e0 e1))
    as [? [? [? ?]]].
  { splitb.
    all: rewrite /add_node_type_order (add_node_order_1_eq O).
    all: generalize (order G) as o => o.
    all: induction o as [ | a A IH]; trivial.
    all: change (a :: A) with ([:: a] ++ A).
    all: rewrite filter_cat map_cat mem_cat negb_or IH andb_true_r /=.
    all: case_if. }
  simpl order. rewrite /add_node_order.
  destruct (all_sigP _) as [a A]. simpl.
  intros [[[[e | e] | ] | ] Hin]; cbn;
  rewrite in_seq_sig /= -A /add_node_order_2 /=.
  - apply (iff_stepl (A := e \in order G)); [ | by apply iff_sym, p_order_full].
    assert (e != e0 /\ e != e1) as [He0 He1].
    { split; apply /eqP => Hc;
      contradict Hin; apply /negP;
      rewrite Hc !in_set !in_set1; caseb. }
    destruct t;
    rewrite ?in_cons /add_node_type_order (add_node_order_1_eq O) mem_map ?mem_filter ?He0 ?He1 //=.
    all: by move => ? ? /eqP; cbn => /eqP.
  - by destruct t;
    [destruct e as [[[] | []] | ] | destruct e as [[[] | []] | ] | destruct e as []].
  - destruct t; simpl.
    all: split => H //; contradict H; apply /negP; by rewrite ?in_cons.
  - destruct t; simpl.
    all: split => H //; contradict H; apply /negP; by rewrite ?in_cons.
Qed.

Lemma add_node_p_order_uniq (t : trilean) (G : proof_structure) :
  proper_order_uniq (add_node_graph_data_bis t G).
Proof.
  rewrite /add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 l]] eqn:O; try by [].
  move: t.
  enough (E : forall (t : trilean), proper_order_uniq (add_node_graph_data t e0 e1)).
  { intros []; case_if; apply E. }
  move=> t.
  rewrite /proper_order_uniq /= /add_node_order.
  assert (Some None \notin add_node_type_order t e0 e1 (add_node_order_1 e0 e1)
    /\ None \notin add_node_type_order t e0 e1 (add_node_order_1 e0 e1)
    /\ Some (Some (inr None)) \notin add_node_type_order tens_t e0 e1 (add_node_order_1 e0 e1)
    /\ Some (Some (inr None)) \notin add_node_type_order parr_t e0 e1 (add_node_order_1 e0 e1))
    as [? [? [? ?]]].
  { splitb.
    all: rewrite /add_node_type_order (add_node_order_1_eq O).
    all: generalize (order G) as o => o.
    all: induction o as [ | a A IH]; trivial.
    all: change (a :: A) with ([:: a] ++ A).
    all: rewrite filter_cat map_cat mem_cat negb_or IH andb_true_r /=.
    all: case_if. }
  destruct (all_sigP _) as [a A].
  rewrite /= uniq_seq_sig -A /add_node_order_2.
  destruct t;
  rewrite ?cons_uniq.
  all: splitb.
  all: rewrite (add_node_order_1_eq O) map_inj_uniq //=; first by apply filter_uniq, p_order_uniq.
  all: by move => ? ? /eqP; cbn => /eqP-->.
Qed.

Definition add_node_ps (t : trilean) (G : proof_structure) : proof_structure := {|
  graph_data_of := add_node_graph_data_bis t G;
  p_deg := @add_node_p_deg _ _;
  p_ax_cut := @add_node_p_ax_cut _ _;
  p_tens_parr := @add_node_p_tens_parr _ _;
  p_noleft := @add_node_p_noleft _ _;
  p_order_full := @add_node_p_order_full _ _;
  p_order_uniq := @add_node_p_order_uniq _ _;
  |}.

(** Sequent for adding a node *)
Lemma add_node_sequent_eq (t : trilean) (G : graph_data) (e0 e1 : edge G) :
  sequent (add_node_graph_data t e0 e1) =
  [seq flabel e | e <- add_node_order_2 t e0 e1].
Proof.
  rewrite /add_node_graph_data /= /add_node_order.
  destruct (all_sigP _) as [l ->].
  by rewrite -map_comp.
Qed.

Lemma add_node_sequent_type_order (t : trilean) (G : graph_data) (e0 e1 : edge G) l :
  [seq flabel e | e <- add_node_type_order t e0 e1 l] = [seq flabel e | e <- l].
Proof. by rewrite /add_node_type_order -map_comp. Qed.

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
              else [::]
      | _ => behead (behead (sequent G))
      end
    | _ => [::]
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
    case_if. }
  rewrite add_node_sequent_eq /add_node_order_2 map_cat add_node_sequent_type_order (add_node_order_1_eq O).
  f_equal; [by destruct t | ].
  f_equal.
  rewrite O /= !eq_refl /= andb_false_r.
  apply /all_filterP/allP => e E.
  have := p_order_uniq G.
  rewrite /proper_order_uniq O /= in_cons => /andP[/norP[_ /negP-U0] /andP[/negP-U1 _]].
  by splitb; apply /eqP => ?; subst e.
Qed.



(** ** Proof Net of a Proof Sequent *)
Lemma add_node_s0 (t : trilean) (G : proof_structure) (e0 e1 : edge G) :
  order G = e0 :: e1 :: behead (behead (order G)) ->
  (inl (source e0)) \in ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)).
Proof. move=> O. destruct (add_node_hyp O e0). rewrite !in_set !in_set1; cbn. splitb. Qed.

Lemma add_node_s1 (t : trilean) (G : proof_structure) (e0 e1 : edge G) :
  order G = e0 :: e1 :: behead (behead (order G)) ->
  (inl (source e1)) \in ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)).
Proof. move=> O. destruct (add_node_hyp O e1). rewrite !in_set !in_set1; cbn. splitb. Qed.

Definition add_node_iso_v_bij_fwd (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  (O : order G = e0 :: e1 :: behead (behead (order G))) :
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
  (O : order G = e0 :: e1 :: behead (behead (order G))) :
  add_node_graph_1 t e0 e1 ->
  @add_concl_graph _
    (@add_concl_graph _
      (add_node_graph t e0 e1) (Sub (inl (source e0)) (add_node_s0 _ O)) c (flabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ O))) c (flabel e1) :=
  fun v => if @boolP (v \in [set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1))
  is AltTrue p then inl (inl (Sub v p)) else if v == inl (target e0) then inl (inr tt) else inr tt.

Lemma add_node_iso_v_bijK (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  (O : order G = e0 :: e1 :: behead (behead (order G))) :
  cancel (@add_node_iso_v_bij_fwd t _ _ _ O) (@add_node_iso_v_bij_bwd t _ _ _ O).
Proof.
  intros [[[v V] | []] | []]; cbn; unfold add_node_iso_v_bij_bwd.
  - case: {-}_ /boolP => [? | /negP-? //]; cbnb.
  - case: {-}_ /boolP => [Hc | ?].
    + contradict Hc; apply /negP.
      by rewrite !in_set !in_set1 eq_refl andb_false_r.
    + case_if.
  - case: {-}_ /boolP => [Hc | ?].
    + contradict Hc; apply /negP.
      by rewrite !in_set !in_set1 eq_refl.
    + case_if.
      enough (target e1 <> target e0) by by [].
      apply nesym, (add_node_neq_t O).
Qed.

Lemma add_node_iso_v_bijK' (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  (O : order G = e0 :: e1 :: behead (behead (order G))) :
  cancel (@add_node_iso_v_bij_bwd t _ _ _ O) (@add_node_iso_v_bij_fwd t _ _ _ O).
Proof.
  intros [v | v]; unfold add_node_iso_v_bij_bwd; case: {-}_ /boolP => [? | In]; cbnb.
  - case_if. cbnb.
    by revert In; rewrite !in_set !in_set1 andb_true_r; cbn => /nandP[/negPn/eqP--> | /negPn/eqP-?].
  - contradict In. apply/negP/negPn.
    by rewrite !in_set !in_set1.
Qed.

Definition add_node_iso_v (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  (O : order G = e0 :: e1 :: behead (behead (order G))) := {|
  bij_fwd := @add_node_iso_v_bij_fwd t _ _ _ O;
  bij_bwd:= @add_node_iso_v_bij_bwd _ _ _ _ _;
  bijK:= @add_node_iso_v_bijK _ _ _ _ _;
  bijK':= add_node_iso_v_bijK' _;
  |}.

Definition add_node_iso_e_bij_fwd (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  (O : order G = e0 :: e1 :: behead (behead (order G))) :
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
  (O : order G = e0 :: e1 :: behead (behead (order G))) :
  edge (add_node_graph_1 t e0 e1) ->
  edge (@add_concl_graph _
    (@add_concl_graph _
      (add_node_graph t e0 e1) (Sub (inl (source e0)) (add_node_s0 _ O)) c (flabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ O))) c (flabel e1)) :=
  fun e => if @boolP (e \in edge_set ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)))
  is AltTrue p then Some (inl (Some (inl (Sub e p))))
  else if e == Some (Some (inl e0)) then Some (inl (None)) else None.

Lemma add_node_iso_e_bijK (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  (O : order G = e0 :: e1 :: behead (behead (order G))) :
  cancel (@add_node_iso_e_bij_fwd t _ _ _ O) (@add_node_iso_e_bij_bwd t _ _ _ O).
Proof.
  intros [[[[[e E] | []] | ] | []] | ]; cbn; unfold add_node_iso_e_bij_bwd; case: {-}_ /boolP => [Hc | ?].
  - apply /eqP; cbn; simpl; destruct e as [[[? | ?] | ] | ]; by cbn.
  - by contradict E; apply /negP.
  - contradict Hc; apply /negP. by rewrite !in_set !in_set1 /= eq_refl !andb_false_r.
  - case_if.
  - contradict Hc; apply /negP. by rewrite !in_set !in_set1 /= eq_refl !andb_false_r.
  - case_if.
    have := p_order_uniq G.
    by rewrite /proper_order_uniq O cons_uniq in_cons negb_or => /andP[/andP[/eqP-Neq _] _].
Qed.

Lemma add_node_iso_e_bijK' (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  (O : order G = e0 :: e1 :: behead (behead (order G))) :
  cancel (@add_node_iso_e_bij_bwd t _ _ _ O) (@add_node_iso_e_bij_fwd t _ _ _ O).
Proof.
  destruct (add_node_c O).
  intros [[[e | e] | ] | ]; unfold add_node_iso_e_bij_bwd.
  - case: {-}_ /boolP => [? | In]; cbnb.
    case_if; cbnb. apply /eqP.
    revert In; rewrite !in_set !in_set1 !andb_true_r; cbn =>
      /nandP[/nandP[/negPn/eqP-E | /negPn/eqP-E] | /nandP[/negPn/eqP-E | /negPn/eqP-E]].
    + destruct (add_node_hyp O e) as [_ He]. by rewrite E eq_refl in He.
    + destruct (add_node_hyp O e) as [He _]. by rewrite E eq_refl in He.
    + symmetry; by apply one_target_c.
    + enough (e = e0) by by []. by apply one_target_c.
  - case: {-}_ /boolP => [? | In]; cbnb.
    contradict In; apply /negP/negPn. by rewrite !in_set !in_set1.
  - case: {-}_ /boolP => [? | In]; cbnb.
    contradict In; apply /negP/negPn.
    rewrite !in_set !in_set1; cbn.
    destruct (add_node_hyp O e0), t; splitb.
  - case: {-}_ /boolP => [? | In]; cbnb.
    contradict In; apply /negP/negPn.
    rewrite !in_set !in_set1; cbn.
    destruct (add_node_hyp O e1), t; splitb.
Qed.

Definition add_node_iso_e (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  (O : order G = e0 :: e1 :: behead (behead (order G))) := {|
  bij_fwd := @add_node_iso_e_bij_fwd t _ _ _ O;
  bij_bwd:= @add_node_iso_e_bij_bwd _ _ _ _ _;
  bijK:= @add_node_iso_e_bijK _ _ _ _ _;
  bijK':= add_node_iso_e_bijK' _;
  |}.

Lemma add_node_iso_ihom (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  (O : order G = e0 :: e1 :: behead (behead (order G))) :
  is_ihom (add_node_iso_v t O) (add_node_iso_e t O) pred0.
Proof.
  destruct (add_node_c O).
  split.
  - by intros [[[[[? ?] | []] | ] | []] | ] [].
  - by intros [[[[? | ?] ?] | []] | []].
  - assert (llabel e0 /\ llabel e1) as [? ?] by (split; apply p_noleft; caseb).
    move => [[[[[[[[? | ?] | ] | ] ?] | []] | ] | []] | ] //; by cbnb; case_if.
Qed.

Definition add_node_iso (t : trilean) (G : proof_structure) (e0 e1 : edge G)
  (O : order G = e0 :: e1 :: behead (behead (order G))) := {|
  iso_v := add_node_iso_v t O;
  iso_e := add_node_iso_e _ _;
  iso_d := pred0;
  iso_ihom := add_node_iso_ihom _ _ |}.


Definition add_node_ps_tens (G0 G1 : proof_structure) := add_node_ps tens_t (union_ps G0 G1).
Definition add_node_ps_cut (G0 G1 : proof_structure) := add_node_ps cut_t (union_ps G0 G1).
Definition add_node_ps_parr (G : proof_structure) := add_node_ps parr_t G.


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

Definition add_node_parr_iso_bis (G : proof_structure) e0 e1 (O : order G = e0 :: e1 :: behead (behead (order G))) :
  @add_concl_graph _
    (@add_concl_graph _
      (add_node_graph parr_t e0 e1) (Sub (inl (source e0)) (add_node_s0 _ O)) c (flabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ O))) c (flabel e1) ≃
  @add_concl_graph _ (add_parr_graph (source e0) (source e1) (flabel e0) (flabel e1))
  (inr tt) c (parr (flabel e0) (flabel e1)).
Proof.
  etransitivity.
  exact (add_node_iso parr_t O).
  exact (add_node_parr_iso e0 e1).
Defined.

Lemma add_node_parr_correct (G : proof_net) : (* TODO replace exists with arguments *)
  (exists e0 e1, order G = e0 :: e1 :: behead (behead (order G))) ->
  correct (add_node_ps_parr G).
Proof.
  move=> [e0 [e1 O]].
  rewrite /= /add_node_graph_data_bis O /=.
  enough (H': correct (@add_concl_graph _ (@add_concl_graph _ (add_node_graph parr_t e0 e1)
    (Sub (inl (source e0)) (add_node_s0 _ O)) c (flabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ O))) c (flabel e1)))
    by apply (rem_concl_correct (correct_to_weak (rem_concl_correct (correct_to_weak H')))).
  apply (iso_correct (add_node_parr_iso_bis O)),
    add_concl_correct, correct_to_weak, add_parr_correct, correct_to_weak, p_correct.
Qed.

Definition add_node_pn_parr (G : proof_net) (H : exists e0 e1, order G = e0 :: e1 :: behead (behead (order G))) :
  proof_net := {|
  ps_of := _;
  p_correct := add_node_parr_correct H;
  |}.

Lemma add_node_parr_correct' (G : proof_structure) (e0 e1 : edge G) :
  order G = e0 :: e1 :: behead (behead (order G)) -> correct (add_node_graph parr_t e0 e1) -> correct G.
Proof.
  move=> O C.
  assert (C': correct (@add_concl_graph _ (@add_concl_graph _ (add_node_graph parr_t e0 e1)
    (Sub (inl (source e0)) (add_node_s0 _ O)) c (flabel e0))
    (inl (Sub (inl (source e1)) (add_node_s1 _ O))) c (flabel e1)))
    by by apply add_concl_correct, correct_to_weak, add_concl_correct, correct_to_weak.
  by apply (iso_correct (iso_sym (add_node_parr_iso_bis O))), correct_to_weak,
    rem_concl_correct, correct_to_weak, rem_parr_correct in C'.
Qed.


Definition add_node_tens_iso_0 (G0 G1 : base_graph) (e0 : edge G0) (e1 : edge G1) :
  G0 ⊎ G1 ⊎ (unit_graph (⊗) ⊎ unit_graph c)
  ∔ [inl tt, (tens (flabel e0) (flabel e1), true), inr tt]
  ≃
  (G0 ⊎ G1 ⊎ unit_graph (⊗) ⊎ unit_graph c)
  ∔ [inl (inr tt), (tens (flabel e0) (flabel e1), true), inr tt].
Proof.
  etransitivity. by apply (@union_add_edge_r _ _ (G0 ⊎ G1) (unit_graph _ ⊎ unit_graph _) _ _ _).
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
  etransitivity. by apply union_A.
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
  etransitivity. by apply (add_edge_iso (add_edge_iso (add_node_tens_iso_0 e0 e1) _ _ _)).
  etransitivity. by apply (add_edge_iso (@add_edge_C _ _ _ _ _ _ _ _ _)).
  etransitivity. by apply add_edge_C.
  symmetry.
  etransitivity. by apply (add_edge_iso (add_node_tens_iso_1 e0 e1)).
  etransitivity. by apply (add_edge_iso (add_node_tens_iso_2 e0 e1)).
  apply (add_edge_iso (add_edge_iso (add_edge_iso (add_node_tens_iso_3 e0 e1) (inl (inr (inl (source e0))))
    _ (inl (inr (inr tt)))) (inl (inl (source e1))) _ (inl (inr (inr tt))))).
Defined.

Definition add_node_tens_iso_bis (G0 G1 : proof_structure) (e0 : edge G0) (e1 : edge G1)
  (Hl : order (union_ps G0 G1) = inl e0 :: inr e1 :: behead (behead (order (union_ps G0 G1)))) :
  @add_concl_graph _ (@add_concl_graph _ (@add_node_graph tens_t (G0 ⊎ G1) (inl e0) (inr e1))
    (Sub (_ : @add_node_graph_1 tens_t (G0 ⊎ G1) (inl e0) (inr e1)) (add_node_s0 _ Hl)) c (flabel e0))
    (inl (Sub (_ : @add_node_graph_1 tens_t (G0 ⊎ G1) (inl e0) (inr e1)) (add_node_s1 _ Hl))) c (flabel e1) ≃
  @add_concl_graph _
    (@union_edge_graph _ G1
      (@add_concl_graph _ G0 (source e0) (⊗) (flabel e0))
      (source e1) (inr tt) (flabel e1, false))
  (inr (inr tt)) c (tens (flabel e0) (flabel e1)).
Proof.
  etransitivity.
  exact (add_node_iso tens_t Hl).
  exact (add_node_tens_iso e0 e1).
Defined.

Lemma add_node_tens_correct (G0 G1 : proof_net) :
  (exists e0 e1, order G0 = e0 :: behead (order G0) /\ order G1 = e1 :: behead (order G1)) ->
  correct (add_node_ps_tens G0 G1).
Proof.
  intros [e0 [e1 [Hl0 Hl1]]].
  assert (Hl : order (union_ps G0 G1) = inl e0 :: inr e1 :: behead (behead (order (union_ps G0 G1)))).
  { by rewrite /= /union_order Hl0 Hl1. }
  rewrite /= /add_node_graph_data_bis /union_order Hl0 Hl1.
  enough (H': correct (@add_concl_graph _ (@add_concl_graph _ (@add_node_graph tens_t (G0 ⊎ G1) (inl e0) (inr e1))
    (Sub (_ : @add_node_graph_1 tens_t (G0 ⊎ G1) (inl e0) (inr e1)) (add_node_s0 _ Hl)) c (flabel e0))
    (inl (Sub (_ : @add_node_graph_1 tens_t (G0 ⊎ G1) (inl e0) (inr e1)) (add_node_s1 _ Hl))) c (flabel e1)))
    by apply (rem_concl_correct (correct_to_weak (rem_concl_correct (correct_to_weak H')))).
  apply (iso_correct (add_node_tens_iso_bis Hl)), add_concl_correct, correct_to_weak, union_edge_correct.
  - caseb.
  - by apply correct_to_weak, p_correct.
  - by apply correct_to_weak, add_concl_correct, correct_to_weak, p_correct.
Qed.

Definition add_node_pn_tens (G0 G1 : proof_net)
  (H : exists e0 e1, order G0 = e0 :: behead (order G0) /\ order G1 = e1 :: behead (order G1)) :
  proof_net := {|
  ps_of := _;
  p_correct := add_node_tens_correct H;
  |}.

Lemma add_node_tens_correct' (G0 G1 : proof_structure) :
  (exists e0 e1, order G0 = e0 :: behead (order G0) /\ order G1 = e1 :: behead (order G1)) ->
  correct (add_node_ps_tens G0 G1) -> correct G0 /\ correct G1.
Proof.
  intros [e0 [e1 [Hl0 Hl1]]].
  assert (Hl : order (union_ps G0 G1) = inl e0 :: inr e1 :: behead (behead (order (union_ps G0 G1)))).
  { by rewrite /= /union_order Hl0 Hl1. }
  rewrite /= /add_node_graph_data_bis /union_order Hl0 Hl1 /=.
  move=> C.
  assert (C1 : correct (add_node_graph_1 tens_t (inl e0 : edge (G0 ⊎ G1)) (inr e1))).
  { apply (iso_correct (iso_sym (add_node_iso tens_t Hl))), add_concl_correct,
      correct_to_weak, add_concl_correct, correct_to_weak, C. }
  apply (iso_correct (iso_sym (add_node_tens_iso e0 e1))), correct_to_weak,
    rem_concl_correct, correct_to_weak, union_edge_correct2 in C1 as [C1 C0].
  by apply correct_to_weak, rem_concl_correct in C0.
Qed.

Definition add_node_cut_iso_0 (G0 G1 : base_graph) (e0 : edge G0) (e1 : edge G1) :
  G1 ⊎ (G0 ⊎ unit_graph cut) ≃ G0 ⊎ G1 ⊎ unit_graph cut.
Proof.
  etransitivity. by apply union_A.
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
  etransitivity. by apply (add_edge_iso (@union_add_edge_r _ _ _ _ _ _ _)).
  apply (add_edge_iso (@add_edge_iso _ _ _ _ (add_node_cut_iso_0 e0 e1)
    (inr (inl (source e0))) _ (inr (inr tt)))).
Defined.

Definition add_node_cut_iso_bis (G0 G1 : proof_structure) (e0 : edge G0) (e1 : edge G1)
  (Hl : order (union_ps G0 G1) = inl e0 :: inr e1 :: behead (behead (order (union_ps G0 G1)))) :
  @add_concl_graph _ (@add_concl_graph _ (@add_node_graph cut_t (G0 ⊎ G1) (inl e0) (inr e1))
    (Sub (_ : @add_node_graph_1 cut_t (G0 ⊎ G1) (inl e0) (inr e1)) (add_node_s0 _ Hl)) c (flabel e0))
    (inl (Sub (_ : @add_node_graph_1 cut_t (G0 ⊎ G1) (inl e0) (inr e1)) (add_node_s1 _ Hl))) c (flabel e1) ≃
  @union_edge_graph _ G1 (@add_concl_graph _ G0 (source e0) cut (flabel e0))
    (source e1) (inr tt) (flabel e1, true).
Proof.
  etransitivity.
  exact (add_node_iso cut_t Hl).
  exact (add_node_cut_iso e0 e1).
Defined.

Lemma add_node_cut_correct (G0 G1 : proof_net) :
  (exists e0 e1, order G0 = e0 :: behead (order G0) /\ order G1 = e1 :: behead (order G1) /\ flabel e1 = dual (flabel e0)) ->
  correct (add_node_ps_cut G0 G1).
Proof.
  intros [e0 [e1 [Hl0 [Hl1 ?]]]].
  assert (Hl : order (union_ps G0 G1) = inl e0 :: inr e1 :: behead (behead (order (union_ps G0 G1)))).
  { by rewrite /= /union_order Hl0 Hl1. }
  rewrite /= /add_node_graph_data_bis /union_order Hl0 Hl1.
  case_if.
  enough (H': correct (@add_concl_graph _ (@add_concl_graph _ (@add_node_graph cut_t (G0 ⊎ G1) (inl e0) (inr e1))
    (Sub (_ : @add_node_graph_1 cut_t (G0 ⊎ G1) (inl e0) (inr e1)) (add_node_s0 _ Hl)) c (flabel e0))
    (inl (Sub (_ : @add_node_graph_1 cut_t (G0 ⊎ G1) (inl e0) (inr e1)) (add_node_s1 _ Hl))) c (flabel e1)))
    by apply (rem_concl_correct (correct_to_weak (rem_concl_correct (correct_to_weak H')))).
  apply (iso_correct (add_node_cut_iso_bis Hl)), union_edge_correct.
  - caseb.
  - by apply correct_to_weak, p_correct.
  - by apply correct_to_weak, add_concl_correct, correct_to_weak, p_correct.
Qed.

Definition add_node_pn_cut (G0 G1 : proof_net)
  (H : exists e0 e1, order G0 = e0 :: behead (order G0) /\ order G1 = e1 :: behead (order G1) /\ flabel e1 = dual (flabel e0)) :
  proof_net := {|
  ps_of := _;
  p_correct := add_node_cut_correct H;
  |}.

Lemma add_node_cut_correct' (G0 G1 : proof_structure) :
  (exists e0 e1, order G0 = e0 :: behead (order G0) /\ order G1 = e1 :: behead (order G1) /\ @flabel _ (G0 ⊎ G1) (inr e1) == @flabel _ (G0 ⊎ G1) (inl e0)^) ->
  correct (add_node_ps_cut G0 G1) -> correct G0 /\ correct G1.
Proof.
  intros [e0 [e1 [Hl0 [Hl1 Hl2]]]].
  assert (Hl : order (union_ps G0 G1) = inl e0 :: inr e1 :: behead (behead (order (union_ps G0 G1)))).
  { by rewrite /= /union_order Hl0 Hl1. }
  rewrite /= /add_node_graph_data_bis /union_order Hl0 Hl1 Hl2 /=.
  move=> C.
  assert (C1 : correct (add_node_graph_1 cut_t (inl e0 : edge (G0 ⊎ G1)) (inr e1))).
  { apply (iso_correct (iso_sym (add_node_iso cut_t Hl))), add_concl_correct,
      correct_to_weak, add_concl_correct, correct_to_weak, C. }
  apply (iso_correct (iso_sym (add_node_cut_iso e0 e1))), correct_to_weak,
    union_edge_correct2 in C1 as [C1 C0].
  by apply correct_to_weak, rem_concl_correct in C0.
Qed.


Lemma add_node_parr_correct_contra G :
  correct (add_node_ps_parr G) ->
  {'(e0, e1) & order G = e0 :: e1 :: behead (behead (order G))}.
Proof.
  rewrite /= /add_node_graph_data_bis.
  destruct (order G) as [ | e0 [ | e1 ?]] eqn:Ho; try by [].
  - intro Hf. contradict Hf. apply v_notcorrect.
  - intro Hf. contradict Hf. apply v_notcorrect.
  - intros _. by exists (e0, e1).
Qed.

Lemma add_node_bad_path_l (t : trilean) (G0 G1 : base_graph)
  e0 e1 v V p (u : add_node_graph t (inl e0 : edge (G0 ⊎ G1)) (inl e1)) :
  uwalk u (Sub (unl (unr v)) V) p -> exists u', val u = unl (unr u').
Proof.
  move: u. induction p as [ | [[[[[[a | a] | a] | ] | ] ?] b] p IH] => u; cbnb.
  - move=> /eqP-->. by exists v.
  - move=> /andP[_ P]. by destruct (IH _ P).
  - move=> /andP[/eqP-<- _]. by exists (endpoint (~~ b) a).
  - move=> /andP[_ P]. by destruct (IH _ P).
  - move=> /andP[_ P]. destruct (IH _ P) as [? X]. contradict X. by destruct t, b.
  - move=> /andP[_ P]. destruct (IH _ P) as [? X]. contradict X. by destruct t, b.
Qed.

Lemma add_node_bad_path_r (t : trilean) (G0 G1 : base_graph)
  e0 e1 v V p (u : add_node_graph t (inr e0 : edge (G0 ⊎ G1)) (inr e1)) :
  uwalk u (Sub (unl (unl v)) V) p -> exists u', val u = unl (unl u').
Proof.
  move: u. induction p as [ | [[[[[[a | a] | a] | ] | ] ?] b] p IH] => u; cbnb.
  - move=> /eqP-->. by exists v.
  - move=> /andP[/eqP-<- _]. by exists (endpoint (~~ b) a).
  - move=> /andP[_ P]. by destruct (IH _ P).
  - move=> /andP[_ P]. by destruct (IH _ P).
  - move=> /andP[_ P]. destruct (IH _ P) as [? X]. contradict X. by destruct t, b.
  - move=> /andP[_ P]. destruct (IH _ P) as [? X]. contradict X. by destruct t, b.
Qed. (* TODO merge these lemmae if possible *)

Lemma add_node_bad_not_correct_l (t : trilean) (G0 G1 : proof_net) e0 e1 :
  order G0 = e0 :: e1 :: behead (behead (order G0)) ->
  ~ uconnected (@switching_left _ (add_node_graph t (inl e0 : edge (G0 ⊎ G1)) (inl e1))).
Proof.
  move=> O C. unfold uconnected in C.
  assert (v : G1) by by apply exists_node.
  assert (V : unl (unr v) \in ([set: add_node_graph_1 t (inl e0 : edge (G0 ⊎ G1)) (inl e1)] :\ unl (target (inl e0 : edge (G0 ⊎ G1)))
   :\ unl (target (inl e1 : edge (G0 ⊎ G1))))).
  { by rewrite !in_set !in_set1. }
  assert (W : unl (unl (source e0)) \in ([set: add_node_graph_1 t (inl e0 : edge (G0 ⊎ G1)) (inl e1)] :\ unl (target (inl e0 : edge (G0 ⊎ G1)))
   :\ unl (target (inl e1 : edge (G0 ⊎ G1))))).
  { rewrite !in_set !in_set1. splitb; cbnb. all: apply (add_node_hyp O). }
  specialize (C (Sub (unl (unl (source e0))) W) (Sub (unl (unr v)) V)). destruct C as [C _].
  enough (I : forall u, Well_colored_utrail switching_left (u : add_node_graph t _ _) (Sub (unl (unr v)) V) -> exists u', val u = unl (unr u')).
  { apply I in C. by destruct C. }
  move=> u [p /andP[/andP[P _] _]]. move: p u P.
  by apply add_node_bad_path_l.
Qed.

Lemma add_node_bad_not_correct_r (t : trilean) (G0 G1 : proof_net) (e0 e1 : edge G1) :
  order G1 = e0 :: e1 :: behead (behead (order G1)) ->
  ~ uconnected (@switching_left _ (add_node_graph t (inr e0 : edge (G0 ⊎ G1)) (inr e1))).
Proof.
  move=> O C.
  assert (v : G0).
  { have /eqP := correct_not_empty (p_correct G0).
    by rewrite -cardsT cards_eq0 => /set0Pn/sigW[v _]. }
  assert (V : unl (unl v) \in ([set: add_node_graph_1 t (inr e0 : edge (G0 ⊎ G1)) (inr e1)] :\ unl (target (inr e0 : edge (G0 ⊎ G1)))
   :\ unl (target (inr e1 : edge (G0 ⊎ G1))))).
  { by rewrite !in_set !in_set1. }
  assert (W : unl (unr (source e0)) \in ([set: add_node_graph_1 t (inr e0 : edge (G0 ⊎ G1)) (inr e1)] :\ unl (target (inr e0 : edge (G0 ⊎ G1)))
   :\ unl (target (inr e1 : edge (G0 ⊎ G1))))).
  { rewrite !in_set !in_set1. splitb; cbnb. all: apply (add_node_hyp O). }
  specialize (C (Sub (unl (unr (source e0))) W) (Sub (unl (unl v)) V)). destruct C as [C _].
  enough (I : forall u, Well_colored_utrail switching_left (u : add_node_graph t _ _) (Sub (unl (unl v)) V) -> exists u', val u = unl (unl u')).
  { apply I in C. by destruct C. }
  move=> u [p /andP[/andP[P _] _]]. move: p u P.
  by apply add_node_bad_path_r.
Qed.
(* TODO merge these lemmae if possible *)

Lemma add_node_tens_correct_contra (G0 G1 : proof_net) :
  correct (add_node_ps_tens G0 G1) ->
  {'(e0, e1) & order G0 = e0 :: behead (order G0) /\ order G1 = e1 :: behead (order G1)}.
Proof.
  rewrite /= /add_node_graph_data_bis /union_order.
  destruct (order G0) as [ | e0 l0] eqn:L0;
  destruct (order G1) as [ | e1 l1] eqn:L1; simpl.
  - move=> Hf. contradict Hf. apply v_notcorrect.
  - destruct l1 as [ | e2 l1]; simpl.
    + move=> Hf. contradict Hf. apply v_notcorrect.
    + move=> C. apply correct_to_weak in C as [_ C]. contradict C.
      apply (add_node_bad_not_correct_r).
      by rewrite L1.
  - destruct l0 as [ | e2 l0]; simpl.
    + move=> Hf. contradict Hf. apply v_notcorrect.
    + move=> C. apply correct_to_weak in C as [_ C]. contradict C.
      apply (add_node_bad_not_correct_l).
      by rewrite L0.
  - move=> _. by exists (e0, e1).
Qed.

Lemma add_node_cut_correct_contra (G0 G1 : proof_net) :
  correct (add_node_ps_cut G0 G1) ->
  {'(e0, e1) & order G0 = e0 :: behead (order G0) /\ order G1 = e1 :: behead (order G1) /\
  @flabel _ (G0 ⊎ G1) (inr e1) == @flabel _ (G0 ⊎ G1) (inl e0)^}.
Proof.
  rewrite /= /add_node_graph_data_bis /union_order.
  destruct (order G0) as [ | e0 l0] eqn:L0;
  destruct (order G1) as [ | e1 l1] eqn:L1; simpl.
  - move=> Hf. contradict Hf. apply v_notcorrect.
  - destruct l1 as [ | e2 l1]; simpl.
    + move=> Hf. contradict Hf. apply v_notcorrect.
    + case : ifP => _.
      * move=> C. apply correct_to_weak in C. destruct C as [_ C]. contradict C.
        apply (add_node_bad_not_correct_r).
        by rewrite L1.
      * move=> Hf. contradict Hf. apply v_notcorrect.
  - destruct l0 as [ | e2 l0]; simpl.
    + move=> Hf. contradict Hf. apply v_notcorrect.
    + case : ifP => _.
      * move=> C. apply correct_to_weak in C. destruct C as [_ C]. contradict C.
        apply (add_node_bad_not_correct_l).
        by rewrite L0.
      * move=> Hf. contradict Hf. apply v_notcorrect.
  - case : ifP => ?.
    + by exists (e0, e1).
    + move=> Hf. contradict Hf. apply v_notcorrect.
Qed.



Fixpoint ps {l : list formula} (pi : ⊢ l) : proof_structure := match pi with
  | ax_r A                  => ax_ps A
  | ex_r _ _ pi0 sigma      => perm_ps sigma (ps pi0)
  | tens_r _ _ _ _ pi0 pi1  => add_node_ps_tens (ps pi0) (ps pi1)
  | parr_r _ _ _ pi0        => add_node_ps_parr (ps pi0)
  | cut_r _ _ _ pi0 pi1     => add_node_ps_cut (ps pi0) (ps pi1)
  end.

Lemma ps_consistent {l : list formula} (pi : ⊢ l) : sequent (ps pi) = l.
Proof.
  induction pi as [ | | A B l0 l1 pi0 H0 pi1 H1 | A B l0 pi0 H0 | A l0 l1 pi0 H0 pi1 H1].
  - apply ax_sequent.
  - by apply perm_sequent.
  - rewrite add_node_sequent union_sequent H0 H1; cbn.
    move: H0 H1.
    unfold union_order, sequent.
    destruct (order (ps pi0)) as [ | e0 o0] eqn:Ho0; try by [].
    destruct (order (ps pi1)) as [ | e1 o1] eqn:Ho1; try by [].
    rewrite Ho0 Ho1 /=.
    move=> /eqP; cbn => /andP[/eqP-E0 _].
    move=> /eqP; cbn => /andP[/eqP-E1 _].
    by replace (tens A B) with (tens (flabel e0) (flabel e1)) by by rewrite E0 E1.
  - rewrite add_node_sequent H0.
    move: H0.
    unfold sequent.
    destruct (order (ps pi0)) as [ | e0 [ | e1 o]] eqn:Ho; try by [].
    rewrite Ho /=.
    by move=> /eqP; cbn => /andP[/eqP--> /andP[/eqP--> _]].
  - rewrite add_node_sequent union_sequent H0 H1; cbn.
    move: H0 H1.
    unfold union_order, sequent.
    destruct (order (ps pi0)) as [ | e0 o0] eqn:Ho0; try by [].
    destruct (order (ps pi1)) as [ | e1 o1] eqn:Ho1; try by [].
    rewrite Ho0 Ho1 /=.
    move=> /eqP; cbn => /andP[/eqP-E0 _].
    move=> /eqP; cbn => /andP[/eqP-E1 _].
    replace (@flabel _ (_ ⊎ _) (inl e0)) with A.
    replace (@flabel _ (_ ⊎ _) (inr e1)) with (dual A).
    case_if.
Qed.

Lemma sound {l : list formula} (pi : ⊢ l) : correct (ps pi).
Proof.
  induction pi as [ | | ? ? ? ? pi0 c0 pi1 c1 | ? ? ? pi0 c0 | A ? ? pi0 c0 pi1 c1]; trivial.
  - apply ax_correct.
  - apply (@add_node_tens_correct {| ps_of := _ ; p_correct := c0 |}
                                  {| ps_of := _ ; p_correct := c1 |}); simpl.
    destruct (order (ps pi0)) as [ | e0 ?] eqn:HO0.
    { assert (Hf : sequent (ps pi0) = [::]) by by rewrite /sequent HO0.
      by rewrite ps_consistent in Hf. }
    destruct (order (ps pi1)) as [ | e1 ?] eqn:HO1.
    { assert (Hf : sequent (ps pi1) = [::]) by by rewrite /sequent HO1.
      by rewrite ps_consistent in Hf. }
    by exists e0, e1.
  - destruct (order (ps pi0)) as [ | e0 [ | e1 ?]] eqn:HO.
    * assert (Hf : sequent (ps pi0) = [::]) by by rewrite /sequent HO.
      by rewrite ps_consistent in Hf.
    * assert (Hf : sequent (ps pi0) = [:: flabel e0]) by by rewrite /sequent HO.
      by rewrite ps_consistent in Hf.
    * apply (@add_node_parr_correct {| ps_of := _ ; p_correct := c0 |}).
      exists e0, e1. by rewrite HO.
  - apply (@add_node_cut_correct {| ps_of := _ ; p_correct := c0 |}
                                 {| ps_of := _ ; p_correct := c1 |}); simpl.
    destruct (order (ps pi0)) as [ | e0 ?] eqn:HO0.
    { assert (Hf : sequent (ps pi0) = [::]) by by rewrite /sequent HO0.
      by rewrite ps_consistent in Hf. }
    destruct (order (ps pi1)) as [ | e1 ?] eqn:HO1.
    { assert (Hf : sequent (ps pi1) = [::]) by by rewrite /sequent HO1.
      by rewrite ps_consistent in Hf. }
    exists e0, e1. splitb.
    have := ps_consistent pi0.
    have := ps_consistent pi1.
    rewrite /sequent HO0 HO1 /=.
    move=> /eqP; cbn => /andP[/eqP--> _].
    by move=> /eqP; cbn => /andP[/eqP--> _].
Qed.

Definition pn {l : list formula} (pi : ⊢ l) : proof_net := {|
  ps_of := ps pi;
  p_correct := sound pi;
  |}.


Lemma ps_rew {l l' : list formula} (pi : ⊢ l) (H : l = l') :
  ps (rew [ll] H in pi) = ps pi.
Proof. by subst. Qed. (* TODO not exactly rew_const *)



Lemma add_node_graph_1_ecard (t : trilean) G (e0 e1 : edge G) :
  #|edge (add_node_graph_1 t e0 e1)| = #|edge G| + (match t with | cut_t => 2 | _ => 3 end).
Proof.
  rewrite /add_node_graph_1 card_edge_add_edge /=.
  destruct t;
  rewrite ?card_option ?card_sum ?card_option ?card_sum ?card_void /=;
  lia.
Qed.

Lemma add_node_edge_set (t : trilean) (G : proof_structure) (e0 e1 : edge G) :
  order G = e0 :: e1 :: behead (behead (order G)) ->
  edge_set ([set: add_node_graph_1 t e0 e1] :\ inl (target e0) :\ inl (target e1)) =
  edge_set [set: add_node_graph_1 t e0 e1] :\ (Some (Some (inl (e0)))) :\ (Some (Some (inl (e1)))).
Proof.
  move=> O.
  apply /setP => e.
  rewrite !in_set !in_set1 !andb_true_r.
  destruct (add_node_c O).
  destruct e as [[[e | e] | ] | ]; cbn; trivial.
  - destruct (add_node_hyp O e) as [Se0 Se1].
    rewrite Se0 Se1 {Se0 Se1} !target_eq_c //.
  - destruct (add_node_hyp O e0) as [Se0 Se1].
    rewrite Se0 Se1 {Se0 Se1} /=.
    by destruct t.
  - destruct (add_node_hyp O e1) as [Se0 Se1].
    rewrite Se0 Se1 {Se0 Se1} /=.
    by destruct t.
Qed.

Lemma add_node_graph_ecard (t : trilean) (G : proof_structure) (e0 e1 : edge G) :
  order G = e0 :: e1 :: behead (behead (order G)) ->
  #|edge (add_node_graph t e0 e1)| = #|edge G| + (match t with | cut_t => 0 | _ => 1 end).
Proof.
  move=> O.
Opaque add_node_graph_1. (* TODO ugly *)
  rewrite /add_node_graph /= (add_node_edge_set t O) card_sig.
  assert (In0 : (Some (Some (inl e1)) \in
    edge_set [set: add_node_graph_1 t e0 e1] :\ Some (Some (inl e0)))).
  { rewrite !in_set !in_set1 !andb_true_r. apply /eqP => Heq. inversion Heq. subst e1.
    by assert (H := add_node_neq_t O). }
  transitivity (#|edge_set [set: add_node_graph_1 t e0 e1] :\ Some (Some (inl e0))| - 1).
  { rewrite [in RHS](cardsD1 (Some (Some (inl e1)))) In0 /=.
    set n := #|_|. lia. (* TODO lia does not work by itself here ... *) }
  transitivity (#|edge_set [set: add_node_graph_1 t e0 e1]| - 2).
  { rewrite [in RHS](cardsD1 (Some (Some (inl e0)))) !in_set /=.
    set n := #|_|. lia. (* TODO lia does not work by itself here ... *) }
  rewrite edge_set_setT cardsT add_node_graph_1_ecard.
Transparent add_node_graph_1.
  destruct t; clear; rewrite /=; lia.
Qed.

Lemma add_node_ps_parr_ecard (G : proof_net) :
  correct (add_node_ps_parr G) ->
  #|edge (add_node_ps_parr G)| = #|edge G| + 1.
Proof.
  move=> C.
  destruct (add_node_parr_correct_contra C) as [[e0 e1] Hl].
  by rewrite /= /add_node_graph_data_bis Hl (add_node_graph_ecard _ Hl).
Qed.

Lemma add_node_ps_tens_ecard (G0 G1 : proof_net) :
  correct (add_node_ps_tens G0 G1) ->
  #|edge (add_node_ps_tens G0 G1)| = #|edge G0| + #|edge G1| + 1.
Proof.
  move=> C.
  destruct (add_node_tens_correct_contra C) as [[e0 e1] [Hl0 Hl1]].
  assert (O : order (union_ps G0 G1) = [:: inl e0, inr e1
    & behead (behead (order (union_ps G0 G1)))])
    by by rewrite /= /union_order Hl0 Hl1.
  by rewrite /= /union_order Hl0 Hl1 (add_node_graph_ecard _ O) card_sum.
Qed.

Lemma add_node_ps_cut_ecard (G0 G1 : proof_net) :
  correct (add_node_ps_cut G0 G1) ->
  #|edge (add_node_ps_cut G0 G1)| = #|edge G0| + #|edge G1|.
Proof.
  move=> C.
  destruct (add_node_cut_correct_contra C) as [[e0 e1] [Hl0 [Hl1 Hf]]].
  assert (O : order (union_ps G0 G1) = [:: inl e0, inr e1
    & behead (behead (order (union_ps G0 G1)))])
    by by rewrite /= /union_order Hl0 Hl1.
  rewrite /= /union_order Hl0 Hl1 Hf (add_node_graph_ecard _ O) card_sum /=.
  lia.
Qed.


(* All previous operations preserves isomorphisms *)
Definition perm_isod (F G : graph_data) :
  F ≃d G -> forall {A : Type} {l l' : seq A} (sigma : Permutation_Type l l'),
  perm_graph_data sigma F ≃d perm_graph_data sigma G.
Proof.
  move=> h ? ? ? sigma.
  exists (h : perm_graph_data _ _ ≃ perm_graph_data _ _).
  by rewrite /= (order_iso h) perm_of_map.
Defined.

Definition union_isod (Gl Gr Hl Hr : graph_data) :
  Gl ≃d Hl -> Gr ≃d Hr -> union_graph_data Gl Gr ≃d union_graph_data Hl Hr.
Proof.
  move=> hl hr.
  exists (union_iso hl hr).
  rewrite /= /union_order (order_iso hl) (order_iso hr).
  destruct (order Gl), (order Gr);
  by rewrite /= ?map_cat -?map_comp.
Defined.

Lemma add_node_graph_1_iso'' (t : trilean) (F G : graph_data) (h : F ≃ G) (e0 e1 : edge F) :
  F ⊎ match t with
  | tens_t => edge_graph (⊗) (forward (flabel e0 ⊗ flabel e1)) c
  | parr_t => edge_graph (⅋) (forward (flabel e0 ⅋ flabel e1)) c
  | cut_t => unit_graph cut
  end ≃ G ⊎ match t with
  | tens_t => edge_graph (⊗) (forward (flabel (h.e e0) ⊗ flabel (h.e e1))) c
  | parr_t => edge_graph (⅋) (forward (flabel (h.e e0) ⅋ flabel (h.e e1))) c
  | cut_t => unit_graph cut
  end.
Proof.
  apply (union_iso h).
  by destruct t; trivial; apply @edge_graph_iso; rewrite !flabel_iso.
Defined.

Lemma add_node_graph_1_iso' (t : trilean) (F G : graph_data) (h : F ≃ G) (e0 e1 : edge F) :
  (F ⊎ match t with
  | tens_t => edge_graph (⊗) (forward (flabel e0 ⊗ flabel e1)) c
  | parr_t => edge_graph (⅋) (forward (flabel e0 ⅋ flabel e1)) c
  | cut_t => unit_graph cut
  end) ∔ [inl (source e0), forward (flabel e0), match t
  with | cut_t => inr tt | _ => inr (inl tt) end] ≃
  (G ⊎ match t with
  | tens_t => edge_graph (⊗) (forward (flabel (h.e e0) ⊗ flabel (h.e e1))) c
  | parr_t => edge_graph (⅋) (forward (flabel (h.e e0) ⅋ flabel (h.e e1))) c
  | cut_t => unit_graph cut
  end) ∔ [inl (source (h.e e0)), forward (flabel (h.e e0)), match t
  with | cut_t => inr tt | _ => inr (inl tt) end].
Proof.
  apply (@add_edge_iso'' _ _ _ _ (add_node_graph_1_iso'' t h e0 e1)).
  - by rewrite endpoint_iso iso_noflip.
  - by destruct t.
  - by rewrite flabel_iso.
Defined.

Definition add_node_graph_1_iso (t : trilean) (F G : graph_data) (h : F ≃ G) (e0 e1 : edge F) :
  add_node_graph_1 t e0 e1 ≃ add_node_graph_1 t (h.e e0) (h.e e1).
Proof.
  apply (@add_edge_iso'' _ _ _ _ (add_node_graph_1_iso' t h e0 e1)).
  - by rewrite !endpoint_iso !iso_noflip.
  - by destruct t.
  - by rewrite flabel_iso.
Defined.

Definition add_node_graph_iso (t : trilean) (F G : graph_data) (h : F ≃ G) (e0 e1 : edge F) :
  add_node_graph t e0 e1 ≃ add_node_graph t (h.e e0) (h.e e1).
Proof.
  unfold add_node_graph.
  apply (@induced_iso _ _ _ _ (add_node_graph_1_iso t h e0 e1)).
  apply /setP => e.
  rewrite !endpoint_iso !iso_noflip.
  rewrite -{2}(bijK' (add_node_graph_1_iso t h e0 e1) e) bij_imset_f !in_set !in_set1 !andb_true_r.
  destruct e as [e | e]; trivial; cbn.
  by rewrite eq_sym (eq_sym _ (h (target e0))) (eq_sym (h^-1 e)) (eq_sym (h^-1 e) (target e0))
      -!bij_eqLR.
Defined.

Lemma add_node_graph_iso_order' (t : trilean) (F G : graph_data) (h : F ≃d G) (e0 e1 : edge F) l :
  add_node_type_order t e0 e1 (add_node_order_1 e0 e1) = [seq sval i | i <- l] ->
  add_node_type_order t (h.e e0) (h.e e1) (add_node_order_1 (h.e e0) (h.e e1)) =
  [seq ([eta sval] \o [eta (add_node_graph_iso t h e0 e1).e]) i | i <- l].
Proof.
Opaque add_node_graph_iso. (* To prevent simpl from unfolding the definition *)
  rewrite /add_node_type_order /add_node_order_1 (order_iso h).
  move: l. induction (order F) as [ | o O IH] => l /=.
  { by destruct l. }
  assert ((target (h.e o) != target (h.e e0)) && (source (h.e o) != target (h.e e0)) &&
    (target (h.e o) != target (h.e e1)) && (source (h.e o) != target (h.e e1))
    = (target o != target e0) && (source o != target e0) &&
    (target o != target e1) && (source o != target e1)) as ->
    by by rewrite !endpoint_iso !iso_noflip !(@bij_eq _ _ h).
  case: ifP => _; last by apply IH.
  destruct l as [ | [l0 L0] l] => L //=.
  inversion L as [[L' L'']]. clear L. subst l0.
  by rewrite (IH _ L'').
Transparent add_node_graph_iso.
Qed. (* TODO trouver mieux que ces opaque / transparent ... *)

Lemma add_node_graph_iso_order (t : trilean) (F G : graph_data) (h : F ≃d G) (e0 e1 : edge F) :
  order (add_node_graph_data t (h.e e0) (h.e e1)) =
  [seq (add_node_graph_iso t h e0 e1).e e | e <- order (add_node_graph_data t e0 e1)].
Proof.
Opaque add_node_graph_iso.
  rewrite /= /add_node_order.
  apply eq_seq_sig.
  destruct (all_sigP _) as [l L].
  rewrite -L {l L} -!map_comp.
  destruct (all_sigP _) as [l L].
  assert (Hr : sval (exist (fun _ => _) l L) = l) by cbnb. (* TODO ce lemme doit exister *)
  rewrite Hr {Hr}.
  move: L. rewrite /add_node_order_2.
  destruct t; simpl.
  - destruct l as [ | [l0 L0] l]; first by by []. simpl.
    move=> L. inversion L. clear L. subst l0.
    f_equal. clear L0.
    by apply (@add_node_graph_iso_order' tens_t).
  - destruct l as [ | [l0 L0] l]; first by by []. simpl.
    move=> L. inversion L. clear L. subst l0.
    f_equal. clear L0.
    by apply (@add_node_graph_iso_order' parr_t).
  - by apply (@add_node_graph_iso_order' cut_t).
Transparent add_node_graph_iso.
Qed.

Definition add_node_graph_isod (t : trilean) (F G : graph_data) (h : F ≃d G) (e0 e1 : edge F) :
  add_node_graph_data t e0 e1 ≃d add_node_graph_data t (h.e e0) (h.e e1) :=
  {|iso_of := _; order_iso := add_node_graph_iso_order t h e0 e1 |}.

Definition add_node_graph_data_bis_isod (t : trilean) (F G : graph_data) :
  F ≃d G -> add_node_graph_data_bis t F ≃d add_node_graph_data_bis t G.
Proof.
  move=> h.
  rewrite /add_node_graph_data_bis (order_iso h).
  destruct (order F) as [ | ? [ | ? ?]]; simpl; try reflexivity.
  destruct t; try apply add_node_graph_isod.
  rewrite 2!flabel_iso. case_if.
  apply add_node_graph_isod.
Defined.

Definition add_node_ps_parr_isod (G H : proof_structure) :
  G ≃d H -> add_node_ps_parr G ≃d add_node_ps_parr H.
Proof. apply add_node_graph_data_bis_isod. Defined.

Definition add_node_ps_tens_isod (Gl Gr Hl Hr : proof_structure) :
  Gl ≃d Hl -> Gr ≃d Hr -> add_node_ps_tens Gl Gr ≃d add_node_ps_tens Hl Hr.
Proof. move=> *. by apply add_node_graph_data_bis_isod, union_isod. Defined.

Definition add_node_ps_cut_isod (Gl Gr Hl Hr : proof_structure) :
  Gl ≃d Hl -> Gr ≃d Hr -> add_node_ps_cut Gl Gr ≃d add_node_ps_cut Hl Hr.
Proof. move=> *. by apply add_node_graph_data_bis_isod, union_isod. Defined.

End Atoms.
