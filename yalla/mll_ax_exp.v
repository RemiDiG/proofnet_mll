(* Expanding axioms in a proof net *)
(* TODO remove unused imports *)
From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export mll_prelim graph_more upath supath mll_def mll_basic mll_seq_to_pn mll_correct.

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
Notation ll := (@ll atom).
Notation base_graph := (graph (flat rule) (flat (formula * bool))).
Notation graph_data := (@graph_data atom).
Notation proof_structure := (@proof_structure atom).
Notation proof_net := (@proof_net atom).


(** ** The substitution in a proof net/structure of an atom by a proof net/structure
       yields a proof net/structure *)

(** Results on a proof structure with two conclusions *)
Lemma subst_ax_conc_H_neq (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  c1 <> c2.
Proof. have := p_order_uniq H. rewrite /proper_order_uniq Ho /= !in_cons. introb. Qed.

Lemma subst_ax_conc_H_c (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  vlabel (target c1) = c /\ vlabel (target c2) = c.
Proof. split; apply p_order_full; rewrite /= Ho !in_cons; caseb. Qed.

Lemma subst_ax_target_conc_H_neq (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  target c1 <> target c2.
Proof.
  intros ?.
  enough (F : c1 = c2) by by apply subst_ax_conc_H_neq in F.
  apply one_target_c; trivial.
  apply (subst_ax_conc_H_c Ho).
Qed.

(* Graph where we replaced the axiom node v by the proof structure H *)
(* Lemmas to simplify the definition by keeping their proofs opaque *)
Lemma subst_ax_graph_0 (G : proof_structure) (v : G) (V : vlabel v = ax) (e : edge G) :
  source e = source (ax_formula_edge V) -> target e \in [set~ v].
Proof.
  intro E.
  rewrite !in_set in_set1 -(ax_formula_edge_in V) -E.
  apply /eqP. apply nesym, no_loop.
Qed.

Lemma subst_ax_graph_01 (G : proof_structure) (v : G) (V : vlabel v = ax) :
  target (ax_formula_edge V) \in [set~ v].
Proof. exact (subst_ax_graph_0 erefl). Qed.
Lemma subst_ax_graph_02 (G : proof_structure) (v : G) (V : vlabel v = ax) :
  target ((other_ax (ax_formula_endpoint V))) \in [set~ v].
Proof. exact (subst_ax_graph_0 (other_ax_e (ax_formula_endpoint V))). Qed.

Lemma subst_ax_graph_1 (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  source c1 \in setT :\ target c1 :\ target c2 /\
  source c2 \in setT :\ target c1 :\ target c2.
Proof.
  rewrite !in_set !in_set1 !andb_true_r. splitb; apply /eqP.
  - apply no_source_c, (subst_ax_conc_H_c Ho).
  - apply no_loop.
  - apply no_loop.
  - apply no_source_c, (subst_ax_conc_H_c Ho).
Qed.

Lemma subst_ax_graph_11 (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  source c1 \in setT :\ target c1 :\ target c2.
Proof. by destruct (subst_ax_graph_1 Ho). Qed.
Lemma subst_ax_graph_12 (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  source c2 \in setT :\ target c1 :\ target c2.
Proof. by destruct (subst_ax_graph_1 Ho). Qed.

Definition subst_ax_graph (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) : base_graph :=
  (remove_vertex v ⊎ induced (setT :\ target c1 :\ target c2))
  ∔ [inr (Sub (source c1) (subst_ax_graph_11 Ho)), elabel (ax_formula_edge V),
    inl (Sub (target (ax_formula_edge V)) (subst_ax_graph_01 V))]
  ∔ [inr (Sub (source c2) (subst_ax_graph_12 Ho)), elabel (other_ax (ax_formula_endpoint V)),
    inl (Sub (target (other_ax (ax_formula_endpoint V))) (subst_ax_graph_02 V))].

Lemma subst_ax_G_removed (G : proof_structure) (v : G) (V : vlabel v = ax) :
  edges_at v = [set ax_formula_edge V ; other_ax (ax_formula_endpoint V)].
Proof.
  apply /setP => e.
  rewrite edges_at_eq -other_ax_set.
  replace (target e == v) with false by by (symmetry; apply /eqP; apply no_target_ax).
  by rewrite !in_set orb_false_r ax_cut_formula_edge_in.
Qed.

Lemma subst_ax_H_removed (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  edge_set (setT :\ target c1 :\ target c2) = setT :\ c1 :\ c2.
Proof.
  apply/setP => e.
  rewrite !in_set !in_set1 !andb_true_r.
  destruct (eq_comparable e c1) as [? | Neq1];
  [ | destruct (eq_comparable e c2) as [? | Neq2]];
  try (subst e; by rewrite !eq_refl /= !andb_false_r).
  transitivity true; last by (symmetry; splitb; apply /eqP).
  destruct (subst_ax_conc_H_c Ho).
  splitb; apply /eqP.
  - by apply no_source_c.
  - by apply no_source_c.
  - intros ?. contradict Neq2. by apply one_target_c.
  - intros ?. contradict Neq1. by apply one_target_c.
Qed.

(* Inclusion of edges from G *)
Definition subst_ax_incl_EG (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) (e : edge G) :
  edge (subst_ax_graph V Ho) :=
  if @boolP (e \in ~: edges_at v) is AltTrue p then Some (Some (inl (Sub e p)))
  else if e == ax_formula_edge V then Some None
  else None.

(* Last case in subst_ax_incl_EG *)
Lemma subst_ax_incl_EG_other_edge (G : proof_structure) (v : G) (V : vlabel v = ax) (e : edge G) :
  e \notin ~: edges_at v -> e <> ax_formula_edge V -> e = other_ax (ax_formula_endpoint V).
Proof.
  intros H ?.
  apply other_ax_eq. split; trivial.
  rewrite ax_formula_edge_in.
  revert H. rewrite !in_set => /negPn/existsP[[] /eqP-H] //.
  contradict H.
  by apply no_target_ax.
Qed.

Lemma subst_ax_incl_EG_SS (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (e : edge G) (E : e \in ~: edges_at v) :
  subst_ax_incl_EG V Ho e = Some (Some (inl (Sub e E))).
Proof. unfold subst_ax_incl_EG. case: {-}_ /boolP => [? | /negP-? //]. cbnb. Qed.

Lemma subst_ax_incl_EG_SN (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  subst_ax_incl_EG V Ho (ax_formula_edge V) = Some None.
Proof.
  unfold subst_ax_incl_EG.
  case: {-}_ /boolP => [In | ?]; [ | case_if].
  contradict In. apply /negP.
  rewrite subst_ax_G_removed !in_set !in_set1.
  apply /negPn. caseb.
Qed.

Lemma subst_ax_incl_EG_N (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  subst_ax_incl_EG V Ho (other_ax (ax_formula_endpoint V)) = None.
Proof.
  unfold subst_ax_incl_EG.
  case: {-}_ /boolP => [In | In].
  - contradict In. apply /negP.
    rewrite subst_ax_G_removed !in_set !in_set1.
    apply /negPn. caseb.
  - case_if.
    by assert (other_ax (ax_formula_endpoint V) <> ax_formula_edge V) by apply other_ax_neq.
Qed.

Lemma subst_ax_incl_EG_inj (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  injective (subst_ax_incl_EG V Ho).
Proof.
  intros e f.
  unfold subst_ax_incl_EG.
  case: {-}_ /boolP => [E | E];
  case: {-}_ /boolP => [F | F].
  { intro Eq. by inversion Eq. }
  all: case_if.
  transitivity (other_ax (ax_formula_endpoint V)); [ | symmetry];
  by apply subst_ax_incl_EG_other_edge.
Qed.

Lemma subst_ax_incl_EG_elabel (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) (e : edge G) :
  elabel (subst_ax_incl_EG V Ho e) = elabel e.
Proof.
  unfold subst_ax_incl_EG.
  case: {-}_ /boolP => [// | In].
  case_if.
  f_equal.
  symmetry. apply other_ax_eq. split; trivial.
  rewrite ax_formula_edge_in.
  revert In. rewrite !in_set => /negPn/existsP[[] /eqP-In] //.
  contradict In.
  by apply no_target_ax.
Qed.

Lemma subst_ax_incl_EG_flabel (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) (e : edge G) :
  flabel (subst_ax_incl_EG V Ho e) = flabel e.
Proof. by rewrite /flabel subst_ax_incl_EG_elabel. Qed.

Lemma subst_ax_incl_EG_llabel (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) (e : edge G) :
  llabel (subst_ax_incl_EG V Ho e) = llabel e.
Proof. by rewrite /llabel subst_ax_incl_EG_elabel. Qed.

Lemma subst_ax_incl_EG_edges_at (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (b : bool) (u : G) (U : u \in [set~ v]) :
  edges_at_outin b (inl (Sub u U) : subst_ax_graph V Ho) =
  [set subst_ax_incl_EG V Ho e | e in edges_at_outin b u].
Proof.
  apply setP => e.
  rewrite in_set.
  destruct (eq_comparable (endpoint b e) (inl (Sub u U))) as [Heq | Hneq]; symmetry.
  - rewrite Heq eq_refl.
    apply /imsetP.
    destruct e as [[[[e E] | ?] | ] | ]; try by [].
    + exists e.
      * inversion Heq. apply endpoint_in_edges_at_outin.
      * symmetry. apply subst_ax_incl_EG_SS.
    + exists (ax_formula_edge V).
      * destruct b; simpl in Heq; try by [].
        inversion Heq. apply endpoint_in_edges_at_outin.
      * symmetry. apply subst_ax_incl_EG_SN.
    + exists (other_ax (ax_formula_endpoint V)).
      * destruct b; simpl in Heq; try by [].
        inversion Heq. apply endpoint_in_edges_at_outin.
      * symmetry. apply subst_ax_incl_EG_N.
  - transitivity false; last by (symmetry; by apply /eqP).
    apply /imsetP.
    intros [f F ?]. subst e.
    revert F. rewrite in_set => /eqP-?. subst u.
    revert Hneq.
    unfold subst_ax_incl_EG.
    case: {-}_ /boolP => [In | ]; [ | case_if].
    + by move => /eqP; cbn; simpl => /eqP.
    + destruct b.
      * by replace U with (subst_ax_graph_01 V) in * by apply eq_irrelevance.
      * clear - U. contradict U. apply /negP.
        rewrite !in_set in_set1. apply /negPn/eqP.
        apply ax_formula_edge_in.
    + assert (f = other_ax (ax_formula_endpoint V)) by by apply subst_ax_incl_EG_other_edge.
      subst f.
      destruct b.
      * by replace U with (subst_ax_graph_02 V) in * by apply eq_irrelevance.
      * clear - U. contradict U. apply /negP.
        rewrite !in_set in_set1 other_ax_e. apply /negPn/eqP.
        apply ax_formula_edge_in.
Qed.

(* Inclusion of edges from H *)
Definition subst_ax_incl_EH (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) (e : edge H) :
  edge (subst_ax_graph V Ho) :=
  if @boolP (e \in edge_set (setT :\ target c1 :\ target c2))
    is AltTrue p then Some (Some (inr (Sub e p)))
    else if e == c1 then Some None
    else None.

(* Last case in subst_ax_incl_EH *)
Lemma subst_ax_incl_EH_other_edge (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (e : edge H) :
  e \notin edge_set (setT :\ target c1 :\ target c2) -> e <> c1 -> e = c2.
Proof. rewrite subst_ax_H_removed // !in_set !in_set1. introb. Qed.

Lemma subst_ax_incl_EH_SS (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (e : edge H) (E : e \in edge_set (setT :\ target c1 :\ target c2)) :
  subst_ax_incl_EH V Ho e = Some (Some (inr (Sub e E))).
Proof. unfold subst_ax_incl_EH. case: {-}_ /boolP => [? | /negP-? //]. cbnb. Qed.

Lemma subst_ax_incl_EH_SN (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  subst_ax_incl_EH V Ho c1 = Some None.
Proof.
  unfold subst_ax_incl_EH.
  case: {-}_ /boolP => [In | ?]; [ | case_if].
  contradict In. apply /negP.
  rewrite subst_ax_H_removed // !in_set !in_set1. caseb.
Qed.

Lemma subst_ax_incl_EH_N (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  subst_ax_incl_EH V Ho c2 = None.
Proof.
  unfold subst_ax_incl_EH.
  case: {-}_ /boolP => [In | In].
  - contradict In. apply /negP.
    rewrite !in_set !in_set1. caseb.
  - case_if.
    by assert (c1 <> c1) by apply (subst_ax_conc_H_neq Ho).
Qed.

Lemma subst_ax_incl_EH_inj (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  injective (subst_ax_incl_EH V Ho).
Proof.
  intros e f.
  unfold subst_ax_incl_EH.
  case: {-}_ /boolP => [E | E];
  case: {-}_ /boolP => [F | F].
  { intro Eq. by inversion Eq. }
  all: case_if.
  transitivity c2; [ | symmetry];
  by apply (subst_ax_incl_EH_other_edge Ho).
Qed.

Lemma subst_ax_incl_EH_edges_at (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (b : bool) (u : H) (U : u \in (setT :\ target c1 :\ target c2)) :
  edges_at_outin b (inr (Sub u U) : subst_ax_graph V Ho) =
  [set subst_ax_incl_EH V Ho e | e in edges_at_outin b u].
Proof.
  apply setP => e.
  rewrite in_set.
  destruct (eq_comparable (endpoint b e) (inr (Sub u U))) as [Heq | Hneq]; symmetry.
  - rewrite Heq eq_refl.
    apply /imsetP.
    destruct e as [[[? | [e E]] | ] | ]; try by [].
    + exists e.
      * inversion Heq. apply endpoint_in_edges_at_outin.
      * symmetry. apply subst_ax_incl_EH_SS.
    + exists c1.
      * destruct b; simpl in Heq; try by [].
        inversion Heq. apply endpoint_in_edges_at_outin.
      * symmetry. apply subst_ax_incl_EH_SN.
    + exists c2.
      * destruct b; simpl in Heq; try by [].
        inversion Heq. apply endpoint_in_edges_at_outin.
      * symmetry. apply subst_ax_incl_EH_N.
  - transitivity false; last by (symmetry; by apply /eqP).
    apply /imsetP.
    intros [f F ?]. subst e.
    revert F. rewrite in_set => /eqP-?. subst u.
    revert Hneq.
    unfold subst_ax_incl_EH.
    case: {-}_ /boolP => [In | ]; [ | case_if].
    + by move => /eqP; cbn; simpl => /eqP.
    + destruct b.
      * clear - U. contradict U. apply /negP.
        rewrite !in_set !in_set1. caseb.
      * by replace U with (subst_ax_graph_11 Ho) in * by apply eq_irrelevance.
    + assert (f = c2) by by apply (subst_ax_incl_EH_other_edge Ho).
      subst f.
      destruct b.
      * clear - U. contradict U. apply /negP.
        rewrite !in_set !in_set1. caseb.
      * by replace U with (subst_ax_graph_12 Ho) in * by apply eq_irrelevance.
Qed.

Lemma subst_ax_incl_EH_flabel (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) (e : edge H) :
  flabel c1 = flabel (ax_formula_edge V) ->
  flabel c2 = (flabel (ax_formula_edge V))^ ->
  flabel (subst_ax_incl_EH V Ho e) = flabel e.
Proof.
  intros F1 F2.
  unfold subst_ax_incl_EH.
  case: {-}_ /boolP => [// | In].
  case_if.
  assert (e = c2) as -> by by apply (subst_ax_incl_EH_other_edge Ho).
  enough (F : flabel (other_ax (ax_formula_endpoint V)) = (flabel (ax_formula_edge V))^)
    by by revert F; unfold flabel => ->.
  apply other_ax_flabel.
Qed.

Lemma subst_ax_incl_EH_llabel (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) (e : edge H) :
  target e \in setT :\ target c1 :\ target c2 ->
  llabel (subst_ax_incl_EH V Ho e) = llabel e.
Proof.
  intro E.
  unfold subst_ax_incl_EH.
  case: {-}_ /boolP => [// | In].
  contradict In. apply /negP/negPn.
  rewrite in_set E !in_set !in_set1. splitb; apply /eqP.
  all: apply no_source_c, (subst_ax_conc_H_c Ho).
Qed.

(* TODO Pour H et G : gros copié collé, comment factoriser ça ? fonction incl avec i : bool en param ? *)

(** Graph data of an expanded axiom *)
Definition subst_ax_graph_data (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) : graph_data := {|
  graph_of := _;
  order := [seq subst_ax_incl_EG V Ho e | e <- order G];
  |}.

(** Proof structure of an expanded axiom *)
Lemma subst_ax_p_deg (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  proper_degree (subst_ax_graph V Ho).
Proof.
  unfold proper_degree.
  intros b [[u U] | [u U]].
  - rewrite -(p_deg b u) subst_ax_incl_EG_edges_at.
    apply card_imset, subst_ax_incl_EG_inj.
  - rewrite -(p_deg b u) subst_ax_incl_EH_edges_at.
    apply card_imset, subst_ax_incl_EH_inj.
Qed.

Lemma subst_ax_p_ax_cut (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  flabel c1 = flabel (ax_formula_edge V) ->
  flabel c2 = (flabel (ax_formula_edge V))^ ->
  proper_ax_cut (subst_ax_graph V Ho).
Proof.
  intros.
  unfold proper_ax_cut.
  move => b [[u U] | [u U]] /= Hl.
  - destruct (p_ax_cut Hl) as [l [r [L [R LR]]]].
    exists (subst_ax_incl_EG V Ho l), (subst_ax_incl_EG V Ho r).
    rewrite !subst_ax_incl_EG_edges_at !subst_ax_incl_EG_flabel.
    splitb; by apply imset_f.
  - destruct (p_ax_cut Hl) as [l [r [L [R LR]]]].
    exists (subst_ax_incl_EH V Ho l), (subst_ax_incl_EH V Ho r).
    rewrite !subst_ax_incl_EH_edges_at !subst_ax_incl_EH_flabel //.
    splitb; by apply imset_f.
Qed.

Lemma subst_ax_p_tens_parr (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  flabel c1 = flabel (ax_formula_edge V) ->
  flabel c2 = (flabel (ax_formula_edge V))^ ->
  proper_tens_parr (subst_ax_graph V Ho).
Proof.
  intros F1 F2.
  unfold proper_tens_parr.
  move => b [[u U] | [u U]] /= Hl.
  - destruct (p_tens_parr Hl) as [l [r [c [? [? [? [? [? ?]]]]]]]].
    exists (subst_ax_incl_EG V Ho l), (subst_ax_incl_EG V Ho r), (subst_ax_incl_EG V Ho c).
    rewrite !subst_ax_incl_EG_edges_at !subst_ax_incl_EG_flabel !subst_ax_incl_EG_llabel.
    splitb; by apply imset_f.
  - destruct (p_tens_parr Hl) as [l [r [c [L [? [R [? [? ?]]]]]]]].
    exists (subst_ax_incl_EH V Ho l), (subst_ax_incl_EH V Ho r), (subst_ax_incl_EH V Ho c).
    rewrite !subst_ax_incl_EH_edges_at !subst_ax_incl_EH_flabel //.
    splitb; try by apply imset_f.
    all: rewrite subst_ax_incl_EH_llabel //.
    + by revert L; rewrite in_set => /eqP-->.
    + by revert R; rewrite in_set => /eqP-->.
Qed.

Lemma subst_ax_p_noleft (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  proper_noleft (subst_ax_graph V Ho).
Proof.
  intros [[[? | ?] | ] | ].
  - apply p_noleft.
  - apply p_noleft.
  - rewrite /= -subst_ax_incl_EG_SN subst_ax_incl_EG_llabel.
    apply p_noleft.
  - rewrite /= -subst_ax_incl_EG_N subst_ax_incl_EG_llabel.
    apply p_noleft.
Qed.

Lemma subst_ax_p_order_full (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  proper_order_full (subst_ax_graph_data V Ho).
Proof.
  rewrite /proper_order_full. simpl order.
  intros [[[[e E] | [e E]] | ] | ]; simpl.
  - rewrite -(subst_ax_incl_EG_SS V Ho) mem_map; last by apply subst_ax_incl_EG_inj.
    apply p_order_full.
  - assert (forall i, Some (Some (inr i)) \in [seq subst_ax_incl_EG V Ho u | u <- order G] = false)
      as ->.
    { intros ?.
      apply /negP => /mapP[? _].
      unfold subst_ax_incl_EG.
      case: {-}_ /boolP; case_if. }
    split => C //.
    apply p_order_full in C.
    contradict E. apply /negP.
    revert C.
    rewrite Ho /= !in_cons in_nil !in_set !in_set1.
    introb; caseb.
  - rewrite -subst_ax_incl_EG_SN mem_map; last by apply subst_ax_incl_EG_inj.
    apply p_order_full.
  - rewrite -subst_ax_incl_EG_N mem_map; last by apply subst_ax_incl_EG_inj.
    apply p_order_full.
Qed.

Lemma subst_ax_p_order_uniq (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  proper_order_uniq (subst_ax_graph_data V Ho).
Proof.
  rewrite /proper_order_uniq. simpl order.
  rewrite map_inj_uniq; last by apply subst_ax_incl_EG_inj.
  apply p_order_uniq.
Qed.

Definition subst_ax_ps (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (F1 : flabel c1 = flabel (ax_formula_edge V))
  (F2 : flabel c2 = (flabel (ax_formula_edge V))^) : proof_structure := {|
  graph_data_of := subst_ax_graph_data V Ho;
  p_deg := @subst_ax_p_deg _ _ _ _ _ _ _;
  p_ax_cut := @subst_ax_p_ax_cut _ _ _ _ _ _ _ F1 F2;
  p_tens_parr := @subst_ax_p_tens_parr _ _ _ _ _ _ _ F1 F2;
  p_noleft := @subst_ax_p_noleft _ _ _ _ _ _ _;
  p_order_full := @subst_ax_p_order_full _ _ _ _ _ _ _;
  p_order_uniq := subst_ax_p_order_uniq _ _;
  |}.

Fixpoint subst_ax_upath_bwd_G (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (p : @upath _ _ (subst_ax_graph V Ho)) : @upath _ _ G :=
  match p with
  | [::] => [::]
  | (e, b) :: p' => match e with
    | Some (Some (inl (exist e' _))) => [:: (e', b)]
    | Some (Some (inr _)) => [::]
    | Some None => [:: (ax_formula_edge V, b)]
    | None => [:: (other_ax (ax_formula_endpoint V), b)]
  end ++ subst_ax_upath_bwd_G p'
end.

(* méthode : si cycle c dans graph,
alors expanse_ax_upath_bwd c cycle dans G;
si expanse_ax_upath_bwd p vide, alors p inclut dans expanded_ax (ie p = Some Some inr p'
et p' chem entre antécédents)
donc si cycle c, alors cycle c' dans expanded, absurde *)

Definition subst_ax_u_G (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (u : subst_ax_graph V Ho) : G :=
  match u with
  | inl (exist u _) => u
  | _ => v
  end.

Lemma subst_ax_switching_eq (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (e f : edge G) :
  switching e = switching f ->
  switching (subst_ax_incl_EG V Ho e) = switching (subst_ax_incl_EG V Ho f).
Proof.
  move => /eqP.
  unfold subst_ax_incl_EG.
  case: {-}_ /boolP => [E | E];
  case: {-}_ /boolP => [F | F];
  unfold switching; case_if; cbnb; simpl in *.
  all: try ((assert (f = other_ax (ax_formula_endpoint V)) by by apply subst_ax_incl_EG_other_edge);
    subst f); try by [].
  all: try ((assert (e = other_ax (ax_formula_endpoint V)) by by apply subst_ax_incl_EG_other_edge);
    subst e); try by [].
  all: try by assert (~ eqb_rule (vlabel (target (ax_formula_edge V))) (⅋)) by by apply /negP.
  all: try by assert (~ eqb_rule (vlabel (target (other_ax (ax_formula_endpoint V)))) (⅋)) by by apply /negP.
  all: try by contradict E; apply /negP.
  all: try by contradict F; apply /negP.
Qed.
(* TODO 100 cas, long *)

Lemma subst_ax_image_in (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (p : upath) (e : edge G) (b : bool) :
  (e, b) \in subst_ax_upath_bwd_G p -> (subst_ax_incl_EG V Ho e, b) \in p.
Proof.
  revert e b. induction p as [ | (f, fb) p IH] => e eb //=.
  rewrite in_cons mem_cat.
  move => /orP[In | ?]; apply /orP; [left | right; by apply IH].
  destruct f as [[[[f F] | f] | ] | ].
  all: revert In; rewrite ?in_cons in_nil ?orb_false_r => /eqP-In //.
  all: inversion In; clear In; subst e eb.
  - by rewrite subst_ax_incl_EG_SS.
  - by rewrite subst_ax_incl_EG_SN.
  - by rewrite subst_ax_incl_EG_N.
Qed.

Lemma subst_ax_switching_notin (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (p : upath) (e : edge G) :
  switching (subst_ax_incl_EG V Ho e) \notin [seq switching f.1 | f <- p] ->
  switching e \notin [seq switching f.1 | f <- subst_ax_upath_bwd_G p].
Proof.
  intro Nin.
  apply /mapP.
  intros [(f, b) F EF].
  contradict Nin. apply /negP/negPn/mapP.
  exists (subst_ax_incl_EG V Ho f, b).
  - by apply subst_ax_image_in.
  - by apply subst_ax_switching_eq.
Qed.

Lemma subst_ax_switching_eq_SSR (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (e f : edge H)
  (E : e \in edge_set (setT :\ target c1 :\ target c2))
  (F : f \in edge_set (setT :\ target c1 :\ target c2)) :
  switching e = switching f ->
  switching (Some (Some (inr (Sub e E))) : edge (subst_ax_graph V Ho)) =
    switching (Some (Some (inr (Sub f F))) : edge (subst_ax_graph V Ho)).
Proof. move => /eqP. unfold switching; case_if; cbnb. Qed.

Lemma subst_ax_supath_bwd (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (p : upath) (s t : subst_ax_graph V Ho) :
  supath switching s t p ->
  supath switching (subst_ax_u_G s) (subst_ax_u_G t) (subst_ax_upath_bwd_G p).
Proof.
  revert s t. induction p as [ | (e, b) p IH] => s t.
  { move => /andP[/andP[/eqP-? _] _]. subst. apply supath_nilK. }
  rewrite /supath /= !in_cons !map_cat cat_uniq mem_cat !negb_orb.
  move => /andP[/andP[/andP[/eqP-? W] /andP[u U]] /andP[/eqP-n N]]. subst s.
  assert (P : supath switching (endpoint b e) t p) by splitb.
  revert IH => /(_ _ _ P) {W U N P} /andP[/andP[W2 ->] ->]. splitb.
  - rewrite uwalk_cat.
    move: W2.
    destruct e as [[[[e E] | e] | ] | ], b;
    by rewrite /= /uendpoint /= !eq_refl //= ?other_ax_e ax_formula_edge_in // eq_refl !andb_true_r /=.
  - by destruct e as [[[[e E] | e] | ] | ].
  - destruct e as [[[[e E] | e] | ] | ];
    rewrite has_sym //= orb_false_r;
    apply subst_ax_switching_notin.
    + by rewrite subst_ax_incl_EG_SS.
    + by rewrite subst_ax_incl_EG_SN.
    + by rewrite subst_ax_incl_EG_N.
  - by destruct e as [[[[? ?] | ?] | ] | ].
Qed.

Lemma subst_ax_upath_bwd_empty (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (p : @upath _ _ (subst_ax_graph V Ho)) :
  subst_ax_upath_bwd_G p = [::] ->
  {p' | p = [seq (Some (Some (inr e.1)), e.2) | e <- p']}.
Proof.
  induction p as [ | (e, b) p IH].
  { intros _. by exists [::]. }
  move=> /= /eqP. rewrite cat_nil => /andP[/eqP-E /eqP-P].
  destruct (IH P) as [p' ?]. subst p. clear IH P.
  destruct e as [[[[? ?] | e] | ] | ]; try by []. clear E.
  by exists ((e, b) :: p').
Qed.

Definition subst_ax_upath_bwd_empty' (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (p : @upath _ _ (subst_ax_graph V Ho)) (P : subst_ax_upath_bwd_G p = [::]) : upath :=
  [seq (val e.1,e.2) | e <- projT1 (subst_ax_upath_bwd_empty P)].

Lemma subst_ax_supath_bwd_empty (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (p : upath) (P : subst_ax_upath_bwd_G p = [::]) (s t : subst_ax_graph V Ho) :
  supath switching s t p -> p <> [::] ->
  { '(s', t') | s = inr s' /\ t = inr t' /\ supath switching (val s') (val t') (subst_ax_upath_bwd_empty' P)}.
Proof.
  unfold subst_ax_upath_bwd_empty'.
  destruct (subst_ax_upath_bwd_empty P) as [p' ?]. clear P. subst p. simpl.
  destruct s as [s | s].
  { by destruct p'. }
  destruct t as [t | t].
  { move => /andP[/andP[W _] _]. contradict W.
    case/lastP: p' => [// | ? ?]. by rewrite map_rcons uwalk_rcons => /andP[_ ?]. }
  intros P' _.
  exists (s, t). split; [ | split]; trivial.
  revert s t P'. induction p' as [ | ([e E], b) p' IH] => // [[s S] t].
  rewrite /supath /= in_cons SubK'. cbn. rewrite SubK => /andP[/andP[/andP[/eqP-? ?] /andP[u' ?]] ?].
  subst s.
  assert (P' : supath switching (inr (Sub (endpoint b e) (induced_proof b E)) : subst_ax_graph V Ho)
    (inr t) [seq (Some (Some (inr e.1)), e.2) | e <- p']) by splitb.
  revert IH => /(_ _ _ P') {P'} /andP[/andP[-> ->] ->].
  clear - u'. splitb.
  rewrite -map_comp {b}.
  apply /negP. move => /mapP[f Fin EF].
  contradict u'. apply /negP/negPn.
  rewrite -map_comp. apply /mapP.
  exists f; trivial.
  revert EF. simpl.
  destruct f as ([f F], bf).
  apply subst_ax_switching_eq_SSR.
Qed.

Lemma subst_ax_uacyclic (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  uacyclic (@switching _ G) -> uacyclic (@switching _ H) ->
  uacyclic (@switching _ (subst_ax_graph V Ho)).
Proof.
  move => AG AH u [p P]. cbnb. apply /eqP/negPn/negP => /eqP-?.
  revert AG => /(_ _ (Sub _ (subst_ax_supath_bwd P)))/eqP. cbn => /= /eqP-AG.
  destruct (subst_ax_supath_bwd_empty AG P) as [[s' t'] [S [T P']]]; first by by [].
  subst u. inversion T. clear T. subst t'.
  unfold subst_ax_upath_bwd_empty' in P'.
  destruct (subst_ax_upath_bwd_empty AG) as [p' ?]. subst p. simpl in P'.
  revert AH => /(_ _ (Sub _ P'))/eqP. cbn => /= /eqP/eqP.
  rewrite map_nil => /eqP-?. by subst p'.
Qed.

Lemma subst_ax_nb_vertices (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  #|G| + #|H| = #|subst_ax_graph V Ho| + 3.
Proof.
  rewrite /subst_ax_graph /= card_sum card_set_subset card_set_subset !setE cardsC1.
  rewrite -(cardsE H) (cardsD1 (target c1)) (cardsD1 (target c2)) cardsE.
  rewrite !in_set !in_set1 /=.
  replace (target c2 != target c1) with true
    by (symmetry; apply /eqP; apply nesym, (subst_ax_target_conc_H_neq Ho)).
  assert (#|G| <> 0) by by apply fintype0.
  simpl in *. lia.
Qed.

Lemma subst_ax_nb_edges (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  #|edge G| + #|edge H| = #|edge (subst_ax_graph V Ho)| + 2.
Proof.
  rewrite /= !card_option card_sum /= subst_ax_G_removed subst_ax_H_removed // !card_set_subset
    !setE setC2.
  rewrite -cardsT (cardsD1 (ax_formula_edge V)) (cardsD1 (other_ax (ax_formula_endpoint V))).
  rewrite -cardsT (cardsD1 c1) (cardsD1 c2).
  rewrite !in_set !in_set1 /=.
  replace (other_ax (ax_formula_endpoint V) != ax_formula_edge V) with true
    by by (symmetry; apply /eqP; apply other_ax_neq).
  replace (c2 != c1) with true
    by by (symmetry; apply /eqP; apply nesym, subst_ax_conc_H_neq).
  lia.
Qed.

Lemma subst_ax_nb_parr (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  #|[set u : G | vlabel u == ⅋]| + #|[set u : H | vlabel u == ⅋]| = #|[set u : subst_ax_graph V Ho | vlabel u == ⅋]|.
Proof.
  rewrite cards_sum_pred. f_equal.
  - by rewrite (cards_subgraph_pred _ (fun x => vlabel x == ⅋)) set1CI (cardsD1 v) in_set V.
  - rewrite (cards_subgraph_pred (@induced_proof _ _ _ _) (fun x => vlabel x == ⅋)) !setIDA setIT.
    rewrite (cardsD1 (target c1)) (cardsD1 (target c2)) !in_set !in_set1.
    destruct (subst_ax_conc_H_c Ho) as [-> ->].
    replace (target c2 != target c1) with true
      by (symmetry; apply /eqP; apply nesym, (subst_ax_target_conc_H_neq Ho)).
    simpl. lia.
Qed.

Lemma subst_ax_uconnected_nb (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  flabel c1 = flabel (ax_formula_edge V) ->
  flabel c2 = (flabel (ax_formula_edge V))^ ->
  uacyclic (@switching _ G) -> uacyclic (@switching _ H) ->
  uconnected_nb (@switching_left _ (subst_ax_graph V Ho)) + 1 =
  uconnected_nb (@switching_left _ G) + uconnected_nb (@switching_left _ H).
Proof.
  move => F1 F2 AG AH.
  assert (NG := switching_left_uconnected_nb AG).
  assert (NH := switching_left_uconnected_nb AH).
  assert (N := @switching_left_uconnected_nb atom (subst_ax_ps Ho F1 F2) (subst_ax_uacyclic AG AH)).
  assert (X0 := subst_ax_nb_vertices V Ho).
  assert (X1 := subst_ax_nb_edges V Ho).
  assert (X2 := subst_ax_nb_parr V Ho).
  simpl in *. lia.
Qed.

Lemma subst_ax_correct (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  flabel c1 = flabel (ax_formula_edge V) ->
  flabel c2 = (flabel (ax_formula_edge V))^ ->
  correct G -> correct H -> correct (subst_ax_graph V Ho).
Proof.
  intros F1 F2 [AG CG] [AH CH]. split.
  - by apply subst_ax_uacyclic.
  - assert (N := subst_ax_uconnected_nb Ho F1 F2 AG AH). lia.
Qed.

Definition subst_ax_pn (G : proof_net)(v : G) (V : vlabel v = ax)
  (H : proof_net) (c1 c2 : edge H) (Ho : order H = [:: c1; c2])
  (F1 : flabel c1 = flabel (ax_formula_edge V))
  (F2 : flabel c2 = (flabel (ax_formula_edge V))^) : proof_net := {|
  ps_of := subst_ax_ps Ho F1 F2;
  p_correct := subst_ax_correct Ho F1 F2 (p_correct G) (p_correct H);
  |}.

(** Sequent of an expanded axiom *)
Lemma subst_ax_sequent (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (c1 c2 : edge H) (Ho : order H = [:: c1; c2]) :
  sequent (subst_ax_graph_data V Ho) = sequent G.
Proof.
  rewrite /sequent -map_comp.
  apply eq_map => e.
  by rewrite /= subst_ax_incl_EG_flabel.
Qed.

Lemma subst_ax_proofs (H : graph_data) (A B : formula) :
  sequent H = [:: A ; B] ->
  {'(c1, c2) | order H = [:: c1; c2] /\ flabel c1 = A /\ flabel c2 = B}.
Proof.
  unfold sequent.
  destruct (order H) as [ | c1 [ | c2 [ | ? ?]]];
  cbn; rewrite ?andb_false_r //.
  intro Ho. inversion Ho.
  by exists (c1, c2).
Qed.

Definition subst_ax_ps_seq (G : proof_structure) (v : G) (V : vlabel v = ax)
  (H : proof_structure) (Hs : sequent H = [:: flabel (ax_formula_edge V) ; (flabel (ax_formula_edge V))^]) :
  proof_structure.
Proof. destruct (subst_ax_proofs Hs) as [(c1, c2) [Ho [F1 F2]]]. exact (subst_ax_ps Ho F1 F2). Defined.


(** ** Graph of an expanded axiom - all steps at once *)
Lemma ax_expanded_all_0 (G : proof_structure) (v : G) (V : vlabel v = ax) (A B : formula) :
  ax_formula V = A ⊗ B ->
  sequent (pn (ax_exp (dual B ⅋ A^))) = [:: flabel (ax_formula_edge V) ; (flabel (ax_formula_edge V))^].
Proof. by rewrite ps_consistent /= !bidual /ax_formula => ->. Qed.

Definition ax_expanded_all (G : proof_structure) (v : G) (V : vlabel v = ax) (A B : formula) (F : ax_formula V = A ⊗ B) :
  proof_structure := subst_ax_ps_seq (ax_expanded_all_0 F).

(** ** Graph of an expanded axiom - one step *)
Definition Permutation_Type_2_def {A : Type} (a b : A) : Permutation_Type [:: a; b] [:: b; a] :=
  Permutation_Type_swap b a [::].

Definition Permutation_Type_3_def {A : Type} (a b c : A) : Permutation_Type [:: a; b; c] [:: b; c; a].
Proof.
  etransitivity. apply Permutation_Type_swap.
  apply Permutation_Type_skip, Permutation_Type_swap.
Defined.

Lemma expanded_ax_step0 (A B : formula) :
  exists e0 e1,
  order (ax_pn (A^)) = e0 :: behead (order (ax_pn (A^))) /\
  order (ax_pn (B^)) = e1 :: behead (order (ax_pn (B^))).
Proof. by exists ord0, ord0. Qed.

(** * Graph of two axioms A B linked by a tensor A ⊗ B *)
Definition ax_expanded_tens (A B : formula) : proof_net :=
  add_node_pn_tens (expanded_ax_step0 A B).
Lemma ax_expanded_tens_sequent (A B : formula) :
  sequent (ax_expanded_tens A B) = [:: A ⊗ B; B^; A^].
Proof. rewrite (@add_node_sequent atom). cbn. by rewrite !bidual. Qed.

Definition ax_expanded_tens_perm (A B : formula) :=
  perm_pn (Permutation_Type_3_def (A ⊗ B) (B^) (A^)) (ax_expanded_tens A B).
Lemma ax_expanded_tens_perm_sequent (A B : formula) :
  sequent (ax_expanded_tens_perm A B) = [:: B^; A^; A ⊗ B].
Proof. apply perm_sequent, ax_expanded_tens_sequent. Qed.

Lemma expanded_ax_step1' (A B : formula) :
  { '(e0, e1, e2) | order (ax_expanded_tens_perm A B) = [:: e0; e1; e2]
  /\ val e0 = (Some (Some (inl (inr ord1))) : edge (@add_node_graph_1 _ tens_t (union_ps _ _)
    (@inl (edge (ax_pn (A^))) (edge (ax_pn (B^))) ord0) (inr ord0)))
  /\ val e1 = (Some (Some (inl (inl ord1))) : edge (@add_node_graph_1 _ tens_t (union_ps _ _)
    (@inl (edge (ax_pn (A^))) (edge (ax_pn (B^))) ord0) (inr ord0)))
  /\ val e2 = (Some (Some (inr None)) : edge (@add_node_graph_1 _ tens_t (union_ps _ _)
    (@inl (edge (ax_pn (A^))) (edge (ax_pn (B^))) ord0) (inr ord0)))}.
Proof.
  rewrite /= /add_node_order.
  destruct (all_sigP _) as [l L].
  revert L. rewrite /add_node_order_2 /add_node_type_order /add_node_order_1 /=.
  destruct l as [ | [l0 L0] [ | [l1 L1] [ | [l2 L2] [ | ? ?]]]]; try by []; simpl.
  intro L. inversion L. subst.
  by exists ((Sub _ L1), (Sub _ L2), (Sub _ L0)).
Qed.

Lemma expanded_ax_step1 (A B : formula) :
  exists e0 e1, order (ax_expanded_tens_perm A B) = [:: e0, e1 & behead (behead (order (ax_expanded_tens_perm A B)))].
Proof.
  destruct (expanded_ax_step1' A B) as [[[e0 e1] e2] [-> _]].
  by exists e0, e1.
Qed.

Definition ax_expanded (A B : formula) := perm_pn
  (Permutation_Type_2_def (dual B ⅋ A^) (A ⊗ B)) (add_node_pn_parr (expanded_ax_step1 A B)).

Lemma ax_expanded_sequent (A B : formula) :
  sequent (ax_expanded A B) = [:: A ⊗ B; dual B ⅋ A^].
Proof.
  rewrite perm_sequent // add_node_sequent.
  destruct (expanded_ax_step1' A B) as [[[[? ?] [? ?]] [? ?]] [O [? [? ?]]]].
  rewrite !O {O} ax_expanded_tens_perm_sequent. simpl in *. by subst.
Qed.

Lemma ax_expanded_one_0 (G : proof_structure) (v : G) (V : vlabel v = ax) (A B : formula) :
  ax_formula V = A ⊗ B ->
  sequent (ax_expanded A B) = [:: flabel (ax_formula_edge V) ; (flabel (ax_formula_edge V))^].
Proof. by rewrite ax_expanded_sequent /ax_formula => ->. Qed.


Definition ax_expanded_one (G : proof_structure) (v : G) (V : vlabel v = ax)
  (A B : formula) (F : ax_formula V = A ⊗ B) : proof_structure :=
  subst_ax_ps_seq (ax_expanded_one_0 F).

(* TODO définir transformation rendant un réseau ax_atomic : par induction
sur ax_formula *)

(** Rewriting to expanse axioms *)
Definition is_atomicb (A : formula) :=
  if A is var _ then true else false.

Definition is_ax_atomic (G : proof_structure) (v : G) :=
  if @boolP (vlabel v == ax) is AltTrue V then is_atomicb (ax_formula (eqP V))
  else true.

Lemma expanse_term (G : proof_structure) :
  {ax_atomic G} + {exists v : G, ~~ is_ax_atomic v}.
Proof.
  destruct [exists v : G, ~~ is_ax_atomic v] eqn:H.
  { right. apply /existsP. exact H. }
  left.
  intros v V.
  revert H => /existsPn/(_ v)/negPn.
  unfold is_ax_atomic.
  case: {-}_ /boolP => [H | H].
  2:{ contradict H. by apply /negP/negPn/eqP. }
  replace (eqP H) with V by apply eq_irrelevance. clear H.
  unfold is_atomic, is_atomicb.
  by destruct (ax_formula V) eqn:F.
Qed.

(* TODO define the quantity which decrease: sum of the size of formulas on axioms ? *)
(* Show it decrease when expanding *)(*
Lemma expanse_one_nb (G : proof_structure) (v : G) (V : vlabel v = ax) (A B : formula)
  (VAB : flabel (ax_formula_edge V) = A ⊗ B) :
  #|expanse_ax_ps VAB| < #|G|.
Proof. (* TODO with good measure *)
Abort.*)

(** All steps *)(*
Lemma expanse_all (G : proof_structure) :
  {P : proof_structure | correct G -> correct P & sequent P = sequent G /\ ax_atomic P}.
(* TODO these properties are sufficient? *)
Proof.
  revert G.
  enough (Hm : forall n (G : proof_structure), #|G| = n ->
    {P : proof_structure | correct G -> correct P & sequent P = sequent G /\ ax_atomic P})
    by (intro G; by apply (Hm #|G|)).
  intro n; induction n as [n IH] using lt_wf_rect; intros G Hc.
  have [/has_cutP/existsP/sigW[v /eqP-Hcut] | /has_cutP-?] := altP (has_cutP G).
  2:{ by exists G. }
  assert (N : (#|red_one_ps Hcut| < n)%coq_nat) by (rewrite -Hc; apply /leP; apply red_one_nb).
  specialize (IH _ N _ erefl). destruct IH as [P CC [S C]].
  exists P; [ | split; trivial].
  - move => ?. by apply CC, red_one_correct.
  - rewrite S. apply red_one_sequent.
Qed.

Definition red (G : proof_structure) : proof_structure := proj1_sig (red_all G).

Lemma red_correct (G : proof_structure) : correct G -> correct (red G).
Proof. by destruct (proj2_sig (red_all G)) as [? _]. Qed.

Definition red_pn (G : proof_net) : proof_net := {|
  ps_of := red G;
  p_correct := red_correct (p_correct G);
  |}.

Lemma red_sequent (G : proof_structure) : sequent (red G) = sequent G.
Proof. by destruct (proj2_sig (red_all G)) as [_ [? _]]. Qed.

Lemma red_has_cut (G : proof_structure) : ~ has_cut (red G).
Proof. by destruct (proj2_sig (red_all G)) as [_ [_ ?]]. Qed.

(* TODO et definir une etape, puis repetition, idem cut *)
*)
End Atoms.
