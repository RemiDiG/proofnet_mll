(* Sequentialisation - A terminal parr vertex is sequentializing *)

From Coq Require Import Bool.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export mll_prelim graph_more upath supath mll_def mll_basic mll_seq_to_pn
  mll_pn_to_seq_def.

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
Notation switching := (@switching atom).
Notation switching_left := (@switching_left atom).


Lemma add_node_parr_correct' (G : proof_structure) (e0 e1 : edge G) l :
  order G = e0 :: e1 :: l -> correct (add_node_graph parr_t e0 e1) -> correct G.
Proof.
  intros O C.
  assert (C' : correct (add_node_graph_1 parr_t e0 e1)).
  { apply (iso_correct (iso_sym (add_node_iso parr_t O))), add_concl_correct, correct_to_weak,
      add_concl_correct, correct_to_weak, C. }
  by apply (iso_correct (iso_sym (add_node_parr_iso e0 e1))), correct_to_weak,
    rem_concl_correct, correct_to_weak, rem_parr_correct in C'.
Qed.


Section Sequentializing_parr.
Context {G : proof_net} {v : G}.
Hypothesis (V : vlabel v = ⅋) (T : terminal v).

(* Vertices neighbourhing v *)
Local Notation elv := (left_parr V).
Local Notation erv := (right_parr V).
Local Notation ecv := (ccl_parr V).
Local Notation lv := (source elv).
Local Notation rv := (source erv).
Local Notation cv := (target ecv).

Lemma ecv_neq_elv : ecv != elv.
Proof.
  apply/eqP => F.
  assert (F' : target elv = target ecv) by by rewrite F.
  contradict F'.
  rewrite left_e -[in LHS](ccl_e (or_intror V)).
  apply no_selfloop.
Qed.

Lemma ecv_neq_erv : ecv != erv.
Proof.
  apply/eqP => F.
  assert (F' : target erv = target ecv) by by rewrite F.
  contradict F'.
  rewrite right_e -[in LHS](ccl_e (or_intror V)).
  apply no_selfloop.
Qed.

Lemma erv_neq_elv : erv != elv.
Proof. apply/eqP. apply nesym, left_neq_right. Qed.

Definition rem_parr_ps := rem_node_ps (or_intror V) T.

(* TODO Choose fwd for this direction, so that ihom is simpler *)
Definition rem_parr_v_bij_fwd (u : add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None))) : G :=
  match val u with
  | inl (inl (inl (exist a _))) => a
  | inr (inr tt)                => cv
  | _                           => v (* case inr (inl tt), other cases are absurd *)
  end.

Definition rem_parr_v_bij_bwd_1 (u : G) : add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None)) :=
  if @boolP (u \in [set: G] :\ v :\ cv)  is AltTrue U then
      inl (inl (inl (Sub u U))) : add_node_graph_1 parr_t (None : edge (rem_node_graph (or_intror V)))
        (Some (inl None))
  else if u == cv then inr (inr tt)
  else (* u == v *) inr (inl tt).

Lemma rem_parr_v_bij_bwd_helper (u : G) :
  rem_parr_v_bij_bwd_1 u \in [set: add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None))]
  :\ inl (target (None : edge rem_parr_ps)) :\ inl (target (Some (inl None) : edge rem_parr_ps)).
Proof.
  rewrite !in_set !in_set1 /= /rem_parr_v_bij_bwd_1.
  case: {-}_ /boolP => [// | _].
  by case: ifP.
Qed.

Definition rem_parr_v_bij_bwd (u : G) : add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None)) :=
  Sub (rem_parr_v_bij_bwd_1 u) (rem_parr_v_bij_bwd_helper u).

Lemma rem_parr_v_bij_bwd_last_case (u : G) :
  u \notin [set: G] :\ v :\ cv -> u != cv -> u == v.
Proof. by rewrite !in_set !in_set1 andb_true_r negb_andb !negb_involutive => /orP[-> | ->]. Qed.

Lemma rem_parr_v_bijK : cancel rem_parr_v_bij_fwd rem_parr_v_bij_bwd.
Proof.
  move=> [u U].
  apply val_inj.
  rewrite /rem_parr_v_bij_bwd /rem_parr_v_bij_fwd !SubK.
  rewrite !in_set !in_set1 /= in U.
  move: U => /andP[? /andP[? _]].
  destruct u as [[[[u Uin] | []] | []] | [[] | []]];
  rewrite // /rem_parr_v_bij_bwd_1.
  - case: {-}_ /boolP => [? | U']; first by cbnb.
    exfalso. by rewrite Uin in U'.
  - case: {-}_ /boolP => [U' | _].
    { contradict U'. by rewrite !in_set !in_set1 eq_refl andb_false_r. }
    case: ifP => [/eqP-F | //].
    contradict F. by apply v_neq_cv.
  - case: {-}_ /boolP => [U' | _].
    { contradict U'. by rewrite !in_set !in_set1 eq_refl. }
    by rewrite eq_refl.
Qed.

Lemma rem_parr_v_bijK' : cancel rem_parr_v_bij_bwd rem_parr_v_bij_fwd.
Proof.
  move=> u.
  rewrite /rem_parr_v_bij_fwd /rem_parr_v_bij_bwd SubK /rem_parr_v_bij_bwd_1.
  case: {-}_ /boolP => [// | Ul].
  case: ifP => [/eqP--> // | /eqP/eqP-UV] /=.
  symmetry. apply /eqP. by apply rem_parr_v_bij_bwd_last_case.
Qed.

Definition rem_parr_iso_v := {|
  bijK:= rem_parr_v_bijK;
  bijK':= rem_parr_v_bijK';
  |}.

Definition rem_parr_e_bij_bwd_1 (e : edge G) : edge (add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None))) :=
  if @boolP (e \in edge_set ([set: G] :\ v :\ cv)) is AltTrue E then
      Some (Some (inl (Some (inl (Some (inl (Sub e E : edge (induced ([set: G] :\ v :\ cv)))))) : edge rem_parr_ps)))
  else if e == elv then Some None
  else if e == erv then None
  else (* e == ecv *) Some (Some (inr None)).

Lemma rem_parr_e_bij_bwd_helper (e : edge G) :
  rem_parr_e_bij_bwd_1 e \in edge_set ([set: add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None))]
  :\ inl (target (None : edge rem_parr_ps)) :\ inl (target (Some (inl None) : edge rem_parr_ps))).
Proof.
  rewrite !in_set !in_set1 /= /rem_parr_e_bij_bwd_1.
  case: {-}_ /boolP => [// | _].
  by repeat (case: ifP).
Qed.

Definition rem_parr_e_bij_bwd (e : edge G) : edge (add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None))) :=
  Sub (rem_parr_e_bij_bwd_1 e) (rem_parr_e_bij_bwd_helper e).

Lemma rem_parr_e_bij_bwd_last_case (e : edge G) :
  e \notin edge_set ([set: G] :\ v :\ cv) -> e != elv -> e != erv -> e == ecv.
Proof. by rewrite rem_node_removed // !in_set !in_set1 andb_true_r !negb_andb
  !negb_involutive => /orP[-> | /orP[-> | ->]]. Qed.

Definition rem_parr_e_bij_fwd (e : edge (add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None)))) : edge G :=
  match val e with
  | Some (Some (inl (Some (inl (Some (inl (exist a _))))))) => a
  | Some None                                               => elv
  | None                                                    => erv
  | _                                                       => ecv (* case Some (Some (inr None)) *)
  end.

Lemma rem_parr_e_bijK : cancel rem_parr_e_bij_fwd rem_parr_e_bij_bwd.
Proof.
  move=> [e E].
  apply val_inj.
  rewrite /rem_parr_e_bij_bwd /rem_parr_e_bij_fwd !SubK.
  rewrite !in_set !in_set1 in E.
  move: E => /andP[/andP[? /andP[? _]] /andP[? /andP[? _]]].
  destruct e as [[[[[[[[e Ein] | []] | ] | []] | ] | [[[] | []] | ]] | ] | ];
  rewrite // /rem_parr_e_bij_bwd_1.
  - case: {-}_ /boolP => [? | E']; first by cbnb.
    exfalso. clear - Ein E'. by rewrite Ein in E'.
  - case: {-}_ /boolP => [E' | ?].
    { contradict E'. by rewrite rem_node_removed // !in_set !in_set1 eq_refl. }
    by rewrite (negPf ecv_neq_elv) (negPf ecv_neq_erv).
  - case: {-}_ /boolP => [E' | ?].
    { contradict E'. by rewrite rem_node_removed // !in_set !in_set1 eq_refl !andb_false_r. }
    by rewrite eq_refl.
  - case: {-}_ /boolP => [E' | ?].
    { contradict E'. by rewrite rem_node_removed // !in_set !in_set1 eq_refl !andb_false_r. }
    by rewrite (negPf erv_neq_elv) eq_refl.
Qed.

Lemma rem_parr_e_bijK' : cancel rem_parr_e_bij_bwd rem_parr_e_bij_fwd.
Proof.
  move=> e.
  rewrite /rem_parr_e_bij_bwd /rem_parr_e_bij_fwd SubK /rem_parr_e_bij_bwd_1.
  case: {-}_ /boolP => [// | E].
  case: ifP => [/eqP--> // | /eqP/eqP-?].
  case: ifP => [/eqP--> // | /eqP/eqP-?].
  apply/eqP. rewrite eq_sym. by apply rem_parr_e_bij_bwd_last_case.
Qed.

Definition rem_parr_iso_e :={|
  bijK:= rem_parr_e_bijK;
  bijK':= rem_parr_e_bijK';
  |}.

Lemma rem_parr_iso_ihom : is_ihom rem_parr_iso_v rem_parr_iso_e pred0.
Proof.
  split.
  - move=> [e E] b.
    rewrite /rem_parr_iso_e /rem_parr_e_bij_fwd /rem_parr_iso_v /rem_parr_v_bij_fwd /=.
    rewrite !in_set !in_set1 in E.
    move: E => /andP[/andP[? /andP[? _]] /andP[? /andP[? _]]].
    by destruct e as [[[[[[[[e Ein] | []] | ] | []] | ] | [[[] | []] | ]] | ] | ];
      try by []; destruct b; rewrite //= ?left_e ?right_e ?ccl_e.
  - move=> [u U].
    rewrite /rem_parr_iso_v /rem_parr_v_bij_fwd /=.
    rewrite !in_set !in_set1 /= in U.
    move: U => /andP[? /andP[? _]].
    destruct u as [[[[u Uin] | []] | []] | [[] | []]]; try by [].
    by apply vlabel_cv.
  - move=> [e E].
    rewrite /rem_parr_iso_e /rem_parr_e_bij_fwd /=.
    rewrite !in_set !in_set1 in E.
    move: E => /andP[/andP[? /andP[? _]] /andP[? /andP[? _]]].
    destruct e as [[[[[[[[e Ein] | []] | ] | []] | ] | [[[] | []] | ]] | ] | ];
      try by [].
    + rewrite elabel_eq.
      destruct (p_tens_parr_bis G) as [_ VE]. move: VE => /(_ _ V)-->.
      enough (llabel ecv) as -> by by [].
      apply p_noleft. rewrite vlabel_cv //. auto.
    + by rewrite elabel_eq left_l.
    + rewrite elabel_eq.
      enough (llabel erv = false) as -> by by [].
      apply/negP/negP. apply right_l.
Qed.

Definition rem_parr_iso : add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None)) ≃ G :=
  {| iso_ihom := rem_parr_iso_ihom |}.

Lemma rem_parr_ps_correct : correct rem_parr_ps.
Proof. by refine (add_node_parr_correct' _ (iso_correct rem_parr_iso (p_correct G))). Qed.

Lemma terminal_parr_is_sequentializing : sequentializing v.
Proof.
  rewrite /sequentializing V.
  exists {| p_correct := rem_parr_ps_correct |}. exact (iso_sym rem_parr_iso).
Qed.

End Sequentializing_parr.

End Atoms.