(* Sequentialisation - A terminal ax vertex is sequentializing *)

From Coq Require Import Bool.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export mll_prelim mll_def mll_basic mll_seq_to_pn mll_pn_to_seq_def.

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


Section Sequentializing_ax.
Context {G : proof_net} {v : G} (V : vlabel v = ax) (T : terminal v).

Lemma sequentializing_ax_step0 :
  {'(e, e') | flabel e = flabel e'^ /\ source e = v /\ source e' = v /\ vlabel (target e) = c /\
  vlabel (target e') = c}.
Proof.
  destruct (p_ax_type V) as [[e e'] [E [E' F]]]. subst v.
  exists (e, e'); splitb; by apply (terminal_source T).
Qed.
Local Notation e := (fst (proj1_sig sequentializing_ax_step0)).
Local Notation e' := (snd (proj1_sig sequentializing_ax_step0)).

Lemma sequentializing_ax_step1 (u : G) : u = source e \/ u = target e \/ u = target e'.
Proof.
  destruct sequentializing_ax_step0 as [[e e'] [F [E [E' [Te Te']]]]];
  simpl; subst v.
  assert (C := p_correct G).
  apply correct_to_weak in C as [_ C].
  elim: (C (source e) u) => [[p /andP[/andP[W U] N]] _].
  destruct p as [ | [a b] p]; first by (move: W => /= /eqP-->; caseb).
  move: W => /= /andP[/eqP-Hf W].
  destruct b; last by (contradict Hf; by apply no_target_ax).
  enough (A : a = e \/ a = e').
  { destruct A; [set ae := e | set ae := e']; subst a.
    all: destruct p as [ | (a, b) p]; first by (revert W => /= /eqP-->; caseb).
    all: revert W => /= /andP[/eqP-Hf2 _].
    all: destruct b; first by (contradict Hf2; by apply no_source_c).
    all: contradict U; apply /negP.
    all: assert (a = ae) by (by apply one_target_c); subst a.
    all: rewrite /= in_cons; caseb. }
  assert (C2 : #|edges_at_out (source e)| == 2) by by apply /eqP; rewrite p_deg_out V.
  revert C2 => /cards2P[f [f' [/eqP-Fneq FF]]].
  assert (a \in edges_at_out (source e) /\ e \in edges_at_out (source e) /\
    e' \in edges_at_out (source e)) as [Ina [Ine Ine']]
    by by splitb; rewrite !in_set; apply /eqP.
  revert Ina Ine Ine'. rewrite !FF !in_set !in_set1. introb; subst; caseb.
  all: contradict F; apply nesym, no_selfdual.
Qed.

Lemma sequentializing_ax_step2 (a : edge G) : (a == e) || (a == e').
Proof.
  destruct (sequentializing_ax_step1 (target a)) as [A | A];
  destruct sequentializing_ax_step0 as [[e e'] [F [E [E' [Te Te']]]]];
  simpl; simpl in A; subst v.
  - contradict A. by apply no_target_ax.
  - destruct A as [A | A]; apply one_target_c in A; rewrite // A; caseb.
Qed.

Lemma sequentializing_ax_step3 :
  e' <> e /\ target e' <> source e /\ target e <> source e /\ target e' <> target e.
Proof.
  destruct sequentializing_ax_step0 as [[e e'] [F [E [E' [Te Te']]]]];
  simpl; subst v.
  assert (En : e' <> e).
  { intros ?. subst e'. contradict F. apply nesym, no_selfdual. }
  splitb.
  - rewrite -E'. apply nesym, no_selfloop.
  - by apply nesym, no_selfloop.
  - intros ?. contradict En. by by apply one_target_c.
Qed.

Definition terminal_ax_v_bij_fwd (u : G) : ax_graph (flabel e) :=
  if u == source e then ord0
  else if u == target e then ord2
  else ord1.

Definition terminal_ax_v_bij_bwd (u : ax_graph (flabel e)) : G :=
  match val u with
  | 0 => source e
  | 1 => target e'
  | _ => target e
  end.

Lemma terminal_ax_v_bijK : cancel terminal_ax_v_bij_fwd terminal_ax_v_bij_bwd.
Proof.
  intro u.
  unfold terminal_ax_v_bij_bwd, terminal_ax_v_bij_fwd. case_if.
  by destruct (sequentializing_ax_step1 u) as [? | [? | ?]].
Qed.

Lemma terminal_ax_v_bijK' : cancel terminal_ax_v_bij_bwd terminal_ax_v_bij_fwd.
Proof.
  destruct sequentializing_ax_step3 as [En [T'S [TS T'T]]].
  intro u.
  unfold terminal_ax_v_bij_bwd, terminal_ax_v_bij_fwd.
  destruct_I u; case_if; cbnb.
Qed.

Definition terminal_ax_iso_v := {|
  bijK:= terminal_ax_v_bijK;
  bijK':= terminal_ax_v_bijK';
  |}.

Definition terminal_ax_e_bij_fwd (a : edge G) : edge (ax_graph (flabel e)) :=
  if a == e then ord1 else ord0.

Definition terminal_ax_e_bij_bwd (a : edge (ax_graph (flabel e))) : edge G :=
  match val a with
  | 0 => e'
  | _ => e
  end.

Lemma terminal_ax_e_bijK : cancel terminal_ax_e_bij_fwd terminal_ax_e_bij_bwd.
Proof.
  intro a.
  unfold terminal_ax_e_bij_bwd, terminal_ax_e_bij_fwd. case_if.
  by elim: (orb_sum (sequentializing_ax_step2 a)) => /eqP-?.
Qed.

Lemma terminal_ax_e_bijK' : cancel terminal_ax_e_bij_bwd terminal_ax_e_bij_fwd.
Proof.
  destruct sequentializing_ax_step3 as [En _].
  intro a.
  unfold terminal_ax_e_bij_bwd, terminal_ax_e_bij_fwd.
  destruct_I a; case_if; cbnb.
Qed.

Definition terminal_ax_iso_e := {|
  bijK:= terminal_ax_e_bijK;
  bijK':= terminal_ax_e_bijK';
  |}.

Lemma terminal_ax_iso_ihom : is_ihom terminal_ax_iso_v terminal_ax_iso_e pred0.
Proof.
  rewrite /= /terminal_ax_v_bij_fwd /terminal_ax_e_bij_fwd.
  assert (Cu := sequentializing_ax_step1).
  assert (Ca := sequentializing_ax_step2).
  destruct sequentializing_ax_step3 as [En [T'S [TS T'T]]].
  destruct sequentializing_ax_step0 as [[e e'] [F [E [E' [Te Te']]]]];
  simpl in *; subst v.
  split.
  - intros a []; elim: (orb_sum (Ca a)) => /eqP-?; subst a; simpl.
    all: unfold terminal_ax_e_bij_fwd, terminal_ax_v_bij_fwd; case_if.
    enough (source e' <> target e) by by [].
    rewrite E'. by apply nesym.
  - intros u; destruct (Cu u) as [? | [? | ?]]; subst u; case_if.
  - intros a; elim: (orb_sum (Ca a)) => /eqP-?; subst a; case_if.
    + destruct (elabel e) as [Fe Le] eqn:LL.
      apply /eqP. revert LL => /eqP. cbn => /andP[? /eqP-L]. splitb.
      rewrite -L. apply p_noleft. caseb.
    + destruct (elabel e') as [Fe Le] eqn:LL.
      apply /eqP. revert LL => /eqP. cbn => /andP[/eqP-F' /eqP-L]. subst Fe Le. splitb.
      * rewrite F bidual. cbnb.
      * apply p_noleft. auto.
Qed.

Definition sequentializing_ax_iso : G ≃ ax_graph (flabel e) :=
  {| iso_ihom := terminal_ax_iso_ihom |}.

Lemma terminal_ax_is_sequentializing : sequentializing v.
Proof.
  rewrite /sequentializing V.
  exists (flabel e). exact sequentializing_ax_iso.
Qed.

End Sequentializing_ax.

End Atoms.