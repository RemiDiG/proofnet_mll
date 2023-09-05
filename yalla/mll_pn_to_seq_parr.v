(* Sequentialisation - A terminal parr vertex is sequentializing *)
(* From a Proof Net, return a LL proof of the same sequent *)

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

Definition rem_parr_ps := rem_node_ps (or_intror V) T.

Lemma rem_parr_v_bij_helper (u : induced ([set: G] :\ v :\ cv)) :
  inl (inl (inl u))
  \in [set: add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None))] :\
    inl (target (None : edge rem_parr_ps)) :\
    inl (target (Some (inl None) : edge rem_parr_ps)).
Proof. rewrite /= !in_set. splitb. Qed.

Lemma rem_parr_v_bij_fwd_helper0 :
 (inl (inl (inr tt))
      \in [set: add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None))]
          :\ inl (target (None : edge rem_parr_ps)) :\ inl (target (Some (inl None) : edge rem_parr_ps))) -> False.
Proof. rewrite !in_set. caseb. Qed.

Lemma rem_parr_v_bij_fwd_helper1 :
 (inl (inr tt)
      \in [set: add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None))]
          :\ inl (target (None : edge rem_parr_ps)) :\ inl (target (Some (inl None) : edge rem_parr_ps))) -> False.
Proof. rewrite /= !in_set. caseb. Qed.

(* Choose fwd for this direction, so that ihom is simpler *)
Definition rem_parr_v_bij_fwd2 (u : add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None))) : G :=
  match u with
  | exist (inl (inl (inl (exist u _)))) _ => u
  | exist (inl (inl (inr tt)))          U => match (rem_parr_v_bij_fwd_helper0 U) with end
  | exist (inl (inr tt))                U => match (rem_parr_v_bij_fwd_helper1 U) with end
  | exist (inr (inl tt))                _ => v
  | exist (inr (inr tt))                _ => cv
  end.
Definition rem_parr_v_bij_fwd (u : add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None))) : G :=
  match u with
  | exist (inl (inl (inl a))) _ => val a
  | exist (inr (inr tt))      _ => cv
  | _                           => v (* case inr (inl tt), other cases are absurd *)
  end.
(* We do not use match val u with ... as then Coq takes longer to compute. *)
(*
Time Print rem_parr_v_bij_fwd. (* Finished transaction in 0.013 secs (0.013u,0.s) (successful) *)
Time Print rem_parr_v_bij_fwd2. (* Finished transaction in 1.58 secs (1.576u,0.s) (successful) *)
*)

Lemma rem_parr_v_bij_bwd_helper0 :
  inr (inr tt) \in [set: add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None))]
  :\ inl (target (None : edge rem_parr_ps)) :\ inl (target (Some (inl None) : edge rem_parr_ps)).
Proof. rewrite /= !in_set. splitb. Qed.

Lemma rem_parr_v_bij_bwd_helper1 :
  inr (inl tt) \in [set: add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None))]
  :\ inl (target (None : edge rem_parr_ps)) :\ inl (target (Some (inl None) : edge rem_parr_ps)).
Proof. rewrite /= !in_set. splitb. Qed.

Lemma rem_parr_v_bij_bwd_helper2 u : u \notin setT :\ v :\ cv -> (u == cv) + (u == v).
Proof.
  rewrite !in_set andb_true_r => /nandP/orP-U.
  elim: (orb_sum U) => /negPn/eqP-->; caseb.
Qed.

Definition rem_parr_v_bij_bwd (u : G) : add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None)) :=
  match @boolP (u \in [set: G] :\ v :\ cv) with
  | @AltTrue _ _ U =>
      (Sub (inl (inl (inl (Sub u U))) : add_node_graph_1 parr_t (None : edge (rem_node_graph (or_intror V)))
        (Some (inl None))) (rem_parr_v_bij_helper (Sub u U)))
  | @AltFalse _ _ U => match rem_parr_v_bij_bwd_helper2 U with
    | inl _ => Sub (inr (inr tt)) rem_parr_v_bij_bwd_helper0
    | inr _ => Sub (inr (inl tt)) rem_parr_v_bij_bwd_helper1
  end end.

Lemma rem_parr_v_bijK : cancel rem_parr_v_bij_fwd rem_parr_v_bij_bwd.
Proof.
  unfold rem_parr_v_bij_fwd.
  move => [[[[[u Uin] | []] | []] | [[] | []]] U] /=.
  - unfold rem_parr_v_bij_bwd. case: {-}_ /boolP => U'; cbnb.
    exfalso; clear U; contradict Uin; apply /negP.
    rewrite !in_set.
    elim: (rem_parr_v_bij_bwd_helper2 U') => /eqP-? /=; subst u; caseb.
  - contradict U. rewrite !in_set. caseb.
  - contradict U. rewrite /= !in_set. caseb.
  - unfold rem_parr_v_bij_bwd. case: {-}_ /boolP => U'.
    + contradict U'; apply /negP. rewrite !in_set. caseb.
    + elim: (rem_parr_v_bij_bwd_helper2 U') => /eqP-U'' /=; cbnb.
      contradict U''. by apply v_neq_cv.
  - unfold rem_parr_v_bij_bwd. case: {-}_ /boolP => U'.
    + contradict U'; apply /negP. rewrite !in_set. caseb.
    + elim: (rem_parr_v_bij_bwd_helper2 U') => /eqP-U'' /=; cbnb.
      contradict U''. by apply nesym, v_neq_cv.
Qed.

Lemma rem_parr_v_bijK' : cancel rem_parr_v_bij_bwd rem_parr_v_bij_fwd.
Proof.
  intro u. unfold rem_parr_v_bij_bwd, rem_parr_v_bij_fwd.
  case: {-}_ /boolP => U //. by elim: (rem_parr_v_bij_bwd_helper2 U) => /eqP-? /=.
Qed.

Definition rem_parr_iso_v := {|
  bijK:= rem_parr_v_bijK;
  bijK':= rem_parr_v_bijK';
  |}.

Lemma rem_parr_e_bij_helper (e : edge (induced ([set: G] :\ v :\ cv))) :
  Some (Some (inl (Some (inl (Some (inl e))))))
  \in edge_set ([set: add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None))]
  :\ inl (target (None : edge rem_parr_ps)) :\ inl (target (Some (inl None) : edge rem_parr_ps))).
Proof. rewrite /= !in_set. splitb. Qed.

Lemma rem_parr_e_bij_helper2 (e : edge G) :
  e \notin edge_set ([set: G] :\ v :\ cv) -> (e == elv) + (e == erv) + (e == ecv).
Proof.
  rewrite rem_node_removed // !in_set !negb_andb !negb_involutive => E.
  repeat (elim: (orb_sum E) => {E}-E); caseb.
Qed.

Lemma rem_parr_e_bij_helper3 :
  let S := [set: add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None))]
  :\ inl (target (None : edge rem_parr_ps)) :\ inl (target (Some (inl None) : edge rem_parr_ps)) in
  None \in edge_set S /\ Some None \in edge_set S.
Proof. eapply add_node_new_edges_at_in. by rewrite /= /rem_node_order. Qed.

Lemma rem_parr_e_bij_helper4 :
  let S := [set: add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None))]
  :\ inl (target (None : edge rem_parr_ps)) :\ inl (target (Some (inl None) : edge rem_parr_ps)) in
  Some (Some (inr None)) \in edge_set S.
Proof. rewrite /= !in_set. splitb. Qed.

Definition rem_parr_e_bij_bwd (e : edge G) : edge (add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None))) :=
  match @boolP (e \in edge_set ([set: G] :\ v :\ cv)) with
  | @AltTrue _ _ E =>
      (Sub (Some (Some (inl (Some (inl (Some (inl (Sub e E : edge (induced ([set: G] :\ v :\ cv))))))))) :
    edge (add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None) : edge rem_parr_ps)))
    (rem_parr_e_bij_helper (Sub e E : edge (induced ([set: G] :\ v :\ cv)))))
  | @AltFalse _ _ E => match rem_parr_e_bij_helper2 E with
    | inl (inl _) => Sub (Some None : edge (add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None)))) (proj2 rem_parr_e_bij_helper3)
    | inl (inr _) => Sub (None : edge (add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None)))) (proj1 rem_parr_e_bij_helper3)
    | inr _ => Sub (Some (Some (inr None)) : edge (add_node_graph_1 parr_t (None : edge rem_parr_ps) (Some (inl None)))) rem_parr_e_bij_helper4
  end end.

Definition rem_parr_e_bij_fwd (e : edge (add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None)))) : edge G :=
  match e with
  | exist (Some (Some (inl (Some (inl (Some (inl a))))))) _ => val a
  | exist (Some None)                                     _ => elv
  | exist None                                            _ => erv
  | exist _                                               _ => ecv (* case Some (Some (inr None)) *)
  end.

Lemma rem_parr_e_bijK : cancel rem_parr_e_bij_fwd rem_parr_e_bij_bwd.
Proof.
  assert (Vcv : vlabel cv = c) by by apply vlabel_cv.
  unfold rem_parr_e_bij_fwd.
  intros [[[[[[[[[e Ein] | []] | ] | []] | ] | [[[] | []] | ]] | ] | ] E]; simpl.
  - unfold rem_parr_e_bij_bwd. case: {-}_ /boolP => E'; first by cbnb.
    exfalso. clear - E' Ein. by rewrite Ein in E'.
  - contradict E. by rewrite /= !in_set.
  - contradict E. by rewrite /= !in_set.
  - unfold rem_parr_e_bij_bwd. case: {-}_ /boolP => E'.
    + contradict E'; apply /negP. rewrite /= !in_set. caseb.
    + destruct (rem_parr_e_bij_helper2 E') as [[E'' | E''] | E''];
      revert E'' => /= /eqP-E'''; cbnb.
      * contradict Vcv. by rewrite E''' left_e V.
      * contradict Vcv. by rewrite E''' right_e V.
  - unfold rem_parr_e_bij_bwd. case: {-}_ /boolP => E'.
    + contradict E'; apply /negP. rewrite rem_node_removed // !in_set. caseb.
    + destruct (rem_parr_e_bij_helper2 E') as [[E'' | E''] | E''];
      revert E'' => /= /eqP-E'''; cbnb.
      * assert (L : llabel elv) by by apply left_l.
        contradict L; apply /negP.
        rewrite E'''. apply right_l.
      * contradict Vcv. by rewrite -E''' left_e V.
  - unfold rem_parr_e_bij_bwd. case: {-}_ /boolP => E'.
    + contradict E'; apply /negP. rewrite /= !in_set right_e. caseb.
    + destruct (rem_parr_e_bij_helper2 E') as [[E'' | E''] | E''];
      revert E'' => /= /eqP-E'''; cbnb.
      * assert (L : llabel elv) by by apply left_l.
        contradict L; apply /negP.
        rewrite -E'''. apply right_l.
      * contradict Vcv. by rewrite -E''' right_e V.
Qed. (* Too long: Finished transaction in 990.18 secs (988.335u,0.431s) (successful) *)

Lemma rem_parr_e_bijK' : cancel rem_parr_e_bij_bwd rem_parr_e_bij_fwd.
Proof.
  intro e.
  unfold rem_parr_e_bij_bwd. case: {-}_ /boolP => E //.
  unfold rem_parr_e_bij_fwd. by elim: (rem_parr_e_bij_helper2 E) => [[]/= /eqP--> | /= /eqP-->].
Qed.

Definition rem_parr_iso_e :={|
  bijK:= rem_parr_e_bijK;
  bijK':= rem_parr_e_bijK';
  |}.

Lemma rem_parr_iso_ihom : is_ihom rem_parr_iso_v rem_parr_iso_e pred0.
Proof.
  split.
  - intros [[[[[[[[[e Ein] | []] | ] | []] | ] | [[[] | []] | ]] | ] | ] E] b; simpl; try by by []. (* intros is quicker than move => *)
    + contradict E. by rewrite !in_set.
    + contradict E. by rewrite !in_set.
    + destruct b; [trivial | by rewrite ccl_e].
    + destruct b; [by rewrite left_e | trivial].
    + destruct b; [by rewrite right_e | trivial].
  - intros [[[[[u Uin] | []] | []] | [[] | []]] U]; simpl; try by by [].
    + destruct (rem_parr_v_bij_fwd_helper0 U).
    + destruct (rem_parr_v_bij_fwd_helper1 U).
    + by apply vlabel_cv.
  - intros [[[[[[[[[e Ein] | []] | ] | []] | ] | [[[] | []] | ]] | ] | ] E]; trivial; cbn.
    + contradict E. by rewrite !in_set.
    + contradict E. by rewrite !in_set.
    + have := p_parr_bis V.
      have : llabel ecv by (apply p_noleft; rewrite vlabel_cv; auto).
      rewrite /flabel /llabel -/elv -/erv.
      by destruct (elabel ecv) => /= -> ->.
    + have := left_l (or_intror V).
      rewrite /flabel /llabel -/elv.
      by destruct (elabel elv) => /= ->.
    + have := right_l (or_intror V).
      rewrite /flabel /llabel -/erv.
      by destruct (elabel erv) as [? []].
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

End Sequentializing_parr. (* TODO simplify all this, timeouts *)

End Atoms.