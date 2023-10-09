(* Sequentialisation - Prove the theorem *)
(* From a Proof Net, return a LL proof desequentializing to an isomorphic graph, with the corresponding order *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export mll_prelim graph_more mll_def mll_basic mll_seq_to_pn
  mll_pn_to_seq_def mll_pn_to_seq_ax mll_pn_to_seq_parr mll_pn_to_seq_tens mll_pn_to_seq_cut mll_pn_to_seq.

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

Lemma splitting_terminal_is_sequentializing (G : proof_net) (v : G) :
  splitting bridge v -> terminal v -> sequentializing v.
Proof.
  move=> splitting_v terminal_v.
  destruct (vlabel v) eqn:vlabel_v.
  - by apply terminal_ax_is_sequentializing.
  - by apply splitting_terminal_tens_is_sequentializing.
  - by apply terminal_parr_is_sequentializing.
  - by apply splitting_cut_is_sequentializing.
  - contradict terminal_v. by rewrite /terminal vlabel_v.
Qed.

Lemma has_sequentializing (G : proof_net) :
  {v : G & sequentializing v}.
Proof.
  have [v /andP[splitting_v terminal_v]] := (@exists_terminal_splitting _ G).
  exists v. by apply splitting_terminal_is_sequentializing.
Qed.


(* If two proof structures are isomorphic, then the order of one is the order of the other up
   to a permutation. *)
Definition iso_to_isod (F G : proof_structure) (h : F ≃ G) :
  F ≃d perm_graph_data (sequent_iso_perm h) G.
Proof. eexists; simpl. apply perm_of_sequent_iso_perm. Defined.

(** ** Sequentialization Theorem *)
Theorem sequentialize (G : proof_net) : { p : ll (sequent G) & ps p ≃d G }.
Proof.
  move: G.
  enough (Hm : forall n (G : proof_net), #|edge G| = n -> { p : ll (sequent G) & ps p ≃d G })
    by by move=> G; apply (Hm #|edge G|).
  move=> n. induction n as [n IH] using lt_wf_rect => G ?; subst n.
  destruct (@has_sequentializing G) as [v V].
  rewrite /sequentializing in V. destruct (vlabel v); try by [].
  - destruct V as [A h].
    exists (ex_r (ax_r A) (sequent_iso_perm h)).
    symmetry. exact (iso_to_isod h).
  - destruct V as [[G0 G1] h].
    assert (C : mll_def.correct (add_node_ps_tens G0 G1))
      by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_tens_correct_contra C) as [[e0 e1] [Hl0 Hl1]].
    assert ((#|edge G0| < #|edge G|)%coq_nat /\ (#|edge G1| < #|edge G|)%coq_nat) as [C0 C1].
    { rewrite (card_bij h.e) add_node_ps_tens_ecard //. lia. }
    have := IH _ C1 G1 erefl.
    have := IH _ C0 G0 erefl.
    rewrite {IH C C0 C1} /sequent Hl0 Hl1 /= => IH0 [IH1 h1]. destruct IH0 as [IH0 h0].
    assert (H : flabel e0 ⊗ flabel e1 :: [seq flabel e | e <- behead (order G1)] ++ [seq flabel e | e <- behead (order G0)]
      = sequent (add_node_ps_tens G0 G1))
      by by rewrite add_node_sequent union_sequent /sequent /= /union_order Hl0 Hl1.
    exists (ex_r (rew H in tens_r IH0 IH1) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_tens_isod.
  - destruct V as [G0 h].
    assert (C : mll_def.correct (add_node_ps_parr G0))
      by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_parr_correct_contra C) as [[e0 e1] Hl].
    assert (C0 : (#|edge G0| < #|edge G|)%coq_nat).
    { rewrite (card_bij h.e) add_node_ps_parr_ecard //. lia. }
    have := IH _ C0 G0 erefl.
    rewrite {IH C C0} /sequent Hl /= => IH0. destruct IH0 as [IH0 h0].
    assert (H : flabel e0 ⅋ flabel e1 :: [seq flabel e | e <- behead (behead (order G0))]
      = sequent (add_node_ps_parr G0))
      by by rewrite add_node_sequent /sequent /= Hl.
    exists (ex_r (rew H in parr_r IH0) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_parr_isod.
  - destruct V as [[G0 G1] h].
    assert (C : mll_def.correct (add_node_ps_cut G0 G1))
      by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_cut_correct_contra C) as [[e0 e1] [Hl0 [Hl1 Hf]]].
    assert (Hf2 : flabel e1 = flabel e0^) by by apply /eqP.
    assert ((#|edge G0| < #|edge G|)%coq_nat /\ (#|edge G1| < #|edge G|)%coq_nat) as [C0 C1].
    { rewrite (card_bij h.e) add_node_ps_cut_ecard //.
      have := card_edge_proof_net G0.
      have := card_edge_proof_net G1.
      lia. }
    have := IH _ C1 G1 erefl.
    have := IH _ C0 G0 erefl.
    rewrite {IH C C0 C1} /sequent Hl0 Hl1 /= Hf2 => IH0 [IH1 h1]. destruct IH0 as [IH0 h0].
    assert (H : [seq flabel e | e <- behead (order G1)] ++ [seq flabel e | e <- behead (order G0)]
      = sequent (add_node_ps_cut G0 G1))
      by by rewrite add_node_sequent union_sequent /sequent /= /union_order Hl0 Hl1 Hf.
    exists (ex_r (rew H in cut_r IH0 IH1) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_cut_isod.
Qed.


(* TODO Possible things to prove: same number of cuts... *)
Fixpoint nb_cut {l : list formula} (pi : ⊢ l) := match pi with
  | ax_r x                 => 0
  | ex_r _ _ pi0 _         => nb_cut pi0
  | tens_r _ _ _ _ pi0 pi1 => nb_cut pi0 + nb_cut pi1
  | parr_r _ _ _ pi0       => nb_cut pi0
  | cut_r _ _ _ pi0 pi1    => nb_cut pi0 + nb_cut pi1 + 1
  end.

Lemma ps_nb_cut {l : list formula} (pi : ⊢ l) : #|[set v : ps pi | vlabel v == cut]| = nb_cut pi.
Proof.
  induction pi as [x | | A B l0 l1 pi0 H0 pi1 H1 | A B l0 pi0 H0 | A l0 l1 pi0 H0 pi1 H1].
  - enough (H : [set v : ax_ps x | vlabel v == cut] = set0) by by rewrite H cards0.
    apply/setP => v; destruct_I v;
    by rewrite !in_set.
  - by [].
  - rewrite /= -H0 -H1.
Abort.
(* TODO Lemma : nb cut ps (pi) = nb cut pi, idem other rules, et dans le sens sequentialisation aussi -> déductible de p = ps pi ! *)

End Atoms.
