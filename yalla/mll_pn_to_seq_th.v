(* Sequentialisation - Prove the theorem *)
(* From a Proof Net, return a LL proof of the same sequent *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export mll_prelim graph_more mgraph_tree mll_def mll_basic mll_seq_to_pn
  mll_pn_to_seq_def mll_pn_to_seq_ax mll_pn_to_seq_parr mll_pn_to_seq_tens.

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


Lemma has_sequentializing (G : proof_net) :
  {v : G & sequentializing v}.
Proof.
(* utiliser has_terminal, se ramener au cas où il n'y a que des cut / tens term
puis tenseur scindant *)
Admitted.

(* TODO admettre lemme tenseur scindant puis sequantialisation directement *)
(* ax : pas iso a G mais ps p iso à ax exp G *)
(* TODO ne séquentializer que des réseaux atomiques ! ou mettre preuve ac ax on A *)
(** ** Sequentialization Theorem *)
Definition sequentialize (G : proof_net) : { p : ll (sequent G) & ps p ≃d G }.
Proof.
  revert G.
  enough (Hm : forall n (G : proof_net), #|edge G| = n -> { p : ll (sequent G) & ps p ≃d G })
    by by intro G; apply (Hm #|edge G|).
  intro n; induction n as [n IH] using lt_wf_rect; intros G ?; subst n.
  destruct (has_sequentializing G) as [v V].
  unfold sequentializing in V. destruct (vlabel v); try by [].
  - destruct V as [A h].
    set pi := ax_exp A : ⊢ sequent (ax_graph_data A).
    exists (ex_r pi (sequent_iso_perm h)). simpl. unfold pi.
    unfold ax_exp.
    assert({x | A = var x}) as [? ?]. { admit. } (* easy case where A is an atomic axiom *)
    subst A. simpl.
    symmetry. exact (iso_to_isod h).
  - destruct V as [[G0 G1] h].
    assert (C : correct (add_node_ps_tens G0 G1)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_tens_correct_contra C) as [[[[e0 l0] e1] l1] [Hl0 Hl1]].
    assert ((#|edge G0| < #|edge G|)%coq_nat /\ (#|edge G1| < #|edge G|)%coq_nat) as [C0 C1].
    { rewrite (card_bij h.e) add_node_ps_tens_ecard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    assert (IH1 := IH _ C1 G1 erefl).
    revert IH0 IH1. rewrite {IH C C0 C1} /sequent Hl0 Hl1 /= => IH0 IH1.
    destruct IH0 as [IH0 h0]. destruct IH1 as [IH1 h1].
    assert (H : flabel e0 ⊗ flabel e1 :: [seq flabel e | e <- l1] ++ [seq flabel e | e <- l0]
      = sequent (add_node_ps_tens G0 G1))
      by by rewrite add_node_sequent union_sequent /sequent /= /union_order Hl0 Hl1.
    exists (ex_r (rew H in tens_r IH0 IH1) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_tens_isod.
  - destruct V as [G0 h].
    assert (C : correct (add_node_ps_parr G0)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_parr_correct_contra C) as [[[e0 e1] l] Hl].
    assert (C0 : (#|edge G0| < #|edge G|)%coq_nat).
    { rewrite (card_bij h.e) add_node_ps_parr_ecard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    revert IH0. rewrite {IH C C0} /sequent Hl /= => IH0.
    destruct IH0 as [IH0 h0].
    assert (H : flabel e0 ⅋ flabel e1 :: [seq flabel e | e <- l]
      = sequent (add_node_ps_parr G0))
      by by rewrite add_node_sequent /sequent /= Hl.
    exists (ex_r (rew H in parr_r IH0) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_parr_isod.
  - destruct V as [[G0 G1] h].
    assert (C : correct (add_node_ps_cut G0 G1)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_cut_correct_contra C) as [[[[e0 l0] e1] l1] [Hl0 [Hl1 Hf]]].
    assert (Hf2 : flabel e1 = flabel e0^) by by apply /eqP.
    assert ((#|edge G0| < #|edge G|)%coq_nat /\ (#|edge G1| < #|edge G|)%coq_nat) as [C0 C1].
    { rewrite (card_bij h.e) add_node_ps_cut_ecard //.
      assert (E0 := card_edge_proof_net G0).
      assert (E1 := card_edge_proof_net G1).
      lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    assert (IH1 := IH _ C1 G1 erefl).
    revert IH0 IH1. rewrite {IH C C0 C1} /sequent Hl0 Hl1 /= Hf2 => IH0 IH1.
    destruct IH0 as [IH0 h0]. destruct IH1 as [IH1 h1].
    assert (H : [seq flabel e | e <- l1] ++ [seq flabel e | e <- l0]
      = sequent (add_node_ps_cut G0 G1))
      by by rewrite add_node_sequent union_sequent /sequent /= /union_order Hl0 Hl1 Hf.
    exists (ex_r (rew H in cut_r IH0 IH1) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_cut_isod.
(*
Restart.
  revert G.
  enough (Hm : forall n (G : proof_net), r#|G| = n -> { p : ll (sequent G) & ps p ≃d G })
    by by intro G; apply (Hm r#|G|).
  intro n; induction n as [n IH] using lt_wf_rect; intros G ?; subst n.
  destruct (has_sequentializing G) as [v V].
  unfold sequentializing in V. destruct (vlabel v); try by [].
  - destruct V as [A h].
    set pi := ax_exp A : ⊢ sequent (ax_graph_data A).
    exists (ex_r pi (sequent_iso_perm h)). simpl. unfold pi.
    unfold ax_exp.
    assert({x | A = var x}) as [? ?]. admit. (* easy case where A is an atomic axiom *)
    subst A. simpl.
    symmetry. exact (iso_to_isod h).
  - destruct V as [[G0 G1] h].
    assert (C : correct (add_node_ps_tens G0 G1)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_tens_correct_contra C) as [[[[e0 l0] e1] l1] [Hl0 Hl1]].
    assert ((r#|G0| < r#|G|)%coq_nat /\ (r#|G1| < r#|G|)%coq_nat) as [C0 C1].
    { rewrite (rcard_iso h) add_node_ps_tens_rcard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    assert (IH1 := IH _ C1 G1 erefl).
    revert IH0 IH1. rewrite {IH C C0 C1} /sequent Hl0 Hl1 /= => IH0 IH1.
    destruct IH0 as [IH0 h0]. destruct IH1 as [IH1 h1].
    assert (H : flabel e0 ⊗ flabel e1 :: [seq flabel e | e <- l1] ++ [seq flabel e | e <- l0]
      = sequent (add_node_ps_tens G0 G1))
      by by rewrite add_node_sequent union_sequent /sequent /= /union_order Hl0 Hl1.
    exists (ex_r (rew H in tens_r IH0 IH1) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_tens_isod.
  - destruct V as [G0 h].
    assert (C : correct (add_node_ps_parr G0)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_parr_correct_contra C) as [[[e0 e1] l] Hl].
    assert (C0 : (r#|G0| < r#|G|)%coq_nat).
    { rewrite (rcard_iso h) add_node_ps_parr_rcard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    revert IH0. rewrite {IH C C0} /sequent Hl /= => IH0.
    destruct IH0 as [IH0 h0].
    assert (H : flabel e0 ⅋ flabel e1 :: [seq flabel e | e <- l]
      = sequent (add_node_ps_parr G0))
      by by rewrite add_node_sequent /sequent /= Hl.
    exists (ex_r (rew H in parr_r IH0) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_parr_isod.
  - destruct V as [[G0 G1] h].
    assert (C : correct (add_node_ps_cut G0 G1)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_cut_correct_contra C) as [[[[e0 l0] e1] l1] [Hl0 [Hl1 Hf]]].
    assert (Hf2 : flabel e1 = flabel e0^) by by apply /eqP.
    assert ((r#|G0| < r#|G|)%coq_nat /\ (r#|G1| < r#|G|)%coq_nat) as [C0 C1].
    { rewrite (rcard_iso h) add_node_ps_cut_rcard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    assert (IH1 := IH _ C1 G1 erefl).
    revert IH0 IH1. rewrite {IH C C0 C1} /sequent Hl0 Hl1 /= Hf2 => IH0 IH1.
    destruct IH0 as [IH0 h0]. destruct IH1 as [IH1 h1].
    assert (H : [seq flabel e | e <- l1] ++ [seq flabel e | e <- l0]
      = sequent (add_node_ps_cut G0 G1))
      by by rewrite add_node_sequent union_sequent /sequent /= /union_order Hl0 Hl1 Hf.
    exists (ex_r (rew H in cut_r IH0 IH1) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_cut_isod.
*)
Admitted.
(* TODO voir derniere quest exam et focalisation + seqpn *)

(* TOTHINK utiliser seulement connexité left possible (ie pas besoin de demontrer que
un graphe de correc correct ac notre def) ? to check, parr bloquant *)



Fixpoint nb_cut {l : list formula} (pi : ⊢ l) := match pi with
  | ax_r x                 => 0
  | ex_r _ _ pi0 _         => nb_cut pi0
  | tens_r _ _ _ _ pi0 pi1 => nb_cut pi0 + nb_cut pi1
  | parr_r _ _ _ pi0       => nb_cut pi0
  | cut_r _ _ _ pi0 pi1    => nb_cut pi0 + nb_cut pi1 + 1
  end.
(*
Lemma ps_nb_cut {l : list formula} (pi : ⊢ l) : #|[set v : ps pi | vlabel v == cut]| = nb_cut pi.
Proof.
  induction pi as [x | | A B l0 l1 pi0 H0 pi1 H1 | A B l0 pi0 H0 | A l0 l1 pi0 H0 pi1 H1].
  - enough (H : [set v : ax_ps x | vlabel v == cut] = set0) by by rewrite H cards0.
    apply /setP; intro v; destruct_I v;
    by rewrite !in_set.
  - by [].
  - rewrite /= -H0 -H1.
Abort. *)
(* TODO Lemma : nb cut ps (pi) = nb cut pi, idem other rules, et dans le sens sequentialisation aussi -> déductible de p = ps pi ! *)
End Atoms.