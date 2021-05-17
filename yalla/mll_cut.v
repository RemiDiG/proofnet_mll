(* Cut Elimination in Proof Nets *)

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


(** * Axiom - cut reduction *)
Definition red_ax_graph_1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : base_graph :=
  G ∔ [source (other_cut Hcut) , dual (elabel e) , target (other_ax Hax)].

Definition red_ax_graph (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : base_graph :=
  induced ([set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)).

Lemma red_ax_degenerate_source (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  source e = source (other_cut Hcut) <-> other_cut Hcut = other_ax Hax.
Proof.
  split; intro H.
  - apply other_ax_eq.
    rewrite H. splitb.
    apply /eqP; apply other_cut_in_neq.
  - rewrite H.
    by destruct (other_ax_in_neq Hax) as [-> _].
Qed.

Lemma red_ax_degenerate_target (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  target e = target (other_ax Hax) <-> other_cut Hcut = other_ax Hax.
Proof.
  split; intro H.
  - symmetry; apply other_cut_eq.
    rewrite H. splitb.
    apply /eqP; apply other_ax_in_neq.
  - rewrite -H.
    by destruct (other_cut_in_neq Hcut) as [-> _].
Qed.

Lemma red_ax_degenerate_None (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  None \notin edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)
  <-> other_cut Hcut = other_ax Hax.
Proof.
  rewrite !in_set; cbn. split.
  - move => /nandP[/nandP[/negPn /eqP H | /nandP[/negPn /eqP H | //]]
                 | /nandP[/negPn /eqP H | /nandP[/negPn /eqP H | //]]].
    + assert (Hf := p_deg_out (target e)).
      rewrite Hcut in Hf; cbn in Hf.
      assert (Hdone : other_cut Hcut \in set0) by by rewrite -(cards0_eq Hf) in_set H.
      contradict Hdone; by rewrite in_set.
    + by apply red_ax_degenerate_source.
    + by apply red_ax_degenerate_target.
    + assert (Hf := p_deg_in (source e)).
      rewrite Hax in Hf; cbn in Hf.
      assert (Hdone : other_ax Hax \in set0) by by rewrite -(cards0_eq Hf) in_set H.
      contradict Hdone; by rewrite in_set.
    - move => ->.
      destruct (other_ax_in_neq Hax) as [-> _].
      caseb.
Qed.

Definition red_ax_left_1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : red_ax_graph_1 Hcut Hax -> edge (red_ax_graph_1 Hcut Hax) :=
  fun (v : red_ax_graph_1 Hcut Hax) =>
    if (left v == e) || (left v == other_cut Hcut) || (left v == other_ax Hax) then
      if source e == source (other_cut Hcut) then Some (pick_edge_at v)
      else None
    else Some (left v).

Lemma red_ax_consistent_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  let S := [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e) in
  forall (v : red_ax_graph Hcut Hax), red_ax_left_1 (val v) \in edge_set S.
Proof.
  intros S [v Hv].
  rewrite !in_set /red_ax_left_1; cbn.
  destruct (other_cut_in_neq Hcut) as [Htc Hneqc];
  destruct (other_ax_in_neq Hax) as [Hsa Hneqa].
  assert ((forall a, source a != target e) /\ forall a, target a != source e) as [? ?].
  { split; intro a; apply /eqP => Hc.
    1: assert (Hf := p_deg_out (target e)).
    2: assert (Hf := p_deg_in (source e)).
    all: rewrite ?Hcut ?Hax in Hf; cbn in Hf.
    all: assert (Hf' : a \in set0) by by rewrite -(cards0_eq Hf) in_set Hc.
    all: contradict Hf'; by rewrite in_set. }
  assert (Hm : source e = source (other_cut Hcut) -> forall b b',
    endpoint b (pick_edge_at v) != endpoint b' (other_cut Hcut)).
  { intros Hs b b'; apply /eqP => Hc.
    assert (Hc' : pick_edge_at v \in edges_at_outin b (endpoint b' e)) by
      (destruct b'; by rewrite in_set Hc ?Htc ?Hs).
    destruct (red_ax_degenerate_source Hcut Hax) as [Ho _].
    specialize (Ho Hs).
    contradict Hv; apply /negP.
    assert (Hvin := pick_edge_at_some v).
    revert Hvin; rewrite !in_set; move => /orP[/eqP Heq | /eqP Heq];
    destruct b, b';
    apply /nandP; rewrite andb_true_r !negb_involutive.
    all: try (contradict Hc'; apply /negP; by rewrite in_set).
    all: revert Hc'; rewrite ?other_cut_set ?other_ax_set !in_set; move => /orP[/eqP Hd | /eqP Hd];
      rewrite -Heq Hd ?Hs -?Htc ?Ho; caseb. }
  assert (Hm2 : source e <> source (other_cut Hcut) -> target (other_ax Hax) != target e).
  { intro Hs; apply /eqP => Hc.
    enough (Hdone : other_cut Hcut = other_ax Hax) by by rewrite Hdone Hsa in Hs.
    assert (Hm2 : other_ax Hax \in edges_at_in (target e)) by by rewrite in_set Hc.
    revert Hm2; rewrite other_cut_set !in_set; move => /orP[/eqP Hd | /eqP Hd //].
    contradict Hd; apply /eqP; apply other_ax_in_neq. }
  splitb; case_if.
  all: try (apply /eqP; by apply nesym).
  all: try (rewrite -?Htc; by apply Hm).
  all: try by apply Hm2.
  - apply /eqP => Hc.
    assert (Hf : left v \in edges_at_out (source e)) by by rewrite in_set Hc.
    contradict Hf; apply /negP.
    rewrite other_ax_set !in_set.
    splitb; by apply /eqP.
  - apply /eqP => Hc.
    assert (Hf : left v \in edges_at_in (target e)) by by rewrite in_set Hc.
    contradict Hf; apply /negP.
    rewrite other_cut_set !in_set.
    splitb; by apply /eqP.
Qed. (* TODO essayer de simplifier (ça et les autres preuves de cette partie red) *)

Definition red_ax_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : red_ax_graph Hcut Hax -> edge (red_ax_graph Hcut Hax) :=
  fun v => Sub (red_ax_left_1 (val v)) (red_ax_consistent_left v).

Definition red_ax_graph_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : graph_left := {|
  graph_of := red_ax_graph Hcut Hax;
  left := @red_ax_left _ _ _ _;
  |}.

Lemma red_ax_consistent_order (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  all (pred_of_set ([set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e))) (order G).
Proof.
  apply /allP => v Hv.
  assert (Hl : vlabel v = concl_l) by by apply p_order.
  repeat (apply /setD1P; split); trivial.
  all: apply /eqP => Hc; contradict Hl; by rewrite Hc ?Hcut ?Hax.
Qed.

Definition red_ax_order (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : seq (red_ax_graph Hcut Hax) :=
  sval (all_sigP (red_ax_consistent_order Hcut Hax)).

Definition red_ax_graph_data (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : graph_data := {|
  graph_left_of := red_ax_graph_left Hcut Hax;
  order := red_ax_order _ _;
  |}.

Definition red_ax_transport (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : red_ax_graph_data Hcut Hax) :=
  fun (a : edge (red_ax_graph_data Hcut Hax)) => match val a with
  | None => if b then other_ax Hax else other_cut Hcut
  | Some a' => a'
  end.
Notation red_ax_transport_out := (@red_ax_transport _ _ _ _ false).
Notation red_ax_transport_in := (@red_ax_transport _ _ _ _ true).

Lemma red_ax_transport_inj (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : red_ax_graph_data Hcut Hax) :
  {in edges_at_outin b v &, injective (@red_ax_transport _ _ Hcut Hax b v)}.
Proof.
  destruct (other_cut_in_neq Hcut) as [Hc0 _].
  destruct (other_ax_in_neq Hax) as [Ha0 _].
  destruct v as [v Hv]; intros [a A] [a' A'].
  rewrite !in_set /red_ax_transport; cbn; rewrite !SubK.
  move => /eqP ? /eqP ? ?; subst; apply /eqP; rewrite sub_val_eq SubK.
  destruct a as [a | ], a' as [a' | ]; subst; trivial;
  [contradict A | contradict A']; apply /negP.
  all: destruct b; rewrite !in_set /= ?Ha0 ?Hc0; caseb.
Qed.

Lemma red_ax_transport_edges (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  edges_at_outin b v =
  [set red_ax_transport b (Sub v Hv) a | a in edges_at_outin b (Sub v Hv : red_ax_graph_data Hcut Hax)].
Proof.
  assert ((forall a, source a != target e) /\ forall a, target a != source e) as [? ?].
  { split; intro a; apply /eqP; intro Ha;
    [assert (Hf := p_deg_out (target e)) | assert (Hf := p_deg_in (source e))].
    all: rewrite ?Hcut ?Hax in Hf; cbn in Hf.
    all: assert (Hdone : a \in set0) by by rewrite -(cards0_eq Hf) in_set Ha.
    all: contradict Hdone; by rewrite in_set. }
  assert (v != source e /\ v != target e) as [Hvs Hvt]
    by (revert Hv; rewrite !in_set; by move => /andP[? /andP[? _]]).
  destruct (other_cut_in_neq Hcut) as [Hc0 Hc1].
  destruct (other_ax_in_neq Hax) as [Ha0 Ha1].
  apply /setP => a.
  rewrite Imset.imsetE !in_set.
  symmetry; apply /imageP; case_if.
  - assert (a <> e) by
      by (intro Hc; destruct b; subst; by rewrite_all eq_refl).
    destruct (eq_comparable a (other_cut Hcut)) as [Heqc | Hneqc];
    [ | destruct (eq_comparable a (other_ax Hax)) as [Heqa | Hneqa]]; subst.
    + destruct b.
      { contradict Hvt; apply /negP; rewrite negb_involutive; apply /eqP.
        apply other_cut_in_neq. }
      assert (Hn : None \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)).
      { rewrite !in_set; cbn. splitb.
        apply /eqP => Hf.
        assert (Hin : other_ax Hax \in edges_at_in (target e))
          by by rewrite in_set Hf.
        revert Hin. rewrite other_cut_set !in_set. move => /orP[/eqP Hin | /eqP Hin].
        - contradict Hin; apply /eqP.
          apply other_ax_in_neq.
        - contradict Hvs; apply /negP; rewrite negb_involutive; apply /eqP.
          by rewrite -Hin Ha0. }
      exists (Sub None Hn); trivial.
      by rewrite !in_set; cbn.
    + destruct b.
      2:{ contradict Hvs; apply /negP; rewrite negb_involutive; apply /eqP.
          apply other_ax_in_neq. }
      assert (Hn : None \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)).
      { rewrite !in_set; cbn. splitb.
        apply /eqP => Hf.
        assert (Hin : other_cut Hcut \in edges_at_out (source e))
          by by rewrite in_set Hf.
        revert Hin. rewrite other_ax_set !in_set. move => /orP[/eqP Hin | /eqP Hin].
        - contradict Hin; by apply /eqP.
        - by rewrite Hin in Hneqc. }
      exists (Sub None Hn); trivial.
      by rewrite !in_set; cbn.
    + assert (Ha : Some a \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)).
      { rewrite !in_set; cbn.
        splitb; destruct b; try by [].
        - apply /eqP => Hf.
          assert (Hc : a \in edges_at_out (source e)) by by rewrite in_set Hf.
          revert Hc; rewrite other_ax_set !in_set; by move => /orP[/eqP ? | /eqP ?].
        - apply /eqP => Hf.
          assert (Hc : a \in edges_at_in (target e)) by by rewrite in_set Hf.
          revert Hc; rewrite other_cut_set !in_set; by move => /orP[/eqP ? | /eqP ?]. }
      exists (Sub (Some a) Ha); trivial.
      by rewrite !in_set; cbn.
  - intros [[x Hxin] Hx Hxx].
    rewrite /red_ax_transport SubK in Hxx. subst.
    contradict Hx; apply /negP.
    rewrite in_set; cbn; rewrite !SubK; apply /eqP.
    by destruct x, b.
Qed.
Notation red_ax_transport_edges_at_out := (@red_ax_transport_edges _ _ _ _ false).
Notation red_ax_transport_edges_at_in := (@red_ax_transport_edges _ _ _ _ true).

Lemma red_ax_transport_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  vlabel v = ⊗ \/ vlabel v = ⅋ ->
  red_ax_transport_in (Sub v Hv) (left (Sub v Hv : red_ax_graph_data Hcut Hax)) = left v.
Proof.
  intro Hl. cbn. rewrite /red_ax_transport /red_ax_left /red_ax_left_1 !SubK.
  assert (left v <> e).
  { intros ?; subst e.
    contradict Hv; apply /negP.
    rewrite !in_set left_e; caseb. }
  assert (left v <> other_cut Hcut).
  { intro Hf.
    assert (Hc := left_e Hl); contradict Hc.
    rewrite Hf.
    destruct (other_cut_in_neq Hcut) as [-> _].
    intros ?; subst v.
    clear - Hl Hcut; contradict Hcut.
    by destruct Hl as [-> | ->]. }
  case_if.
  enough (left v = other_cut Hcut) by by [].
  replace (left v) with (other_ax Hax); symmetry.
  by apply (red_ax_degenerate_source Hcut Hax).
Qed.


Lemma red_ax_p_deg (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_degree (red_ax_graph_data Hcut Hax).
Proof.
  unfold proper_degree, red_ax_graph_data.
  intros b [v Hv]; cbn.
  rewrite -(p_deg b v) (red_ax_transport_edges _ Hv) card_in_imset //.
  apply red_ax_transport_inj.
Qed.

Lemma red_ax_p_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_left (red_ax_graph_data Hcut Hax).
Proof.
  unfold proper_left, red_ax_graph_data.
  intros [v Hv] Hl; cbn in *.
  assert (H := p_left Hl).
  revert H; rewrite (red_ax_transport_edges_at_in Hv) Imset.imsetE in_set => /imageP [a Ha Heq].
  enough (Hdone : red_ax_left (Sub v Hv) = a) by by rewrite Hdone.
  symmetry; apply /eqP; rewrite /red_ax_left sub_val_eq /red_ax_left_1 SubK Heq; apply /eqP.
  destruct (other_cut_in_neq Hcut) as [Hc0 Hc1].
  destruct (other_ax_in_neq Hax) as [Ha0 Ha1].
  destruct a as [a Hain].
  rewrite /red_ax_transport SubK.
  destruct a as [a | ].
  - assert (a <> e /\ a <> other_cut Hcut /\ a <> other_ax Hax) as [? [? ?]].
    { splitb;
      intros ?; subst;
      clear - Hain Hc0 Ha0; contradict Hain; apply /negP.
      all: rewrite !in_set; cbn; rewrite ?Hc0 ?Ha0; caseb. }
    case_if.
  - revert Ha; rewrite in_set; cbn; rewrite /red_ax_transport !SubK => /eqP ?; subst v.
    rewrite eq_refl.
    revert Ha1 Hc1 => /eqP Ha1 /eqP Hc1.
    assert (other_ax Hax <> other_cut Hcut).
    { intro Hf.
      clear Heq; contradict Hain; apply /negP.
      rewrite !in_set; cbn; rewrite Hf Hc0; caseb. }
    assert (source e <> source (other_cut Hcut)).
    { intro Hf.
      destruct (red_ax_degenerate_source Hcut Hax) as [Ho _].
      specialize (Ho Hf). by symmetry in Ho. }
    case_if.
Qed.

Lemma red_ax_p_order (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_order (red_ax_graph_data Hcut Hax).
Proof.
  unfold proper_order, red_ax_graph_data, red_ax_order; cbn.
  split.
  - intros [? ?]; cbn.
    rewrite in_seq_sig SubK -(proj2_sig (all_sigP _)).
    apply p_order.
  - rewrite uniq_seq_sig -(proj2_sig (all_sigP _)).
    apply p_order.
Qed.

Definition red_ax_geos (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : geos := {|
  graph_data_of := red_ax_graph_data Hcut Hax;
  p_deg := @red_ax_p_deg _ _ _ _;
  p_left := @red_ax_p_left _ _ _ _;
  p_order := @red_ax_p_order _ _ _ _;
  |}.

Lemma red_ax_transport_right (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  vlabel v = ⊗ \/ vlabel v = ⅋ ->
  red_ax_transport_in (Sub v Hv) (right (Sub v Hv : red_ax_geos Hcut Hax)) = right v.
Proof.
  intro Hl.
  set w := Sub v Hv : red_ax_geos Hcut Hax.
  apply right_eq; trivial.
  assert (Hdone : red_ax_transport_in w (right w) \in edges_at_in (v : G)).
  { rewrite (red_ax_transport_edges_at_in Hv).
    by apply imset_f, (p_right (v := w)). }
  revert Hdone; rewrite in_set => /eqP Hdone. splitb.
  rewrite -(red_ax_transport_left Hv) //.
  intro Hf.
  assert (Hl' : vlabel w = ⊗ \/ vlabel w = ⅋) by (cbn; by rewrite SubK).
  assert (Hle := p_left Hl').
  destruct (p_right Hl') as [Hr Hc].
  contradict Hc; apply /negP; rewrite negb_involutive; apply /eqP.
  by apply (red_ax_transport_inj Hr Hle).
Qed.

Lemma red_ax_transport_ccl (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  vlabel v = ⊗ \/ vlabel v = ⅋ ->
  red_ax_transport_out (Sub v Hv) (ccl (Sub v Hv : red_ax_geos Hcut Hax)) = ccl v.
Proof.
  intro Hl.
  set w := Sub v Hv : red_ax_geos Hcut Hax.
  apply ccl_eq; trivial.
  assert (Hdone : red_ax_transport_out w (ccl w) \in edges_at_out v).
  { rewrite (red_ax_transport_edges_at_out Hv).
    by apply imset_f, (p_ccl (v := w)). }
  by revert Hdone; rewrite in_set => /eqP ?.
Qed.

Lemma red_ax_transport_edge_of_concl (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  vlabel v = c ->
  red_ax_transport_in (Sub v Hv) (edge_of_concl (Sub v Hv : red_ax_geos Hcut Hax)) = edge_of_concl v.
Proof.
  intro Hl.
  set w := Sub v Hv : red_ax_geos Hcut Hax.
  apply concl_eq; trivial.
  assert (Hdone : red_ax_transport_in w (edge_of_concl w) \in edges_at_in v).
  { rewrite (red_ax_transport_edges_at_in Hv).
    by apply imset_f, (p_concl (v := w)). }
  by revert Hdone; rewrite in_set => /eqP Hdone.
Qed.

Lemma red_ax_transport_label (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  forall a, elabel a = elabel (red_ax_transport b (Sub v Hv) a).
Proof.
  unfold red_ax_transport.
  intros [[a | ] Ha]; trivial; cbn.
  assert (dual (elabel e) = elabel (other_ax Hax) /\ dual (elabel e) = elabel (other_cut Hcut)) as [? ?].
  { destruct (proper_ax_cut_bis G) as [Hpax Hpcut].
    specialize (Hpax (source e) Hax);
    specialize (Hpcut (target e) Hcut).
    unfold true_on2 in Hpax;
    unfold true_on2 in Hcut.
    specialize (Hpax e (source_in_edges_at_out e));
    specialize (Hpcut e (target_in_edges_at_in e)).
    unfold is_dual_f, is_dual in Hpax;
    unfold is_dual_f, is_dual in Hpcut.
    by revert Hpax Hpcut => /eqP Hpax /eqP Hpcut. }
  by destruct b.
Qed.


Lemma red_ax_p_ax_cut (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_ax_cut (red_ax_geos Hcut Hax).
Proof.
  unfold proper_ax_cut.
  intros b [v Hv] Hl; cbn in Hl.
  destruct (p_ax_cut Hl) as [el [er H]].
  revert H; rewrite (red_ax_transport_edges b Hv) => /andP[/andP[Hel Her] /eqP ?].
  revert Hel; rewrite Imset.imsetE in_set => /imageP [El ? ?]; subst el;
  revert Her; rewrite Imset.imsetE in_set => /imageP [Er ? ?]; subst er.
  exists El, Er.
  splitb; apply /eqP.
  by rewrite !(red_ax_transport_label b Hv).
Qed.

Lemma red_ax_p_tens_parr (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_tens_parr (red_ax_geos Hcut Hax).
Proof.
  unfold proper_tens_parr.
  intros b [v Hv] Hl; cbn in Hl.
  rewrite (red_ax_transport_label false Hv) 2!(red_ax_transport_label true Hv)
    red_ax_transport_left ?red_ax_transport_right ?red_ax_transport_ccl;
  try (destruct b; by caseb).
  by apply p_tens_parr.
Qed.

Definition red_ax_ps (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proof_structure := {|
  geos_of := red_ax_geos Hcut Hax;
  p_ax_cut := @red_ax_p_ax_cut _ _ _ _;
  p_tens_parr := @red_ax_p_tens_parr _ _ _ _;
  |}.


(** Sequent of an axiom - cut reduction *)
Lemma red_ax_sequent (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  sequent (red_ax_ps Hcut Hax) = sequent G.
Proof.
  assert (sequent (red_ax_ps Hcut Hax) = [seq elabel (red_ax_transport_in v (edge_of_concl v)) |
    v <- red_ax_order Hcut Hax]) as ->.
  { apply eq_map; intros [? ?]. apply red_ax_transport_label. }
  transitivity ([seq elabel ((edge_of_concl v)) | v <- [seq val v | v <- red_ax_order Hcut Hax]]).
  { rewrite -map_comp.
    apply (@eq_in_map _); intros [a Ha] Ho.
    rewrite !red_ax_transport_edge_of_concl ?SubK //.
    by assert (vlabel (Sub a Ha : red_ax_graph Hcut Hax) = c)
      by by apply (p_order (red_ax_geos Hcut Hax)). }
  by rewrite -(proj2_sig (all_sigP _)).
Qed.

(** Decreasing number of vertices *)
(* TOTHINK nb without cut vertices ? *)
Lemma red_ax_nb (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  #|red_ax_graph Hcut Hax| = #|G| - 2.
Proof.
  rewrite -(card_imset (f := val)); [ | apply val_inj].
  assert (#|setT :\ (source e) :\ (target e)| = #|G| - 2) as <-.
  { rewrite -cardsT [in RHS](cardsD1 (source e)) [in RHS](cardsD1 (target e)) !in_set.
    assert (target e != source e).
    { apply /negP => /eqP Hf. contradict Hcut. by rewrite Hf Hax. }
    lia. }
  apply eq_card; intro v.
  rewrite Imset.imsetE in_set.
  destruct (v \in [set: G] :\ source e :\ target e) eqn:Hv.
  - apply /imageP.
    by exists (Sub v Hv).
  - apply /imageP; intros [[u U] _ ?]; subst v.
    by rewrite U in Hv.
Qed.


(** * Tensor - cut reduction *)
Definition red_tens_graph_1 (G : graph_data) (et ep : edge G) :
  base_graph :=
  let ltens := left (source et) in
  let rtens := right (source et) in
  let lparr := left (source ep) in
  let rparr := right (source ep) in
  G ∔ cut ∔ cut
    ∔ [inl (inl (source ltens)) , elabel (ltens) , inl (inr tt)]
    ∔ [inl (inl (source rtens)) , elabel (rtens) , inr tt]
    ∔ [inl (inl (source lparr)) , elabel (lparr) , inr tt]
    ∔ [inl (inl (source rparr)) , elabel (rparr) , inl (inr tt)].

Definition red_tens_graph (G : graph_data) (v : G) (et ep : edge G) : base_graph :=
  induced ([set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\ (inl (inl (source ep)))
  :\ (inl (inl v))).

Lemma red_tens_cut_set (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  edges_at_in v = [set et; ep].
Proof.
  subst v.
  rewrite other_cut_set.
  replace ep with (other_cut Hcut); trivial.
  symmetry; apply other_cut_eq. splitb.
  intros ?; subst; contradict Hparr.
  by rewrite Htens.
Qed.

Lemma red_tens_ineq_in (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  (forall a, source a != v) /\
  source (left (source et)) != source et /\
  source (right (source et)) != source et /\
  source (left (source ep)) != source ep /\
  source (right (source ep)) != source ep /\
  source (left (source et)) != source ep /\
  source (right (source et)) != source ep /\
  source (left (source ep)) != source et /\
  source (right (source ep)) != source et.
Proof.
  assert (forall a, source a != v).
  { intro a; apply /eqP => Ha.
    assert (Hf := p_deg_out v).
    rewrite Hcut in Hf; cbn in Hf.
    assert (Hdone : a \in set0) by by rewrite -(cards0_eq Hf) in_set Ha.
    contradict Hdone; by rewrite in_set. }
  assert (source (left (source et)) != source ep /\ source (right (source et)) != source ep /\
    source (left (source ep)) != source et /\ source (right (source ep)) != source et /\
    source (left (source et)) != source et /\ source (right (source et)) != source et /\
    source (left (source ep)) != source ep /\ source (right (source ep)) != source ep)
    as [? [? [? [? [? [? [? ?]]]]]]].
  { splitb; apply /eqP => Hc;
    [set a := et | set a := et | set a := ep | set a := ep | set a := et | set a := et | set a := ep | set a := ep];
    [set b := ep | set b := ep | set b := et | set b := et | set b := et | set b := et | set b := ep | set b := ep];
    [set f := left (g := G) | set f :=  right (G := G) | set f := left (g := G) | set f := right (G := G)
    | set f := left (g := G) | set f :=  right (G := G) | set f := left (g := G) | set f := right (G := G)].
    all: assert (f (source a) = ccl (source b) /\ b = ccl (source b)) as [Hc0 Hc1] by (split; apply ccl_eq; caseb).
    all: assert (Hc2 : source a = v) by
      (replace v with (target b); rewrite Hc1 -Hc0 ?left_e ?right_e; caseb).
    all: contradict Hcut; by rewrite -Hc2 ?Htens ?Hparr. }
  splitb.
Qed.

Lemma red_tens_ineq_if (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  left (source et) <> right (source et) /\ right (source et) <> left (source et) /\
  left (source ep) <> right (source ep) /\ right (source ep) <> left (source ep) /\
  left (source et) <> left (source ep) /\ left (source ep) <> left (source et) /\
  left (source et) <> right (source ep) /\ right (source ep) <> left (source et) /\
  left (source ep) <> right (source et) /\ right (source et) <> left (source ep) /\
  right (source et) <> right (source ep) /\ right (source ep) <> right (source et).
Proof.
  assert (right (source et) <> left (source et) /\ right (source ep) <> left (source ep)) as [? ?].
  { by elim: (p_right (v := source et)); [ | caseb] => _ /eqP ?;
    elim: (p_right (v := source ep)); [ | caseb] => _ /eqP ?. }
  assert (Hf : source et <> source ep) by (intro Hf; contradict Htens; by rewrite Hf Hparr).
  assert (left (source et) <> left (source ep) /\ left (source et) <> right (source ep) /\
    right (source et) <> left (source ep) /\ right (source et) <> right (source ep)) as [? [? [? ?]]].
  { splitb; intro Hc; contradict Hf.
    - rewrite -(left_e (v := source et)) -1?(left_e (v := source ep)) ?Hc; caseb.
    - rewrite -(left_e (v := source et)) -1?(right_e (v := source ep)) ?Hc; caseb.
    - rewrite -(right_e (v := source et)) -1?(left_e (v := source ep)) ?Hc; caseb.
    - rewrite -(right_e (v := source et)) -1?(right_e (v := source ep)) ?Hc; caseb. }
  assert (left (source et) <> right (source et) /\ left (source ep) <> right (source ep) /\
    left (source ep) <> left (source et) /\ right (source ep) <> left (source et) /\
    left (source ep) <> right (source et) /\ right (source ep) <> right (source et))
    as [? [? [? [? [? ?]]]]] by (splitb; by apply nesym).
  splitb.
Qed.

Lemma red_tens_new_edges_at_in (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  let S := [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\ (inl (inl (source ep)))
    :\ (inl (inl v)) in
  Some (Some (Some None)) \in edge_set S /\ Some (Some None) \in edge_set S /\
  Some None \in edge_set S /\ None \in edge_set S.
Proof.
  destruct (red_tens_ineq_in Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? ?]]]]]]]].
  intro. rewrite !in_set; cbn. splitb.
Qed.

Definition red_tens_left_1 (G : graph_data) (et ep : edge G) :
  red_tens_graph_1 et ep -> edge (red_tens_graph_1 et ep) :=
  fun v => match v with
  | inl (inl v) =>
    if left v == left (source et) then Some (Some (Some None))
    else if left v == right (source et) then Some (Some None)
    else if left v == left (source ep) then Some None
    else if left v == right (source ep) then None
    else if left v == et then None
    else if left v == ep then None
    else Some (Some (Some (Some (inl (inl (left v))))))
  | _ => None
  end.

Lemma red_tens_consistent_left (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  let S := [set: red_tens_graph_1 _ _] :\ (inl (inl (source et))) :\ (inl (inl (source ep))) :\ (inl (inl v)) in
  forall (u : red_tens_graph v et ep), red_tens_left_1 (val u) \in edge_set S.
Proof.
  intros S [u Hu].
  destruct (red_tens_ineq_in Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? ?]]]]]]]].
  destruct (red_tens_new_edges_at_in Hcut Het Hep Htens Hparr) as [? [? [? ?]]].
  rewrite !in_set /red_tens_left_1 !SubK.
  destruct u as [[u | ] | ]; cbn;
  case_if; splitb.
  all: apply /eqP => Hc.
  - assert (ep = ccl (source ep) /\ left u = ccl (source ep)) as [Heq Heq'] by (split; apply ccl_eq; caseb).
    by rewrite -Heq in Heq'.
  - assert (et = ccl (source et) /\ left u = ccl (source et)) as [Heq Heq'] by (split; apply ccl_eq; caseb).
    by rewrite -Heq in Heq'.
  - assert (Hin : left u \in edges_at_in v) by by rewrite in_set Hc.
    by revert Hin; rewrite (red_tens_cut_set Hcut Het Hep Htens Hparr) !in_set => /orP[/eqP ? | /eqP ?].
  - assert (Hin : left u \in edges_at_in (source ep)) by by rewrite in_set Hc.
    by revert Hin; rewrite right_set ?in_set; caseb => /orP[/eqP ? | /eqP ?].
  - assert (Hin : left u \in edges_at_in (source et)) by by rewrite in_set Hc.
    by revert Hin; rewrite right_set ?in_set; caseb => /orP[/eqP ? | /eqP ?].
Qed.

Definition red_tens_left (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  red_tens_graph v et ep -> edge (red_tens_graph v et ep) :=
  fun u => Sub (red_tens_left_1 (val u)) (red_tens_consistent_left Hcut Het Hep Htens Hparr u).

Definition red_tens_graph_left (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) : graph_left := {|
  graph_of := red_tens_graph v et ep;
  left := red_tens_left Hcut Het Hep Htens Hparr;
  |}.

Definition red_tens_order_1 (G : graph_data) (et ep : edge G) :
  list (red_tens_graph_1 et ep) := [seq (inl (inl v)) | v <- order G].

Lemma red_tens_consistent_order (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  let S := [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\ (inl (inl (source ep)))
  :\ (inl (inl v)) in
  all (pred_of_set S) (red_tens_order_1 et ep).
Proof.
  rewrite /red_tens_order_1 all_map.
  apply /allP => u Hu; cbn.
  assert (Hl : vlabel u = concl_l) by by apply p_order.
  repeat (apply /setD1P; split); trivial; cbn.
  all: apply /eqP => Hc; contradict Hl; by rewrite Hc ?Hcut ?Htens ?Hparr.
Qed.

Definition red_tens_order (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  seq (red_tens_graph v et ep) := sval (all_sigP (red_tens_consistent_order Hcut Het Hep Htens Hparr)).

Definition red_tens_graph_data (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) : graph_data := {|
  graph_left_of := red_tens_graph_left Hcut Het Hep Htens Hparr;
  order := red_tens_order Hcut Het Hep Htens Hparr;
  |}.

Definition red_tens_transport (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :=
  fun (a : edge (red_tens_graph_data Hcut Het Hep Htens Hparr)) => match val a with
  | None => right (source ep)
  | Some None => left (source ep)
  | Some (Some None) => right (source et)
  | Some (Some (Some None)) => left (source et)
  | Some (Some (Some (Some (inl (inl a))))) => a
  | Some (Some (Some (Some (inl (inr a))))) => match a with end
  | Some (Some (Some (Some (inr a)))) => match a with end
  end.

Lemma red_tens_transport_inj (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  injective (@red_tens_transport _ _ Hcut _ _ Het Hep Htens Hparr).
Proof.
  intros [a Ha] [b Hb]. rewrite /red_tens_transport !SubK. intro H.
  apply /eqP; rewrite sub_val_eq SubK; apply /eqP.
  revert Ha Hb.
  rewrite !in_set.
  destruct (red_tens_ineq_if Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]].
  destruct a as [[[[[[a | []] | []] | ] | ] | ] | ], b as [[[[[[b | []] | []] | ] | ] | ] | ];
  subst; cbn; try by [].
  all: rewrite ?left_e ?right_e; caseb.
  all: (by move => /andP[_ /andP[_ /andP[/eqP ? /andP[/eqP ? _]]]] _) ||
       (by move => _ /andP[_ /andP[_ /andP[/eqP ? /andP[/eqP ? _]]]]).
Qed.

Lemma red_tens_transport_edges (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (b : bool) (u : G) (Hu : inl (inl u) \in
  (setT :\ (inl (inl (source et))) :\ (inl (inl (source ep))) :\ (inl (inl v)))),
  edges_at_outin b u =
  [set red_tens_transport a | a in edges_at_outin b (Sub (inl (inl u)) Hu : red_tens_graph_data Hcut Het Hep Htens Hparr)].
Proof.
  set S := [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\ (inl (inl (source ep))) :\ (inl (inl v)).
  intros b u Hu; apply /setP => a.
  rewrite Imset.imsetE !in_set.
  symmetry; apply /imageP; case_if.
  - subst u.
    destruct (red_tens_ineq_in Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? ?]]]]]]]].
    destruct (red_tens_new_edges_at_in Hcut Het Hep Htens Hparr) as [Insssn [Inssn [Insn Inn]]].
    assert (a <> et /\ a <> ep) as [? ?].
    { split; intros ?; subst; contradict Hu; apply /negP.
      all: rewrite !in_set; cbn.
      all: destruct b; rewrite ?Hep; caseb. }
    destruct (eq_comparable a (left (source et)));
    [ | destruct (eq_comparable a (left (source ep)))];
    [ | | destruct (eq_comparable a (right (source et)))];
    [ | | | destruct (eq_comparable a (right (source ep)))];
    try subst a.
    5:{ assert (Ina : Some (Some (Some (Some (inl (inl a))))) \in edge_set S).
        { rewrite !in_set; cbn. splitb.
          all: apply /eqP => Hf.
          - assert (a = ccl (source ep) /\ ep = ccl (source ep))
              as [? ?] by (split; apply ccl_eq; caseb).
            by assert (a = ep) by by subst.
          - assert (a = ccl (source et) /\ et = ccl (source et))
              as [? ?] by (split; apply ccl_eq; caseb).
            by assert (a = et) by by subst.
          - assert (Hin : a \in edges_at_in v) by by rewrite in_set Hf.
            by revert Hin; rewrite (red_tens_cut_set Hcut Het Hep Htens Hparr) !in_set => /orP[/eqP ? | /eqP ?].
          - assert (Hin : a \in edges_at_in (source ep)) by by rewrite in_set Hf.
            by revert Hin; rewrite right_set ?in_set; [ | caseb] => /orP[/eqP ? | /eqP ?].
          - assert (Hin : a \in edges_at_in (source et)) by by rewrite in_set Hf.
            by revert Hin; rewrite right_set ?in_set; [ | caseb] => /orP[/eqP ? | /eqP ?]. }
        exists (Sub (Some (Some (Some (Some (inl (inl a)))))) Ina); trivial.
        by rewrite !in_set; cbn; rewrite !SubK; cbn. }
    all: destruct b;
      [contradict Hu; apply /negP; rewrite !in_set ?left_e ?right_e; caseb | ].
    4: exists (Sub None Inn); trivial.
    3: exists (Sub (Some (Some None)) Inssn); trivial.
    2: exists (Sub (Some None) Insn); trivial.
    1: exists (Sub (Some (Some (Some None))) Insssn); trivial.
    all: by rewrite !in_set; cbn; rewrite !SubK; cbn.
  - intros [[[[[[[[d | []] | []] | ] | ] | ] | ] ?] Hdin Hdeq].
    all: cbn in Hdeq; subst a.
    all: revert Hdin; rewrite !in_set; cbn; rewrite !SubK; cbn => /eqP Hd //.
    all: destruct b; contradict Hd; by apply /eqP; cbn; apply /eqP.
Qed.

Lemma red_tens_transport_left (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (u : G) (Hu : inl (inl u) \in [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\
    (inl (inl (source ep))) :\ (inl (inl v))),
  vlabel u = ⊗ \/ vlabel u = ⅋ ->
  red_tens_transport (left (Sub (inl (inl u)) Hu : red_tens_graph_data Hcut Het Hep Htens Hparr)) = left u.
Proof.
  intros u Hu Hl.
  cbn; rewrite /red_tens_transport /red_tens_left /red_tens_left_1 !SubK.
  revert Hu; rewrite !in_set; cbn => /andP[/eqP Hu /andP[/eqP ? /andP[/eqP ? _]]].
  case_if; subst.
  all: by rewrite -{1}(left_e Hl) in Hu.
Qed.


Lemma red_tens_p_deg (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  proper_degree (red_tens_graph_data Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_degree, red_tens_graph_data.
  destruct (red_tens_new_edges_at_in Hcut Het Hep Htens Hparr) as [Insssn [Inssn [Insn Inn]]].
  set n := Sub None Inn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr);
  set sn := Sub (Some None) Insn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr);
  set ssn := Sub (Some (Some None)) Inssn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr);
  set sssn := Sub (Some (Some (Some None))) Insssn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr).
  intros b [[[u | []] | []] Hu]; cbn.
  - rewrite -(p_deg b u) (red_tens_transport_edges _ _ _ _ _ _ Hu) card_imset //.
    apply red_tens_transport_inj.
  - assert (edges_at_in (Sub (inl (inr tt)) Hu : red_tens_graph_data Hcut Het Hep Htens Hparr) = [set sssn; n]
      /\ edges_at_out (Sub (inl (inr tt)) Hu : red_tens_graph_data Hcut Het Hep Htens Hparr) = set0) as [Hin Hout].
    { split; apply /setP; intros [[[[[[[a | []] | []] | ] | ] | ] | ] ?]; by rewrite !in_set. }
    destruct b; by rewrite ?Hin ?Hout ?cards2 ?cards0.
  - assert (edges_at_in (Sub (inr tt) Hu : red_tens_graph_data Hcut Het Hep Htens Hparr) = [set ssn; sn]
      /\ edges_at_out (Sub (inr tt) Hu : red_tens_graph_data Hcut Het Hep Htens Hparr) = set0) as [Hin Hout].
    { split; apply /setP; intros [[[[[[[a | []] | []] | ] | ] | ] | ] ?]; by rewrite !in_set. }
    destruct b; by rewrite ?Hin ?Hout ?cards2 ?cards0.
Qed.

Lemma red_tens_p_left (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  proper_left (red_tens_graph_data Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_left.
  intros [[[u | []] | []] Hu] Hl; cbn in *;
  try (destruct Hl as [Hl | Hl]; by contradict Hl).
  assert (H := p_left Hl).
  revert H; rewrite (red_tens_transport_edges _ _ _ _ _ _ Hu) Imset.imsetE in_set => /imageP [a Ha Heq].
  enough (Hd : red_tens_left Hcut Het Hep Htens Hparr (Sub (inl (inl u)) Hu) = a) by by rewrite Hd.
  rewrite -(red_tens_transport_left _ _ _ _ _ Hu Hl) in Heq.
  apply (red_tens_transport_inj Heq).
Qed.

Lemma red_tens_p_order (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  proper_order (red_tens_graph_data Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_order, red_tens_graph_data, red_tens_order; cbn.
  split.
  - intros [[[u | ] | ] ?]; cbn;
    rewrite in_seq_sig SubK -(proj2_sig (all_sigP _)) /red_tens_order_1.
    { rewrite mem_map; [ | apply inj_comp; apply inl_inj].
      apply p_order. }
    all: split; intro H; try by [].
    all: contradict H; apply /negP.
    all: clear; by induction (order G).
  - rewrite uniq_seq_sig -(proj2_sig (all_sigP _)) /red_tens_order_1 map_inj_uniq;
    [ | apply inj_comp; apply inl_inj].
    apply p_order.
Qed.

Definition red_tens_geos (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) : geos := {|
  graph_data_of := red_tens_graph_data Hcut Het Hep Htens Hparr;
  p_deg := @red_tens_p_deg _ _ _ _ _ _ _ _ _;
  p_left := @red_tens_p_left _ _ _ _ _ _ _ _ _;
  p_order := @red_tens_p_order _ _ _ _ _ _ _ _ _;
  |}.

Lemma red_tens_transport_right (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (u : G) (Hu : inl (inl u) \in [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\
    (inl (inl (source ep))) :\ (inl (inl v))),
  vlabel u = ⊗ \/ vlabel u = ⅋ ->
  red_tens_transport (right (Sub (inl (inl u)) Hu : red_tens_geos Hcut Het Hep Htens Hparr)) = right u.
Proof.
  intros u Hu Hl.
  set w : red_tens_geos Hcut Het Hep Htens Hparr := Sub (inl (inl u)) Hu.
  apply right_eq; trivial.
  assert (Hdone : red_tens_transport (right w) \in edges_at_in u).
  { rewrite (red_tens_transport_edges _ _ _ _ _ _ Hu).
    by apply imset_f, (p_right (v := w)). }
  revert Hdone; rewrite in_set => /eqP Hdone. splitb.
  rewrite -(red_tens_transport_left _ _ _ _ _ Hu) // -/w.
  intro Hf.
  assert (Hl' : vlabel w = ⊗ \/ vlabel w = ⅋) by by [].
  destruct (p_right Hl') as [_ Hc].
  contradict Hc; apply /negP; rewrite negb_involutive; apply /eqP.
  by apply red_tens_transport_inj.
Qed.

Lemma red_tens_transport_ccl (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (u : G) (Hu : inl (inl u) \in [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\
    (inl (inl (source ep))) :\ (inl (inl v))),
  vlabel u = ⊗ \/ vlabel u = ⅋ ->
  red_tens_transport (ccl (Sub (inl (inl u)) Hu : red_tens_geos Hcut Het Hep Htens Hparr)) = ccl u.
Proof.
  intros u Hu Hl.
  set w : red_tens_geos Hcut Het Hep Htens Hparr := Sub (inl (inl u)) Hu.
  apply ccl_eq; trivial.
  assert (Hdone : red_tens_transport (ccl w) \in edges_at_out u).
  { rewrite (red_tens_transport_edges _ _ _ _ _ _ Hu).
    by apply imset_f, (p_ccl (v := w)). }
  by revert Hdone; rewrite in_set => /eqP ?.
Qed.

Lemma red_tens_transport_edge_of_concl (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (u : G) (Hu : inl (inl u) \in [set: red_tens_graph_1 et ep] :\ (inl (inl (source et))) :\
    (inl (inl (source ep))) :\ (inl (inl v))),
  vlabel u = c ->
  red_tens_transport (edge_of_concl (Sub (inl (inl u)) Hu : red_tens_geos Hcut Het Hep Htens Hparr)) = edge_of_concl u.
Proof.
  intros u Hu Hl.
  set w : red_tens_geos Hcut Het Hep Htens Hparr := Sub (inl (inl u)) Hu.
  apply concl_eq; trivial.
  assert (Hdone : red_tens_transport (edge_of_concl w) \in edges_at_in u).
  { rewrite (red_tens_transport_edges _ _ _ _ _ _ Hu).
    by apply imset_f, (p_concl (v := w)). }
  by revert Hdone; rewrite in_set => /eqP Hdone.
Qed.

Lemma red_tens_transport_label (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (a : edge (red_tens_geos Hcut Het Hep Htens Hparr)), elabel a = elabel (red_tens_transport a).
Proof. by intros [[[[[[[? | []] | []] | ] | ] | ] | ] ?]. Qed.


Lemma red_tens_p_ax_cut (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  proper_ax_cut (red_tens_geos Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_ax_cut.
  destruct (red_tens_new_edges_at_in Hcut Het Hep Htens Hparr) as [Insssn [Inssn [Insn Inn]]].
  set n := Sub None Inn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr);
  set sn := Sub (Some None) Insn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr);
  set ssn := Sub (Some (Some None)) Inssn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr);
  set sssn := Sub (Some (Some (Some None))) Insssn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr).
  destruct (proper_ax_cut_bis G) as [_ Hpcut].
  assert (Hvet : et \in edges_at_in v) by by rewrite in_set Het.
  specialize (Hpcut _ Hcut _ Hvet).
  unfold is_dual_f, is_dual in Hpcut; revert Hpcut => /eqP Hpcut.
  assert (Ht := p_tens Htens); cbn in Ht.
  assert (Hp := p_parr Hparr); cbn in Hp.
  assert (et = ccl (source et) /\ ep = ccl (source ep)) as [Hct Hcp] by (split; apply ccl_eq; caseb).
  rewrite -Hct in Ht;
  rewrite -Hcp in Hp.
  assert (Hoep : ep = other (pre_proper_cut Hcut) Hvet).
  { apply other_eq.
    - by rewrite in_set Hep.
    - intro Hc; clear - Hc Htens Hparr; contradict Hparr.
      by rewrite Hc Htens. }
  rewrite -Hoep Ht Hp in Hpcut; cbn in Hpcut; clear Hoep Hvet Hct Hcp Ht Hp.
  inversion Hpcut as [[H0 H1]]; clear Hpcut.
  intros b [[[u | []] | []] Hu] Hl; cbn in Hl.
  { destruct (p_ax_cut Hl) as [el [er H]].
    revert H. rewrite (red_tens_transport_edges _ _ _ _ _ b Hu) => /andP[/andP[Hel Her] /eqP Heq].
    revert Hel; rewrite Imset.imsetE in_set => /imageP [El ? HeEl]; subst el;
    revert Her; rewrite Imset.imsetE in_set => /imageP [Er ? HeEr]; subst er.
    exists El, Er.
    splitb; apply /eqP.
    by rewrite !red_tens_transport_label. }
  all: destruct b; try by [].
  1: exists sssn, n.
  2: exists ssn, sn.
  all: rewrite !in_set; cbn; rewrite !SubK; cbn; apply /eqP.
  all: by rewrite -?H0 -?H1 bidual.
Qed.

Lemma red_tens_p_tens_parr (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  proper_tens_parr (red_tens_geos Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_tens_parr.
  intros b [[[u | []] | []] Hu] Hl; cbn in Hl.
  all: try (destruct b; by contradict Hl).
  rewrite !red_tens_transport_label red_tens_transport_left ?red_tens_transport_right ?red_tens_transport_ccl;
  try (destruct b; by caseb).
  by apply p_tens_parr.
Qed.

Definition red_tens_ps (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) : proof_structure := {|
  geos_of := red_tens_geos Hcut Het Hep Htens Hparr;
  p_ax_cut := @red_tens_p_ax_cut _ _ _ _ _ _ _ _ _;
  p_tens_parr := @red_tens_p_tens_parr _ _ _ _ _ _ _ _ _;
  |}.


(** Sequent of an tensor - cut reduction *)
Lemma red_tens_sequent (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  sequent (red_tens_geos Hcut Het Hep Htens Hparr) = sequent G.
Proof.
  transitivity ([seq elabel (@red_tens_transport _ _ Hcut _ _ Het Hep Htens Hparr (edge_of_concl u)) |
    u <- red_tens_order Hcut Het Hep Htens Hparr]).
  { apply eq_map; intros [? ?]. apply red_tens_transport_label. }
  destruct (red_tens_new_edges_at_in Hcut Het Hep Htens Hparr) as [_ [_ [_ Inn]]].
  set n := Sub None Inn : edge (red_tens_graph_data Hcut Het Hep Htens Hparr).
  assert ([seq elabel (red_tens_transport (edge_of_concl u)) | u <- red_tens_order Hcut Het Hep Htens Hparr] =
    [seq (match u with | inl (inl u) => elabel (edge_of_concl u) | _ => elabel n end)
    | u <- [seq val u | u <- red_tens_order Hcut Het Hep Htens Hparr]]) as ->.
  { rewrite -map_comp.
    apply (@eq_in_map _); intros [a Ha].
    rewrite /red_tens_order in_seq_sig !SubK -(proj2_sig (all_sigP _)) /red_tens_order_1.
    move => /mapP [x Hx Hax].
    assert (Hxx : inl (inl x) \in [set: red_tens_graph_1 et ep] :\ inl (inl (source et))
      :\ inl (inl (source ep)):\ inl (inl v)) by by rewrite -Hax.
    assert (Sub a Ha = Sub (inl (inl x)) Hxx) as -> by (apply /eqP; by rewrite sub_val_eq SubK Hax).
    rewrite red_tens_transport_edge_of_concl /comp ?SubK //; by apply p_order. }
  rewrite -(proj2_sig (all_sigP _)) /red_tens_order_1 -map_comp.
  by apply eq_map.
Qed.

(** Decreasing number of vertices *)
Lemma red_tens_nb (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  #|red_tens_graph v et ep| = #|G| - 1.
Proof.
  set f := fun (u : red_tens_graph v et ep) => match val u with
  | inl (inl u) => u
  | inl (inr _) => source et
  | inr _ => source ep
  end.
  assert (injective f).
  { assert (source et <> source ep).
    { intro Hc. contradict Htens.
      by rewrite Hc Hparr. }
    assert (source ep <> source et) by by apply nesym.
    intros [[[u | []] | []] Hu] [[[u' | []] | []] Hu']; rewrite /f !SubK; intro Heq.
    all: apply /eqP; rewrite // sub_val_eq SubK ?Heq //; cbn.
    all: revert Hu Hu'; rewrite !in_set Heq; cbn.
    all: (by move => /andP[/eqP ? /andP[/eqP ? /andP[/eqP ? _]]] _)
      || by move => _ /andP[/eqP ? /andP[/eqP ? /andP[/eqP ? _]]]. }
  rewrite -(card_imset (f := f)) //.
  assert (#|setT :\ v| = #|G| - 1) as <-.
  { rewrite -cardsT [in RHS](cardsD1 v) in_set. lia. }
  apply eq_card; intro u.
  rewrite Imset.imsetE !in_set andb_true_r.
  destruct (eq_comparable u v) as [ | Hneq].
  - subst; rewrite eq_refl; cbn.
    apply /imageP; intros [[[[u | []] | []] Hin] _ Huv]; rewrite /f SubK in Huv.
    + revert Hin; rewrite !in_set; cbn => /andP[/eqP ? /andP[/eqP ? /andP[/eqP ? _]]].
      by subst.
    + contradict Htens.
      by rewrite -Huv Hcut.
    + contradict Hparr.
      by rewrite -Huv Hcut.
  - transitivity true.
    2:{ symmetry; by apply /negP /negP /eqP. }
    apply /imageP.
    set S := [set: red_tens_graph_1 et ep] :\ inl (inl (source et))
      :\ inl (inl (source ep)):\ inl (inl v).
    destruct (eq_comparable u (source et));
    [ | destruct (eq_comparable u (source ep))].
    + assert (Hin : inl (inr tt) \in S) by by rewrite !in_set.
      by exists (Sub (inl (inr tt)) Hin).
    + assert (Hin : inr tt \in S) by by rewrite !in_set.
      by exists (Sub (inr tt) Hin).
    + assert (Hin : inl (inl u) \in S) by
        (rewrite !in_set; cbn; splitb; by apply /eqP).
      by exists (Sub (inl (inl u)) Hin).
Qed.


(** * Cut reduction procedure *)
Lemma red_term (G : proof_structure) (v : G) (H : vlabel v = cut) :
  [exists e, (target e == v) && (vlabel (source e) == ax)] || [exists et, exists ep,
  (target et == v) && (target ep == v) && (vlabel (source et) == ⊗) && (vlabel (source ep) == ⅋)].
Proof.
  enough (Hdone : (exists e, target e = v /\ vlabel (source e) = ax) \/
    exists et ep, target et = v /\ target ep = v /\ vlabel (source et) = ⊗ /\ vlabel (source ep) = ⅋).
  { destruct Hdone as [[e [He0 He1]] | [et [ep [He0 [He1 [He2 He3]]]]]].
    - apply /orP; left. apply /existsP; exists e. rewrite He0 He1. splitb.
    - apply /orP; right. apply /existsP; exists et. apply /existsP; exists ep. rewrite He0 He1 He2 He3. splitb. }
  destruct (p_cut H) as [e [e' H']];
  revert H'; rewrite !in_set => /andP[/andP[/eqP Hin /eqP Hin'] /eqP Heq].
  rewrite -Hin in H.
  assert (Hout := p_deg_out (source e)).
  assert (Hout' := p_deg_out (source e')).
  assert (#|edges_at_out (source e)| <> 0 /\ #|edges_at_out (source e')| <> 0) as [? ?].
  { split; intro Hc; [set f := e | set f := e'].
    all: assert (Hf : f \in set0) by by rewrite -(cards0_eq Hc) in_set.
    all: contradict Hf; by rewrite in_set. }
  destruct (vlabel (source e)) eqn:Hle; try done;
  destruct (vlabel (source e')) eqn:Hle'; try done.
  all: try (by left; exists e; splitb).
  all: try (by left; exists e'; splitb).
  - contradict Heq.
    enough (elabel e = tens (elabel (left (source e))) (elabel (right (source e)))
      /\ elabel e' = tens (elabel (left (source e'))) (elabel (right (source e')))) as [-> ->] by by [].
    assert (e = ccl (source e) /\ e' = ccl (source e')) as [He He'] by (split; apply ccl_eq; trivial; caseb).
    split; [rewrite {1}He | rewrite {1}He']; by apply p_tens.
  - right; by exists e, e'.
  - right; by exists e', e.
  - contradict Heq.
    enough (elabel e = parr (elabel (left (source e))) (elabel (right (source e)))
      /\ elabel e' = parr (elabel (left (source e'))) (elabel (right (source e')))) as [-> ->] by by [].
    assert (e = ccl (source e) /\ e' = ccl (source e')) as [He He'] by (split; apply ccl_eq; trivial; caseb).
    split; [rewrite {1}He | rewrite {1}He']; by apply p_parr.
Qed.

Definition red_one (G : proof_structure) (v : G) (H : vlabel v = cut) : proof_structure.
Proof.
  elim: (orb_sum (red_term H)).
  - move => /existsP /sigW [? /andP[/eqP ? /eqP ?]]; subst.
    by apply (red_ax_ps H).
  - move => /existsP /sigW [? /existsP /sigW [? /andP[/andP[/andP[/eqP Het /eqP Hep] /eqP ?] /eqP ?]]].
    by apply (red_tens_ps H Het Hep).
Defined.

Lemma red_one_sequent (G : proof_structure) (v : G) (H : vlabel v = cut) :
  sequent (red_one H) = sequent G.
Proof.
  unfold red_one.
  elim: (orb_sum (red_term H)) => Hex /=.
  - elim: (sigW (elimTF existsP Hex)) => {Hex} ? /andP[He ?].
    set Hr := elimTF eqP He; destruct Hr.
    apply red_ax_sequent.
  - elim: (sigW (elimTF existsP Hex)) => {Hex} ? Hex;
    elim: (sigW (elimTF existsP Hex)) => {Hex} ? /andP[/andP[/andP[? ?] ?] ?].
    apply red_tens_sequent.
Qed.

Lemma red_one_nb (G : proof_structure) (v : G) (H : vlabel v = cut) :
  #|red_one H| < #|G|.
Proof.
  unfold red_one.
  assert (#|G| <> 0) by by apply fintype0.
  elim: (orb_sum (red_term H)) => Hex /=.
  - elim: (sigW (elimTF existsP Hex)) => {Hex} e /andP[He Hax].
    set Hr := elimTF eqP He; destruct Hr.
    rewrite red_ax_nb.
    set n := #|G|; lia.
  - elim: (sigW (elimTF existsP Hex)) => {Hex} et Hex.
    elim: (sigW (elimTF existsP Hex)) => {Hex} ep /andP[/andP[/andP[Het Hep] Htens] Hparr].
    rewrite red_tens_nb //; try by apply /eqP.
    set n := #|G|; lia.
Qed.

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

Definition red_all (G : proof_structure) : {P : proof_structure | sequent P = sequent G & ~(has_cut P)}.
Proof.
  revert G.
  enough (Hm : forall n (G : proof_structure), #|G| = n ->
    {P : proof_structure | sequent P = sequent G & ~(has_cut P)})
    by (intro G; by apply (Hm #|G|)).
  intro n; induction n as [n IH] using lt_wf_rect; intros G Hc.
  have [H | H] := altP (@has_cutP G).
  + revert H => /has_cutP /existsP /sigW [v /eqP Hcut].
    rewrite -(red_one_sequent Hcut).
    assert (Hc' := red_one_nb Hcut).
    apply (IH #|red_one Hcut|); lia.
  + eexists G; trivial.
    by revert H => /has_cutP H.
Qed.

Definition red (G : proof_structure) : proof_structure := proj1_sig (red_all G).

Lemma red_sequent (G : proof_structure) : sequent (red G) = sequent G.
Proof. by destruct (proj2_sig (red_all G)). Qed.

Lemma red_has_cut (G : proof_structure) : ~ has_cut (red G).
Proof. by destruct (proj2_sig (red_all G)). Qed.



Fixpoint nb_cut l (pi : ll l) := match pi with
  | ax_r x                 => 0
  | ex_r _ _ pi0 _         => nb_cut pi0
  | tens_r _ _ _ _ pi0 pi1 => nb_cut pi0 + nb_cut pi1
  | parr_r _ _ _ pi0       => nb_cut pi0
  | cut_r _ _ _ pi0 pi1    => nb_cut pi0 + nb_cut pi1 + 1
  end.
(* UTILISE ps, AUTRE FICHIER 
Lemma ps_nb_cut l (pi : ll l) : #|[set v : ps pi | vlabel v == cut]| = nb_cut pi.
Proof.
  induction pi as [x | | A B l0 l1 pi0 H0 pi1 H1 | A B l0 pi0 H0 | A l0 l1 pi0 H0 pi1 H1].
  - enough (H : [set v : ax_ps x | vlabel v == cut] = set0) by by rewrite H cards0.
    apply /setP; intro v; destruct_I3 v;
    by rewrite !in_set.
  - by [].
  - rewrite /= -H0 -H1.
Abort. *)
(* TODO Lemma : nb cut ps (pi) = nb cut pi, idem other rules + mettre ça vers ps
-> vraiment utile ? ça a l'air mieux dans le sens sequentialisation ... *)
(* lemma: sub-confluence + convergence *)

(** * Cut elimination preserves correctness *)
(** Axiom - cut reduction *)
Unset Mangle Names. (* TODO *)
Definition red_ax_G (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut) (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :=
  @invert_edge_graph_left _
  (@extend_edge_graph_left _
    (@extend_edge_graph_left _ (red_ax_graph_left Hcut Hax) (Sub None N) cut (dual (elabel e)) (elabel e))
    (Some (Sub None N)) ax (elabel e) (dual (elabel e)))
  None.

Definition red_ax_iso_v_bij_fwd (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  red_ax_G N -> G :=
  fun v => match v with
  | Some (Some (exist u _)) => u
  | Some None               => target e
  | None                    => source e
  end.

Definition red_ax_iso_v_bij_bwd (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  G -> red_ax_G N :=
  fun v => if @boolP _ is AltTrue p then Some (Some (Sub v p))
    else if v == source e then None else Some None.

Lemma red_ax_iso_v_bijK (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  cancel (@red_ax_iso_v_bij_fwd _ _ _ _ N) (red_ax_iso_v_bij_bwd N).
Proof.
  intros [[[v V] | ] | ]; cbn;
  unfold red_ax_iso_v_bij_bwd; case: {-}_ /boolP => [Hc | /negP ?] //.
  - cbnb.
  - contradict Hc; apply /negP.
    rewrite !in_set. caseb.
  - case: ifP; trivial.
    clear - Hcut Hax => /eqP H.
    contradict Hcut. by rewrite H Hax.
  - contradict Hc; apply /negP.
    rewrite !in_set. caseb.
  - case_if.
Qed.

Lemma red_ax_iso_v_bijK' (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  cancel (red_ax_iso_v_bij_bwd N) (@red_ax_iso_v_bij_fwd _ _ _ _ N).
Proof.
  intro v; unfold red_ax_iso_v_bij_bwd.
  case: {-}_ /boolP => [// | ].
  rewrite !in_set => /nandP[/negPn /eqP ? | /nandP[/negPn /eqP ? | //]]; subst; case_if.
Qed.

Definition red_ax_iso_v (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) := {|
  bij_fwd := @red_ax_iso_v_bij_fwd _ _ _ _ N;
  bij_bwd:= red_ax_iso_v_bij_bwd N;
  bijK:= @red_ax_iso_v_bijK _ _ _ _ _;
  bijK':= red_ax_iso_v_bijK' _;
  |}.

Definition red_ax_iso_e_bij_fwd (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  edge (red_ax_G N) -> edge G :=
  fun a => match a with
  | None                            => e
  | Some None                       => other_cut Hcut
  | Some (Some (exist None _))      => other_ax Hax
  | Some (Some (exist (Some a) _))  => a
  end.

Definition red_ax_iso_e_bij_bwd (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  edge G -> edge (red_ax_G N) :=
  fun a => if @boolP _ is AltTrue p then Some (Some (Sub (Some a) p))
    else if a == e then None
      else if a == other_ax Hax then Some (Some (Sub None N))
        else Some None.

Lemma red_ax_iso_e_bijK (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  cancel (@red_ax_iso_e_bij_fwd _ _ _ _ N) (@red_ax_iso_e_bij_bwd _ _ _ _ N).
Proof.
  intros [[[[a | ] A] | ] | ]; cbn;
  unfold red_ax_iso_e_bij_bwd; case: {-}_ /boolP => [Hc | /negP ?] //.
  - cbnb.
  - contradict Hc; apply /negP.
    rewrite !in_set /=; destruct (other_ax_in_neq Hax) as [-> _]. caseb.
  - assert (other_ax Hax == e = false) as -> by (apply /negP/negP; apply (other_ax_in_neq Hax)).
    case_if. cbnb.
  - contradict Hc; apply /negP.
    rewrite !in_set; cbn; destruct (other_cut_in_neq Hcut) as [-> _]. caseb.
  - assert (other_cut Hcut == e = false) as -> by (apply /negP/negP; apply (other_cut_in_neq Hcut)).
    enough (other_cut Hcut == other_ax Hax = false) as -> by trivial.
    apply /eqP => Hc. apply red_ax_degenerate_None in Hc. by contradict Hc; apply /negP/negPn.
  - contradict Hc; apply /negP.
    rewrite !in_set. caseb.
  - case_if.
Qed.

Lemma red_ax_iso_e_bijK' (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  cancel (@red_ax_iso_e_bij_bwd _ _ _ _ N) (@red_ax_iso_e_bij_fwd _ _ _ _ N).
Proof.
  intro a.
  unfold red_ax_iso_e_bij_bwd. case: {-}_ /boolP => [Hc | Ha].
  - cbnb.
  - case_if.
    revert Ha; rewrite !in_set /= => /nandP[/nandP[/negPn/eqP Ha | /nandP[/negPn/eqP Ha | //]]
                                          | /nandP[/negPn/eqP Ha | /nandP[/negPn/eqP Ha | //]]].
    + enough (Hf : a \in set0) by (contradict Hf; by rewrite in_set).
      assert (Hc := p_deg_out (target e)).
      rewrite Hcut /= in Hc.
      by rewrite -(cards0_eq Hc) in_set Ha.
    + enough (a = other_ax Hax) by by [].
      by apply other_ax_eq.
    + symmetry; by apply other_cut_eq.
    + enough (Hf : a \in set0) by (contradict Hf; by rewrite in_set).
      assert (Hc := p_deg_in (source e)).
      rewrite Hax /= in Hc.
      by rewrite -(cards0_eq Hc) in_set Ha.
Qed.

Definition red_ax_iso_e (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) := {|
  bij_fwd := @red_ax_iso_e_bij_fwd _ _ _ _ N;
  bij_bwd:= @red_ax_iso_e_bij_bwd _ _ _ _ _;
  bijK:= @red_ax_iso_e_bijK _ _ _ _ _;
  bijK':= red_ax_iso_e_bijK' _;
  |}.

Lemma red_ax_iso_ihom (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  is_ihom (red_ax_iso_v N) (red_ax_iso_e N) pred0.
Proof.
  split.
  - intros [[[[a | ] A] | ] | ] b; cbn.
    + cbnb.
    + cbnb.
      destruct b; cbnb.
      by destruct (other_ax_in_neq Hax) as [-> _].
    + destruct b; cbnb.
      by destruct (other_cut_in_neq Hcut) as [-> _].
    + by destruct b.
  - by intros [[[? ?] | ] | ].
  - move => [[[[a | ] A] | ] | ] //; cbnb.
    + destruct (proper_ax_cut_bis G) as [Hpax _].
      specialize (Hpax _ Hax _ (source_in_edges_at_out e)).
      by revert Hpax => /eqP Hpax.
    + destruct (proper_ax_cut_bis G) as [_ Hpcut].
      specialize (Hpcut _ Hcut _ (target_in_edges_at_in e)).
      by revert Hpcut => /eqP Hpcut.
Qed.

Definition red_ax_iso (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) := {|
  iso_v := red_ax_iso_v N;
  iso_e := red_ax_iso_e _;
  iso_d := pred0;
  iso_ihom := red_ax_iso_ihom _ |}.

Lemma red_ax_isol (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
   red_ax_G N ≃l G.
Proof.
  exists (red_ax_iso N).
  intros [[[v V] | ] | ] Hl; try by []; unfold red_ax_iso_v_bij_bwd; cbn; cbn in *.
  cbnb. unfold red_ax_left_1.
  assert (left v <> e).
  { intros ?; subst e.
    clear - Hcut Hl; contradict Hcut.
    rewrite left_e ?Hl; caseb. }
  assert (left v <> other_cut Hcut).
  { intro Hc.
    clear - Hcut Hl Hc. enough (vlabel (target e) <> cut) by by [].
    destruct (other_cut_in_neq Hcut) as [<- _].
    rewrite -Hc left_e ?Hl; caseb. }
    case_if.
    contradict N; apply /negP.
    by apply red_ax_degenerate_None, red_ax_degenerate_source.
Qed.

Lemma red_ax_correct (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  correct G -> correct (red_ax_graph_left Hcut Hax).
Proof.
  intro C.
  enough (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))).
  { assert (C' := iso_correct (red_ax_isol N) C).
    by apply invert_edge_correct, extend_edge_correct, extend_edge_correct in C'. }
  apply /negPn /negP => N.
  apply red_ax_degenerate_None in N.
  destruct C as [A _].
  unfold uacyclic in A.
  enough (exists (p :  Supath switching (source e) (source e)),
    p <> supath_nil switching (source e)) as [p ?] by by specialize (A _ p).
  enough (P : supath switching (source e) (source e) (forward e :: backward (other_cut Hcut) :: nil))
    by by exists {| upval := _ ; upvalK := P |}.
  rewrite /supath /= in_cons in_nil orb_false_r {2}N.
  destruct (other_cut_in_neq Hcut) as [-> _].
  destruct (other_ax_in_neq Hax) as [-> _].
  splitb.
  cbn. destruct (other_cut_in_neq Hcut) as [-> ?]. rewrite !Hcut /=.
  by apply /eqP; apply nesym; apply /eqP.
Qed.

(********************************** WORKING generalize
Fixpoint red_ax_uwalk (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (p : @upath _ _ (red_ax_graph Hcut Hax)) : @upath _ _ G :=
  match p with
  | [::] => [::]
  | (exist (Some a) _, b) :: q => (a, b) :: red_ax_uwalk q
  | forward (exist None _) :: q =>
    forward (other_cut Hcut) :: backward e :: forward (other_ax Hax) :: red_ax_uwalk q
  | backward (exist None _) :: q =>
    backward (other_ax Hax) :: forward e :: backward (other_cut Hcut) :: red_ax_uwalk q
  end.

Lemma red_ax_uwalkK (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (p : @upath _ _ (red_ax_graph_left Hcut Hax)) :
  forall u v, uwalk u v p -> @uwalk _ _ G (val u) (val v) (red_ax_uwalk p).
Proof.
  induction p as [ | (a, b) p H]; try by [].
  move => [u U] [v V]. cbn. rewrite SubK => /andP[/eqP ? W]. subst u.
  specialize (H _ _ W). clear W.
  destruct a as [[a | ] A]; [splitb | ].
  destruct b; cbn;
  destruct (other_cut_in_neq Hcut) as [-> _];
  destruct (other_ax_in_neq Hax) as [-> _];
  splitb.
Qed.

Lemma red_ax_uwalkNone (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (p : @upath _ _ (red_ax_graph_left Hcut Hax)) :
  forall (N : None \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e))) (b : bool),
  ((e, ~~ b) \in red_ax_uwalk p) = ((Sub None N, b) \in p).
Proof.
  intros N b. induction p as [ | ([[a | ] A], c) p IH]; try by []; cbn;
  rewrite !in_cons -IH {IH}; cbn.
  - enough ((e == a) = false) as -> by reflexivity.
    apply /eqP => ?; subst a.
    contradict A; apply /negP.
    rewrite !in_set. caseb.
  - rewrite SubK /=.
    destruct (other_ax_in_neq Hax) as [_ ?].
    destruct (other_cut_in_neq Hcut) as [_ ?].
    assert ((e == other_ax Hax) = false /\ (e == other_cut Hcut) = false) as [Hr0 Hr1]
      by (split; by apply /eqP; apply nesym; apply /eqP).
    destruct b, c; cbn;
    by rewrite !in_cons ?eq_refl; cbn; rewrite ?Hr0 ?Hr1 ?andb_false_r.
Qed.

Lemma red_ax_uwalkNone' (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (p : @upath _ _ (red_ax_graph_left Hcut Hax)) :
  forall (b : bool),
  (other_ax Hax, b) \in red_ax_uwalk p = ((e, ~~ b) \in red_ax_uwalk p) /\
  (other_cut Hcut, b) \in red_ax_uwalk p = ((e, ~~ b) \in red_ax_uwalk p).
Proof.
  intro b. induction p as [ | ([[a | ] A], c) p IH]; try by []; cbn;
  destruct IH as [IHax IHcut].
  - rewrite !in_cons -{1}IHax -IHcut {IHax IHcut}; cbn.
    enough ((other_ax Hax == a) = false /\ (e == a) = false /\ (other_cut Hcut == a) = false)
      as [-> [-> ->]] by by split.
    splitb; apply /eqP => ?; subst a.
    all: contradict A; apply /negP; rewrite !in_set; cbn.
    all: try (destruct (other_ax_in_neq Hax) as [-> _]).
    all: try (destruct (other_cut_in_neq Hcut) as [-> _]).
    all: caseb.
  - destruct (other_ax_in_neq Hax) as [_ ?].
    destruct (other_cut_in_neq Hcut) as [_ ?].
    assert ((other_ax Hax == e) = false /\ (other_cut Hcut == e) = false) as [Hr0 Hr1]
      by (split; by apply /eqP /eqP).
    assert ((e == other_ax Hax) = false /\ (e == other_cut Hcut) = false) as [Hr2 Hr3]
      by (split; by apply /eqP; apply nesym; apply /eqP).
    destruct b, c; rewrite !in_cons -{1}IHax -IHcut ?eq_refl {IHax IHcut}; cbn;
    by rewrite ?Hr0 ?Hr1 ?Hr2 ?Hr3 ?andb_false_r ?orb_true_r.
Qed.

Lemma red_ax_uwalkSome (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (p : @upath _ _ (red_ax_graph_left Hcut Hax)) :
  forall f F (b : bool),
  ((f, b) \in red_ax_uwalk p) = ((Sub (Some f) F, b) \in p).
Proof.
  intros f F b. induction p as [ | [[[a | ] A] c] p IH]; try by []; cbn.
  - rewrite !in_cons IH {IH}; cbn; rewrite SubK. reflexivity.
  - assert ((f == other_cut Hcut) = false /\ (f == e) = false /\ (f == other_ax Hax) = false)
      as [Hr0 [Hr1 Hr2]].
    { splitb; apply /eqP => ?; subst f.
      all: clear IH; contradict F; apply /negP; rewrite !in_set; cbn.
      all: try (destruct (other_ax_in_neq Hax) as [-> _]).
      all: try (destruct (other_cut_in_neq Hcut) as [-> _]).
      all: caseb. }
    destruct c; rewrite !in_cons IH {IH}; cbn; rewrite SubK Hr0 Hr1 Hr2; reflexivity.
Qed.

Lemma red_ax_upathK (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (p : @upath _ _ (red_ax_graph_left Hcut Hax)) :
  forall u v, supath switching u v p -> supath switching (val u) (val v) (red_ax_uwalk p).
Proof.
  move => x v /andP[/andP[W U] _].
  splitb.
  - by apply red_ax_uwalkK.
  - clear - U. induction p as [ | (a, b) p IH]; trivial.
    revert U; cbn; move => /andP[u U].
    specialize (IH U); clear U.
    destruct (other_cut_in_neq Hcut) as [C0 ?].
    destruct (other_ax_in_neq Hax) as [A0 ?].
    assert (forall m, source m <> target e).
    { clear - Hcut. intros m Hc.
      assert (Hc' : m \in edges_at_out (target e)) by by rewrite in_set Hc.
      contradict Hc'; apply /negP.
      enough (edges_at_out (target e) = set0) as -> by by rewrite in_set.
      apply cards0_eq.
      by rewrite p_deg Hcut. }
    assert (forall m, target m <> source e).
    { clear - Hax. intros m Hc.
      assert (Hc' : m \in edges_at_in (source e)) by by rewrite in_set Hc.
      contradict Hc'; apply /negP.
      enough (edges_at_in (source e) = set0) as -> by by rewrite in_set.
      apply cards0_eq.
      by rewrite p_deg Hax. }
    destruct a as [[a | ] A]; cbn.
    + splitb. clear b IH.
      apply /negP => /mapP [[f b] N E]. cbn in E.
      contradict u; apply /negP; rewrite negb_involutive.
      assert (Hta := switching_eq E).
      unfold switching in E; revert E; cbn.
      rewrite Hta.
      move => /eqP. case_if.
      2:{ subst f.
        apply /mapP.
        exists (Sub (Some a) A, b); trivial.
        by rewrite -red_ax_uwalkSome. }
      assert (Hf : vlabel (target f) = ⅋) by by apply /eqP; cbn; apply /eqP.
      rewrite {1}/switching /= {1}Hta Hf /red_ax_left /red_ax_left_1; cbn.
      assert (left (target a) <> e).
      { intros ?; subst e.
        clear - Hcut Hta Hf; contradict Hcut.
        rewrite left_e ?Hta ?Hf; caseb. }
      assert (left (target a) <> other_cut Hcut).
      { intro Hc.
        enough (vlabel (target e) <> cut) by by [].
        rewrite -C0 -Hc left_e ?Hta ?Hf; caseb. }
      apply /mapP.
      destruct (eq_comparable f (other_ax Hax)) as [ | Hneq']; [subst f | ].
      * assert (HN : None \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e))).
        { rewrite !in_set; cbn.
          splitb; apply /eqP => // Hc.
          - destruct (red_ax_degenerate_source Hcut Hax) as [Hc' _].
            symmetry in Hc; specialize (Hc' Hc).
            contradict Hf.
            by rewrite -Hc' C0 Hcut.
          - assert (Hc' : other_ax Hax \in edges_at_in (target e)) by by rewrite in_set Hc.
            rewrite other_cut_set in Hc'.
            revert Hc'; rewrite !in_set => /orP[Hc' | /eqP Hc'].
            + contradict Hc'; apply /negP.
              apply other_ax_in_neq.
            + contradict Hf.
              by rewrite Hc' C0 Hcut. }
        exists (Sub None HN, b).
        { rewrite -red_ax_uwalkNone. by destruct (red_ax_uwalkNone' p b) as [<- _]. }
        apply /eqP; cbn; rewrite !SubK; cbn.
        assert (source e <> source (other_cut Hcut)).
        { intro Hc.
          destruct (red_ax_degenerate_source Hcut Hax) as [Hc' _].
          specialize (Hc' Hc).
          contradict Hf.
          by rewrite -Hc' C0 Hcut. }
        rewrite Hf !SubK /red_ax_left_1 Hta.
        case_if.
      * assert (F : Some f \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e))).
        { rewrite !in_set. splitb; cbn; apply /eqP => // Hc.
          - assert (Hc' : f \in edges_at_out (source e)) by by rewrite in_set Hc.
            contradict Hc'; apply /negP.
            rewrite other_ax_set !in_set.
            splitb; apply /eqP; trivial.
            intro; subst f; contradict Hf.
            by rewrite Hcut.
          - assert (Hc' : f \in edges_at_in (target e)) by by rewrite in_set Hc.
            contradict Hc'; apply /negP.
            rewrite other_cut_set !in_set.
            splitb; apply /eqP => ?; subst f; contradict Hf;
            by rewrite ?C0 Hcut. }
        exists (Sub (Some f) F, b).
        { by rewrite -red_ax_uwalkSome. }
        apply /eqP; cbn. rewrite Hf !SubK /red_ax_left_1 -Hta.
        case_if.
    + assert (other_cut Hcut != other_ax Hax).
      { apply /eqP => Hc.
        clear u; contradict A; apply /negP.
        rewrite !in_set; cbn.
        apply red_ax_degenerate_source in Hc.
        rewrite -Hc. caseb. }
      assert (switching (other_ax Hax) \notin map (fun x => switching x.1) (red_ax_uwalk p)).
      { apply /negP => /mapP [[a c] Hin Heq]. cbn in Heq.
        contradict u; apply /negP; rewrite negb_involutive.
        destruct (eq_comparable a (other_ax Hax)) as [ | Hneq].
        - subst a.
          destruct (red_ax_uwalkNone' p c) as [Hin' _].
          rewrite Hin' red_ax_uwalkNone in Hin.
          apply (map_f (fun x => switching x.1) Hin).
        - assert (Hta := switching_eq Heq).
          assert (A' : Some a \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)).
          { rewrite !in_set; cbn. rewrite -Hta.
            assert (target (other_ax Hax) <> target e).
            { intro.
              enough (Hdone : other_cut Hcut = other_ax Hax) by by rewrite_all Hdone; rewrite_all eq_refl.
              by apply red_ax_degenerate_target. }
            splitb; apply /eqP; try by [].
            intro Hc.
            assert (Hc' : a \in edges_at_out (source e)) by by rewrite in_set Hc.
            contradict Hc'; apply /negP.
            rewrite other_ax_set !in_set.
            splitb; apply /eqP; trivial.
            intros ?; by subst a. }
         rewrite red_ax_uwalkSome in Hin.
         assert (Hl : vlabel (target (other_ax Hax)) = ⅋).
         { revert Heq.
           rewrite /switching -Hta. case_if.
           - by apply /eqP; cbn; apply /eqP.
           - assert (Hc : Some (other_ax Hax) == Some a) by by apply /eqP.
             by revert Hc; cbn => /eqP ?; subst a. }
         assert (Hs : switching (Sub None A : edge (red_ax_graph_left Hcut Hax)) =
           switching (Sub (Some a) A' : edge (red_ax_graph_left Hcut Hax))).
         { apply /eqP; rewrite /switching /= Hl.
           rewrite Hta in Hl.
           rewrite Hl /red_ax_left /red_ax_left_1; cbn; rewrite !SubK -!Hta.
           case_if. }
         rewrite Hs.
         apply (map_f (fun x => switching x.1) Hin). }
      assert(switching (other_cut Hcut) \notin map (fun x => switching x.1) (red_ax_uwalk p)).
      { unfold switching at 1; rewrite C0 Hcut; cbn.
        apply /negP => /mapP [[a c] Hin Heq]. cbn in Heq.
        assert (a = other_cut Hcut).
        { revert Heq. unfold switching => /eqP; cbn => /eqP.
          case_if.
          assert (Ha : vlabel (target a) = ⅋) by by (apply /eqP; cbn; apply /eqP).
          enough (vlabel (target e) <> cut) by by [].
          rewrite -C0.
          replace (other_cut Hcut) with (left (target a)).
          rewrite left_e ?Ha; caseb. }
        subst a.
        destruct (red_ax_uwalkNone' p c) as [_ Hin'].
        rewrite Hin' red_ax_uwalkNone in Hin.
        contradict u; apply /negP; rewrite negb_involutive.
        apply (map_f (fun x => switching x.1) Hin). }
      assert (switching e \notin map (fun x => switching x.1) (red_ax_uwalk p)).
      { unfold switching at 1; rewrite Hcut; cbn.
        apply /negP => /mapP [[a c] Hin Heq]. cbn in Heq.
        assert (a = e).
        { revert Heq. unfold switching => /eqP; cbn => /eqP.
          case_if.
          assert (Ha : vlabel (target a) = ⅋) by by (apply /eqP; cbn; apply /eqP).
          enough (vlabel (target e) <> cut) by by [].
          replace e with (left (target a)).
          rewrite left_e ?Ha; caseb. }
        subst a.
        rewrite -(negb_involutive c) red_ax_uwalkNone in Hin.
        contradict u; apply /negP; rewrite negb_involutive.
        apply (map_f (fun x => switching x.1) Hin). }
      assert (other_cut Hcut != (if eqb_rule (vlabel (target (other_ax Hax))) (⅋)
        then left (target (other_ax Hax)) else other_ax Hax)).
      { case_if. apply /eqP => Hc.
        enough (Hf : vlabel (target e) = ⅋) by by rewrite Hcut in Hf.
        assert (vlabel (target (other_ax Hax)) = ⅋) by (by apply /eqP; cbn; apply /eqP).
        rewrite -C0 Hc left_e; caseb. }
      assert (e != (if eqb_rule (vlabel (target (other_ax Hax))) (⅋)
        then left (target (other_ax Hax)) else other_ax Hax)).
      { case_if.
        2:{ by apply/eqP; apply nesym; apply /eqP. }
        apply /eqP => Hc.
        assert (vlabel (target (other_ax Hax)) = ⅋) by by (apply /eqP; cbn; apply /eqP).
        enough (vlabel (target (other_ax Hax)) <> ⅋) by by [].
        rewrite -(left_e (v := target (other_ax Hax))) -?Hc ?Hcut; caseb. }
      destruct b; splitb; cbn; rewrite ?C0 ?A0 ?Hcut ?Hax //; cbn.
      all: by apply/eqP; apply nesym; apply /eqP.
  - clear; by induction p as [ | ([[? | ] ?], []) ? ?].
Qed. (* TODO simplifier *)

Definition red_ax_upath (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (u v : red_ax_graph_left Hcut Hax) :
  Supath switching u v -> Supath switching (val u) (val v) :=
  fun p => {| upval := red_ax_uwalk (upval p) ; upvalK := red_ax_upathK (upvalK p) |}.

Lemma red_ax_uacyclic (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  uacyclic (switching (G := G)) -> uacyclic (switching (G := red_ax_geos Hcut Hax)).
Proof.
  intros A ? P.
  specialize (A _ (red_ax_upath P)).
  apply /eqP; cbn; apply /eqP.
  by destruct P as [[ | [[[? | ] ?] []] ?] ?].
Qed.


Unset Mangle Names.

Fixpoint red_ax_uwalk' (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (p : @upath _ _ G) : @upath _ _ (red_ax_graph Hcut Hax) :=
  match p with
  | [::] => [::]
  | (a, b) :: q => if @boolP (Some a \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))
    is AltTrue p then (Sub (Some a) p, b) :: red_ax_uwalk' Hcut Hax q
    else if @boolP (None \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))
      is AltTrue p then (Sub None p, b) :: behead (behead (red_ax_uwalk' Hcut Hax q))
      else [::]
  end.
(* Fixpoint red_ax_uwalk' (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (p : @upath _ _ G) : @upath _ _ (red_ax_graph Hcut Hax) :=
  match p with
  | [::] => [::]
  | (a, b) :: q => if @boolP (Some a \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))
    is AltTrue p then (Sub (Some a) p, b) :: red_ax_uwalk' Hcut Hax q
    else if a == e then
      if @boolP (None \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))
      is AltTrue p then (Sub None p, b) :: red_ax_uwalk' Hcut Hax q
      else red_ax_uwalk' Hcut Hax q
      else red_ax_uwalk' Hcut Hax q
  end. *)

Lemma red_ax_uwalk'Ax (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (p : @upath _ _ G) :
  forall (b : bool) (u v : G) (U : u \in [set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)
  (V : v \in [set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e),
  uwalk u v ((other_ax Hax, b) :: p) -> p = (e, ~~b) :: (other_cut Hcut, b) :: behead (behead p).
Proof.
Admitted.

Lemma red_ax_uwalk'Cut (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (p : @upath _ _ G) :
  forall (b : bool) (u v : G) (U : u \in [set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)
  (V : v \in [set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e),
  uwalk u v ((other_cut Hcut, b) :: p) -> p = (e, ~~b) :: (other_ax Hax, b) :: behead (behead p).
Proof.
Admitted.
(* TODO remplacer 1 arete par un chemin fait correct avant = correct apres *)

Lemma red_ax_uwalk'K (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (p : @upath _ _ G) :
  forall (u v : G) (U : u \in [set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)
  (V : v \in [set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e),
  uwalk u v p -> @uwalk _ _ (red_ax_graph Hcut Hax) (Sub u U) (Sub v V) (red_ax_uwalk' Hcut Hax p).
Proof.
  induction p as [ | (a, b) p H]; try by [].
  move => u v U V. cbn => /andP[/eqP ? W]. subst u.
  case: {-}_ /boolP => [? | Hnin]; cbn.
  - rewrite !SubK. splitb.
    by apply H.
  - assert (Hin : endpoint (~~ b) a \in [set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e) by trivial.
    revert Hin Hnin.
    rewrite !in_set. cbn.
    move => /andP[? /andP[? _]].
(*   induction p as [ | (a, b) p H]; try by [].
  move => u v U V. cbn => /andP[/eqP ? W]. subst u.
  case: {-}_ /boolP => [? | Hc]; cbn.
  - rewrite !SubK. splitb.
    by apply H.
  - assert (endpoint b a \notin [set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e).
    { (* 
contradict U; apply /negP. revert Hc.
    rewrite !in_set; cbn.
    move =>/nandP[/nandP[Hc | /nandP[Hc | //]] | /nandP[Hc | /nandP[Hc | //]]];
    rewrite negb_involutive in Hc.
    revert Hc; move => /eqP Hc.
destruct b; cbn; caseb. *) admit. }
    case_if.
    + subst a.
      contradict U; apply /negP.
      rewrite !in_set; cbn.
      destruct b; caseb.
    + 
(* TODO montrer que a est other cut/ax (faire 2 cas selon b), puis FAUX *)
(* hyp à modifier *)
 *)
Abort.

Lemma red_ax_uconnected (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  uconnected (switching_left (G := G)) -> uconnected (switching_left (G := red_ax_geos Hcut Hax)).
Proof.
Abort.

Lemma red_tens_correct (G : geos) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  correct G -> correct (red_tens_geos Hcut Het Hep Htens Hparr).
Proof.
Abort.
*************************************************************)
(* TODO mettre tout ça au niveau de redcut et definir red one et red sur
des proof net plutot que des proof structures, ou faire un pour ps et un pour pn *)
(* TODO dire red cut iso à graph union ce qui bouge + ce qui bouge pas, plus facile pour faire des cas *)

End Atoms.
