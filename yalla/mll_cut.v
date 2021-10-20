(* Cut Elimination in Proof Nets *)(* TODO trop long à compiler *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype.
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
Notation base_graph := (graph (flat rule) (flat (formula * bool))).
Notation graph_data := (@graph_data atom).
Notation proof_structure := (@proof_structure atom).
Notation proof_net := (@proof_net atom).


(** * Axiom - cut reduction *)
(* TODO essayer de simplifier les preuves de cette partie red *)
(* The label on the added edge is the label of the other arrow of the ax node,
  meaning (dual (flabel e), ?) *)
Definition red_ax_graph_1 (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : base_graph :=
  G ∔ [source (other_cut Hcut), elabel (other_ax Hax), target (other_ax Hax)].

Definition red_ax_graph (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : base_graph :=
  induced ([set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)).

Lemma red_ax_degenerate_None (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  None \notin edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)
  <-> other_cut Hcut = other_ax Hax.
Proof.
  rewrite !in_set !andb_true_r /=. split.
  - move => /nandP[/nandP[/negPn/eqP-H | /negPn/eqP-H] | /nandP[/negPn/eqP-H | /negPn/eqP-H]].
    + contradict H. by apply no_source_cut.
    + apply other_ax_eq.
      rewrite H. splitb.
      apply other_cut_neq.
    + symmetry; apply other_cut_eq.
      rewrite H. splitb.
      apply other_ax_neq.
    + contradict H. by apply no_target_ax.
  - move => ->. rewrite other_ax_e. caseb.
Qed.

Definition red_ax_order_1 (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : seq (edge (red_ax_graph_1 Hcut Hax)) :=
  [seq if a == other_ax Hax then None else Some a | a <- order G].

Lemma red_ax_consistent_order (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  all (pred_of_set (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e))))
    (red_ax_order_1 Hcut Hax).
Proof.
  apply /allP => a A.
  destruct a as [a | ].
  - rewrite /edge_set. apply /setIdP.
    rewrite !in_set /=.
    assert (Hl : vlabel (target a) = c).
    { apply p_order.
      revert A => /mapP[b B /eqP-AB].
      enough (a = b) by by subst b.
      revert AB. case_if. }
    splitb; apply /eqP.
    + by apply no_source_cut.
    + intro Hc.
      assert (a = other_ax Hax).
      { apply other_ax_eq. splitb.
        intros ?; subst a.
        by rewrite Hcut in Hl. }
      subst a.
      contradict A; apply /negP.
      rewrite /red_ax_order_1.
      induction (order G) as [ | f F IH]; trivial.
      rewrite /= in_cons. splitb.
      destruct (eq_comparable f (other_ax Hax)) as [ | Neq]; [subst f | ];
      case_if.
      by apply /eqP; apply nesym.
    + intro Hc. by rewrite Hc Hcut in Hl.
    + by apply no_target_ax.
  - rewrite -in_set.
    destruct (red_ax_degenerate_None Hcut Hax) as [I _].
    apply /negPn/negP. rewrite memKset.
    apply (contra_not I).
    intro Hc.
    assert (Hl : vlabel (target (other_ax Hax)) = c).
    { apply p_order.
      revert A => /mapP[b B /eqP-AB].
      enough (other_ax Hax = b) by by subst b.
      revert AB. case_if. }
    contradict Hl.
    by rewrite -Hc other_cut_e Hcut.
Qed.

Definition red_ax_order (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : seq (edge (red_ax_graph Hcut Hax)) :=
  sval (all_sigP (red_ax_consistent_order Hcut Hax)).

Definition red_ax_graph_data (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : graph_data := {|
  graph_of := red_ax_graph Hcut Hax;
  order := red_ax_order _ _;
  |}.

Definition red_ax_transport (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : red_ax_graph Hcut Hax) :=
  fun (a : edge (red_ax_graph Hcut Hax)) => match val a with
  | None => if b then other_ax Hax else other_cut Hcut
  | Some a' => a'
  end.
Notation red_ax_transport_out := (@red_ax_transport _ _ _ _ false).
Notation red_ax_transport_in := (@red_ax_transport _ _ _ _ true).

Lemma red_ax_transport_inj (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : red_ax_graph Hcut Hax) :
  {in edges_at_outin b v &, injective (@red_ax_transport _ _ Hcut Hax b v)}.
Proof.
  destruct v as [v Hv]; intros [a A] [a' A'].
  rewrite !in_set /red_ax_transport; cbn; rewrite !SubK.
  move => /eqP ? /eqP ? ?; subst; apply /eqP; rewrite sub_val_eq SubK.
  destruct a as [a | ], a' as [a' | ]; subst; trivial;
  [contradict A | contradict A']; apply /negP.
  all: destruct b; rewrite !in_set /= ?other_ax_e ?other_cut_e; caseb.
Qed.

Lemma red_ax_transport_edges (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  edges_at_outin b v =
  [set red_ax_transport b (Sub v Hv) a | a in edges_at_outin b (Sub v Hv : red_ax_graph_data Hcut Hax)].
Proof.
  assert ((forall a, source a != target e) /\ forall a, target a != source e) as [? ?].
  { split; intros; apply /eqP.
    - by apply no_source_cut.
    - by apply no_target_ax. }
  assert (v != source e /\ v != target e) as [Hvs Hvt]
    by (revert Hv; rewrite !in_set; by move => /andP[? /andP[? _]]).
  apply /setP => a.
  rewrite Imset.imsetE !in_set.
  symmetry; apply /imageP; case_if.
  - assert (a <> e) by by (intro Hc; destruct b; subst; by rewrite_all eq_refl).
    destruct (eq_comparable a (other_cut Hcut)) as [Heqc | Hneqc];
    [ | destruct (eq_comparable a (other_ax Hax)) as [Heqa | Hneqa]]; subst.
    + destruct b.
      { contradict Hvt; apply /negP/negPn/eqP.
        apply other_cut_e. }
      assert (Hn : None \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)).
      { rewrite !in_set; cbn. splitb.
        apply /eqP => Hf.
        assert (Hin : other_ax Hax \in edges_at_in (target e))
          by by rewrite in_set Hf.
        revert Hin; rewrite other_cut_set !in_set => /orP[/eqP-Hin | /eqP-Hin].
        - contradict Hin.
          apply other_ax_neq.
        - contradict Hvs; apply /negP/negPn/eqP.
          by rewrite -Hin other_ax_e. }
      exists (Sub None Hn); trivial.
      by rewrite !in_set; cbn.
    + destruct b.
      2:{ contradict Hvs; apply /negP/negPn/eqP.
          apply other_ax_e. }
      assert (Hn : None \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)).
      { rewrite !in_set; cbn. splitb.
        apply /eqP => Hf.
        assert (Hin : other_cut Hcut \in edges_at_out (source e))
          by by rewrite in_set Hf.
        revert Hin. rewrite other_ax_set !in_set. move => /orP[/eqP Hin | /eqP Hin].
        - contradict Hin.
          apply other_cut_neq.
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

Lemma red_ax_transport_flabel (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) (b : bool) (v : G)
  (Hv : v \in [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)) :
  forall a, flabel a = flabel (red_ax_transport b (Sub v Hv) a).
Proof.
  unfold red_ax_transport.
  intros [[a | ] Ha]; trivial; cbn.
  destruct b; trivial.
  destruct (p_ax_cut_bis G) as [Hpax Hpcut].
  transitivity (dual (flabel e)); [symmetry | ].
  - specialize (Hpax (source e) Hax).
    unfold true_on2 in Hpax.
    specialize (Hpax e (source_in_edges_at_out e)).
    unfold is_dual_f, is_dual in Hpax.
    by revert Hpax => /eqP Hpax.
  - specialize (Hpcut (target e) Hcut).
    unfold true_on2 in Hcut.
    specialize (Hpcut e (target_in_edges_at_in e));
    unfold is_dual_f, is_dual in Hpcut.
    by revert Hpcut => /eqP Hpcut.
Qed.

Lemma red_ax_p_deg (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_degree (red_ax_graph Hcut Hax).
Proof.
  unfold proper_degree.
  intros b [v Hv]; cbn.
  rewrite -(p_deg b v) (red_ax_transport_edges _ Hv) card_in_imset //.
  apply red_ax_transport_inj.
Qed.


Lemma red_ax_p_ax_cut (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_ax_cut (red_ax_graph Hcut Hax).
Proof.
  unfold proper_ax_cut.
  intros b [v Hv] Hl; cbn in Hl.
  destruct (p_ax_cut Hl) as [el [er H]].
  revert H; rewrite (red_ax_transport_edges b Hv) Imset.imsetE 2!in_set.
  move => [/imageP [El ? ?] [/imageP [Er ? ?] Eq]]. subst el er.
  exists El, Er. splitb.
  by rewrite !(red_ax_transport_flabel b Hv).
Qed.

Lemma red_ax_p_tens_parr (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_tens_parr (red_ax_graph Hcut Hax).
Proof.
  unfold proper_tens_parr.
  intros b [v Hv] Hl; cbn in Hl.
  destruct (p_tens_parr Hl) as [el [er [ec [Lt [Ll [Rt [Rl [Ct Cl]]]]]]]].
  assert (Lt' : el \in edges_at_in (v : graph_of _)) by trivial.
  revert Lt'; rewrite (red_ax_transport_edges true Hv) => /imsetP[el' Lt' ?]. subst el.
  assert (Rt' : er \in edges_at_in (v : graph_of _)) by trivial.
  revert Rt'; rewrite (red_ax_transport_edges true Hv) => /imsetP[er' Rt' ?]. subst er.
  assert (Ct' : ec \in edges_at_out (v : graph_of _)) by trivial.
  revert Ct'; rewrite (red_ax_transport_edges false Hv) => /imsetP[ec' Ct' ?]. subst ec.
  rewrite -!(red_ax_transport_flabel) in Cl.
  exists el', er', ec'. splitb.
  - destruct el' as [[el' | ] El']; cbnb.
  - destruct er' as [[er' | ] Er']; cbnb.
Qed.

Lemma red_ax_p_noleft (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_noleft (red_ax_graph Hcut Hax).
Proof. intros [[v | ] Hv] Hl; by apply p_noleft. Qed.

Lemma red_ax_p_order (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proper_order (red_ax_graph_data Hcut Hax).
Proof.
  unfold proper_order, red_ax_graph_data, red_ax_order; cbn.
  destruct (p_order G).
  split.
  - intros [a A]; cbn.
    rewrite in_seq_sig !SubK -(proj2_sig (all_sigP _)) /red_ax_order_1.
    destruct a as [a | ].
    + apply (iff_stepl (A := a \in order G)); [ | by apply iff_sym].
      split.
      * intro In. apply /mapP.
        exists a; trivial.
        case_if. subst a.
        contradict A; apply /negP.
        rewrite !in_set /= other_ax_e. caseb.
      * move => /mapP[b B /eqP-AB].
        revert AB. case_if.
    + apply (iff_stepl (A := other_ax Hax \in order G)); [ | by apply iff_sym].
      split.
      * intro In. apply /mapP.
        exists (other_ax Hax); trivial. case_if.
      * move => /mapP[b B /eqP-AB].
        revert AB. case_if. by subst b.
  - rewrite uniq_seq_sig -(proj2_sig (all_sigP _)) /red_ax_order_1 map_inj_uniq //.
    move => ? ? /eqP. case_if.
Qed.

Definition red_ax_ps (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proof_structure := {|
  graph_data_of := red_ax_graph_data Hcut Hax;
  p_deg := @red_ax_p_deg _ _ _ _;
  p_ax_cut := @red_ax_p_ax_cut _ _ _ _;
  p_tens_parr := @red_ax_p_tens_parr _ _ _ _;
  p_noleft := @red_ax_p_noleft _ _ _ _;
  p_order := @red_ax_p_order _ _ _ _;
  |}.


(** Sequent of an axiom - cut reduction *)
Lemma red_ax_sequent_eq (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  sequent (red_ax_graph_data Hcut Hax) =
  [seq flabel e | e <- red_ax_order_1 Hcut Hax].
Proof.
  rewrite /red_ax_graph_data /red_ax_order /=.
  set l := sval (all_sigP _).
  rewrite (proj2_sig (all_sigP (red_ax_consistent_order Hcut Hax))).
  by rewrite -map_comp.
Qed.

Lemma red_ax_sequent (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  sequent (red_ax_ps Hcut Hax) = sequent G.
Proof.
  rewrite red_ax_sequent_eq /red_ax_order_1 /sequent -map_comp.
  apply eq_map => a /=.
  case_if.
Qed.

(** Decreasing number of vertices *)
Lemma red_ax_nb (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
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


(** Correctness *)
Definition red_ax_G (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut) (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :=
  @invert_edge_graph _ _
  (@extend_edge_graph _
    (@extend_edge_graph _ (red_ax_graph Hcut Hax) (Sub None N) cut (dual (flabel e)) (flabel e))
    (Some (Sub None N)) ax (flabel e) (dual (flabel e)))
  None.

Definition red_ax_iso_v_bij_fwd (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  red_ax_G N -> G :=
  fun v => match v with
  | Some (Some (exist u _)) => u
  | Some None               => target e
  | None                    => source e
  end.

Definition red_ax_iso_v_bij_bwd (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  G -> red_ax_G N :=
  fun v => if @boolP _ is AltTrue p then Some (Some (Sub v p))
    else if v == source e then None else Some None.

Lemma red_ax_iso_v_bijK (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
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

Lemma red_ax_iso_v_bijK' (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  cancel (red_ax_iso_v_bij_bwd N) (@red_ax_iso_v_bij_fwd _ _ _ _ N).
Proof.
  intro v; unfold red_ax_iso_v_bij_bwd.
  case: {-}_ /boolP => [// | ].
  rewrite !in_set => /nandP[/negPn /eqP ? | /nandP[/negPn /eqP ? | //]]; subst; case_if.
Qed.

Definition red_ax_iso_v (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) := {|
  bij_fwd := @red_ax_iso_v_bij_fwd _ _ _ _ N;
  bij_bwd:= red_ax_iso_v_bij_bwd N;
  bijK:= @red_ax_iso_v_bijK _ _ _ _ _;
  bijK':= red_ax_iso_v_bijK' _;
  |}.

Definition red_ax_iso_e_bij_fwd (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  edge (red_ax_G N) -> edge G :=
  fun a => match a with
  | None                            => e
  | Some None                       => other_cut Hcut
  | Some (Some (exist None _))      => other_ax Hax
  | Some (Some (exist (Some a) _))  => a
  end.

Definition red_ax_iso_e_bij_bwd (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  edge G -> edge (red_ax_G N) :=
  fun a => if @boolP _ is AltTrue p then Some (Some (Sub (Some a) p))
    else if a == e then None
      else if a == other_ax Hax then Some (Some (Sub None N))
        else Some None.

Lemma red_ax_iso_e_bijK (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  cancel (@red_ax_iso_e_bij_fwd _ _ _ _ N) (@red_ax_iso_e_bij_bwd _ _ _ _ N).
Proof.
  intros [[[[a | ] A] | ] | ]; cbn;
  unfold red_ax_iso_e_bij_bwd; case: {-}_ /boolP => [Hc | /negP ?] //.
  - cbnb.
  - contradict Hc; apply /negP.
    rewrite !in_set /= other_ax_e. caseb.
  - assert (other_ax Hax == e = false) as -> by (apply /eqP; apply other_ax_neq).
    case_if. cbnb.
  - contradict Hc; apply /negP.
    rewrite !in_set /= other_cut_e. caseb.
  - assert (other_cut Hcut == e = false) as -> by (apply /eqP; apply other_cut_neq).
    enough (other_cut Hcut == other_ax Hax = false) as -> by trivial.
    apply /eqP => Hc. apply red_ax_degenerate_None in Hc. by contradict Hc; apply /negP/negPn.
  - contradict Hc; apply /negP.
    rewrite !in_set. caseb.
  - case_if.
Qed.

Lemma red_ax_iso_e_bijK' (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  cancel (@red_ax_iso_e_bij_bwd _ _ _ _ N) (@red_ax_iso_e_bij_fwd _ _ _ _ N).
Proof.
  intro a.
  unfold red_ax_iso_e_bij_bwd. case: {-}_ /boolP => [ | Ha]; cbnb.
  case_if.
  revert Ha; rewrite !in_set !andb_true_r /=
    => /nandP[/nandP[/negPn/eqP-Ha | /negPn/eqP-Ha] | /nandP[/negPn/eqP-Ha | /negPn/eqP-Ha]].
  - contradict Ha. by apply no_source_cut.
  - enough (a = other_ax Hax) by by [].
    by apply other_ax_eq.
  - symmetry; by apply other_cut_eq.
  - contradict Ha. by apply no_target_ax.
Qed.

Definition red_ax_iso_e (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
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
  - intros [[[[? | ] ?] | ] | ] []; cbnb.
    + by apply other_ax_e.
    + by apply other_cut_e.
  - by intros [[[? ?] | ] | ].
  - move => [[[[? | ] ?] | ] | ] /=;
    apply /eqP; cbn; splitb; apply /eqP; trivial.
    + destruct (p_ax_cut_bis G) as [Hpax _].
      specialize (Hpax _ Hax _ (source_in_edges_at_out e)).
      by revert Hpax => /eqP-Hpax.
    + destruct (p_ax_cut_bis G) as [_ Hpcut].
      specialize (Hpcut _ Hcut _ (target_in_edges_at_in e)).
      by revert Hpcut => /eqP-Hpcut.
    + apply p_noleft.
      rewrite other_cut_e Hcut. caseb.
    + apply p_noleft.
      rewrite Hcut. caseb.
Qed.

Definition red_ax_iso (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) := {|
  iso_v := red_ax_iso_v N;
  iso_e := red_ax_iso_e _;
  iso_d := pred0;
  iso_ihom := red_ax_iso_ihom _ |}.

Lemma red_ax_correct (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  correct G -> correct (red_ax_graph Hcut Hax).
Proof.
  intro C.
  enough (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))).
  { assert (C' := iso_correct (red_ax_iso N) C).
    by apply invert_edge_correct, extend_edge_correct, extend_edge_correct in C'. }
  apply /negPn /negP => N.
  apply red_ax_degenerate_None in N.
  destruct C as [A _].
  unfold uacyclic in A.
  enough (exists (p :  Supath switching (source e) (source e)),
    p <> supath_nil switching (source e)) as [p ?] by by specialize (A _ p).
  enough (P : supath switching (source e) (source e) (forward e :: backward (other_cut Hcut) :: nil))
    by by exists {| upval := _ ; upvalK := P |}.
  rewrite /supath /= in_cons in_nil orb_false_r {2}N other_cut_e other_ax_e.
  splitb. cbn.
  rewrite other_cut_e Hcut /=.
  apply /eqP; apply nesym, other_cut_neq.
Qed.
(* TODO faire un lemma qui donne N avant, pour ne pas à avoir se le trimballer de partout *)

Definition red_ax_pn (G : proof_net) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proof_net := {|
  ps_of := red_ax_ps Hcut Hax;
  p_correct := @red_ax_correct _ _ _ _ (p_correct G);
  |}.



(** * Tensor - cut reduction *)
Definition red_tens_graph_1 (G : base_graph) (v : G) (et ep : edge G) : base_graph :=
  induced (setT :\ source et :\ source ep :\ v).

Lemma red_tens_ineq_in (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  (forall a, source a != v) /\
  source (left_tens Htens) != source et /\
  source (right_tens Htens) != source et /\
  source (left_parr Hparr) != source ep /\
  source (right_parr Hparr) != source ep /\
  source (left_tens Htens) != source ep /\
  source (right_tens Htens) != source ep /\
  source (left_parr Hparr) != source et /\
  source (right_parr Hparr)!= source et.
Proof.
  assert (forall a, source a != v).
  { intro a; apply /eqP. by apply no_source_cut. }
  splitb; apply /eqP => Hc;
  [set a := Htens | set a := Htens | set a := Hparr | set a := Hparr
  |set a := Htens | set a := Htens | set a := Hparr | set a := Hparr];
  [set a' := et | set a' := et | set a' := ep | set a' := ep
  |set a' := et | set a' := et | set a' := ep | set a' := ep];
  [set b := Htens | set b := Htens | set b := Hparr | set b := Hparr
  |set b := Hparr | set b := Hparr | set b := Htens | set b := Htens];
  [set b' := et | set b' := et | set b' := ep | set b' := ep
  |set b' := ep | set b' := ep | set b' := et | set b' := et];
  [set f := left_tens (G := G) | set f := right_tens (G := G) | set f := left_parr (G := G) | set f := right_parr (G := G)
  |set f := left_tens (G := G) | set f := right_tens (G := G) | set f := left_parr (G := G) | set f := right_parr (G := G)];
  [set g := ccl_tens (G := G) | set g := ccl_tens (G := G) | set g := ccl_parr (G := G) | set g := ccl_parr (G := G)
  |set g := ccl_parr (G := G) | set g := ccl_parr (G := G) | set g := ccl_tens (G := G) | set g := ccl_tens (G := G)].
    all: assert (f _ a = g _ b /\ b' = g _ b) as [Hc0 Hc1] by (split; apply ccl_eq; caseb).
    all: assert (Hc2 : source a' = v) by
      (replace v with (target b'); rewrite Hc1 -Hc0 ?left_e ?right_e; caseb).
    all: contradict Hcut; by rewrite -Hc2 ?Htens ?Hparr.
Qed.

Lemma red_tens_in (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  source (left_tens Htens) \in [set: G] :\ (source et) :\ (source ep) :\ v /\
  source (right_tens Htens) \in [set: G] :\ (source et) :\ (source ep) :\ v /\
  source (left_parr Hparr) \in [set: G] :\ (source et) :\ (source ep) :\ v /\
  source (right_parr Hparr) \in [set: G] :\ (source et) :\ (source ep) :\ v.
Proof.
  destruct (red_tens_ineq_in Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? ?]]]]]]]].
  rewrite !in_set. splitb.
Qed.

Lemma red_tens_in_slt (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  source (left_tens Htens) \in setT :\ source et :\ source ep :\ v.
Proof. by destruct (red_tens_in Hcut Het Hep Htens Hparr) as [? [? [? ?]]]. Qed.

Lemma red_tens_in_srt (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  source (right_tens Htens) \in setT :\ source et :\ source ep :\ v.
Proof. by destruct (red_tens_in Hcut Het Hep Htens Hparr) as [? [? [? ?]]]. Qed.

Lemma red_tens_in_slp (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  source (left_parr Hparr) \in setT :\ source et :\ source ep :\ v.
Proof. by destruct (red_tens_in Hcut Het Hep Htens Hparr) as [? [? [? ?]]]. Qed.

Lemma red_tens_in_srp (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  source (right_parr Hparr) \in setT :\ source et :\ source ep :\ v.
Proof. by destruct (red_tens_in Hcut Het Hep Htens Hparr) as [? [? [? ?]]]. Qed.

Definition red_tens_graph (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :=
  (red_tens_graph_1 v et ep) ∔ cut ∔ cut
    ∔ [inl (inl (Sub (source (left_tens Htens)) (red_tens_in_slt Hcut Het Hep Htens Hparr))) ,
        (flabel (left_tens Htens), true) , inl (inr tt)]
    ∔ [inl (inl (Sub (source (right_tens Htens)) (red_tens_in_srt Hcut Het Hep Htens Hparr))) ,
        (flabel (right_tens Htens), true) , inr tt]
    ∔ [inl (inl (Sub (source (left_parr Hparr)) (red_tens_in_slp Hcut Het Hep Htens Hparr))) ,
        (flabel (left_parr Hparr), true) , inr tt]
    ∔ [inl (inl (Sub (source (right_parr Hparr)) (red_tens_in_srp Hcut Het Hep Htens Hparr))) ,
        (flabel (right_parr Hparr), true) , inl (inr tt)].

Lemma red_tens_cut_set (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
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

Lemma red_tens_ineq_if (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  left_tens Htens <> right_tens Htens /\ right_tens Htens <> left_tens Htens /\
  left_parr Hparr <> right_parr Hparr /\ right_parr Hparr <> left_parr Hparr /\
  left_tens Htens <> left_parr Hparr /\ left_parr Hparr <> left_tens Htens /\
  left_tens Htens <> right_parr Hparr /\ right_parr Hparr <> left_tens Htens /\
  left_parr Hparr <> right_tens Htens /\ right_tens Htens <> left_parr Hparr /\
  right_tens Htens <> right_parr Hparr /\ right_parr Hparr <> right_tens Htens.
Proof.
  assert (right_tens Htens <> left_tens Htens /\ right_parr Hparr <> left_parr Hparr) as [? ?].
  { split; apply nesym, left_neq_right. }
  assert (Hf : source et <> source ep) by (intro Hf; clear - Htens Hparr Hf; contradict Htens; by rewrite Hf Hparr).
  assert (left_tens Htens <> left_parr Hparr /\ left_tens Htens <> right_parr Hparr /\
    right_tens Htens <> left_parr Hparr /\ right_tens Htens <> right_parr Hparr) as [? [? [? ?]]].
  { splitb; intro Hc; contradict Hf.
    - rewrite -(left_e (tens_is_tensparr Htens)) -(left_e (parr_is_tensparr Hparr)). by f_equal.
    - rewrite -(left_e (tens_is_tensparr Htens)) -(right_e (parr_is_tensparr Hparr)). by f_equal.
    - rewrite -(right_e (tens_is_tensparr Htens)) -(left_e (parr_is_tensparr Hparr)). by f_equal.
    - rewrite -(right_e (tens_is_tensparr Htens)) -(right_e (parr_is_tensparr Hparr)). by f_equal. }
  assert (left_tens Htens <> right_tens Htens /\ left_parr Hparr <> right_parr Hparr /\
    left_parr Hparr <> left_tens Htens /\ right_parr Hparr <> left_tens Htens /\
    left_parr Hparr <> right_tens Htens /\ right_parr Hparr <> right_tens Htens)
    as [? [? [? [? [? ?]]]]] by (splitb; by apply nesym).
  splitb.
Qed.
(* TODO simplifier ces lemmes *)

Lemma red_tens_consistent_order (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  all (pred_of_set (edge_set (setT :\ source et :\ source ep :\ v))) (order G).
Proof.
  apply /allP => e E.
  rewrite /edge_set. apply /setIdP.
  rewrite !in_set.
  assert (Hl : vlabel (target e) = c) by by apply p_order.
(* TODO lemma si target e est un c alors il est non retire, et l'utilise ici et pour left/right toujours là *)
  splitb.
  - apply /eqP. by apply no_source_cut.
  - apply /eqP => Hc.
    assert (e = ep).
    { transitivity (ccl_parr Hparr); [ | symmetry];
      by apply ccl_eq. }
    subst e.
    by rewrite Hep Hcut in Hl.
  - apply /eqP => Hc.
    assert (e = et).
    { transitivity (ccl_tens Htens); [ | symmetry];
      by apply ccl_eq. }
    subst e.
    by rewrite Het Hcut in Hl.
  - apply /eqP => Hc; contradict Hl; by rewrite Hc ?Hcut ?Htens ?Hparr.
  - apply /eqP => Hc; contradict Hl; by rewrite Hc ?Hcut ?Htens ?Hparr.
  - apply /eqP => Hc; contradict Hl; by rewrite Hc ?Hcut ?Htens ?Hparr.
Qed.

Definition red_tens_order (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  seq (edge (red_tens_graph Hcut Het Hep Htens Hparr)) :=
  [seq Some (Some (Some (Some (inl (inl u))))) | u <- sval (all_sigP (red_tens_consistent_order Hcut Het Hep Htens Hparr))].

Definition red_tens_graph_data (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) : graph_data := {|
  graph_of := red_tens_graph Hcut Het Hep Htens Hparr;
  order := red_tens_order _ _ _ _ _;
  |}.

Definition red_tens_transport (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :=
  fun (a : edge (red_tens_graph_data Hcut Het Hep Htens Hparr)) => match a with
  | None => right_parr Hparr
  | Some None => left_parr Hparr
  | Some (Some None) => right_tens Htens
  | Some (Some (Some None)) => left_tens Htens
  | Some (Some (Some (Some (inl (inl (exist a _)))))) => a
  | Some (Some (Some (Some (inl (inr a))))) => match a with end
  | Some (Some (Some (Some (inr a)))) => match a with end
  end.

Lemma red_tens_transport_inj (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  injective (@red_tens_transport _ _ Hcut _ _ Het Hep Htens Hparr).
Proof.
  unfold red_tens_transport.
  destruct (red_tens_ineq_if Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]].
  move => [[[[[[[a A] | []] | []] | ] | ] | ] | ] [[[[[[[b B] | []] | []] | ] | ] | ] | ]
    /eqP; cbn => /eqP E; subst; cbnb.
  all: (contradict A || contradict B); apply /negP.
  all: rewrite !in_set ?left_e ?right_e; caseb.
Qed.

Lemma red_tens_transport_edges (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (b : bool) (u : G) (Hu : u \in (setT :\ source et :\ source ep :\ v)),
  edges_at_outin b u =
  [set red_tens_transport a | a in edges_at_outin b (inl (inl (Sub u Hu)) : red_tens_graph_data Hcut Het Hep Htens Hparr)].
Proof.
  intros b u Hu; apply /setP => a.
  rewrite Imset.imsetE !in_set.
  symmetry; apply /imageP; case_if.
  - subst u.
    destruct (red_tens_ineq_in Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? ?]]]]]]]].
    assert (a <> et /\ a <> ep) as [? ?].
    { split; intros ?; subst; contradict Hu; apply /negP.
      all: rewrite !in_set; cbn.
      all: destruct b; rewrite ?Hep; caseb. }
    destruct (eq_comparable a (left_tens Htens));
    [ | destruct (eq_comparable a (left_parr Hparr))];
    [ | | destruct (eq_comparable a (right_tens Htens))];
    [ | | | destruct (eq_comparable a (right_parr Hparr))];
    try subst a.
    5:{ assert (Ina : a \in edge_set (setT :\ source et :\ source ep :\ v)).
        { rewrite !in_set; cbn. splitb.
          all: apply /eqP => Hf.
          - assert (a = ccl_parr Hparr /\ ep = ccl_parr Hparr)
              as [? ?] by (split; apply ccl_eq; caseb).
            by assert (a = ep) by by subst.
          - assert (a = ccl_tens Htens /\ et = ccl_tens Htens)
              as [? ?] by (split; apply ccl_eq; caseb).
            by assert (a = et) by by subst.
          - assert (Hin : a \in edges_at_in v) by by rewrite in_set Hf.
            by revert Hin; rewrite (red_tens_cut_set Hcut Het Hep Htens Hparr) !in_set => /orP[/eqP ? | /eqP ?].
          - assert (Hin : a \in edges_at_in (source ep)) by by rewrite in_set Hf.
            by revert Hin; rewrite (right_set (parr_is_tensparr Hparr)) ?in_set => /orP[/eqP ? | /eqP ?].
          - assert (Hin : a \in edges_at_in (source et)) by by rewrite in_set Hf.
            by revert Hin; rewrite (right_set (tens_is_tensparr Htens)) ?in_set => /orP[/eqP ? | /eqP ?]. }
        exists (Some (Some (Some (Some (inl (inl (Sub a Ina))))))); trivial.
        by rewrite !in_set; cbnb. }
    all: destruct b;
      [contradict Hu; apply /negP; rewrite !in_set ?left_e ?right_e; caseb | ].
    4: exists None; trivial.
    3: exists (Some (Some None)); trivial.
    2: exists (Some None); trivial.
    1: exists (Some (Some (Some None))); trivial.
    all: by rewrite !in_set; cbnb.
  - intros [[[[[[[[d ?] | []] | []] | ] | ] | ] | ] Hdin Hdeq].
    all: cbn in Hdeq; subst a.
    all: revert Hdin; rewrite !in_set /=.
    all: destruct b; cbn; rewrite ?SubK // => /eqP ? //.
Qed.


Lemma red_tens_transport_flabel (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (a : edge (red_tens_graph Hcut Het Hep Htens Hparr)), flabel (red_tens_transport a) = flabel a.
Proof. by intros [[[[[[[? ?] | []] | []] | ] | ] | ] | ]. Qed.

Lemma red_tens_transport_llabel (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  forall (a : edge (red_tens_graph Hcut Het Hep Htens Hparr)) w W,
  a \in edges_at_in (inl (inl (Sub w W)) : red_tens_graph Hcut Het Hep Htens Hparr) ->
  llabel (red_tens_transport a) = llabel a.
Proof. intros [[[[[[[? ?] | []] | []] | ] | ] | ] | ] w W; by rewrite // in_set. Qed.

Lemma red_tens_p_deg (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  proper_degree (red_tens_graph_data Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_degree, red_tens_graph_data.
  intros b [[[u Hu] | []] | []]; cbn.
  - rewrite -(p_deg b u) (red_tens_transport_edges _ _ _ _ _ _ Hu) card_imset //.
    apply red_tens_transport_inj.
  - assert (edges_at_in (inl (inr tt) : red_tens_graph_data Hcut Het Hep Htens Hparr) =
      [set Some (Some (Some None)); None] /\
      edges_at_out (inl (inr tt) : red_tens_graph_data Hcut Het Hep Htens Hparr) = set0) as [Hin Hout].
    { split; apply /setP; move => [[[[[[[? ?] | []] | []] | ] | ] | ] | ]; by rewrite !in_set. }
    destruct b; by rewrite ?Hin ?Hout ?cards2 ?cards0.
  - assert (edges_at_in (inr tt : red_tens_graph_data Hcut Het Hep Htens Hparr) =
      [set Some (Some None); Some None] /\
      edges_at_out (inr tt : red_tens_graph_data Hcut Het Hep Htens Hparr) = set0) as [Hin Hout].
    { split; apply /setP; move => [[[[[[[? ?] | []] | []] | ] | ] | ] | ]; by rewrite !in_set. }
    destruct b; by rewrite ?Hin ?Hout ?cards2 ?cards0.
Qed.

Lemma red_tens_p_ax_cut (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  proper_ax_cut (red_tens_graph Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_ax_cut.
  intros b w R.
  (* Get informations about the removed cut *)
  destruct (p_ax_cut_bis G) as [_ Hpcut].
  assert (Hvet : et \in edges_at_in v) by by rewrite in_set Het.
  specialize (Hpcut _ Hcut _ Hvet).
  unfold is_dual_f, is_dual in Hpcut; revert Hpcut => /eqP Hpcut.
  assert (Ht := p_tens_bis Htens); cbn in Ht.
  assert (Hp := p_parr_bis Hparr); cbn in Hp.
  assert (et = ccl_tens Htens /\ ep = ccl_parr Hparr) as [Hct Hcp] by (split; apply ccl_eq; caseb).
  rewrite -Hct in Ht;
  rewrite -Hcp in Hp.
  assert (Hoep : ep = other (pre_proper_cut Hcut) Hvet).
  { apply other_eq.
    - by rewrite in_set Hep.
    - intro Hc; clear - Hc Htens Hparr; contradict Hparr.
      by rewrite Hc Htens. }
  rewrite -Hoep Ht Hp {Hoep Hvet Hct Hcp Ht Hp} in Hpcut; cbn in Hpcut.
  inversion Hpcut as [[H0 H1]]; clear Hpcut.
  destruct w as [[[w W] | []] | []]; simpl in R.
  - destruct (p_ax_cut R) as [el [er H]].
    revert H; rewrite (red_tens_transport_edges _ _ _ _ _ _ W) Imset.imsetE 2!in_set.
    move => [/imageP[El ? HeEl] [/imageP[Er ? HeEr] Heq]]. subst el er.
    rewrite !red_tens_transport_flabel in Heq.
    exists El, Er. splitb.
  - destruct b; try by [].
    exists None, (Some (Some (Some None))).
    by rewrite !in_set H1 /=.
  - destruct b; try by [].
    exists (Some None), (Some (Some None)).
    by rewrite !in_set H0 /=.
Qed.

Lemma red_tens_p_tens_parr (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  proper_tens_parr (red_tens_graph Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_tens_parr.
  intros b [[[w W] | []] | []] Hl; cbn in Hl.
  all: try (destruct b; by contradict Hl).
  destruct (p_tens_parr Hl) as [el [er [ec H]]].
  revert H; rewrite !(red_tens_transport_edges _ _ _ _ _ _ W) Imset.imsetE !in_set.
  move => [/imageP[El Elin ?] [Hll [/imageP[Er Erin ?] [Hrl [/imageP[Ec Ecin ?] Heq]]]]].
  subst el er ec.
  rewrite (red_tens_transport_llabel Elin) in Hll.
  rewrite (red_tens_transport_llabel Erin) in Hrl.
  rewrite !red_tens_transport_flabel in Heq.
  exists El, Er, Ec. splitb.
Qed.

Lemma red_tens_p_noleft (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  proper_noleft (red_tens_graph Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_noleft.
  intros [[[[[[[f F] | []] | []] | ] | ] | ] | ] Hl; simpl in Hl; rewrite /llabel //=.
  by apply p_noleft.
Qed.

Lemma red_tens_p_order (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  proper_order (red_tens_graph_data Hcut Het Hep Htens Hparr).
Proof.
  unfold proper_order, red_tens_graph_data, red_tens_order; cbn.
  split.
  - intros [[[[[[f | []] | []] | ] | ] | ] | ]; cbn.
    { rewrite mem_map; [ | repeat (apply inj_comp; trivial)].
      rewrite in_seq_sig SubK -(proj2_sig (all_sigP _)).
      apply p_order. }
    all: split; move => H //.
    all: contradict H; apply /negP.
    all: remember (sval (all_sigP _)) as l; clear. 
    all: induction l as [ | ? ? L]; first by trivial.
    all: by rewrite map_cons in_cons L.
(* TODO by induction l. fait ramer Coq !!!!!!! *)
  - rewrite map_inj_uniq; [ | repeat (apply inj_comp; trivial)].
    rewrite uniq_seq_sig -(proj2_sig (all_sigP _)).
    apply p_order.
Qed.

Definition red_tens_ps (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) : proof_structure := {|
  graph_data_of := red_tens_graph_data Hcut Het Hep Htens Hparr;
  p_deg := @red_tens_p_deg _ _ _ _ _ _ _ _ _;
  p_ax_cut := @red_tens_p_ax_cut _ _ _ _ _ _ _ _ _;
  p_tens_parr := @red_tens_p_tens_parr _ _ _ _ _ _ _ _ _;
  p_noleft := @red_tens_p_noleft _ _ _ _ _ _ _ _ _;
  p_order := @red_tens_p_order _ _ _ _ _ _ _ _ _;
  |}.


(** Sequent of an tensor - cut reduction *)
Lemma red_tens_sequent (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  sequent (red_tens_graph_data Hcut Het Hep Htens Hparr) = sequent G.
Proof.
  transitivity ([seq flabel (@red_tens_transport _ _ Hcut _ _ Het Hep Htens Hparr u) |
    u <- red_tens_order Hcut Het Hep Htens Hparr]).
  { apply eq_map => ?. by rewrite red_tens_transport_flabel. }
  rewrite /red_tens_order -map_comp.
  transitivity ([seq flabel u | u <-
    [seq val u | u <- sval (all_sigP (red_tens_consistent_order Hcut Het Hep Htens Hparr))]]).
  2:{ by rewrite -(proj2_sig (all_sigP _)). }
  rewrite -map_comp.
  apply (@eq_in_map _); move => [a A].
  by rewrite in_seq_sig !SubK -(proj2_sig (all_sigP _)).
Qed.


(** Decreasing number of vertices *)
Lemma red_tens_nb (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  #|red_tens_graph Hcut Het Hep Htens Hparr| = #|G| - 1.
Proof.
  assert (source et <> source ep).
  { intro Hc. contradict Htens.
    by rewrite Hc Hparr. }
  set f := fun (u : red_tens_graph Hcut Het Hep Htens Hparr) => match u with
  | inl (inl u) => val u
  | inl (inr _) => source et
  | inr _ => source ep
  end.
  assert (injective f).
  { assert (source ep <> source et) by by apply nesym.
    intros [[[u Hu] | []] | []] [[[u' Hu'] | []] | []]; rewrite /f ?SubK; intro Heq; cbnb.
    all: revert Hu || revert Hu'; rewrite !in_set Heq;
      by move => /andP[/eqP _ /andP[/eqP ? /andP[/eqP ? _]]]. }
  rewrite -(card_imset (f := f)) //.
  assert (#|setT :\ v| = #|G| - 1) as <-.
  { rewrite -cardsT [in RHS](cardsD1 v) in_set. lia. }
  apply eq_card; intro u.
  rewrite Imset.imsetE !in_set andb_true_r.
  destruct (eq_comparable u v) as [ | Hneq].
  - subst; rewrite eq_refl; cbn.
    apply /imageP; intros [[[[u Hin] | []] | []] _ Huv]; rewrite /f ?SubK in Huv.
    + revert Hin; rewrite !in_set; cbn => /andP[/eqP ? /andP[/eqP ? /andP[/eqP ? _]]].
      by subst.
    + clear - Htens Huv Hcut; contradict Htens.
      by rewrite -Huv Hcut.
    + clear - Hparr Huv Hcut; contradict Hparr.
      by rewrite -Huv Hcut.
  - transitivity true.
    2:{ symmetry; by apply /negP /negP /eqP. }
    apply /imageP.
    destruct (eq_comparable u (source et));
    [ | destruct (eq_comparable u (source ep))].
    + by exists (inl (inr tt)).
    + by exists (inr tt).
    + assert (Hin : u \in setT :\ source et :\ source ep :\ v) by
        (rewrite !in_set; cbn; splitb; by apply /eqP).
      by exists (inl (inl (Sub u Hin))).
Qed.


(** Correctness *)
Lemma red_tens_ineq_switching (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  switching et <> switching ep /\
  switching (left_tens Htens) <> switching (right_tens Htens) /\
  switching (left_tens Htens) <> switching et /\
  switching (left_tens Htens) <> switching ep /\
  switching (left_tens Htens) <> switching (left_parr Hparr) /\
  switching (left_tens Htens) <> switching (right_parr Hparr) /\
  switching (right_tens Htens) <> switching et /\
  switching (right_tens Htens) <> switching ep /\
  switching (right_tens Htens) <> switching (left_parr Hparr) /\
  switching (right_tens Htens) <> switching (right_parr Hparr) /\
  switching et <> switching (left_parr Hparr) /\
  switching ep <> switching (left_parr Hparr) /\
  switching et <> switching (right_parr Hparr) /\
  switching ep <> switching (right_parr Hparr).
Proof.
  split.
  { cbnb. rewrite Het Hep Hcut /=. cbnb. intro Hs.
    enough (vlabel (source et) <> ⊗) by by [].
    by rewrite Hs Hparr. }
  split.
  { cbnb. rewrite left_e ?right_e !Htens /=; caseb. cbnb.
    apply left_neq_right. }
  splitb => Hs.
  all: apply switching_eq in Hs.
  all: rewrite ?left_e ?right_e in Hs; caseb.
  all: enough (vlabel v <> cut) by by [].
  all: try (rewrite -Het Hs).
  all: try (rewrite -Het -Hs).
  all: try (rewrite -Hep Hs).
  all: try (rewrite -Hep -Hs).
  all: try rewrite ?Htens ?Hparr //.
  all: enough (vlabel (source et) <> ⊗) by by [].
  all: by rewrite Hs ?Het ?Hep ?Hcut ?Hparr.
Qed.

Lemma red_tens_target_in (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  forall a f, target a = target f -> a \in edge_set (setT :\ source et :\ source ep :\ v) ->
  f \in edge_set (setT :\ source et :\ source ep :\ v).
Proof.
  move => a f T.
  rewrite !in_set; introb; splitb; apply /eqP => Hc.
  all: try by rewrite_all Hc.
  - contradict Hc. by apply no_source_cut.
  - assert (f = ep).
    { transitivity (ccl_parr Hparr); [ | symmetry]; apply ccl_eq; caseb. }
    subst f.
    by rewrite_all Hep.
  - assert (f = et).
    { transitivity (ccl_tens Htens); [ | symmetry]; apply ccl_eq; caseb. }
    subst f.
    by rewrite_all Het.
Qed.

Lemma red_tens_switching (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  forall a f A F,
  switching a = switching f ->
  switching (Some (Some (Some (Some (inl (inl (Sub a A)))))) : edge (red_tens_graph Hcut Het Hep Htens Hparr)) =
  switching (Some (Some (Some (Some (inl (inl (Sub f F)))))) : edge (red_tens_graph Hcut Het Hep Htens Hparr)).
Proof.
  move => a f A F /eqP.
  unfold switching; case_if; cbnb.
Qed.

Fixpoint red_tens_upath_bwd (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) (p : @upath _ _ (red_tens_graph Hcut Het Hep Htens Hparr))
  {struct p} : @upath _ _ G :=
  match p with
  | [::] => [::]
  | a :: p => (red_tens_transport a.1, a.2) :: red_tens_upath_bwd p
  end.

Lemma red_tens_upath_bwd_in (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  forall (p : @upath _ _ (red_tens_graph Hcut Het Hep Htens Hparr)) a A b,
  [forall b, (None, b) \notin p] -> [forall b, (Some None, b) \notin p] ->
  [forall b, (Some (Some None), b) \notin p] -> [forall b, (Some (Some (Some None)), b) \notin p] ->
  (a, b) \in red_tens_upath_bwd p ->
  (Some (Some (Some (Some (inl (inl (Sub a A)))))), b) \in p.
Proof.
  move => p; induction p as [ | f p IH] => // a A b N SN SSN SSSN.
  destruct f as ([[[[[[[f F] | []] | []] | ] | ] | ] | ], c);
  [ | by revert SSSN => /forallP /(_ c); rewrite in_cons => /norP [/eqP ? _]
    | by revert SSN => /forallP /(_ c); rewrite in_cons => /norP [/eqP ? _]
    | by revert SN => /forallP /(_ c); rewrite in_cons => /norP [/eqP ? _]
    | by revert N => /forallP /(_ c); rewrite in_cons => /norP [/eqP ? _]].
  rewrite !in_cons; cbnb.
  introb.
  { subst. apply /orP; left. splitb; by apply /eqP. }
  apply /orP; right.
  apply IH; try apply /forallP => d;
  [revert N |revert SN |revert SSN |revert SSSN | assumption].
  all: by move => /forallP /(_ d); rewrite in_cons => /norP [_ ->].
Qed.

Lemma red_tens_upath_Some (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋)
  (p : @upath _ _ (red_tens_graph Hcut Het Hep Htens Hparr)) :
  forall (u w : red_tens_graph Hcut Het Hep Htens Hparr),
  p <> nil -> supath switching u w p ->
  [forall b, (None, b) \notin p] -> [forall b, (Some None, b) \notin p] ->
  [forall b, (Some (Some None), b) \notin p] -> [forall b, (Some (Some (Some None)), b) \notin p] ->
  exists u' U' w' W', u = inl (inl (Sub u' U')) /\ w = inl (inl (Sub w' W')) /\
  supath switching u' w' (red_tens_upath_bwd p).
Proof.
  induction p as [ | a p IH] => // u w _ P N SN SSN SSSN.
  assert ([forall b, (None, b) \notin p] /\ [forall b, (Some None, b) \notin p] /\
    [forall b, (Some (Some None), b) \notin p] /\ [forall b, (Some (Some (Some None)), b) \notin p])
    as [N' [SN' [SSN' SSSN']]].
  { splitb; apply /forallP => b;
    [revert N | revert SN | revert SSN | revert SSSN].
    all: move  => /forallP /(_ b); by rewrite in_cons => /norP[_ ?]. }
  destruct a as ([[[[[[[a A] | []] | []] | ] | ] | ] | ], b);
  [ | by revert SSSN => /forallP /(_ b); rewrite in_cons => /norP [/eqP ? _]
    | by revert SSN => /forallP /(_ b); rewrite in_cons => /norP [/eqP ? _]
    | by revert SN => /forallP /(_ b); rewrite in_cons => /norP [/eqP ? _]
    | by revert N => /forallP /(_ b); rewrite in_cons => /norP [/eqP ? _]].
  clear SSSN SSN SN N.
  revert P; unfold supath at 1; cbn; rewrite in_cons
    => /andP[/andP[/andP[/eqP ? W] /andP[U0 U1]] /norP[_ N]]; subst u.
  assert (P : supath switching (inl (inl (Sub (endpoint b a) (induced_proof b (valP (exist _ a A))))) :
    red_tens_graph Hcut Het Hep Htens Hparr) w p) by splitb.
  destruct p as [ | f p].
  { exists (endpoint (~~ b) a), (induced_proof (~~ b) (valP (exist _ a A))),
      (endpoint b a), (induced_proof b (valP (exist _ a A))).
    revert W; cbn => /eqP ?; subst w.
    splitb. }
  assert (Hr : f :: p <> [::]) by by [].
  destruct (IH _ _ Hr P N' SN' SSN' SSSN') as [x [X [y [Y [Hx [Hy P']]]]]].
  clear Hr IH.
  revert Hx => /eqP Hx; cbn in Hx; rewrite !SubK in Hx; revert Hx => /eqP ?. subst w x.
  exists (endpoint (~~ b) a), (induced_proof (~~ b) (valP (exist _ a A))), y, Y.
  revert P'.
  remember (f :: p) as p'.
  unfold supath; cbn => /andP[/andP[W' U'] N''].
  splitb.
  revert U0; apply contra => /mapP [[d db] In Seq]; apply /mapP.
  set D := (red_tens_target_in Hcut Het Hep Htens Hparr (switching_eq Seq) A).
  exists (Some (Some (Some (Some (inl (inl (Sub d D)))))), db).
  - by apply red_tens_upath_bwd_in.
  - by apply red_tens_switching.
Qed.

Lemma red_tens_uacyclic_nocut (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  uacyclic (switching (G := G)) ->
  forall (p : @upath _ _ (red_tens_graph Hcut Het Hep Htens Hparr)),
  forall (u : red_tens_graph Hcut Het Hep Htens Hparr),
  supath switching u u p ->
  [forall b, (None, b) \notin p] -> [forall b, (Some None, b) \notin p] ->
  [forall b, (Some (Some None), b) \notin p] -> [forall b, (Some (Some (Some None)), b) \notin p] ->
  p = [::].
Proof.
  move => A p u P N SN SSN SSSN.
  destruct p as [ | a p]; trivial.
  assert (NN : a :: p <> [::]) by by [].
  destruct (red_tens_upath_Some NN P N SN SSN SSSN) as [? [? [u' [? [? [Hu'' P']]]]]]. subst u.
  revert Hu'' => /eqP; cbnb => /eqP ?. subst u'.
  specialize (A _ {| upval := _ ; upvalK := P' |}).
  contradict A; cbnb.
Qed.

Lemma red_tens_upath_fN (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  forall p u U w W,
  supath switching (inl (inl (Sub u U)) : red_tens_graph Hcut Het Hep Htens Hparr) (inl (inl (Sub w W))) p ->
  (forward None \in p -> exists l r, p = l ++ forward None :: backward (Some (Some (Some None))) :: r) /\
  (forward (Some None) \in p -> exists l r, p = l ++ forward (Some None) :: backward (Some (Some None)) :: r) /\
  (forward (Some (Some None)) \in p -> exists l r, p = l ++ forward (Some (Some None)) :: backward (Some None) :: r) /\
  (forward (Some (Some (Some None))) \in p -> exists l r, p = l ++ forward (Some (Some (Some None))) :: backward None :: r).
Proof.
  move => p u U w W P; splitb => In.
  all: destruct (in_elt_sub In) as [l [r ?]]; subst p.
  all: exists l, (behead r); f_equal; f_equal.
  all: destruct (supath_subKK P) as [_ R]; clear - R.
  all: revert R; rewrite /supath /= in_cons => /andP[/andP[/andP[_ ?] /andP[? _]] _].
  all: by destruct r as [ | ([[[[[[[? ?] | []] | []] | ] | ] | ] | ], []) ?].
Qed.

Lemma red_tens_upath_bN (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  forall p u U w W,
  supath switching (inl (inl (Sub u U)) : red_tens_graph Hcut Het Hep Htens Hparr) (inl (inl (Sub w W))) p ->
  (backward None \in p -> exists l r, p = l ++ forward (Some (Some (Some None))) :: backward None :: r) /\
  (backward (Some None) \in p -> exists l r, p = l ++ forward (Some (Some None)) :: backward (Some None) :: r) /\
  (backward (Some (Some None)) \in p -> exists l r, p = l ++ forward (Some None) :: backward (Some (Some None)) :: r) /\
  (backward (Some (Some (Some None))) \in p -> exists l r, p = l ++ forward None :: backward (Some (Some (Some None))) :: r).
Proof.
  move => p u U w W P.
  destruct (red_tens_upath_fN (supath_revK P)) as [N [SN [SSN SSSN]]].
  splitb => In; [set H := N | set H := SN | set H := SSN | set H := SSSN].
  1: assert (In' : forward None \in upath_rev p) by by rewrite (upath_rev_in p).
  2: assert (In' : forward (Some None) \in upath_rev p) by by rewrite (upath_rev_in p).
  3: assert (In' : forward (Some (Some None)) \in upath_rev p) by by rewrite (upath_rev_in p).
  4: assert (In' : forward (Some (Some (Some None))) \in upath_rev p) by by rewrite (upath_rev_in p).
  all: destruct (H In') as [l [r Hp]].
  all: exists (upath_rev (r : @upath _ _ (red_tens_graph Hcut Het Hep Htens Hparr))),
         (upath_rev (l : @upath _ _ (red_tens_graph Hcut Het Hep Htens Hparr))).
  all: by rewrite -(upath_rev_inv p) Hp upath_rev_cat /= -!cats1 -!catA.
Qed.

Lemma red_tens_NSSSN (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  forall p u U w W,
  supath switching (inl (inl (Sub u U)) : red_tens_graph Hcut Het Hep Htens Hparr) (inl (inl (Sub w W))) p ->
  [forall b, (None, b) \notin p] -> [forall b, (Some (Some (Some None)), b) \notin p].
Proof.
  intros p u U w W P.
  enough (Hd : forall b, (Some (Some (Some None)), b) \in p -> (None, ~~b) \in p).
  { move => /forallP H; apply /forallP => b; revert H => /(_ (~~b)). apply contra, Hd. }
  move => [] In.
  - destruct (red_tens_upath_fN P) as [_ [_ [_ H]]]. specialize (H In).
    destruct H as [l [r ?]]; subst p; clear.
    rewrite mem_cat !in_cons. caseb.
  - destruct (red_tens_upath_bN P) as [_ [_ [_ H]]]. specialize (H In).
    destruct H as [l [r ?]]; subst p; clear.
    rewrite mem_cat !in_cons. caseb.
Qed.

Lemma red_tens_SNSSN (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  forall p u U w W,
  supath switching (inl (inl (Sub u U)) : red_tens_graph Hcut Het Hep Htens Hparr) (inl (inl (Sub w W))) p ->
  [forall b, (Some None, b) \notin p] -> [forall b, (Some (Some None), b) \notin p].
Proof.
  intros p u U w W P.
  enough (Hd : forall b, (Some (Some None), b) \in p -> (Some None, ~~b) \in p).
  { move => /forallP H; apply /forallP => b; revert H => /(_ (~~b)). apply contra, Hd. }
  move => [] In.
  - destruct (red_tens_upath_fN P) as [_ [_ [H _]]]. specialize (H In).
    destruct H as [l [r ?]]; subst p; clear.
    rewrite mem_cat !in_cons. caseb.
  - destruct (red_tens_upath_bN P) as [_ [_ [H _]]]. specialize (H In).
    destruct H as [l [r ?]]; subst p; clear.
    rewrite mem_cat !in_cons. caseb.
Qed.

Lemma red_tens_upath_bwd_nin (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  forall (p : @upath _ _ (red_tens_graph Hcut Het Hep Htens Hparr)) b,
  [forall b, (None, b) \notin p] -> [forall b, (Some None, b) \notin p] ->
  [forall b, (Some (Some None), b) \notin p] -> [forall b, (Some (Some (Some None)), b) \notin p] ->
  (left_tens Htens, b) \notin red_tens_upath_bwd p /\
  (right_tens Htens, b) \notin red_tens_upath_bwd p /\
  (left_parr Hparr, b) \notin red_tens_upath_bwd p /\
  (right_parr Hparr, b) \notin red_tens_upath_bwd p /\
  (et, b) \notin red_tens_upath_bwd p /\
  (ep, b) \notin red_tens_upath_bwd p.
Proof.
  move => p b. induction p as [ | a p IH]; move => // N SN SSN SSSN /=.
  rewrite !in_cons; cbn. repeat (split).
  all: apply /norP; split; [ |
    apply IH; apply /forallP => c;
    [revert N | revert SN | revert SSN | revert SSSN];
    move => /forallP /(_ c);
    rewrite !in_cons; introb].
  all: destruct a as ([[[[[[[a A] | []] | []] | ] | ] | ] | ], c);
  [ | by revert SSSN => /forallP /(_ c); rewrite in_cons => /norP [/eqP ? _]
    | by revert SSN => /forallP /(_ c); rewrite in_cons => /norP [/eqP ? _]
    | by revert SN => /forallP /(_ c); rewrite in_cons => /norP [/eqP ? _]
    | by revert N => /forallP /(_ c); rewrite in_cons => /norP [/eqP ? _]].
  all: cbn; apply /nandP; left; apply /eqP => ?; subst a.
  all: clear - A Htens Hparr; contradict A; apply /negP.
  all: rewrite !in_set ?left_e ?right_e; caseb.
Qed. (* TODO mettre ça ailleurs, et plus généralement organiser cette partie lorsque acyc finie *)

Lemma red_tens_upath_bwd_nin_switching (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  forall (p : @upath _ _ (red_tens_graph Hcut Het Hep Htens Hparr)),
  [forall b, (None, b) \notin p] -> [forall b, (Some None, b) \notin p] ->
  [forall b, (Some (Some None), b) \notin p] -> [forall b, (Some (Some (Some None)), b) \notin p] ->
  switching (left_tens Htens) \notin [seq switching a.1 | a <- red_tens_upath_bwd p] /\
  switching (right_tens Htens) \notin [seq switching a.1 | a <- red_tens_upath_bwd p] /\
  switching (left_parr Hparr) \notin [seq switching a.1 | a <- red_tens_upath_bwd p] /\
  switching (right_parr Hparr) \notin [seq switching a.1 | a <- red_tens_upath_bwd p] /\
  switching et \notin [seq switching a.1 | a <- red_tens_upath_bwd p] /\
  switching ep \notin [seq switching a.1 | a <- red_tens_upath_bwd p].
Proof.
  move => p N SN SSN SSSN.
  splitb.
  all: apply /mapP; move => [[a b] In S].
  all: apply switching_eq in S; rewrite ?left_e ?right_e /= in S; caseb.
  all: destruct (red_tens_upath_bwd_nin b N SN SSN SSSN) as [? [? [? [? [? ?]]]]].
  all: assert (Hc := target_in_edges_at_in a).
  all: rewrite -S in Hc;
    (rewrite Het in Hc || rewrite Hep in Hc || rewrite (right_set (tens_is_tensparr Htens)) ?in_set in Hc
    || rewrite (right_set (parr_is_tensparr Hparr)) ?in_set in Hc; caseb).
  all: try (revert Hc => /orP[/eqP ? | /eqP ?]; subst a; by contradict In; apply /negP).
  all: rewrite (red_tens_cut_set Hcut Het Hep Htens Hparr) !in_set in Hc.
  all: revert Hc => /orP[/eqP ? | /eqP ?]; subst a; by contradict In; apply /negP.
Qed.

Lemma red_tens_upath_SomeNoneNot_ff (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  uacyclic (switching (G := G)) ->
  forall p u U,
  supath switching (inl (inl (Sub u U)) : red_tens_graph Hcut Het Hep Htens Hparr) (inl (inl (Sub u U))) p ->
  forward (Some None) \in p ->
  forward None \notin p.
Proof.
  move => A p u U P SN; apply /negP => N.
  destruct (red_tens_upath_fN P) as [_ [HSN [_ _]]]. specialize (HSN SN).
  destruct HSN as [l [r ?]]; subst p.
  clear SN.
  revert N; rewrite mem_cat !in_cons /= => /orP N.
  wlog : u U l r P N / forward None \in r.
  { destruct N as [N | N].
    2:{ move => /(_ _ _ _ _ P) H. apply H; caseb. }
    destruct (supath_subKK P) as [L _].
    assert (Hr : upath_target (inl (inl (Sub u U)) : red_tens_graph Hcut Het Hep Htens Hparr) l =
      source (Some None : edge (red_tens_graph Hcut Het Hep Htens Hparr))).
    { revert P => /andP[/andP[Wl _] _].
      by rewrite (uwalk_sub_middle Wl). }
    rewrite Hr {Hr} /= in L.
    destruct (red_tens_upath_fN L) as [HN [_ [_ _]]]. specialize (HN N).
    destruct HN as [g [m ?]]; subst l.
    assert (P' := supath_turnsK P).
    assert (Hr : [:: forward (Some None), backward (Some (Some None)) & r] ++ g ++
      [:: forward None, backward (Some (Some (Some None))) & m] = [::] ++
      [:: forward (Some None), backward (Some (Some None)) & r ++ g ++
      [:: forward None, backward (Some (Some (Some None))) & m]]) by by [].
    rewrite Hr {Hr} in P'.
    move => /(_ _ _ _ _ P') H. apply H; rewrite !mem_cat !in_cons; caseb. }
  clear N => N.
  replace (l ++ [:: forward (Some None), backward (Some (Some None)) & r]) with
    ((l ++ [:: forward (Some None); backward (Some (Some None))]) ++ r) in P by by rewrite -catA.
  destruct (supath_subKK P) as [_ R].
  assert (Hr : upath_source (inl (inl (Sub u U)) : red_tens_graph Hcut Het Hep Htens Hparr) r =
    source (Some (Some None) : edge (red_tens_graph Hcut Het Hep Htens Hparr))).
  { revert P => /andP[/andP[W _] _].
    by rewrite -(uwalk_sub_middle W) upath_target_cat. }
  rewrite Hr {Hr} /= in R.
  destruct (red_tens_upath_fN R) as [HN [_ [_ _]]]. specialize (HN N).
  destruct HN as [m [d ?]]; subst r.
  clear N R.
  rewrite -catA in P.
  assert (SN : [forall b, (Some None, b) \notin m]).
  { apply /forallP => b.
    assert (M := supath_nin b P).
    by revert M; repeat (rewrite ?mem_cat ?in_cons /=); introb. }
  assert (N : [forall b, (None, b) \notin m]).
  { apply /forallP => b.
    rewrite !catA in P.
    assert (M := supath_nin b P).
    by revert M; repeat (rewrite ?mem_cat ?in_cons /=); introb. }
  rewrite catA in P.
  assert (M := supath_subK P).
  rewrite upath_target_cat /= in M.
  assert (SSN := red_tens_SNSSN M SN).
  assert (SSSN := red_tens_NSSSN M N).
  assert (NN : m <> nil).
  { intros ?; subst m.
    revert M; rewrite /supath; cbnb => /andP[/andP[/eqP Hc _] _].
    enough (Pc : supath switching (source (right_tens Htens)) (source (right_parr Hparr))
      (forward (right_tens Htens) :: forward et :: backward ep :: backward (right_parr Hparr) :: nil)).
    { rewrite Hc in Pc.
      specialize (A _ {| upval := _ ; upvalK := Pc |}).
      contradict A; cbnb. }
    rewrite /supath /= !in_cons.
    destruct (red_tens_ineq_switching Hcut Het Hep Htens Hparr) as [? [_ [_ [_ [_ [_ [? [? [_ [? [_ [_ [? ?]]]]]]]]]]]]].
    repeat (apply /andP; split); repeat (apply /norP; split); trivial; apply /eqP;
    rewrite // ?right_e ?Het ?Hep; caseb. }
  destruct (red_tens_upath_Some NN M N SN SSN SSSN) as [x [X [y [Y [Hx [Hy Pxy]]]]]].
  revert Hx => /eqP; cbnb => /eqP ?; subst x.
  revert Hy => /eqP; cbnb => /eqP ?; subst y.
  enough (Pf : supath switching (source (right_parr Hparr)) (source (right_parr Hparr))
    (forward (right_parr Hparr) :: forward ep :: backward et :: backward (right_tens Htens) ::
    (@red_tens_upath_bwd _ _ Hcut _ _ Het Hep Htens Hparr m))).
  { specialize (A _ {| upval := _ ; upvalK := Pf |}).
    contradict A; cbnb. }
  revert Pxy => /andP[/andP[Wn Un] ?].
  rewrite /supath /= !in_cons.
  destruct (red_tens_ineq_switching Hcut Het Hep Htens Hparr) as [? [_ [_ [_ [_ [_ [? [? [_ [? [_ [_ [? ?]]]]]]]]]]]]].
  destruct (red_tens_upath_bwd_nin_switching N SN SSN SSSN) as [? [? [? [? [? ?]]]]].
  splitb; simpl; try (by apply /eqP; apply nesym); rewrite ?right_e ?Het ?Hep; caseb.
Qed.

Lemma red_tens_upath_SomeNoneNot_fb (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  uacyclic (switching (G := G)) ->
  forall p u U,
  supath switching (inl (inl (Sub u U)) : red_tens_graph Hcut Het Hep Htens Hparr) (inl (inl (Sub u U))) p ->
  forward (Some None) \in p ->
  backward None \notin p.
Proof.
  move => A p u U P SN; apply /negP => N.
  destruct (red_tens_upath_fN P) as [_ [HSN [_ _]]]. specialize (HSN SN).
  destruct HSN as [l [r ?]]; subst p.
  clear SN.
  revert N; rewrite mem_cat !in_cons /= => /orP N.
  wlog : u U l r P N / backward None \in r.
  { destruct N as [N | N].
    2:{ move => /(_ _ _ _ _ P) H. apply H; caseb. }
    destruct (supath_subKK P) as [L _].
    assert (Hr : upath_target (inl (inl (Sub u U)) : red_tens_graph Hcut Het Hep Htens Hparr) l =
      source (Some None : edge (red_tens_graph Hcut Het Hep Htens Hparr))).
    { revert P => /andP[/andP[Wl _] _].
      by rewrite (uwalk_sub_middle Wl). }
    rewrite Hr {Hr} /= in L.
    destruct (red_tens_upath_bN L) as [HN [_ [_ _]]]. specialize (HN N).
    destruct HN as [g [m ?]]; subst l.
    assert (P' := supath_turnsK P).
    assert (Hr : [:: forward (Some None), backward (Some (Some None)) & r] ++ g ++
      [:: forward (Some (Some (Some None))), backward None & m] = [::] ++
      [:: forward (Some None), backward (Some (Some None)) & r ++ g ++
      [:: forward (Some (Some (Some None))), backward None & m]]) by by [].
    rewrite Hr {Hr} in P'.
    move => /(_ _ _ _ _ P') H. apply H; rewrite !mem_cat !in_cons; caseb. }
  clear N => N.
  replace (l ++ [:: forward (Some None), backward (Some (Some None)) & r]) with
    ((l ++ [:: forward (Some None); backward (Some (Some None))]) ++ r) in P by by rewrite -catA.
  destruct (supath_subKK P) as [_ R].
  assert (Hr : upath_source (inl (inl (Sub u U)) : red_tens_graph Hcut Het Hep Htens Hparr) r =
    source (Some (Some None) : edge (red_tens_graph Hcut Het Hep Htens Hparr))).
  { revert P => /andP[/andP[W _] _].
    by rewrite -(uwalk_sub_middle W) upath_target_cat. }
  rewrite Hr {Hr} /= in R.
  destruct (red_tens_upath_bN R) as [HN [_ [_ _]]]. specialize (HN N).
  destruct HN as [m [d ?]]; subst r.
  clear N R.
  rewrite -catA in P.
  assert (SN : [forall b, (Some None, b) \notin m]).
  { apply /forallP => b.
    assert (M := supath_nin b P).
    by revert M; repeat (rewrite ?mem_cat ?in_cons /=); introb. }
  assert (N : [forall b, (None, b) \notin m]).
  { apply /forallP => b.
    rewrite !catA in P.
    assert (Hr : (((l ++ [:: forward (Some None); backward (Some (Some None))]) ++ m) ++
      [:: forward (Some (Some (Some None))), backward None & d]) = (((l ++
      [:: forward (Some None); backward (Some (Some None))]) ++ m ++
      [:: forward (Some (Some (Some None)))]) ++ backward None :: d)) by by rewrite -!catA.
    rewrite Hr {Hr} in P.
    assert (M := supath_nin b P).
    by revert M; repeat (rewrite ?mem_cat ?in_cons /=); introb. }
  rewrite catA in P.
  assert (M := supath_subK P).
  rewrite upath_target_cat /= in M.
  assert (SSN := red_tens_SNSSN M SN).
  assert (SSSN := red_tens_NSSSN M N).
  assert (NN : m <> nil).
  { intros ?; subst m.
    revert M; rewrite /supath; cbnb => /andP[/andP[/eqP Hc _] _].
    enough (Pc : supath switching (source (left_tens Htens)) (source (right_tens Htens))
      [:: forward (left_tens Htens); backward (right_tens Htens)]).
    { rewrite Hc in Pc.
      specialize (A _ {| upval := _ ; upvalK := Pc |}).
      contradict A; cbnb. }
    rewrite /supath /= !in_cons.
    destruct (red_tens_ineq_switching Hcut Het Hep Htens Hparr) as [_ [? [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ _]]]]]]]]]]]]].
    repeat (apply /andP; split); repeat (apply /norP; split); trivial; apply /eqP;
    rewrite // ?left_e ?right_e ?Het ?Hep; caseb. }
  destruct (red_tens_upath_Some NN M N SN SSN SSSN) as [x [X [y [Y [Hx [Hy Pxy]]]]]].
  revert Hx => /eqP; cbnb => /eqP ?; subst x.
  revert Hy => /eqP; cbnb => /eqP ?; subst y.
  enough (Pf : supath switching (source (left_tens Htens)) (source (left_tens Htens))
    (forward (left_tens Htens) :: backward (right_tens Htens) ::
    (@red_tens_upath_bwd _ _ Hcut _ _ Het Hep Htens Hparr m))).
  { specialize (A _ {| upval := _ ; upvalK := Pf |}).
    contradict A; cbnb. }
  revert Pxy => /andP[/andP[Wn Un] ?].
  rewrite /supath /= !in_cons.
  destruct (red_tens_ineq_switching Hcut Het Hep Htens Hparr) as [_ [? [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ _]]]]]]]]]]]]].
  destruct (red_tens_upath_bwd_nin_switching N SN SSN SSSN) as [? [? [? [? [? ?]]]]].
  splitb; simpl; try (by apply /eqP; apply nesym); apply /eqP; rewrite ?left_e ?right_e ?Het ?Hep; caseb.
Qed.

Lemma red_tens_upath_SomeNoneNot (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  uacyclic (switching (G := G)) ->
  forall p u U b,
  supath switching (inl (inl (Sub u U)) : red_tens_ps Hcut Het Hep Htens Hparr) (inl (inl (Sub u U))) p ->
  (Some None, b) \in p ->
  [forall c, (None, c) \notin p].
Proof.
  move => A p u U b.
  revert p u U.
  wlog: b / b = true.
  { move => /(_ true erefl) H p u U P SN. destruct b; [by apply (H _ _ _ P) | ].
    enough (Hd : [forall b, (None, b) \notin upath_rev p]).
    { apply /forallP => b. revert Hd => /forallP /(_ (~~b)).
      by rewrite (upath_rev_in p) negb_involutive. }
    apply (H _ _ _ (supath_revK P)).
    by rewrite (upath_rev_in p). }
  move => -> {b} p u U P SN.
  apply /forallPn. move => [[] /negPn N]; contradict N; apply /negP.
  - by apply (red_tens_upath_SomeNoneNot_ff A P).
  - by apply (red_tens_upath_SomeNoneNot_fb A P).
Qed.

Lemma red_tens_upath_NoneNot (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  uacyclic (switching (G := G)) ->
  forall p u U b,
  supath switching (inl (inl (Sub u U)) : red_tens_ps Hcut Het Hep Htens Hparr) (inl (inl (Sub u U))) p ->
  (None, b) \in p ->
  [forall c, (Some None, c) \notin p].
Proof.
  move => A p u U b P In.
  apply /forallPn; move => [c /negPn Hc].
  assert (Nin := red_tens_upath_SomeNoneNot A P Hc).
  revert Nin => /forallP /(_ b) Nin.
  by contradict In; apply /negP.
Qed.

Lemma red_tens_uacyclic_notcut_None (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  uacyclic (switching (G := G)) -> forall u U b p,
  supath switching (inl (inl (Sub u U)) : red_tens_ps Hcut Het Hep Htens Hparr) (inl (inl (Sub u U))) p ->
  (None, b) \in p ->
  p = [::].
Proof.
  move => A u U b.
  wlog: b / b = true.
  { move => /(_ true erefl) H p P N. destruct b; [by apply H | ].
    enough (Hd : upath_rev p = [::]).
    { destruct p as [ | [? ?] ?]; trivial. contradict Hd. apply rcons_nil. }
    apply H.
    - by apply supath_revK.
    - by rewrite (upath_rev_in p). }
  move => -> {b} p P N; cbn.
  assert (SN := red_tens_upath_NoneNot A P N).
  destruct (red_tens_upath_fN P) as [HN [_ [_ _]]]. specialize (HN N).
  destruct HN as [l [r ?]]; subst p.
  clear N.
  assert (P' : supath switching (source (Some (Some (Some None)) : edge (red_tens_graph Hcut Het Hep Htens Hparr)))
    (source (None : edge (red_tens_graph Hcut Het Hep Htens Hparr))) (r ++ l)).
  { clear - P.
    assert (P' := supath_turnsK P).
    assert (Hr : [:: forward None, backward (Some (Some (Some None))) & r] ++ l =
      [:: forward None; backward (Some (Some (Some None)))] ++ r ++ l) by by [].
    rewrite Hr {Hr} in P'.
    destruct (supath_subKK P') as [_ P''].
    revert P'; rewrite /supath => /andP[/andP[W _] _].
    by rewrite -(uwalk_sub_middle W) in P''. }
  assert (N' : [forall b, (None, b) \notin r ++ l]).
  { apply /forallP => b.
    assert (M := supath_nin b P).
    revert M; repeat (rewrite ?mem_cat ?in_cons /=); introb. splitb. }
  assert (SN' : [forall b, (Some None, b) \notin r ++ l]).
  { clear - SN. apply /forallP => b. revert SN => /forallP /(_ b).
    rewrite !mem_cat !in_cons. introb. splitb. }
  assert (SSN' := red_tens_SNSSN P' SN').
  assert (SSSN' := red_tens_NSSSN P' N').
  assert (NN' : r ++ l <> nil).
  { intros ?.
    assert (r = nil /\ l = nil) as [? ?] by by destruct r. subst r l.
    revert P; rewrite /supath cat0s => /andP[/andP[W _] _].
    revert W; cbn; rewrite !SubK => /andP[/eqP ? /eqP Hu]. subst u.
    enough (P : supath switching (source (left_tens Htens)) (source (right_parr Hparr))
      (forward (left_tens Htens) :: forward et :: backward ep :: backward (right_parr Hparr) :: nil)).
    { rewrite Hu in P.
      specialize (A _ {| upval := _ ; upvalK := P |}).
      contradict A; cbnb. }
    rewrite /supath /= !in_cons.
    destruct (red_tens_ineq_switching Hcut Het Hep Htens Hparr) as [? [_ [? [? [_ [? [_ [_ [_ [_ [_ [_ [? ?]]]]]]]]]]]]].
    repeat (apply /andP; split); repeat (apply /norP; split); trivial; apply /eqP;
    rewrite // ?left_e ?right_e ?Het ?Hep; caseb. }
  destruct (red_tens_upath_Some NN' P' N' SN' SSN' SSSN') as [x [X [y [Y [Hx [Hy Pxy]]]]]].
  revert Hx => /eqP; cbnb => /eqP ?; subst x.
  revert Hy => /eqP; cbnb => /eqP ?; subst y.
  enough (Pf : supath switching (source (right_parr Hparr)) (source (right_parr Hparr))
    (forward (right_parr Hparr) :: forward ep :: backward et :: backward (left_tens Htens) ::
    (@red_tens_upath_bwd _ _ Hcut _ _ Het Hep Htens Hparr (r ++ l)))).
  { specialize (A _ {| upval := _ ; upvalK := Pf |}).
    contradict A; cbnb. }
  revert Pxy => /andP[/andP[W Un] ?].
  rewrite /supath /= !in_cons.
  destruct (red_tens_ineq_switching Hcut Het Hep Htens Hparr) as [? [_ [? [? [_ [? [_ [_ [_ [_ [_ [_ [? ?]]]]]]]]]]]]].
  destruct (red_tens_upath_bwd_nin_switching N' SN' SSN' SSSN') as [? [? [? [? [? ?]]]]].
  splitb; simpl; try (by apply /eqP; apply nesym); rewrite // ?left_e ?right_e ?Het ?Hep; caseb.
Qed.

Lemma red_tens_uacyclic_notcut_SomeNone (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  uacyclic (switching (G := G)) -> forall u U b p,
  supath switching (inl (inl (Sub u U)) : red_tens_ps Hcut Het Hep Htens Hparr) (inl (inl (Sub u U))) p ->
  (Some None, b) \in p ->
  p = [::].
Proof.
  move => A u U b.
  wlog: b / b = true.
  { move => /(_ true erefl) H p P SN. destruct b; [by apply H | ].
    enough (Hd : upath_rev p = [::]).
    { destruct p as [ | [? ?] ?]; trivial. contradict Hd. apply rcons_nil. }
    apply H.
    - by apply supath_revK.
    - by rewrite (upath_rev_in p). }
  move => -> {b} p P SN; cbn.
  assert (N := red_tens_upath_SomeNoneNot A P SN).
  destruct (red_tens_upath_fN P) as [_ [HSN [_ _]]]. specialize (HSN SN).
  destruct HSN as [l [r ?]]; subst p.
  clear SN.
  assert (P' : supath switching (source (Some (Some None) : edge (red_tens_graph Hcut Het Hep Htens Hparr)))
    (source (Some None : edge (red_tens_graph Hcut Het Hep Htens Hparr))) (r ++ l)).
  { clear - P.
    assert (P' := supath_turnsK P).
    assert (Hr : [:: forward (Some None), backward (Some (Some None)) & r] ++ l =
      [:: forward (Some None); backward (Some (Some None))] ++ r ++ l) by by [].
    rewrite Hr {Hr} in P'.
    destruct (supath_subKK P') as [_ P''].
    revert P'; rewrite /supath => /andP[/andP[W _] _].
    by rewrite -(uwalk_sub_middle W) in P''. }
  assert (N' : [forall b, (None, b) \notin r ++ l]).
  { clear - N. apply /forallP => b. revert N => /forallP /(_ b).
    rewrite !mem_cat !in_cons. introb. splitb. }
  assert (SN' : [forall b, (Some None, b) \notin r ++ l]).
  { apply /forallP => b.
    assert (M := supath_nin b P).
    revert M; repeat (rewrite ?mem_cat ?in_cons /=); introb. splitb. }
  assert (SSN' := red_tens_SNSSN P' SN').
  assert (SSSN' := red_tens_NSSSN P' N').
  assert (NN' : r ++ l <> nil).
  { intros ?.
    assert (r = nil /\ l = nil) as [? ?] by by destruct r. subst r l.
    revert P; rewrite /supath cat0s => /andP[/andP[W _] _].
    revert W; cbn; rewrite !SubK => /andP[/eqP ? /eqP Hu]. subst u.
    enough (P : supath switching (source (right_tens Htens)) (source (left_parr Hparr))
      (forward (right_tens Htens) :: forward et :: backward ep :: backward (left_parr Hparr) :: nil)).
    { rewrite Hu in P.
      specialize (A _ {| upval := _ ; upvalK := P |}).
      contradict A; cbnb. }
    rewrite /supath /= !in_cons.
    destruct (red_tens_ineq_switching Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
    repeat (apply /andP; split); repeat (apply /norP; split); trivial; apply /eqP;
    rewrite // ?left_e ?right_e ?Het ?Hep; caseb. }
  destruct (red_tens_upath_Some NN' P' N' SN' SSN' SSSN') as [x [X [y [Y [Hx [Hy Pxy]]]]]].
  revert Hx => /eqP; cbnb => /eqP ?; subst x.
  revert Hy => /eqP; cbnb => /eqP ?; subst y.
  enough (Pf : supath switching (source (left_parr Hparr)) (source (left_parr Hparr))
    (forward (left_parr Hparr) :: forward ep :: backward et :: backward (right_tens Htens) ::
    (red_tens_upath_bwd (r ++ l)))).
  { specialize (A _ {| upval := _ ; upvalK := Pf |}).
    contradict A; cbnb. }
  revert Pxy => /andP[/andP[W Un] ?].
  rewrite /supath /= !in_cons.
  destruct (red_tens_ineq_switching Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
  destruct (red_tens_upath_bwd_nin_switching N' SN' SSN' SSSN') as [? [? [? [? [? ?]]]]].
  splitb; simpl; try (by apply /eqP; apply nesym); rewrite // ?left_e ?right_e ?Het ?Hep; caseb.
Qed.

Lemma red_tens_uacyclic_notcut (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  uacyclic (switching (G := G)) -> forall u U p,
  supath switching (inl (inl (Sub u U)) : red_tens_ps Hcut Het Hep Htens Hparr) (inl (inl (Sub u U))) p ->
  p = [::].
Proof.
  move => A u U p P.
  remember ([forall b, (None, b) \notin p]) as Hn eqn:N; symmetry in N. destruct Hn.
  - remember ([forall b, (Some None, b) \notin p]) as Hsn eqn:SN; symmetry in SN. destruct Hsn.
    + apply (red_tens_uacyclic_nocut A P); trivial.
      * by apply (red_tens_SNSSN P).
      * by apply (red_tens_NSSSN P).
    + revert SN => /negP/negP/forallPn [b /negPn SN].
      apply (red_tens_uacyclic_notcut_SomeNone A P SN).
  - revert N => /negP/negP/forallPn [b /negPn N].
    apply (red_tens_uacyclic_notcut_None A P N).
Qed.

Lemma red_tens_uacyclic (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  uacyclic (switching (G := G)) ->
  uacyclic (switching (G := red_tens_ps Hcut Het Hep Htens Hparr)).
Proof.
  move => A [[[u U] | []] | []] [p P]; cbnb.
  { apply (red_tens_uacyclic_notcut A P). }
  all: destruct p as [ | (e, b) p]; trivial.
  all: assert (P' := supath_turnK P).
  all: revert P => /andP[/andP[/andP[? _] _] _].
  all: destruct e as [[[[[[[? ?] | []] | []] | ] | ] | ] | ], b; try by [].
  all: assert (N := red_tens_uacyclic_notcut A P').
  all: contradict N; apply rcons_nil.
Qed.

Lemma red_tens_ineq_if2 (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  left_tens Htens <> ep /\ left_tens Htens <> et /\
  right_tens Htens <> ep /\ right_tens Htens <> et /\
  left_parr Hparr <> ep /\ left_parr Hparr <> et /\
 right_parr Hparr <> ep /\ right_parr Hparr <> et.
Proof.
  splitb => Hc; subst; contradict Hcut.
  all: rewrite -1?Hc ?left_e ?right_e ?Htens ?Hparr; caseb.
  all: rewrite -1?Hep -1?Hc ?left_e ?right_e ?Htens ?Hparr; caseb.
Qed.

Definition red_tens_image (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G) (Het : target et = v)
  (Hep : target ep = v) (Htens : vlabel (source et) = ⊗) (Hparr : vlabel (source ep) = ⅋) :
  edge G -> edge (red_tens_graph Hcut Het Hep Htens Hparr) :=
  fun e => if @boolP _ is AltTrue p then Some (Some (Some (Some (inl (inl (Sub e p))))))
    else if e == left_tens Htens then Some (Some (Some None))
    else if e == right_tens Htens then Some (Some None)
    else if e == left_parr Hparr then Some None
    else None.

Lemma red_tens_nb_edges (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  #|edge G| = #|edge (red_tens_ps Hcut Het Hep Htens Hparr)| + 2.
Proof.
  enough (#|setT :\ et :\ ep| = #|edge (red_tens_ps Hcut Het Hep Htens Hparr)|) as <-.
  { rewrite -cardsT (cardsD1 et setT) (cardsD1 ep (setT :\ et)) !in_set.
    enough (ep != et = true) as -> by lia.
    apply /eqP => E. contradict Hparr. by rewrite E Htens. }
  rewrite -card_set_subset.
  set f : {e : edge G | (e \notin [set ep]) && (e \in [set: edge G] :\ et)} ->
    edge (red_tens_graph Hcut Het Hep Htens Hparr) :=
    fun e => red_tens_image Hcut Het Hep Htens Hparr (val e).
  assert (Hg : forall (e : edge (red_tens_ps Hcut Het Hep Htens Hparr)),
    (red_tens_transport e \notin [set ep]) && (red_tens_transport e \in [set: edge G] :\ et)).
  { move => e.
    rewrite !in_set /red_tens_transport.
    destruct (red_tens_ineq_if2 Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? ?]]]]]]].
    destruct e as [[[[[[[e E] | []] | []] | ] | ] | ] | ]; splitb; apply /eqP => // ?; subst e.
    all: contradict E; apply /negP.
    all: rewrite !in_set; caseb. }
  set g : edge (red_tens_graph Hcut Het Hep Htens Hparr) ->
    {e : edge G | (e \notin [set ep]) && (e \in [set: edge G] :\ et)} :=
    fun e => Sub (red_tens_transport e) (Hg e).
  destruct (red_tens_ineq_if Hcut Het Hep Htens Hparr) as [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]].
  apply (bij_card_eq (f := f)), (Bijective (g := g)).
  - move => [e E].
    rewrite /f /red_tens_image /g /= /red_tens_transport.
    case: {-}_ /boolP => In; cbnb.
    revert E; rewrite !in_set => /andP[/eqP Ep /andP[/eqP Et _]].
    case_if.
    revert In; rewrite !in_set !andb_true_r =>
      /nandP[/nandP[/negPn/eqP-He | /nandP[/negPn/eqP-He | /negPn/eqP-He]]
            |/nandP[/negPn/eqP-He | /nandP[/negPn/eqP-He | /negPn/eqP-He]]].
    + contradict He. by apply no_source_cut.
    + contradict Ep. (* TODO simplify here apply one_source_parr.*)
      transitivity (ccl_parr Hparr); [ | symmetry]; apply ccl_eq; caseb.
    + contradict Et.
      transitivity (ccl_tens Htens); [ | symmetry]; apply ccl_eq; caseb.
    + assert (T := target_in_edges_at_in e).
      rewrite He (red_tens_cut_set Hcut Het Hep Htens Hparr) !in_set in T.
      by revert T => /orP[/eqP ? | /eqP ?].
    + symmetry. by apply right_eq2.
    + by assert (e = right_tens Htens) by by apply right_eq2.
  - move => e.
    rewrite /f /red_tens_image /g SubK /red_tens_transport.
    destruct e as [[[[[[[e E] | []] | []] | ] | ] | ] | ].
    { case: {-}_ /boolP => Hc; [cbnb | ].
      by contradict Hc; apply /negP/negPn. }
    all: case: {-}_ /boolP => Hc; [ | case_if].
    all: contradict Hc; apply /negP.
    all: rewrite !in_set ?left_e ?right_e; caseb.
Qed.

Lemma red_tens_nb_parr (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  #|[set u : G | vlabel u == ⅋]| = #|[set u : red_tens_ps Hcut Het Hep Htens Hparr | vlabel u == ⅋]| + 1.
Proof.
  enough (#|[set u : G | vlabel u == ⅋] :\ (source ep)| =
    #|[set u : red_tens_ps Hcut Het Hep Htens Hparr | vlabel u == ⅋]|) as <-.
  { rewrite (cardsD1 (source ep) _) !in_set Hparr /=. lia. }
  rewrite -!card_set_subset.
  assert (Hf : forall (u : {u : G | (u \notin [set source ep]) && (u \in [set w | vlabel w == ⅋])}),
    val u \in [set: G] :\ (source et) :\ (source ep) :\ v).
  { move => [u U].
    rewrite SubK !in_set.
    revert U; rewrite !in_set => /andP[/eqP ? /eqP U].
    splitb; apply /eqP; trivial.
    all: move => ?; subst u; contradict U; by rewrite ?Hcut ?Htens. }
  assert (Hf' : forall (u : {u : G | (u \notin [set source ep]) && (u \in [set w | vlabel w == ⅋])}),
    vlabel (inl (inl (Sub (val u) (Hf u))) : red_tens_graph Hcut Het Hep Htens Hparr) == ⅋).
  { by move => [? /=]; rewrite !in_set => /andP[_ /eqP ->]. }
  set f : {u : G | (u \notin [set source ep]) && (u \in [set w | vlabel w == ⅋])} ->
    {u : red_tens_graph Hcut Het Hep Htens Hparr | vlabel u == ⅋} :=
    fun u => Sub (inl (inl (Sub (val u) (Hf u)))) (Hf' u).
  assert (Hg : forall (u : {u : red_tens_graph Hcut Het Hep Htens Hparr | vlabel u == ⅋}),
    match val u with
    | inl (inl u) => (val u \notin [set source ep]) && (val u \in [set w | vlabel w == ⅋])
    | _ => false
    end).
  { move => [[[[u Uin] | []] | []] /= U] //.
    revert Uin; rewrite !in_set => /andP[_ /andP[? _]]. splitb. }
  apply (bij_card_eq (f := f)). eapply Bijective. Unshelve. 3:{
    move => [[[u | []] | []] U] //. exact (Sub (val u) (Hg (Sub (inl (inl u)) U))). }
  - move => ?; cbnb.
  - move => [[[? | []] | []] ?]; cbnb.
Qed.

Lemma red_tens_uconnected (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  correct G ->
  uconnected (switching_left (G := red_tens_ps Hcut Het Hep Htens Hparr)).
Proof.
  move => [A C].
  assert (#|G| <> 0).
  { clear - v. rewrite -cardsT => Gc. apply cards0_eq in Gc.
    assert (V : v \in set0) by by rewrite -Gc !in_set. by rewrite in_set in V. }
  apply uconnected_to_nb1 in C; trivial; [ | apply switching_left_sinj].
  assert (N := switching_left_uconnected_nb A).
  apply uconnected_from_nb1; [apply switching_left_sinj | ].
  assert (N' := switching_left_uconnected_nb (@red_tens_uacyclic _ _ Hcut _ _ Het Hep Htens Hparr A)).
  rewrite (red_tens_nb_edges Hcut Het Hep Htens Hparr) (red_tens_nb_parr Hcut Het Hep Htens Hparr) in N.
  rewrite red_tens_nb in N'.
  lia.
Qed.

Lemma red_tens_correct (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) :
  correct G -> correct (red_tens_graph Hcut Het Hep Htens Hparr).
Proof.
  move => [A C]. split.
  - by apply red_tens_uacyclic.
  - by apply red_tens_uconnected.
Qed.

Definition red_tens_pn (G : proof_net) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋) : proof_net := {|
  ps_of := red_tens_ps Hcut Het Hep Htens Hparr;
  p_correct := @red_tens_correct _ _ _ _ _ _ _ _ _ (p_correct G);
  |}.


(** * Cut reduction procedure *)
Lemma red_term (G : proof_structure) (v : G) (H : vlabel v = cut) :
  [exists e, (target e == v) && (vlabel (source e) == ax)] || [exists et, exists ep,
  (target et == v) && (target ep == v) && (vlabel (source et) == ⊗) && (vlabel (source ep) == ⅋)].
Proof.
  enough (Hdone : (exists e, target e = v /\ vlabel (source e) = ax) \/
    exists et ep, target et = v /\ target ep = v /\ vlabel (source et) = ⊗ /\ vlabel (source ep) = ⅋).
  { destruct Hdone as [[e [He0 He1]] | [et [ep [He0 [He1 [He2 He3]]]]]].
    - apply /orP; left. apply /existsP; exists e. rewrite He0 He1. splitb.
    - apply /orP; right. apply /existsP; exists et. apply /existsP; exists ep.
      rewrite He0 He1 He2 He3. splitb. }
  destruct (p_cut H) as [e [e' H']];
  revert H'; rewrite !in_set; move => [/eqP-Hin [/eqP-Hin' Heq]].
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
    enough (flabel e = tens (flabel (left_tens Hle)) (flabel (right_tens Hle))
      /\ flabel e' = tens (flabel (left_tens Hle')) (flabel (right_tens Hle'))) as [-> ->] by by [].
    assert (e = ccl_tens Hle /\ e' = ccl_tens Hle') as [He He'] by (split; apply ccl_eq; trivial; caseb).
    split; [rewrite {1}He | rewrite {1}He']; by apply p_tens_bis.
  - right; by exists e, e'.
  - right; by exists e', e.
  - contradict Heq.
    enough (flabel e = parr (flabel (left_parr Hle)) (flabel (right_parr Hle))
      /\ flabel e' = parr (flabel (left_parr Hle')) (flabel (right_parr Hle'))) as [-> ->] by by [].
    assert (e = ccl_parr Hle /\ e' = ccl_parr Hle') as [He He'] by (split; apply ccl_eq; trivial; caseb).
    split; [rewrite {1}He | rewrite {1}He']; by apply p_parr_bis.
Qed.

(** One step *)
Definition red_one_ps (G : proof_structure) (v : G) (H : vlabel v = cut) : proof_structure.
Proof.
  elim: (orb_sum (red_term H)).
  - move => /existsP/sigW[? /andP[/eqP ? /eqP ?]]; subst.
    by apply (red_ax_ps H).
  - move => /existsP/sigW [? /existsP/sigW[? /andP[/andP[/andP[/eqP Het /eqP Hep] /eqP ?] /eqP ?]]].
    by apply (red_tens_ps H Het Hep).
Defined.

Lemma red_one_correct (G : proof_structure) (v : G) (H : vlabel v = cut) :
  correct G -> correct (red_one_ps H).
Proof.
  unfold red_one_ps.
  elim: (orb_sum (red_term H)) => ? /=.
  - elim: (sigW _) => ? /andP[He ?].
    set Hr := elimTF eqP He; destruct Hr.
    apply red_ax_correct.
  - elim: (sigW _) => ? ?;
    elim: (sigW _) => ? /andP[/andP[/andP[? ?] ?] ?].
    apply red_tens_correct.
Qed.

Definition red_one_pn (G : proof_net) (v : G) (H : vlabel v = cut) : proof_net := {|
  ps_of := red_one_ps H;
  p_correct := red_one_correct _ (p_correct G);
  |}.

Lemma red_one_sequent (G : proof_structure) (v : G) (H : vlabel v = cut) :
  sequent (red_one_ps H) = sequent G.
Proof.
  unfold red_one_ps.
  elim: (orb_sum (red_term H)) => ? /=.
  - elim: (sigW _) => ? /andP[He ?]. set Hr := elimTF eqP He; destruct Hr.
    apply red_ax_sequent.
  - elim: (sigW _) => ? ?; elim: (sigW _) => ? /andP[/andP[/andP[? ?] ?] ?].
    apply red_tens_sequent.
Qed.

Lemma red_one_nb (G : proof_structure) (v : G) (H : vlabel v = cut) :
  #|red_one_ps H| < #|G|.
Proof.
  unfold red_one_ps.
  assert (#|G| <> 0) by by apply fintype0.
  elim: (orb_sum (red_term H)) => ? /=.
  - elim: (sigW _) => e /andP[He Hax]. set Hr := elimTF eqP He; destruct Hr.
    rewrite red_ax_nb.
    set n := #|G|; lia.
  - elim: (sigW _) => *. elim: (sigW _); introb.
    rewrite red_tens_nb //; try by apply /eqP.
    set n := #|G|; lia.
Qed.

(** All steps *)
Lemma red_all (G : proof_structure) :
  {P : proof_structure | correct G -> correct P & sequent P = sequent G /\ ~(has_cut P)}.
Proof.
  revert G.
  enough (Hm : forall n (G : proof_structure), #|G| = n ->
    {P : proof_structure | correct G -> correct P & sequent P = sequent G /\ ~(has_cut P)})
    by (intro G; by apply (Hm #|G|)).
  intro n; induction n as [n IH] using lt_wf_rect; intros G Hc.
  have [/has_cutP/existsP/sigW[v /eqP-Hcut] |/has_cutP-?] := altP (has_cutP G).
  2:{ by exists G. }
  assert (N : (#|red_one_ps Hcut| < n)%coq_nat) by (rewrite -Hc; apply /leP; apply red_one_nb).
  specialize (IH _ N _ erefl). destruct IH as [P PN [S C]].
  exists P; [ | split; trivial].
  - move => *. by apply PN, red_one_correct.
  - rewrite S. apply red_one_sequent.
Qed.

Definition red (G : proof_structure) : proof_structure := proj1_sig (red_all G).

Lemma red_correct (G : proof_structure) : correct G -> correct (red G).
Proof. by destruct (proj2_sig (red_all G)) as [? [? ?]]. Qed.

Definition red_pn (G : proof_net) : proof_net := {|
  ps_of := red G;
  p_correct := red_correct (p_correct G);
  |}.

Lemma red_sequent (G : proof_structure) : sequent (red G) = sequent G.
Proof. by destruct (proj2_sig (red_all G)) as [? [? ?]]. Qed.

Lemma red_has_cut (G : proof_structure) : ~ has_cut (red G).
Proof. by destruct (proj2_sig (red_all G)) as [? [? ?]]. Qed.

End Atoms.
