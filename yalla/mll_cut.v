(* Cut Elimination in Proof Nets *)(* TODO uacyclic pour tens trop long à compiler *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export graph_more mll_prelim mll_def mll_basic mll_correct.

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


(** * Axiom - cut reduction *)
Section red_ax.
Variables (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax).

(* The label on the new edge is the one of the other arrow of the ax node, (dual (flabel e), ?) *)
Definition red_ax_graph_1 : base_graph :=
  G ∔ [source (other_cut Hcut), elabel (other_ax Hax), target (other_ax Hax)].

Definition red_ax_graph : base_graph :=
  induced ([set: red_ax_graph_1] :\ (source e) :\ (target e)).

(* the degenerate case where the axiom and the cut form a loop *)
Local Notation non_degenerate := (None \in edge_set ([set: red_ax_graph_1] :\ source e :\ target e)).

Lemma red_ax_degenerate_None :
 non_degenerate = (other_cut Hcut != other_ax Hax).
Proof.
  rewrite !in_set !andb_true_r /=.
  destruct (eq_comparable (other_cut Hcut) (other_ax Hax)) as [Heq | Hneq].
  - rewrite Heq eq_refl other_ax_e. caseb.
  - transitivity true; last by symmetry; apply /eqP.
    splitb; apply /eqP.
    + by apply no_source_cut.
    + intro H. contradict Hneq. apply other_ax_eq.
      rewrite H. splitb. apply other_cut_neq.
    + intro H. contradict Hneq. symmetry; apply other_cut_eq.
      rewrite H. splitb. apply other_ax_neq.
    + by apply no_target_ax.
Qed.

Definition red_ax_order_1 : seq (edge red_ax_graph_1) :=
  [seq if a == other_ax Hax then None else Some a | a <- order G].

Lemma red_ax_order_1_other_ax :
  Some (other_ax Hax) \notin red_ax_order_1.
Proof.
  unfold red_ax_order_1. induction (order G); trivial.
  rewrite /= in_cons. splitb. case_if.
  by apply /eqP; apply nesym.
Qed.

Lemma red_ax_consistent_order :
  all (pred_of_set (edge_set ([set: red_ax_graph_1] :\ (source e) :\ (target e)))) red_ax_order_1.
Proof.
  apply /allP => a A.
  assert (Hl : vlabel (target a) = c).
  { revert A => /mapP[b B]. apply p_order in B.
    case_if. }
  destruct a as [a | ]; simpl in Hl.
  - rewrite /edge_set. apply /setIdP. rewrite !in_set /=.
    splitb; apply /eqP.
    + by apply no_source_cut.
    + intro Hc.
      assert (a = other_ax Hax).
      { apply other_ax_eq. splitb.
        intros ?; subst a.
        by rewrite Hcut in Hl. }
      subst a.
      contradict A; apply /negP.
      apply red_ax_order_1_other_ax.
    + intro Hc. by rewrite Hc Hcut in Hl.
    + by apply no_target_ax.
  - rewrite -in_set.
    rewrite memKset red_ax_degenerate_None.
    apply /eqP. intro Hc.
    contradict Hl. by rewrite -Hc other_cut_e Hcut.
Qed.

Definition red_ax_order : seq (edge red_ax_graph) :=
  sval (all_sigP red_ax_consistent_order).

Definition red_ax_graph_data : graph_data := {|
  graph_of := red_ax_graph;
  order := red_ax_order;
  |}.

Definition red_ax_transport (b : bool) : edge red_ax_graph -> edge G :=
  fun a => match val a with
  | None => if b then other_ax Hax else other_cut Hcut
  | Some a' => a'
  end.

Lemma red_ax_transport_inj (b : bool) : injective (red_ax_transport b).
Proof.
  intros [a A] [a' A'].
  rewrite /red_ax_transport /=.
  move => ?. apply /eqP. rewrite sub_val_eq /=.
  assert (Some (if b then other_ax Hax else other_cut Hcut)
    \notin edge_set ([set: red_ax_graph_1] :\ source e :\ target e)).
  { destruct b; rewrite !in_set /= ?other_ax_e ?other_cut_e; caseb. }
  destruct a, a'; subst; trivial; [contradict A | contradict A']; by apply /negP.
Qed.

Lemma red_ax_transport_edges (b : bool) (v : G) Hv :
  edges_at_outin b v = [set red_ax_transport b a | a in edges_at_outin b (Sub v Hv : red_ax_graph)].
Proof.
  apply /setP => a.
  rewrite Imset.imsetE !in_set.
  symmetry; apply /imageP; case_if.
  - assert (endpoint b a <> source e /\ endpoint b a <> target e) as [Hvs Hvt]
      by by (revert Hv; rewrite !in_set => /andP[/eqP-? /andP[/eqP-? _]]).
    assert (a <> e) by by (intros ?; subst; destruct b; by rewrite_all eq_refl).
    destruct (eq_comparable a (other_cut Hcut)) as [ | Hneqc];
    [ | destruct (eq_comparable a (other_ax Hax)) as [ | Hneqa]]; subst.
    + destruct b.
      { contradict Hvt. apply other_cut_e. }
      assert (Hn : non_degenerate).
      { rewrite red_ax_degenerate_None. apply /eqP => Heq.
        contradict Hv; apply /negP.
        rewrite Heq other_ax_e !in_set. caseb. }
      exists (Sub None Hn); trivial.
      by rewrite !in_set; cbn.
    + destruct b.
      2:{ contradict Hvs. apply other_ax_e. }
      apply nesym in Hneqc. revert Hneqc => /eqP. rewrite -red_ax_degenerate_None => Hn.
      exists (Sub None Hn); trivial.
      by rewrite !in_set; cbn.
    + assert (Ha : Some a \in edge_set ([set: red_ax_graph_1] :\ source e :\ target e)).
      { rewrite !in_set /=.
        splitb; apply /eqP.
        - by apply no_source_cut.
        - intros ?. contradict Hneqa. by apply other_ax_eq.
        - intros ?. contradict Hneqc. by apply other_cut_eq.
        - by apply no_target_ax. }
      exists (Sub (Some a) Ha); trivial.
      by rewrite !in_set; cbn.
  - intros [[x ?] Hx Ha].
    rewrite /red_ax_transport /= in Ha. subst.
    contradict Hx; apply /negP.
    rewrite in_set; cbn; simpl; apply /eqP.
    by destruct x, b.
Qed.

Lemma red_ax_transport_flabel b (a : edge red_ax_graph) :
  flabel a = flabel (red_ax_transport b a).
Proof.
  destruct a as [[a | ] Ha], b; trivial; cbn.
  destruct (p_ax_cut_bis G) as [Hpax Hpcut].
  specialize (Hpcut _ Hcut _ (target_in_edges_at_in e)).
  unfold is_dual_f, is_dual in Hpcut. revert Hpcut => /eqP-<-.
  specialize (Hpax _ Hax _ (source_in_edges_at_out e)).
  unfold is_dual_f, is_dual in Hpax. by revert Hpax => /eqP-->.
Qed.

Lemma red_ax_p_deg : proper_degree red_ax_graph.
Proof.
  intros b [v Hv]; cbn.
  rewrite -p_deg (red_ax_transport_edges _ Hv) card_imset //.
  apply red_ax_transport_inj.
Qed.


Lemma red_ax_p_ax_cut : proper_ax_cut red_ax_graph.
Proof.
  move => b [v Hv] /= Hl.
  destruct (p_ax_cut Hl) as [el [er H]].
  revert H; rewrite (red_ax_transport_edges _ Hv) Imset.imsetE 2!in_set.
  move => [/imageP[El ? ?] [/imageP[Er ? ?] ?]]. subst el er.
  exists El, Er. splitb.
  by rewrite !(red_ax_transport_flabel b).
Qed.

Lemma red_ax_p_tens_parr : proper_tens_parr red_ax_graph.
Proof.
  move => b [v Hv] /= Hl.
  destruct (p_tens_parr Hl) as [el [er [ec [Lt [Ll [Rt [Rl [Ct Cl]]]]]]]].
  revert Lt Rt Ct. rewrite !(red_ax_transport_edges _ Hv).
  move => /imsetP[el' Lt' ?] /imsetP[er' Rt' ?] /imsetP[ec' Ct' ?]. subst el er ec.
  rewrite -!(red_ax_transport_flabel) in Cl.
  exists el', er', ec'. splitb.
  - by destruct el' as [[? | ] ?].
  - by destruct er' as [[? | ] ?].
Qed.

Lemma red_ax_p_noleft : proper_noleft red_ax_graph.
Proof. intros [[? | ] ?] ?; by apply p_noleft. Qed.

Lemma red_ax_p_order : proper_order red_ax_graph_data.
Proof.
  rewrite /proper_order /red_ax_graph_data /red_ax_order /=.
  destruct (all_sigP _) as [l L], (p_order G).
  split.
  - intros [a A]; cbn.
    rewrite in_seq_sig !SubK -L /red_ax_order_1.
    destruct a as [a | ].
    + apply (@iff_stepl (a \in order G)); [ | by apply iff_sym].
      split.
      * intro In. apply /mapP.
        exists a; trivial.
        case_if.
        contradict A; apply /negP.
        rewrite !in_set /= other_ax_e. caseb.
      * move => /mapP[? ? /eqP]. case_if.
    + apply (@iff_stepl (other_ax Hax \in order G)); [ | by apply iff_sym].
      split.
      * intro In. apply /mapP.
        exists (other_ax Hax); trivial. case_if.
      * move => /mapP[? ? /eqP]. case_if.
  - rewrite uniq_seq_sig -L /red_ax_order_1 map_inj_uniq //.
    move => ? ? /eqP. case_if.
Qed.

Definition red_ax_ps : proof_structure := {|
  graph_data_of := red_ax_graph_data;
  p_deg := red_ax_p_deg;
  p_ax_cut := red_ax_p_ax_cut;
  p_tens_parr := red_ax_p_tens_parr;
  p_noleft := red_ax_p_noleft;
  p_order := red_ax_p_order;
  |}.


(** Sequent of an axiom - cut reduction *)
Lemma red_ax_sequent_eq : sequent red_ax_graph_data = [seq flabel e | e <- red_ax_order_1].
Proof.
  rewrite /red_ax_graph_data /red_ax_order.
  destruct (all_sigP _) as [l L].
  by rewrite [in RHS]L -map_comp.
Qed.

Lemma red_ax_sequent : sequent red_ax_ps = sequent G.
Proof.
  rewrite red_ax_sequent_eq /red_ax_order_1 /sequent -map_comp.
  apply eq_map => a /=. case_if.
Qed.

(** Decreasing number of vertices *)
Lemma red_ax_nb : #|G| = #|red_ax_graph| + 2.
Proof.
  rewrite -(@card_imset _ _ val); [ | apply val_inj].
  transitivity (#|setT :\ (source e) :\ (target e)| + 2).
  - rewrite -cardsT [in LHS](cardsD1 (source e)) [in LHS](cardsD1 (target e)) !in_set.
    enough (target e != source e) by lia.
    apply /eqP => Hf. contradict Hcut.
    by rewrite Hf Hax.
  - f_equal. apply eq_card => v.
    rewrite Imset.imsetE in_set.
    symmetry; destruct (v \in [set: G] :\ source e :\ target e) eqn:Hv; rewrite Hv.
    + apply /imageP. by exists (Sub v Hv).
    + apply /imageP; intros [[u U] _ ?]; subst v.
      by rewrite U in Hv.
Qed.


(** Correctness *)
(* For this part, we assume that we are not in the degenerate case, i.e. the edge we added is still here *)
Definition red_ax_G (N : non_degenerate) :=
  @invert_edge_graph _ _
  (@extend_edge_graph _
    (@extend_edge_graph _ red_ax_graph (Sub None N) cut (dual (flabel e)) (flabel e))
    (Some (Sub None N)) ax (flabel e) (dual (flabel e)))
  None.

Definition red_ax_iso_v_bij_fwd (N : non_degenerate) :
  red_ax_G N -> G :=
  fun v => match v with
  | Some (Some (exist u _)) => u
  | Some None               => target e
  | None                    => source e
  end.

Definition red_ax_iso_v_bij_bwd (N : non_degenerate) :
  G -> red_ax_G N :=
  fun v => if @boolP _ is AltTrue p then Some (Some (Sub v p))
    else if v == source e then None else Some None.

Lemma red_ax_iso_v_bijK (N : non_degenerate) :
  cancel (@red_ax_iso_v_bij_fwd N) (red_ax_iso_v_bij_bwd N).
Proof.
  intros [[[v V] | ] | ]; cbn;
  unfold red_ax_iso_v_bij_bwd; case: {-}_ /boolP => [Hc | /negP-?] //.
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

Lemma red_ax_iso_v_bijK' (N : non_degenerate) :
  cancel (red_ax_iso_v_bij_bwd N) (@red_ax_iso_v_bij_fwd N).
Proof.
  intro v; unfold red_ax_iso_v_bij_bwd.
  case: {-}_ /boolP => [// | ].
  rewrite !in_set andb_true_r => /nandP[/negPn/eqP-? | /negPn/eqP-?]; subst; case_if.
Qed.

Definition red_ax_iso_v (N : non_degenerate) := {|
  bij_fwd := _;
  bij_bwd:= _;
  bijK:= @red_ax_iso_v_bijK N;
  bijK':= red_ax_iso_v_bijK' _;
  |}.

Definition red_ax_iso_e_bij_fwd (N : non_degenerate) :
  edge (red_ax_G N) -> edge G :=
  fun a => match a with
  | None                            => e
  | Some None                       => other_cut Hcut
  | Some (Some (exist None _))      => other_ax Hax
  | Some (Some (exist (Some a) _))  => a
  end.

Definition red_ax_iso_e_bij_bwd (N : non_degenerate) :
  edge G -> edge (red_ax_G N) :=
  fun a => if @boolP _ is AltTrue p then Some (Some (Sub (Some a) p))
    else if a == e then None
    else if a == other_ax Hax then Some (Some (Sub None N))
    else Some None.

Lemma red_ax_iso_e_bijK (N : non_degenerate) :
  cancel (@red_ax_iso_e_bij_fwd N) (@red_ax_iso_e_bij_bwd N).
Proof.
  intros [[[[a | ] A] | ] | ]; cbn;
  unfold red_ax_iso_e_bij_bwd; case: {-}_ /boolP => [Hc | /negP ?] //.
  - cbnb.
  - contradict Hc; apply /negP.
    rewrite !in_set /= other_ax_e. caseb.
  - case_if; cbnb.
    by assert (other_ax Hax <> e) by apply other_ax_neq.
  - contradict Hc; apply /negP.
    rewrite !in_set /= other_cut_e. caseb.
  - assert (other_cut Hcut == e = false) as -> by (apply /eqP; apply other_cut_neq).
    case_if. contradict N; apply /negP.
    rewrite red_ax_degenerate_None. by apply /negPn/eqP.
  - contradict Hc; apply /negP.
    rewrite !in_set. caseb.
  - by rewrite eq_refl.
Qed.

Lemma red_ax_iso_e_bijK' (N : non_degenerate) :
  cancel (red_ax_iso_e_bij_bwd N) (@red_ax_iso_e_bij_fwd N).
Proof.
  intro a.
  unfold red_ax_iso_e_bij_bwd. case: {-}_ /boolP => [ | Ha]; cbnb.
  case_if.
  revert Ha; rewrite !in_set !andb_true_r /=
    => /nandP[/nandP[/negPn/eqP-Ha | /negPn/eqP-Ha] | /nandP[/negPn/eqP-Ha | /negPn/eqP-Ha]].
  - contradict Ha. by apply no_source_cut.
  - by assert (a = other_ax Hax) by by apply other_ax_eq.
  - symmetry; by apply other_cut_eq.
  - contradict Ha. by apply no_target_ax.
Qed.

Definition red_ax_iso_e (N : non_degenerate) := {|
  bij_fwd := _;
  bij_bwd:= _;
  bijK:= @red_ax_iso_e_bijK N;
  bijK':= red_ax_iso_e_bijK' _;
  |}.

Lemma red_ax_iso_ihom (N : non_degenerate) :
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
      by revert Hpax => /(_ _ Hax _ (source_in_edges_at_out e)) /eqP-->.
    + destruct (p_ax_cut_bis G) as [_ Hpcut].
      by revert Hpcut => /(_ _ Hcut _ (target_in_edges_at_in e)) /eqP-->.
    + apply p_noleft.
      rewrite other_cut_e Hcut. caseb.
    + apply p_noleft.
      rewrite Hcut. caseb.
Qed.

Definition red_ax_iso (N : non_degenerate) :=
  {| iso_v := _; iso_e := _; iso_d := _; iso_ihom := red_ax_iso_ihom N |}.

Lemma red_ax_correct_None :
  uacyclic (@switching _ G) -> non_degenerate.
Proof.
  intro A.
  rewrite red_ax_degenerate_None. apply /eqP => N.
  unfold uacyclic in A.
  enough (P : supath switching (source e) (source e) (forward e :: backward (other_cut Hcut) :: nil))
    by by specialize (A _ {| upval := _ ; upvalK := P |}).
  rewrite /supath /= in_cons in_nil orb_false_r {2}N other_cut_e other_ax_e.
  splitb. cbn.
  rewrite other_cut_e Hcut /=.
  apply /eqP; apply nesym, other_cut_neq.
Qed.

Lemma red_ax_correct : correct G -> correct red_ax_graph.
Proof.
  intro C.
  assert (N : non_degenerate)
    by (destruct C; by apply red_ax_correct_None).
  set C' := iso_correct (red_ax_iso N) C.
  by apply invert_edge_correct, correct_to_weak, extend_edge_correct_from,
                                correct_to_weak, extend_edge_correct_from in C'.
Qed.

End red_ax.

Definition red_ax_pn (G : proof_net) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : proof_net := {|
  ps_of := red_ax_ps Hcut Hax;
  p_correct := @red_ax_correct _ _ _ _ (p_correct G);
  |}.



(** * Tensor - cut reduction *)
Definition red_tens_graph_1 (G : base_graph) (v : G) (et ep : edge G) : base_graph :=
  induced (setT :\ source et :\ source ep :\ v).

Section red_tens_proof_structure.
Variables (G : proof_structure) (v : G) (Hcut : vlabel v = cut) (et ep : edge G)
  (Het : target et = v) (Hep : target ep = v) (Htens : vlabel (source et) = ⊗)
  (Hparr : vlabel (source ep) = ⅋).

Lemma red_tens_ineq_in :
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

Lemma red_tens_ineq_if :
  source et <> source ep /\ source ep <> source et /\
  left_tens Htens <> right_tens Htens /\ right_tens Htens <> left_tens Htens /\
  left_parr Hparr <> right_parr Hparr /\ right_parr Hparr <> left_parr Hparr /\
  left_tens Htens <> left_parr Hparr /\ left_parr Hparr <> left_tens Htens /\
  left_tens Htens <> right_parr Hparr /\ right_parr Hparr <> left_tens Htens /\
  left_parr Hparr <> right_tens Htens /\ right_tens Htens <> left_parr Hparr /\
  right_tens Htens <> right_parr Hparr /\ right_parr Hparr <> right_tens Htens /\
  left_tens Htens <> ep /\ left_tens Htens <> et /\
  right_tens Htens <> ep /\ right_tens Htens <> et /\
  left_parr Hparr <> ep /\ left_parr Hparr <> et /\
  right_parr Hparr <> ep /\ right_parr Hparr <> et.
Proof.
  assert (Hf : source et <> source ep) by
    (intro Hf; clear - Htens Hparr Hf; contradict Htens; by rewrite Hf Hparr).
  assert (right_tens Htens <> left_tens Htens /\ right_parr Hparr <> left_parr Hparr) as [? ?]
    by (split; apply nesym, left_neq_right).
  assert (left_tens Htens <> left_parr Hparr /\ left_tens Htens <> right_parr Hparr /\
    right_tens Htens <> left_parr Hparr /\ right_tens Htens <> right_parr Hparr) as [? [? [? ?]]].
  { splitb; intro Hc; contradict Hf.
    - rewrite -(left_e (or_introl Htens)) -(left_e (or_intror Hparr)). by f_equal.
    - rewrite -(left_e (or_introl Htens)) -(right_e (or_intror Hparr)). by f_equal.
    - rewrite -(right_e (or_introl Htens)) -(left_e (or_intror Hparr)). by f_equal.
    - rewrite -(right_e (or_introl Htens)) -(right_e (or_intror Hparr)). by f_equal. }
  assert (left_tens Htens <> ep /\ left_tens Htens <> et /\
    right_tens Htens <> ep /\ right_tens Htens <> et /\
    left_parr Hparr <> ep /\ left_parr Hparr <> et /\
    right_parr Hparr <> ep /\ right_parr Hparr <> et) as [? [? [? [? [? [? [? ?]]]]]]].
  { splitb => Hc; subst; contradict Hcut.
    all: rewrite -1?Hc ?left_e ?right_e ?Htens ?Hparr; caseb.
    all: rewrite -1?Hep -1?Hc ?left_e ?right_e ?Htens ?Hparr; caseb. }
  splitb; by apply nesym.
Qed. (* TODO Tout mettre en double ? Rien ? *)

Lemma red_tens_in :
  source (left_tens Htens) \in setT :\ source et :\ source ep :\ v /\
  source (right_tens Htens) \in setT :\ source et :\ source ep :\ v /\
  source (left_parr Hparr) \in setT :\ source et :\ source ep :\ v /\
  source (right_parr Hparr) \in setT :\ source et :\ source ep :\ v.
Proof.
  destruct red_tens_ineq_in as [? [? [? [? [? [? [? [? ?]]]]]]]].
  rewrite !in_set. splitb.
Qed.
Lemma red_tens_in_slt :
  source (left_tens Htens) \in setT :\ source et :\ source ep :\ v.
Proof. by destruct red_tens_in as [? [? [? ?]]]. Qed.
Lemma red_tens_in_srt :
  source (right_tens Htens) \in setT :\ source et :\ source ep :\ v.
Proof. by destruct red_tens_in as [? [? [? ?]]]. Qed.
Lemma red_tens_in_slp :
  source (left_parr Hparr) \in setT :\ source et :\ source ep :\ v.
Proof. by destruct red_tens_in as [? [? [? ?]]]. Qed.
Lemma red_tens_in_srp :
  source (right_parr Hparr) \in setT :\ source et :\ source ep :\ v.
Proof. by destruct red_tens_in as [? [? [? ?]]]. Qed.

Definition red_tens_graph :=
  (red_tens_graph_1 v et ep) ∔ cut ∔ cut
    ∔ [inl (inl (Sub (source (left_tens Htens)) red_tens_in_slt)) ,
        (flabel (left_tens Htens), true) , inl (inr tt)]
    ∔ [inl (inl (Sub (source (right_tens Htens)) red_tens_in_srt)) ,
        (flabel (right_tens Htens), true) , inr tt]
    ∔ [inl (inl (Sub (source (left_parr Hparr)) red_tens_in_slp)) ,
        (flabel (left_parr Hparr), true) , inr tt]
    ∔ [inl (inl (Sub (source (right_parr Hparr)) red_tens_in_srp)) ,
        (flabel (right_parr Hparr), true) , inl (inr tt)].

Lemma red_tens_cut_set : edges_at_in v = [set et; ep].
Proof.
  subst v.
  rewrite other_cut_set.
  replace (other_cut Hcut) with ep; trivial.
  apply other_cut_eq. splitb.
  intros ?; subst; contradict Hparr.
  by rewrite Htens.
Qed.

Lemma red_tens_removed :
  edge_set (setT :\ source et :\ source ep :\ v) =
  setT :\ left_tens Htens :\ left_parr Hparr :\ right_tens Htens :\ right_parr Hparr :\ et :\ ep.
Proof.
  apply /setP => a.
  rewrite !in_set !andb_true_r.
  destruct red_tens_ineq_in as [-> _]. simpl.
  destruct (eq_comparable a et) as [? | Aet];
  [ | destruct (eq_comparable a ep) as [? | Aep]];
  [ | | destruct (eq_comparable a (left_tens Htens))];
  [ | | | destruct (eq_comparable a (right_tens Htens))];
  [ | | | | destruct (eq_comparable a (left_parr Hparr))];
  [ | | | | | destruct (eq_comparable a (right_parr Hparr))];
  try by (subst a; rewrite ?left_e ?right_e !eq_refl ?andb_false_r).
  assert (a != ep /\ a != et /\ a != left_tens Htens /\ a != right_tens Htens /\
    a != left_parr Hparr /\ a != right_parr Hparr) as [-> [-> [-> [-> [-> ->]]]]]
    by by splitb; apply /eqP.
  simpl.
  assert (Hin := target_in_edges_at_in a).
  splitb; apply /eqP => Hc.
  - contradict Aep. by apply one_source_parr.
  - contradict Aet. by apply one_source_tens.
  - contradict Hin; apply /negP.
    rewrite Hc red_tens_cut_set // !in_set.
    splitb; by apply /eqP.
  - contradict Hin; apply /negP.
    rewrite Hc (right_set (or_intror Hparr)) ?in_set.
    splitb; by apply /eqP.
  - contradict Hin; apply /negP.
    rewrite Hc (right_set (or_introl Htens)) ?in_set.
    splitb; by apply /eqP.
Qed.

Lemma red_tens_c_stay e :
  vlabel (target e) = c -> e \in edge_set (setT :\ source et :\ source ep :\ v).
Proof.
  intro E.
  rewrite red_tens_removed // !in_set.
  splitb; apply /eqP => ?; subst e;
  contradict E; by rewrite ?Het ?Hep ?Hcut ?left_e ?right_e ?Htens ?Hparr.
Qed.

Lemma red_tens_consistent_order :
  all (pred_of_set (edge_set (setT :\ source et :\ source ep :\ v))) (order G).
Proof. apply /allP => ? ?. by apply red_tens_c_stay, p_order. Qed.

Definition red_tens_order : seq (edge red_tens_graph) :=
  [seq Some (Some (Some (Some (inl (inl u))))) | u <- sval (all_sigP red_tens_consistent_order)].

Definition red_tens_graph_data : graph_data := {|
  graph_of := red_tens_graph;
  order := red_tens_order;
  |}.

Definition red_tens_transport : edge red_tens_graph -> edge G :=
  fun a => match a with
  | None                                              => right_parr Hparr
  | Some None                                         => left_parr Hparr
  | Some (Some None)                                  => right_tens Htens
  | Some (Some (Some None))                           => left_tens Htens
  | Some (Some (Some (Some (inr a))))                 => match a with end
  | Some (Some (Some (Some (inl (inl (exist a _)))))) => a
  | Some (Some (Some (Some (inl (inr a)))))           => match a with end
  end.

Lemma red_tens_transport_inj : injective red_tens_transport.
Proof.
  unfold red_tens_transport.
  destruct red_tens_ineq_if as [? [? [? [? [? [? [? [? [? [? [? [? [? [? _]]]]]]]]]]]]]].
  move => [[[[[[[a A] | []] | []] | ] | ] | ] | ] [[[[[[[b B] | []] | []] | ] | ] | ] | ]
    /eqP; cbn => /eqP-?; try subst a; try subst b; cbnb.
  all: (contradict A || contradict B); apply /negP.
  all: rewrite red_tens_removed !in_set; caseb.
Qed.

Lemma red_tens_transport_edges (b : bool) (u : G) (Hu : u \in (setT :\ source et :\ source ep :\ v)) :
  edges_at_outin b u = [set red_tens_transport a | a in edges_at_outin b (inl (inl (Sub u Hu)) : red_tens_graph)].
Proof.
  apply /setP => a.
  rewrite Imset.imsetE !in_set.
  symmetry; apply /imageP; case_if.
  - assert (a <> et /\ a <> ep) as [? ?].
    { split; intros ?; subst; contradict Hu; apply /negP.
      all: rewrite !in_set.
      all: destruct b; rewrite ?Hep; caseb. }
    destruct (a \in edge_set (setT :\ source et :\ source ep :\ v)) eqn:Ina.
    + exists (Some (Some (Some (Some (inl (inl (Sub a Ina))))))); rewrite // !in_set; cbnb.
    + rewrite red_tens_removed // !in_set andb_true_r in Ina.
      revert Ina; introb.
      all: destruct b; first by (contradict Hu; apply /negP; rewrite !in_set ?left_e ?right_e; caseb).
      * exists None; rewrite // !in_set; cbnb.
      * exists (Some (Some None)); rewrite // !in_set; cbnb.
      * exists (Some None); rewrite // !in_set; cbnb.
      * exists (Some (Some (Some None))); rewrite // !in_set; cbnb.
  - intros [[[[[[[[? ?] | []] | []] | ] | ] | ] | ] Hin Heq]; cbn in Heq; subst a.
    all: contradict Hin; apply /negP.
    all: rewrite !in_set.
    all: by destruct b; cbnb; apply /eqP.
Qed.

Lemma red_tens_transport_flabel (a : edge red_tens_graph) :
  flabel (red_tens_transport a) = flabel a.
Proof. by destruct a as [[[[[[[? ?] | []] | []] | ] | ] | ] | ]. Qed.

Lemma red_tens_transport_llabel (a : edge red_tens_graph) w W :
  a \in edges_at_in (inl (inl (Sub w W)) : red_tens_graph) ->
  llabel (red_tens_transport a) = llabel a.
Proof. destruct a as [[[[[[[? ?] | []] | []] | ] | ] | ] | ]; by rewrite // in_set. Qed.

Lemma red_tens_edges_at_new :
  edges_at_in (inl (inr tt) : red_tens_graph) = [set Some (Some (Some None)); None] /\
  edges_at_out (inl (inr tt) : red_tens_graph) = set0 /\
  edges_at_in (inr tt : red_tens_graph) = [set Some (Some None); Some None] /\
  edges_at_out (inr tt : red_tens_graph) = set0.
Proof. splitb; apply /setP; move => [[[[[[[? ?] | []] | []] | ] | ] | ] | ]; by rewrite !in_set. Qed.


Lemma red_tens_p_deg : proper_degree red_tens_graph.
Proof.
  destruct red_tens_edges_at_new as [Lin [Lout [Rin Rout]]].
  move => b [[[u Hu] | []] | []] /=.
  - rewrite -(p_deg b u) (red_tens_transport_edges _ Hu) card_imset //.
    apply red_tens_transport_inj.
  - destruct b; by rewrite ?Lin ?Lout ?cards2 ?cards0.
  - destruct b; by rewrite ?Rin ?Rout ?cards2 ?cards0.
Qed.

Lemma red_tens_forms :
  flabel (right_tens Htens)^ = flabel (left_parr Hparr)  /\
  flabel (left_tens Htens)^ = flabel (right_parr Hparr).
Proof.
  destruct (p_ax_cut_bis G) as [_ Hpcut]. (* Get information about the removed cut *)
  assert (Hvet : et \in edges_at_in v) by by rewrite in_set Het.
  revert Hpcut => /(_ _ Hcut _ Hvet) /eqP-Hpcut.
  assert (Ht := p_tens_bis Htens).
  assert (Hp := p_parr_bis Hparr).
  assert (et = ccl_tens Htens /\ ep = ccl_parr Hparr) as [Hct Hcp] by (split; apply ccl_eq; caseb).
  rewrite -Hct in Ht.
  rewrite -Hcp in Hp.
  assert (Hoep : ep = other (pre_proper_cut Hcut) Hvet).
  { apply other_eq.
    - by rewrite in_set Hep.
    - intro Hc; clear - Hc Htens Hparr; contradict Hparr.
      by rewrite Hc Htens. }
  rewrite -Hoep Ht Hp {Hoep Hvet Hct Hcp Ht Hp} in Hpcut.
  by inversion Hpcut.
Qed.

Lemma red_tens_p_ax_cut : proper_ax_cut red_tens_graph.
Proof.
  unfold proper_ax_cut.
  destruct red_tens_forms as [Hl Hr].
  move => b [[[w W] | []] | []] /= R.
  - destruct (p_ax_cut R) as [el [er H]].
    revert H; rewrite (red_tens_transport_edges _ W) Imset.imsetE 2!in_set.
    move => [/imageP[El ? ?] [/imageP[Er ? ?] Heq]]. subst el er.
    rewrite !red_tens_transport_flabel in Heq.
    by exists El, Er.
  - destruct b; [ | by contradict R].
    exists None, (Some (Some (Some None))).
    by rewrite !in_set Hr.
  - destruct b; [ | by contradict R].
    exists (Some None), (Some (Some None)).
    by rewrite !in_set Hl.
Qed.

Lemma red_tens_p_tens_parr : proper_tens_parr red_tens_graph.
Proof.
  unfold proper_tens_parr.
  intros b [[[w W] | []] | []] Hl; cbn in Hl.
  all: try (destruct b; by contradict Hl).
  destruct (p_tens_parr Hl) as [el [er [ec H]]].
  revert H; rewrite !(red_tens_transport_edges _ W) Imset.imsetE !in_set.
  move => [/imageP[El Elin ?] [Hll [/imageP[Er Erin ?] [Hrl [/imageP[Ec Ecin ?] Heq]]]]].
  subst el er ec.
  rewrite (red_tens_transport_llabel Elin) in Hll.
  rewrite (red_tens_transport_llabel Erin) in Hrl.
  rewrite !red_tens_transport_flabel in Heq.
  by exists El, Er, Ec.
Qed.

Lemma red_tens_p_noleft : proper_noleft red_tens_graph.
Proof. move => [[[[[[? | []] | []] | ] | ] | ] | ] ? //. by apply p_noleft. Qed.

Lemma red_tens_p_order : proper_order red_tens_graph_data.
Proof.
  unfold proper_order, red_tens_graph_data, red_tens_order; cbn.
  destruct (all_sigP _) as [l L]. split.
  - intros [[[[[[f | []] | []] | ] | ] | ] | ]; cbn.
    { rewrite mem_map; [ | repeat (apply inj_comp; trivial)].
      rewrite in_seq_sig -L.
      apply p_order. }
    all: split; move => H //.
    all: contradict H; apply /negP; clear.
    all: induction l as [ | ? ? IH]; first by trivial.
    all: by rewrite map_cons in_cons IH.
  - rewrite map_inj_uniq; [ | repeat (apply inj_comp; trivial)].
    rewrite uniq_seq_sig -L.
    apply p_order.
Qed.

Definition red_tens_ps : proof_structure := {|
  graph_data_of := red_tens_graph_data;
  p_deg := red_tens_p_deg;
  p_ax_cut := red_tens_p_ax_cut;
  p_tens_parr := red_tens_p_tens_parr;
  p_noleft := red_tens_p_noleft;
  p_order := red_tens_p_order;
  |}.


(** Sequent of an tensor - cut reduction *)
Lemma red_tens_sequent : sequent red_tens_graph_data = sequent G.
Proof.
  transitivity [seq flabel (red_tens_transport u) | u <- red_tens_order].
  { apply eq_map => ?. by rewrite red_tens_transport_flabel. }
  rewrite /red_tens_order -map_comp.
  destruct (all_sigP _) as [l L].
  by rewrite /sequent [in RHS]L -map_comp.
Qed.

(** Decreasing number of vertices *)
Lemma red_tens_nb : #|G| = #|red_tens_graph| + 1.
Proof.
  rewrite !card_add_vertex -card_induced_all [in LHS](card_inducedD1 _ (source et))
    [in LHS](card_inducedD1 _ (source ep)) [in LHS](card_inducedD1 _ v) !in_set.
  elim red_tens_ineq_if => _ [/eqP--> _].
  elim red_tens_ineq_in => V _.
  rewrite eq_sym V eq_sym V /=. lia.
Qed.


(** Correctness *)
Lemma red_tens_ineq_switching :
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
  { cbnb. rewrite Het Hep Hcut /=. cbnb. intros ?; subst.
    contradict Htens. by rewrite Hparr. }
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
  all: contradict Htens; by rewrite Hs ?Het ?Hep ?Hcut ?Hparr.
Qed.

Lemma red_tens_switching a f A F :
  switching a = switching f ->
  switching (Some (Some (Some (Some (inl (inl (Sub a A)))))) : edge red_tens_graph) =
  switching (Some (Some (Some (Some (inl (inl (Sub f F)))))) : edge red_tens_graph).
Proof. move => /eqP. unfold switching; case_if; cbnb. Qed.

Definition red_tens_upath_bwd (p : @upath _ _ red_tens_graph) : @upath _ _ G :=
  map (fun a => (red_tens_transport a.1, a.2)) p.

Lemma red_tens_upath_bwd_in (p : @upath _ _ red_tens_graph) :
  [forall b, (None, b) \notin p] -> [forall b, (Some None, b) \notin p] ->
  [forall b, (Some (Some None), b) \notin p] -> [forall b, (Some (Some (Some None)), b) \notin p] ->
  forall a b, (a, b) \in red_tens_upath_bwd p ->
  exists A, (Some (Some (Some (Some (inl (inl (Sub a A)))))), b) \in p.
Proof.
  induction p as [ | f p IH]; try by [].
  rewrite !forall_notincons => /andP[n N] /andP[sn SN] /andP[ssn SSN] /andP[sssn SSSN] a b.
  destruct f as ([[[[[[[f F] | []] | []] | ] | ] | ] | ], c);
  [ | by exfalso; revert sssn => /forallP /(_ c) /eqP
    | by exfalso; revert ssn => /forallP /(_ c) /eqP
    | by exfalso; revert sn => /forallP /(_ c) /eqP
    | by exfalso; revert n => /forallP /(_ c) /eqP].
  rewrite /= !in_cons. cbnb. introb.
  - exists F. caseb.
  - elim: (IH N SN SSN SSSN a b _) => // A In.
    exists A. rewrite in_cons In. caseb.
Qed.

Lemma red_tens_upath_bwd_nin_switching (p : @upath _ _ red_tens_graph) :
  [forall b, (None, b) \notin p] -> [forall b, (Some None, b) \notin p] ->
  [forall b, (Some (Some None), b) \notin p] -> [forall b, (Some (Some (Some None)), b) \notin p] ->
  switching (left_tens Htens) \notin [seq switching a.1 | a <- red_tens_upath_bwd p] /\
  switching (right_tens Htens) \notin [seq switching a.1 | a <- red_tens_upath_bwd p] /\
  switching (left_parr Hparr) \notin [seq switching a.1 | a <- red_tens_upath_bwd p] /\
  switching (right_parr Hparr) \notin [seq switching a.1 | a <- red_tens_upath_bwd p] /\
  switching et \notin [seq switching a.1 | a <- red_tens_upath_bwd p] /\
  switching ep \notin [seq switching a.1 | a <- red_tens_upath_bwd p].
Proof.
  intros. splitb.
  all: apply /mapP; move => [[a b] In S].
  all: apply red_tens_upath_bwd_in in In; trivial; destruct In as [A In].
  all: apply switching_eq in S; rewrite ?left_e ?right_e /= in S.
  all: clear - A S Het Hep; contradict A; apply /negP.
  all: rewrite !in_set -S ?Hep ?Het; caseb.
Qed.

Lemma red_tens_upath_Some (p : @upath _ _ red_tens_graph) (u w : red_tens_graph) :
  p <> nil -> supath switching u w p ->
  [forall b, (None, b) \notin p] -> [forall b, (Some None, b) \notin p] ->
  [forall b, (Some (Some None), b) \notin p] -> [forall b, (Some (Some (Some None)), b) \notin p] ->
  exists u' U' w' W', u = inl (inl (Sub u' U')) /\ w = inl (inl (Sub w' W')) /\
  supath switching u' w' (red_tens_upath_bwd p).
Proof.
  revert u w. induction p as [ | a p IH] => // u w _ P.
  rewrite !forall_notincons => /andP[n N] /andP[sn SN] /andP[ssn SSN] /andP[sssn SSSN].
  destruct a as ([[[[[[[a A] | []] | []] | ] | ] | ] | ], b);
  [ | by exfalso; revert sssn => /forallP /(_ b) /eqP
    | by exfalso; revert ssn => /forallP /(_ b) /eqP
    | by exfalso; revert sn => /forallP /(_ b) /eqP
    | by exfalso; revert n => /forallP /(_ b) /eqP].
  revert P; unfold supath at 1; cbn; rewrite in_cons
    => /andP[/andP[/andP[/eqP ? W] /andP[U0 U1]] /norP[_ N']]; subst u.
  rewrite SubK'. rewrite SubK' in W.
  assert (P : supath switching (inl (inl (Sub (endpoint b a) (induced_proof b A))) :
    red_tens_graph) w p) by splitb.
  destruct p as [ | f p].
  { exists (endpoint (~~ b) a), (induced_proof (~~ b) A),
      (endpoint b a), (induced_proof b A).
    revert W; cbn => /eqP ?; subst w.
    splitb. }
  assert (Hr : f :: p <> [::]) by by [].
  destruct (IH _ _ Hr P N SN SSN SSSN) as [x [X [y [Y [Hx [Hy P']]]]]].
  clear Hr IH.
  revert Hx => /eqP Hx; cbn in Hx; simpl in Hx; revert Hx => /eqP ?. subst w x.
  exists (endpoint (~~ b) a), (induced_proof (~~ b) A), y, Y.
  revert P'.
  remember (f :: p) as p'.
  unfold supath; cbn => /andP[/andP[W' U'] N''].
  splitb.
  revert U0; apply contra => /mapP [[d db] In Seq]; apply /mapP.
  destruct (red_tens_upath_bwd_in N SN SSN SSSN In) as [D ?].
  exists (Some (Some (Some (Some (inl (inl (Sub d D)))))), db); trivial.
  by apply red_tens_switching.
Qed.

Lemma red_tens_uacyclic_nocut :
  uacyclic (@switching _ G) ->
  forall (p : @upath _ _ red_tens_graph) (u : red_tens_graph),
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

Lemma red_tens_upath_fN p u U w W :
  supath switching (inl (inl (Sub u U)) : red_tens_graph) (inl (inl (Sub w W))) p ->
  (forward None \in p -> exists l r, p = l ++ forward None :: backward (Some (Some (Some None))) :: r) /\
  (forward (Some None) \in p -> exists l r, p = l ++ forward (Some None) :: backward (Some (Some None)) :: r) /\
  (forward (Some (Some None)) \in p -> exists l r, p = l ++ forward (Some (Some None)) :: backward (Some None) :: r) /\
  (forward (Some (Some (Some None))) \in p -> exists l r, p = l ++ forward (Some (Some (Some None))) :: backward None :: r).
Proof.
  move => P; splitb => In.
  all: destruct (in_elt_sub In) as [n N].
  all: set l := take n p; set r := drop n.+1 p.
  all: exists l, (behead r); f_equal; f_equal.
  all: rewrite N -/l -/r; rewrite N -/l -/r in P.
  all: destruct (supath_subKK P) as [_ R]; clear - R.
  all: revert R; rewrite /supath /= in_cons => /andP[/andP[/andP[_ ?] /andP[? _]] _].
  all: by destruct r as [ | ([[[[[[[? ?] | []] | []] | ] | ] | ] | ], []) ?].
Qed.

Lemma red_tens_upath_bN p u U w W :
  supath switching (inl (inl (Sub u U)) : red_tens_graph) (inl (inl (Sub w W))) p ->
  (backward None \in p -> exists l r, p = l ++ forward (Some (Some (Some None))) :: backward None :: r) /\
  (backward (Some None) \in p -> exists l r, p = l ++ forward (Some (Some None)) :: backward (Some None) :: r) /\
  (backward (Some (Some None)) \in p -> exists l r, p = l ++ forward (Some None) :: backward (Some (Some None)) :: r) /\
  (backward (Some (Some (Some None))) \in p -> exists l r, p = l ++ forward None :: backward (Some (Some (Some None))) :: r).
Proof.
  move => P.
  destruct (red_tens_upath_fN (supath_revK P)) as [N [SN [SSN SSSN]]].
  splitb => In; [set H := N | set H := SN | set H := SSN | set H := SSSN].
  1: assert (In' : forward None \in upath_rev p) by by rewrite (upath_rev_in p).
  2: assert (In' : forward (Some None) \in upath_rev p) by by rewrite (upath_rev_in p).
  3: assert (In' : forward (Some (Some None)) \in upath_rev p) by by rewrite (upath_rev_in p).
  4: assert (In' : forward (Some (Some (Some None))) \in upath_rev p) by by rewrite (upath_rev_in p).
  all: destruct (H In') as [l [r Hp]].
  all: exists (upath_rev (r : @upath _ _ red_tens_graph)), (upath_rev (l : @upath _ _ red_tens_graph)).
  all: by rewrite -(upath_rev_inv p) Hp upath_rev_cat /= -!cats1 -!catA.
Qed.

Lemma red_tens_NSSSN p u U w W :
  supath switching (inl (inl (Sub u U)) : red_tens_graph) (inl (inl (Sub w W))) p ->
  [forall b, (None, b) \notin p] -> [forall b, (Some (Some (Some None)), b) \notin p].
Proof.
  intro P.
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

Lemma red_tens_SNSSN p u U w W :
  supath switching (inl (inl (Sub u U)) : red_tens_graph) (inl (inl (Sub w W))) p ->
  [forall b, (Some None, b) \notin p] -> [forall b, (Some (Some None), b) \notin p].
Proof.
  intro P.
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

Lemma red_tens_upath_SomeNoneNot_ff :
  uacyclic (@switching _ G) ->
  forall p u U,
  supath switching (inl (inl (Sub u U)) : red_tens_graph) (inl (inl (Sub u U))) p ->
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
    assert (Hr : upath_target (inl (inl (Sub u U)) : red_tens_graph) l =
      source (Some None : edge red_tens_graph)).
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
  assert (Hr : upath_source (inl (inl (Sub u U)) : red_tens_graph) r =
    source (Some (Some None) : edge red_tens_graph)).
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
  destruct red_tens_ineq_switching as [? [_ [_ [_ [_ [_ [? [? [_ [? [_ [_ [? ?]]]]]]]]]]]]].
  assert (NN : m <> nil).
  { intros ?; subst m.
    revert M; rewrite /supath; cbnb => /andP[/andP[/eqP-Hc _] _].
    enough (Pc : supath switching (source (right_tens Htens)) (source (right_parr Hparr))
      (forward (right_tens Htens) :: forward et :: backward ep :: backward (right_parr Hparr) :: nil)).
    { rewrite Hc in Pc.
      specialize (A _ {| upval := _ ; upvalK := Pc |}).
      contradict A; cbnb. }
    rewrite /supath /= !in_cons.
    repeat (apply /andP; split); repeat (apply /norP; split); trivial; apply /eqP;
    rewrite // ?right_e ?Het ?Hep; caseb. }
  destruct (red_tens_upath_Some NN M N SN SSN SSSN) as [x [X [y [Y [Hx [Hy Pxy]]]]]].
  revert Hx => /eqP; cbnb => /eqP ?; subst x.
  revert Hy => /eqP; cbnb => /eqP ?; subst y.
  enough (Pf : supath switching (source (right_parr Hparr)) (source (right_parr Hparr))
    (forward (right_parr Hparr) :: forward ep :: backward et :: backward (right_tens Htens) ::
    (red_tens_upath_bwd m))).
  { specialize (A _ {| upval := _ ; upvalK := Pf |}).
    contradict A; cbnb. }
  revert Pxy => /andP[/andP[Wn Un] ?].
  rewrite /supath /= !in_cons.
  destruct (red_tens_upath_bwd_nin_switching N SN SSN SSSN) as [? [? [? [? [? ?]]]]].
  splitb; simpl; try (by apply /eqP; apply nesym); rewrite ?right_e ?Het ?Hep; caseb.
Qed.

Lemma red_tens_upath_SomeNoneNot_fb  :
  uacyclic (@switching _ G) ->
  forall p u U,
  supath switching (inl (inl (Sub u U)) : red_tens_graph) (inl (inl (Sub u U))) p ->
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
    assert (Hr : upath_target (inl (inl (Sub u U)) : red_tens_graph) l =
      source (Some None : edge red_tens_graph)).
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
  assert (Hr : upath_source (inl (inl (Sub u U)) : red_tens_graph) r =
    source (Some (Some None) : edge red_tens_graph)).
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
  destruct red_tens_ineq_switching as [_ [? _]].
  assert (NN : m <> nil).
  { intros ?; subst m.
    revert M; rewrite /supath; cbnb => /andP[/andP[/eqP Hc _] _].
    enough (Pc : supath switching (source (left_tens Htens)) (source (right_tens Htens))
      [:: forward (left_tens Htens); backward (right_tens Htens)]).
    { rewrite Hc in Pc.
      specialize (A _ {| upval := _ ; upvalK := Pc |}).
      contradict A; cbnb. }
    rewrite /supath /= !in_cons.
    repeat (apply /andP; split); repeat (apply /norP; split); trivial; apply /eqP;
    rewrite // ?left_e ?right_e ?Het ?Hep; caseb. }
  destruct (red_tens_upath_Some NN M N SN SSN SSSN) as [x [X [y [Y [Hx [Hy Pxy]]]]]].
  revert Hx => /eqP; cbnb => /eqP ?; subst x.
  revert Hy => /eqP; cbnb => /eqP ?; subst y.
  enough (Pf : supath switching (source (left_tens Htens)) (source (left_tens Htens))
    (forward (left_tens Htens) :: backward (right_tens Htens) ::
    (red_tens_upath_bwd m))).
  { specialize (A _ {| upval := _ ; upvalK := Pf |}).
    contradict A; cbnb. }
  revert Pxy => /andP[/andP[Wn Un] ?].
  rewrite /supath /= !in_cons.
  destruct (red_tens_upath_bwd_nin_switching N SN SSN SSSN) as [? [? [? [? [? ?]]]]].
  splitb; simpl; try (by apply /eqP; apply nesym); apply /eqP; rewrite ?left_e ?right_e ?Het ?Hep; caseb.
Qed.

Lemma red_tens_upath_SomeNoneNot :
  uacyclic (@switching _ G) ->
  forall p u U b,
  supath switching (inl (inl (Sub u U)) : red_tens_graph) (inl (inl (Sub u U))) p ->
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

Lemma red_tens_upath_NoneNot :
  uacyclic (@switching _ G) ->
  forall p u U b,
  supath switching (inl (inl (Sub u U)) : red_tens_graph) (inl (inl (Sub u U))) p ->
  (None, b) \in p ->
  [forall c, (Some None, c) \notin p].
Proof.
  move => A p u U b P In.
  apply /forallPn; move => [c /negPn Hc].
  assert (Nin := red_tens_upath_SomeNoneNot A P Hc).
  revert Nin => /forallP /(_ b) Nin.
  by contradict In; apply /negP.
Qed.

Lemma red_tens_uacyclic_notcut_None :
  uacyclic (@switching _ G) -> forall u U b p,
  supath switching (inl (inl (Sub u U)) : red_tens_graph) (inl (inl (Sub u U))) p ->
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
  assert (P' : supath switching (source (Some (Some (Some None)) : edge red_tens_graph))
    (source (None : edge red_tens_graph)) (r ++ l)).
  { clear - P.
    assert (P' := supath_turnsK P).
    change ([:: forward None, backward (Some (Some (Some None))) & r] ++ l) with
      ([:: forward None; backward (Some (Some (Some None)))] ++ r ++ l) in P'.
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
    destruct red_tens_ineq_switching as [? [_ [? [? [_ [? [_ [_ [_ [_ [_ [_ [? ?]]]]]]]]]]]]].
    repeat (apply /andP; split); repeat (apply /norP; split); trivial; apply /eqP;
    rewrite // ?left_e ?right_e ?Het ?Hep; caseb. }
  destruct (red_tens_upath_Some NN' P' N' SN' SSN' SSSN') as [x [X [y [Y [Hx [Hy Pxy]]]]]].
  revert Hx => /eqP; cbnb => /eqP ?; subst x.
  revert Hy => /eqP; cbnb => /eqP ?; subst y.
  enough (Pf : supath switching (source (right_parr Hparr)) (source (right_parr Hparr))
    (forward (right_parr Hparr) :: forward ep :: backward et :: backward (left_tens Htens) ::
    (red_tens_upath_bwd (r ++ l)))).
  { specialize (A _ {| upval := _ ; upvalK := Pf |}).
    contradict A; cbnb. }
  revert Pxy => /andP[/andP[W Un] ?].
  rewrite /supath /= !in_cons.
  destruct red_tens_ineq_switching as [? [_ [? [? [_ [? [_ [_ [_ [_ [_ [_ [? ?]]]]]]]]]]]]].
  destruct (red_tens_upath_bwd_nin_switching N' SN' SSN' SSSN') as [? [? [? [? [? ?]]]]].
  splitb; simpl; try (by apply /eqP; apply nesym); rewrite // ?left_e ?right_e ?Het ?Hep; caseb.
Qed.

Lemma red_tens_uacyclic_notcut_SomeNone :
  uacyclic (@switching _ G) -> forall u U b p,
  supath switching (inl (inl (Sub u U)) : red_tens_graph) (inl (inl (Sub u U))) p ->
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
  assert (P' : supath switching (source (Some (Some None) : edge red_tens_graph))
    (source (Some None : edge red_tens_graph)) (r ++ l)).
  { clear - P.
    assert (P' := supath_turnsK P).
    change ([:: forward (Some None), backward (Some (Some None)) & r] ++ l) with
      ([:: forward (Some None); backward (Some (Some None))] ++ r ++ l) in P'.
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
  destruct red_tens_ineq_switching as [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
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
  destruct (red_tens_upath_bwd_nin_switching N' SN' SSN' SSSN') as [? [? [? [? [? ?]]]]].
  splitb; simpl; try (by apply /eqP; apply nesym); rewrite // ?left_e ?right_e ?Het ?Hep; caseb.
Qed.

Lemma red_tens_uacyclic_notcut :
  uacyclic (@switching _ G) -> forall u U p,
  supath switching (inl (inl (Sub u U)) : red_tens_graph) (inl (inl (Sub u U))) p ->
  p = [::].
Proof.
  move => A u U p P.
  remember [forall b, (None, b) \notin p] as Hn eqn:N; symmetry in N. destruct Hn.
  - remember [forall b, (Some None, b) \notin p] as Hsn eqn:SN; symmetry in SN. destruct Hsn.
    + apply (red_tens_uacyclic_nocut A P); trivial.
      * by apply (red_tens_SNSSN P).
      * by apply (red_tens_NSSSN P).
    + revert SN => /negP/negP/forallPn[b /negPn-SN].
      apply (red_tens_uacyclic_notcut_SomeNone A P SN).
  - revert N => /negP/negP/forallPn[b /negPn-N].
    apply (red_tens_uacyclic_notcut_None A P N).
Qed.

Lemma red_tens_uacyclic :
  uacyclic (@switching _ G) -> uacyclic (@switching _ red_tens_ps).
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
(* TODO voir si ce n'est pas plus simple de dire il existe ou pas tel chemin dans
le graphe d'origine, en reportant sur le nouveau on en déduit acyclique *)


Definition red_tens_image : edge G -> edge red_tens_graph :=
  fun e => if @boolP _ is AltTrue p then Some (Some (Some (Some (inl (inl (Sub e p))))))
    else if e == left_tens Htens then Some (Some (Some None))
    else if e == right_tens Htens then Some (Some None)
    else if e == left_parr Hparr then Some None
    else None.

Lemma red_tens_graph_1_card_edge :
  #|edge G| = #|edge (red_tens_graph_1 v et ep)| + 6.
Proof.
  rewrite /= red_tens_removed // card_set_subset cardsE.
  rewrite -cardsE (cardsD1 (left_tens Htens)) (cardsD1 (left_parr Hparr)) (cardsD1 (right_tens Htens))
    (cardsD1 (right_parr Hparr)) (cardsD1 et) (cardsD1 ep) !in_set /=.
  destruct red_tens_ineq_if as
    [_ [_ [_ [H1 [_ [H3 [_ [H5 [_ [H7 [_ [H9 [_ [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 H19]]]]]]]]]]]]]]]]]]]]].
  apply nesym in H12. apply nesym in H13. apply nesym in H14. apply nesym in H15.
  apply nesym in H16. apply nesym in H17. apply nesym in H18. apply nesym in H19.
  revert H1 H3 H5 H7 H9 H11 H12 H13 H14 H15 H16 H17 H18 H19 => /eqP--> /eqP--> /eqP--> /eqP-->
    /eqP--> /eqP--> /eqP--> /eqP--> /eqP--> /eqP--> /eqP--> /eqP--> /eqP--> /eqP-->.
  assert (ep != et) as ->.
  { clear - Htens Hparr. apply /eqP => ?; subst. contradict Hparr. by rewrite Htens. }
  rewrite /= cardsE. lia.
Qed. (* TODO voir comment gérer proprement ce red_tens_ineq_if *)

Lemma red_tens_nb_edges :
  #|edge G| = #|edge red_tens_graph| + 2.
Proof. rewrite !card_edge_add_edge !card_edge_add_vertex red_tens_graph_1_card_edge. lia. Qed.

Lemma red_tens_nb_parr :
  #|[set u : G | vlabel u == ⅋]| = #|[set u : red_tens_ps | vlabel u == ⅋]| + 1.
Proof.
  enough (#|[set u : G | vlabel u == ⅋] :\ (source ep)| =
    #|[set u : red_tens_ps | vlabel u == ⅋]|) as <-.
  { rewrite (cardsD1 (source ep)) !in_set Hparr /=. lia. }
  rewrite -!card_set_subset.
  assert (Hf : forall (u : {u : G | (u \notin [set source ep]) && (u \in [set w | vlabel w == ⅋])}),
    val u \in [set: G] :\ (source et) :\ (source ep) :\ v).
  { move => [u U] /=.
    rewrite /= !in_set.
    revert U; rewrite !in_set => /andP[/eqP ? /eqP U].
    splitb; apply /eqP; trivial.
    all: move => ?; subst u; contradict U; by rewrite ?Hcut ?Htens. }
  assert (Hf' : forall (u : {u : G | (u \notin [set source ep]) && (u \in [set w | vlabel w == ⅋])}),
    vlabel (inl (inl (Sub (val u) (Hf u))) : red_tens_graph) == ⅋).
  { by move => [? /=]; rewrite !in_set => /andP[_ /eqP-->]. }
  set f : {u : G | (u \notin [set source ep]) && (u \in [set w | vlabel w == ⅋])} ->
    {u : red_tens_graph | vlabel u == ⅋} :=
    fun u => Sub (inl (inl (Sub (val u) (Hf u)))) (Hf' u).
  assert (Hg : forall (u : {u : red_tens_graph | vlabel u == ⅋}),
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

Lemma red_tens_uconnected_nb :
  uacyclic (@switching _ G) ->
  uconnected_nb (@switching_left _ red_tens_graph) = uconnected_nb (@switching_left _ G).
Proof.
  move => A.
  assert (N := switching_left_uconnected_nb A).
  rewrite red_tens_nb_edges red_tens_nb_parr red_tens_nb in N.
  assert (N' : uconnected_nb (@switching_left _ G) + #|edge red_tens_ps|
    = #|red_tens_graph| + #|[set u : red_tens_ps | vlabel u == ⅋]|) by (simpl in *; lia).
  rewrite -(switching_left_uconnected_nb (red_tens_uacyclic A)) in N'. simpl in *. lia.
Qed.

Lemma red_tens_correct :
  correct G -> correct red_tens_graph.
Proof.
  move => [A C]. split.
  - by apply red_tens_uacyclic.
  - by rewrite red_tens_uconnected_nb.
Qed.

End red_tens_proof_structure.

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
  { apply /orP. destruct Hdone as [[e [<- <-]] | [et [ep [Het [Hep [<- <-]]]]]].
    - left. apply /existsP; exists e. splitb.
    - right. apply /existsP; exists et. apply /existsP; exists ep. rewrite Het Hep. splitb. }
  destruct (p_cut H) as [e [e' H']].
  revert H'; rewrite !in_set; move => [/eqP-Hin [/eqP-Hin' Heq]].
  rewrite -Hin in H.
  assert (Hout := p_deg_out (source e)).
  assert (Hout' := p_deg_out (source e')).
  assert (#|edges_at_out (source e)| <> 0 /\ #|edges_at_out (source e')| <> 0) as [? ?].
  { split; intro Hc; [set f := e | set f := e'].
    all: assert (Hf : f \in set0) by by rewrite -(cards0_eq Hc) in_set.
    all: contradict Hf; by rewrite in_set. }
  destruct (vlabel (source e)) eqn:Hle; try done; try (by left; exists e);
  destruct (vlabel (source e')) eqn:Hle'; try done; try (by left; exists e').
  - contradict Heq.
    enough (flabel e = tens (flabel (left_tens Hle)) (flabel (right_tens Hle))
      /\ flabel e' = tens (flabel (left_tens Hle')) (flabel (right_tens Hle'))) as [-> ->] by by [].
    assert (e = ccl_tens Hle /\ e' = ccl_tens Hle') as [He He'] by (split; apply ccl_eq; caseb).
    by rewrite {1}He {1}He' !p_tens_bis.
  - right; by exists e, e'.
  - right; by exists e', e.
  - contradict Heq.
    enough (flabel e = parr (flabel (left_parr Hle)) (flabel (right_parr Hle)) /\
      flabel e' = parr (flabel (left_parr Hle')) (flabel (right_parr Hle'))) as [-> ->] by by [].
    assert (e = ccl_parr Hle /\ e' = ccl_parr Hle') as [He He'] by (split; apply ccl_eq; trivial).
    by rewrite {1}He {1}He' !p_parr_bis.
Qed.

(** One step *)
Definition red_one_ps (G : proof_structure) (v : G) (H : vlabel v = cut) : proof_structure.
Proof.
  elim: (orb_sum (red_term H)).
  - move => /existsP/sigW[? /andP[/eqP-? /eqP-?]]; subst.
    by apply (red_ax_ps H).
  - move => /existsP/sigW[? /existsP/sigW[? /andP[/andP[/andP[/eqP-Het /eqP-Hep] /eqP-?] /eqP-?]]].
    by apply (red_tens_ps H Het Hep).
Defined.

Lemma red_one_correct (G : proof_structure) (v : G) (H : vlabel v = cut) :
  correct G -> correct (red_one_ps H).
Proof.
  unfold red_one_ps.
  elim: (orb_sum (red_term H)) => ? /=.
  - elim: (sigW _) => ? /andP[He ?]. set Hr := elimTF _ He; destruct Hr.
    apply red_ax_correct.
  - elim: (sigW _) => ? ?; elim: (sigW _); introb.
    by apply red_tens_correct.
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
  - elim: (sigW _) => *; elim: (sigW _); introb.
    apply red_tens_sequent.
Qed.

Lemma red_one_nb (G : proof_structure) (v : G) (H : vlabel v = cut) :
  #|red_one_ps H| < #|G|.
Proof.
  unfold red_one_ps.
  elim: (orb_sum (red_term H)) => ? /=.
  - elim: (sigW _) => e /andP[He Hax]. set Hr := elimTF eqP He; destruct Hr.
    rewrite (red_ax_nb H (elimTF eqP Hax)) /=. lia.
  - elim: (sigW _) => *. elim: (sigW _) => ? /andP[/andP[/andP[Het Hep] Htens] Hparr].
    rewrite (red_tens_nb H (elimTF eqP Het) (elimTF eqP Hep) (elimTF eqP Htens)
      (elimTF eqP Hparr)) /=. lia.
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

End Atoms.

(* TODO confluence, normalisation *)
