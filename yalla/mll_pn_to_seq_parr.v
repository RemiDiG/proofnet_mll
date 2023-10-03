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


Section Rem_node.
Context {G : proof_structure} {v : G}.
Hypothesis (V : vlabel v = ⊗ \/ vlabel v = ⅋) (T : terminal v).

(* Vertices neighbourhing v *)
Local Notation elv := (left V).
Local Notation erv := (right V).
Local Notation ecv := (ccl V).
Local Notation lv := (source elv).
Local Notation rv := (source erv).
Local Notation cv := (target ecv).

(** Base graph for removing a node and its eventual conclusion *) (* TODO faire comme add_node des cas selon vlabel_v pour factoriser ? *)
Definition rem_node_graph_1 := induced ([set: G] :\ v :\ cv).

(* Then add new conclusions *)
Lemma lv_inside : lv \in setT :\ v :\ cv.
Proof.
  rewrite !in_set !in_set1. splitb; apply /eqP => F.
  - assert (P : walk lv lv [:: elv ; ecv]) by by rewrite /= F ccl_e left_e; splitb.
    by specialize (ps_acyclic P).
  - assert (FF : lv = target elv) by by rewrite left_e.
    apply (no_selfloop FF).
Qed.

Lemma rv_inside : rv \in setT :\ v :\ cv.
Proof.
  rewrite !in_set !in_set1. splitb; apply /eqP => F.
  - assert (P : walk rv rv [:: erv ; ecv]) by by rewrite /= F ccl_e right_e; splitb.
    by specialize (ps_acyclic P).
  - assert (FF : rv = target erv) by by rewrite right_e.
    apply (no_selfloop FF).
Qed.

Definition rem_node_graph :=
  @add_concl_graph _ (@add_concl_graph _ rem_node_graph_1 (Sub rv rv_inside) c (flabel erv))
                     (inl (Sub lv lv_inside)) c (flabel elv).

Lemma vlabel_cv : vlabel cv = c.
Proof. apply /eqP. by rewrite -terminal_tens_parr. Qed.

Lemma v_neq_cv : v <> cv.
Proof. intro F. have := vlabel_cv. rewrite -F. by destruct V as [V' | V']; rewrite V'. Qed.

(* Give its order *)
Definition rem_node_transport (e : edge G) : edge rem_node_graph :=
  if @boolP _ is AltTrue p then Some (inl (Some (inl (Sub e p : edge rem_node_graph_1))))
  else if e == elv then None else Some (inl None).

Definition rem_node_order :=
  None :: (Some (inl None)) :: [seq rem_node_transport x | x <- [seq x <- order G | x != ecv]].

Definition rem_node_graph_data := {|
  graph_of := rem_node_graph;
  order := rem_node_order;
  |}.

Lemma rem_node_removed : edge_set (setT :\ v :\ cv) = setT :\ elv :\ erv :\ ecv.
Proof.
  assert (C := vlabel_cv).
  apply /setP => a. rewrite !in_set !in_set1 !andb_true_r.
  destruct (eq_comparable a ecv) as [? | Hc];
  [ | destruct (eq_comparable a erv) as [? | Hr]];
  [ | | destruct (eq_comparable a elv)];
  try by (subst a; rewrite ?left_e ?right_e !eq_refl ?andb_false_r).
  assert (a != ecv /\ a != erv /\ a != elv) as [-> [-> ->]] by by splitb; apply /eqP.
  simpl. splitb; apply /eqP.
  - by apply no_source_c.
  - intros ?. contradict Hc. by apply ccl_eq.
  - intros ?. contradict Hc. by apply one_target_c.
  - intros ?. contradict Hr. by apply right_eq2.
Qed.

Definition rem_node_transport' (e : edge rem_node_graph) : edge G :=
  match e with
  | Some (inl (Some (inl (exist a _)))) => a
  | Some (inl (Some (inr a)))           => match a with end
  | Some (inl None)                     => erv
  | Some (inr a)                        => match a with end
  | None                                => elv
  end.

Lemma rem_node_transport'_inj : injective rem_node_transport'.
Proof.
  assert (elv <> erv) by apply left_neq_right.
  move => [[[[[e E] | []] | ]| []] | ] [[[[[a A] | []] | ]| []] | ];
  cbnb; introb; cbnb.
  all: try by (contradict E || contradict A); apply /negP;
    rewrite rem_node_removed // !in_set !in_set1; caseb.
  by assert (erv <> elv) by by apply nesym.
Qed.

Lemma rem_node_transportK e :
  e <> ecv -> rem_node_transport' (rem_node_transport e) = e.
Proof.
  intros ?.
  unfold rem_node_transport, rem_node_transport'.
  case: {-}_ /boolP => In; cbnb. case_if.
  revert In. rewrite rem_node_removed !in_set !in_set1. introb.
Qed.

Lemma rem_node_transportK' e :
  rem_node_transport (rem_node_transport' e) = e.
Proof.
  unfold rem_node_transport, rem_node_transport'.
  destruct e as [[[[[e E] | []] | ] | []] | ];
  case: {-}_ /boolP => In.
  - cbnb.
  - by contradict E; apply /negP.
  - contradict In; apply /negP. rewrite rem_node_removed !in_set !in_set1. caseb.
  - case_if. by assert (erv <> elv) by apply nesym, left_neq_right.
  - contradict In; apply /negP. rewrite rem_node_removed !in_set !in_set1. caseb.
  - by rewrite eq_refl.
Qed.

Lemma flabel_rem_node_transport' e : flabel (rem_node_transport' e) = flabel e.
Proof. destruct e as [[[[[e E] | []] | ] | []] | ]; cbnb. Qed.

Lemma rem_node_transport_in_edges_at (b : bool) (e : edge G)
  (Hu : endpoint b e \in [set: G] :\ v :\ cv) :
  rem_node_transport e \in edges_at_outin b (inl (inl (Sub (endpoint b e) Hu)) : rem_node_graph).
Proof.
  rewrite in_set /rem_node_transport.
  case: {-}_ /boolP => In; cbnb; case_if; destruct b; cbnb.
  - contradict Hu; apply /negP. rewrite !in_set !in_set1 left_e. caseb.
  - revert In. rewrite rem_node_removed // !in_set !in_set1. introb.
    all: contradict Hu; apply /negP; rewrite !in_set !in_set1 ?right_e; caseb.
  - revert In. rewrite rem_node_removed // !in_set !in_set1. introb.
    contradict Hu; apply /negP.
    rewrite ccl_e !in_set !in_set1. caseb.
Qed.

Lemma rem_node_transport_edges u Hu b : edges_at_outin b u =
  [set rem_node_transport' a | a in edges_at_outin b (inl (inl (Sub u Hu)) : rem_node_graph)].
Proof.
  apply /setP => e. rewrite in_set.
  symmetry. destruct (eq_comparable u (endpoint b e)) as [? | Hc]; [subst u | ].
  - rewrite eq_refl. apply /imsetP. exists (rem_node_transport e).
    + apply rem_node_transport_in_edges_at.
    + rewrite rem_node_transportK //.
      intros ?; subst e.
      contradict Hu; apply /negP.
      rewrite !in_set !in_set1.
      destruct b; rewrite ?ccl_e; caseb.
  - transitivity false; last by by symmetry; apply /eqP; apply nesym.
    apply /imsetP; move => [[[[[[a A] | []] | ] | []] | ] Ain /= ?]; subst e.
    all: contradict Ain; apply /negP.
    all: rewrite !in_set eq_sym; destruct b; cbnb; by apply /eqP.
Qed.

Lemma rem_node_p_deg : proper_degree rem_node_graph.
Proof.
  move => b [[[u U] | []] | []] /=.
  - rewrite -p_deg rem_node_transport_edges card_imset //; by apply rem_node_transport'_inj.
  - destruct b.
    + assert (Hr : edges_at_in (inl (inr tt) : rem_node_graph) = [set Some (inl None)]).
      { apply /setP => e; rewrite !in_set in_set1. by destruct e as [[[[[? ?] | []] | ] | []] | ]. }
      by rewrite Hr cards1.
    + assert (Hr : edges_at_out (inl (inr tt) : rem_node_graph) = set0).
      { apply /setP => e; rewrite !in_set. by destruct e as [[[[[? ?] | []] | ] | []] | ]. }
      by rewrite Hr cards0.
  - destruct b.
    + assert (Hr : edges_at_in (inr tt : rem_node_graph) = [set None]).
      { apply /setP => e. rewrite !in_set in_set1. by destruct e as [[[[[? ?] | []] | ] | []] | ]. }
      by rewrite Hr cards1.
    + assert (Hr : edges_at_out (inr tt : rem_node_graph) = set0).
      { apply /setP => e. rewrite !in_set. by destruct e as [[[[[? ?] | []] | ] | []] | ]. }
      by rewrite Hr cards0.
Qed.

Lemma rem_node_p_ax_cut : proper_ax_cut rem_node_graph.
Proof.
  move => b [[[u U] | []] | []] /= Hu; try by destruct b.
  destruct (p_ax_cut Hu) as [el [er [Lin [Rin LR]]]].
  exists (rem_node_transport el), (rem_node_transport er).
  revert Lin. rewrite rem_node_transport_edges => /imsetP[al Al ?]. subst el.
  revert Rin. rewrite rem_node_transport_edges => /imsetP[ar Ar ?]. subst er.
  revert LR. rewrite !flabel_rem_node_transport' => LR.
  rewrite !rem_node_transportK'. splitb.
Qed.

Lemma rem_node_p_tens_parr : proper_tens_parr rem_node_graph.
Proof.
  move => b [[[u U] | []] | []] /= Hu; try by destruct b.
  destruct (p_tens_parr Hu) as [el [er [ec [Lin [Ll [Rin [Rl [Cin Elrc]]]]]]]].
  exists (rem_node_transport el), (rem_node_transport er), (rem_node_transport ec).
  revert Lin. rewrite rem_node_transport_edges => /imsetP[al Al ?]. subst el.
  revert Rin. rewrite rem_node_transport_edges => /imsetP[ar Ar ?]. subst er.
  revert Cin. rewrite rem_node_transport_edges => /imsetP[ac Ac ?]. subst ec.
  revert Elrc. rewrite !flabel_rem_node_transport' => Elrc.
  rewrite !rem_node_transportK'. splitb.
  - revert Ll. destruct al as [[[[[? ?] | []] | ] | []] | ]; cbnb.
  - revert Rl. destruct ar as [[[[[? ?] | []] | ] | []] | ]; cbnb.
    + contradict Ar. by rewrite !in_set.
    + by rewrite left_l.
Qed.

Lemma rem_node_p_noleft : proper_noleft rem_node_graph.
Proof. move => [[[[[e E] | []] | ]| []] | ] //=. by apply p_noleft. Qed.

Lemma rem_node_p_order_full : proper_order_full rem_node_graph_data.
Proof.
  rewrite /= /rem_node_order.
  move => [[[[[e E] | []] | ] | []] | ] //=.
  rewrite !in_cons /=.
  assert (Hr : Some (inl (Some (inl (Sub e E : edge rem_node_graph_1)))) = rem_node_transport e).
  { rewrite /rem_node_transport. case: {-}_ /boolP => [In | /negP //]. cbnb. }
  rewrite Hr {Hr}. split.
  - move => ?. apply map_f.
    rewrite mem_filter. splitb.
    + revert E. rewrite rem_node_removed !in_set !in_set1. introb.
    + by apply p_order_full.
  - move => /mapP[a A Ha].
    assert (a = e).
    { revert Ha. unfold rem_node_transport. case: {-}_ /boolP => [In | /negP //].
      case: {-}_ /boolP => [In' | /negP-? //]; last by case_if.
      move => /eqP. by cbnb => /eqP-->. }
    subst a.
    revert A. rewrite mem_filter. introb.
    by apply p_order_full.
Qed.

Lemma rem_node_p_order_uniq : proper_order_uniq rem_node_graph_data.
Proof.
  rewrite /proper_order_uniq /= in_cons /=. splitb.
  - apply /mapP; move => [a A] /eqP.
    rewrite /rem_node_transport.
    case: {-}_ /boolP => ?; case_if.
    revert A. rewrite mem_filter => /andP[_ A].
    apply p_order_full in A.
    contradict A.
    rewrite left_e. by destruct V as [H | H]; rewrite H.
  - apply /mapP; move => [a A] /eqP.
    rewrite /rem_node_transport.
    case: {-}_ /boolP => Ain; case_if.
    revert A. rewrite mem_filter => /andP[/eqP-A0 A].
    revert Ain. rewrite rem_node_removed // !in_set !in_set1. introb.
    apply p_order_full in A.
    contradict A.
    rewrite right_e. by destruct V as [H | H]; rewrite H.
  - rewrite map_inj_in_uniq.
    { apply filter_uniq, p_order_uniq. }
    intros a b.
    rewrite !mem_filter => /andP[_ A] /andP[_ B].
    rewrite /rem_node_transport.
    case: {-}_ /boolP => Ain;
    case: {-}_ /boolP => Bin => /eqP; case_if.
    enough (L : forall e, e \notin edge_set (setT :\ v :\ cv) -> e \in order G -> e = ecv).
    { transitivity (ccl V); [ | symmetry]; by apply L. }
    clear - T.
    intros a Ain A.
    apply p_order_full in A.
    revert Ain. rewrite rem_node_removed !in_set !in_set1. introb.
    + contradict A. rewrite right_e. destruct V as [H | H]; by rewrite H.
    + contradict A. rewrite left_e. destruct V as [H | H]; by rewrite H.
Qed.

Definition rem_node_ps := {|
  graph_data_of := rem_node_graph_data;
  p_deg := rem_node_p_deg;
  p_ax_cut := rem_node_p_ax_cut;
  p_tens_parr := rem_node_p_tens_parr;
  p_noleft := rem_node_p_noleft;
  p_order_full := rem_node_p_order_full;
  p_order_uniq := rem_node_p_order_uniq;
  |}.

End Rem_node.


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

(* We choose fwd for this direction, so that ihom is simpler *)
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
  case: {-}_ /boolP => [// | _]. by case: ifP.
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
  case: {-}_ /boolP => [// | _]. by repeat (case: ifP).
Qed.

Definition rem_parr_e_bij_bwd (e : edge G) : edge (add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None))) :=
  Sub (rem_parr_e_bij_bwd_1 e) (rem_parr_e_bij_bwd_helper e).

Lemma rem_parr_e_bij_bwd_last_case (e : edge G) :
  e \notin edge_set ([set: G] :\ v :\ cv) -> e != elv -> e != erv -> e == ecv.
Proof.
  by rewrite rem_node_removed // !in_set !in_set1 andb_true_r !negb_andb
    !negb_involutive => /orP[-> | /orP[-> | ->]].
Qed.

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

Definition rem_parr_pn := {| p_correct := rem_parr_ps_correct |}.

Lemma terminal_parr_is_sequentializing : sequentializing v.
Proof.
  rewrite /sequentializing V.
  exists rem_parr_pn. exact (iso_sym rem_parr_iso).
Qed.

End Sequentializing_parr.

End Atoms.