(* Sequentialisation *)
(* From a Proof Net, return a LL proof of the same sequent *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export mll_prelim graph_more mgraph_tree mll_def mll_basic mll_seq_to_pn.

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


Definition iso_to_isod (F G : proof_structure) (h : F ≃ G) :
  F ≃d perm_graph_data (sequent_iso_perm h) G.
Proof. eexists; simpl. apply perm_of_sequent_iso_perm. Defined.

(* sequentialisation : fonction reliant regles à noeuds => nb cut + quels tens lies à des cut *)
(* seuentialisation sans coupure puis avec (+ de cas ou en remplacant par des tens) *)



Definition sequentializing (G : proof_net) (v : G) : Type :=
  match vlabel v with
  | ax => {A & G ≃ ax_pn A}
  | ⊗ => {'(G0, G1) : proof_net * proof_net & G ≃ add_node_ps_tens G0 G1}
  | ⅋ => {G0 : proof_net & G ≃ add_node_ps_parr G0}
  | cut => {'(G0, G1) : proof_net * proof_net & G ≃ add_node_ps_cut G0 G1}
  | c => void (* a conclusion node is never sequentializing *)
  end.


Section Sequentializing_ax.
Context {G : proof_net} {v : G}.
Hypothesis (V : vlabel v = ax) (T : terminal v).

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
  apply correct_to_weak in C.
  destruct C as [_ C]. elim: (C (source e) u) => [[p /andP[/andP[W U] N]] _].
  destruct p as [ | (a, b) p]; first by (revert W => /= /eqP-->; caseb).
  revert W => /= /andP[/eqP-Hf W].
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
  revert Ina Ine Ine'. rewrite !FF !in_set. introb; subst; caseb.
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
  rewrite !in_set. splitb; apply /eqP => F.
  - assert (P : walk lv lv [:: elv ; ecv]) by by rewrite /= F ccl_e left_e; splitb.
    by specialize (ps_acyclic P).
  - assert (FF : lv = target elv) by by rewrite left_e.
    apply (no_selfloop FF).
Qed.

Lemma rv_inside : rv \in setT :\ v :\ cv.
Proof.
  rewrite !in_set. splitb; apply /eqP => F.
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
  apply /setP => a. rewrite !in_set.
  destruct (eq_comparable a ecv) as [? | Hc];
  [ | destruct (eq_comparable a erv) as [? | Hr]];
  [ | | destruct (eq_comparable a elv)];
  try by (subst a; rewrite ?left_e ?right_e !eq_refl ?andb_false_r).
  assert (a != ecv /\ a != erv /\ a != elv) as [-> [-> ->]] by by splitb; apply /eqP.
  splitb; apply /eqP.
  - by apply no_source_c.
  - intros ?. contradict Hc. by apply ccl_eq.
  - intros ?. contradict Hc. by apply one_target_c.
  - intros ?. contradict Hr. by apply right_eq2.
Qed.

Definition rem_node_transport' : edge rem_node_graph -> edge G :=
  fun e => match e with
  | Some (inl (Some (inl (exist a _)))) => a
  | Some (inl (Some (inr a))) => match a with end
  | Some (inl None) => erv
  | Some (inr a) => match a with end
  | None => elv
  end.

Lemma rem_node_transport'_inj : injective rem_node_transport'.
Proof.
  move => [[[[[e E] | []] | ]| []] | ] [[[[[a A] | []] | ]| []] | ];
  cbnb; introb; cbnb.
  all: try by (contradict E || contradict A); apply /negP; rewrite rem_node_removed // !in_set; caseb.
  - by assert (erv <> elv) by apply nesym, left_neq_right.
  - by assert (elv <> erv) by apply left_neq_right.
Qed.

Lemma rem_node_transportK e :
  e <> ecv -> rem_node_transport' (rem_node_transport e) = e.
Proof.
  intros ?.
  unfold rem_node_transport, rem_node_transport'.
  case: {-}_ /boolP => In; cbnb. case_if.
  revert In. rewrite rem_node_removed !in_set. introb.
Qed.

Lemma rem_node_transportK' e :
  rem_node_transport (rem_node_transport' e) = e.
Proof.
  unfold rem_node_transport, rem_node_transport'.
  destruct e as [[[[[e E] | []] | ] | []] | ];
  case: {-}_ /boolP => In.
  - cbnb.
  - by contradict E; apply /negP.
  - contradict In; apply /negP. rewrite rem_node_removed !in_set. caseb.
  - case_if. by assert (erv <> elv) by apply nesym, left_neq_right.
  - contradict In; apply /negP. rewrite rem_node_removed !in_set. caseb.
  - case_if.
Qed.

Lemma flabel_rem_node_transport' e : flabel (rem_node_transport' e) = flabel e.
Proof. destruct e as [[[[[e E] | []] | ] | []] | ]; cbnb. Qed.

Lemma rem_node_transport_in_edges_at (b : bool) (e : edge G)
  (Hu : endpoint b e \in [set: G] :\ v :\ cv) :
  rem_node_transport e \in edges_at_outin b (inl (inl (Sub (endpoint b e) Hu)) : rem_node_graph).
Proof.
  rewrite in_set /rem_node_transport.
  case: {-}_ /boolP => In; cbnb; case_if; destruct b; cbnb.
  - contradict Hu; apply /negP. rewrite !in_set left_e. caseb.
  - revert In. rewrite rem_node_removed // !in_set. introb.
    all: contradict Hu; apply /negP; rewrite !in_set ?right_e; caseb.
  - revert In. rewrite rem_node_removed // !in_set. introb.
    contradict Hu; apply /negP.
    rewrite ccl_e !in_set. caseb.
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
      rewrite !in_set.
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
      { apply /setP => e; rewrite !in_set. by destruct e as [[[[[? ?] | []] | ] | []] | ]. }
      by rewrite Hr cards1.
    + assert (Hr : edges_at_out (inl (inr tt) : rem_node_graph) = set0).
      { apply /setP => e; rewrite !in_set. by destruct e as [[[[[? ?] | []] | ] | []] | ]. }
      by rewrite Hr cards0.
  - destruct b.
    + assert (Hr : edges_at_in (inr tt : rem_node_graph) = [set None]).
      { apply /setP => e. rewrite !in_set. by destruct e as [[[[[? ?] | []] | ] | []] | ]. }
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

Lemma rem_node_p_order : proper_order rem_node_graph_data.
Proof.
  split.
  - rewrite /= /rem_node_order.
    move => [[[[[e E] | []] | ] | []] | ] //=.
    rewrite !in_cons /=.
    assert (Hr : Some (inl (Some (inl (Sub e E : edge rem_node_graph_1)))) = rem_node_transport e).
    { rewrite /rem_node_transport. case: {-}_ /boolP => [In | /negP //]. cbnb. }
    rewrite Hr {Hr}. split.
    + move => ?. apply map_f.
      rewrite mem_filter. splitb.
      * revert E. rewrite rem_node_removed !in_set. introb.
      * by apply p_order.
    + move => /mapP[a A Ha].
      assert (a = e).
      { revert Ha. unfold rem_node_transport. case: {-}_ /boolP => [In | /negP //].
        case: {-}_ /boolP => [In' | /negP-? //]; last by case_if.
        move => /eqP. by cbnb => /eqP-->. }
      subst a.
      revert A. rewrite mem_filter. introb.
      by apply p_order.
  - rewrite /= in_cons /=. splitb.
    + apply /mapP; move => [a A] /eqP.
      rewrite /rem_node_transport.
      case: {-}_ /boolP => ?; case_if.
      revert A. rewrite mem_filter => /andP[_ A].
      apply p_order in A.
      contradict A.
      rewrite left_e. by destruct V as [H | H]; rewrite H.
    + apply /mapP; move => [a A] /eqP.
      rewrite /rem_node_transport.
      case: {-}_ /boolP => Ain; case_if.
      revert A. rewrite mem_filter => /andP[/eqP-A0 A].
      revert Ain. rewrite rem_node_removed // !in_set. introb.
      apply p_order in A.
      contradict A.
      rewrite right_e. by destruct V as [H | H]; rewrite H.
    + rewrite map_inj_in_uniq.
      { apply filter_uniq, p_order. }
      intros a b.
      rewrite !mem_filter => /andP[_ A] /andP[_ B].
      rewrite /rem_node_transport.
      case: {-}_ /boolP => Ain;
      case: {-}_ /boolP => Bin => /eqP; case_if.
      enough (L : forall e, e \notin edge_set (setT :\ v :\ cv) -> e \in order G -> e = ecv).
      { transitivity (ccl V); [ | symmetry]; by apply L. }
      clear - T.
      intros a Ain A.
      apply p_order in A.
      revert Ain. rewrite rem_node_removed !in_set. introb.
      * contradict A. rewrite right_e. destruct V as [H | H]; by rewrite H.
      * contradict A. rewrite left_e. destruct V as [H | H]; by rewrite H.
Qed.

Definition rem_node_ps := {|
  graph_data_of := rem_node_graph_data;
  p_deg := rem_node_p_deg;
  p_ax_cut := rem_node_p_ax_cut;
  p_tens_parr := rem_node_p_tens_parr;
  p_noleft := rem_node_p_noleft;
  p_order := rem_node_p_order;
  |}.

End Rem_node.


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
Definition rem_parr_v_bij_fwd (u : add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None))) : G :=
  match u with
  | exist (inl (inl (inl (exist u _)))) _ => u
  | exist (inl (inl (inr tt)))          U => match (rem_parr_v_bij_fwd_helper0 U) with end
  | exist (inl (inr tt))                U => match (rem_parr_v_bij_fwd_helper1 U) with end
  | exist (inr (inl tt))                _ => v
  | exist (inr (inr tt))                _ => cv
  end.
Definition rem_parr_v_bij_fwd2 (u : add_node_graph parr_t (None : edge rem_parr_ps) (Some (inl None))) : G :=
  match val u with
  | inl (inl (inl a)) => val a
  | inr (inr tt)      => cv
  | _                 => v (* case inr (inl tt), other cases are absurd *)
  end.
(*
Time Print rem_parr_v_bij_fwd. (* Finished transaction in 1.474 secs (1.464u,0.007s) (successful) *)
Time Print rem_parr_v_bij_fwd2. (* Finished transaction in 0.517 secs (0.516u,0.s) (successful) *)
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

Lemma rem_parr_e_bij_helper2 e :
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
(* TODO does unfolding bwd later save time? *)
  assert (Vcv : vlabel cv = c) by by apply vlabel_cv.
  unfold rem_parr_e_bij_fwd, rem_parr_e_bij_bwd.
  intros [[[[[[[[[e Ein] | []] | ] | []] | ] | [[[] | []] | ]] | ] | ] E]; simpl.
  - case: {-}_ /boolP => E'; first by cbnb.
    exfalso. clear - E' Ein. by rewrite Ein in E'.
  - contradict E. by rewrite /= !in_set.
  - contradict E. by rewrite /= !in_set.
  - case: {-}_ /boolP => E'.
    + contradict E'; apply /negP. rewrite /= !in_set. caseb.
    + destruct (rem_parr_e_bij_helper2 E') as [[E'' | E''] | E''];
      revert E'' => /= /eqP-E'''; cbnb.
      * contradict Vcv. by rewrite E''' left_e V.
      * contradict Vcv. by rewrite E''' right_e V.
  - case: {-}_ /boolP => E'.
    + contradict E'; apply /negP. rewrite rem_node_removed // !in_set. caseb.
    + destruct (rem_parr_e_bij_helper2 E') as [[E'' | E''] | E''];
      revert E'' => /= /eqP-E'''; cbnb.
      * assert (L : llabel elv) by by apply left_l.
        contradict L; apply /negP.
        rewrite E'''. apply right_l.
      * contradict Vcv. by rewrite -E''' left_e V.
  - case: {-}_ /boolP => E'.
    + contradict E'; apply /negP. rewrite /= !in_set right_e. caseb.
    + destruct (rem_parr_e_bij_helper2 E') as [[E'' | E''] | E''];
      revert E'' => /= /eqP-E'''; cbnb.
      * assert (L : llabel elv) by by apply left_l.
        contradict L; apply /negP.
        rewrite -E'''. apply right_l.
      * contradict Vcv. by rewrite -E''' right_e V.
Qed. (* Too long: Finished transaction in 1585.044 secs (1581.541u,0.67s) (successful) *)

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
  - move => [[[[[[[[[e Ein] | []] | ] | []] | ] | [[[] | []] | ]] | ] | ] E] b //=.
    + contradict E. by rewrite !in_set.
    + contradict E. by rewrite !in_set.
    + destruct b; [trivial | by rewrite ccl_e].
    + destruct b; [by rewrite left_e | trivial].
    + destruct b; [by rewrite right_e | trivial].
  - move => [[[[[u Uin] | []] | []] | [[] | []]] U] //=.
    + destruct (rem_parr_v_bij_fwd_helper0 U).
    + destruct (rem_parr_v_bij_fwd_helper1 U).
    + by apply vlabel_cv.
  - move => [[[[[[[[[e Ein] | []] | ] | []] | ] | [[[] | []] | ]] | ] | ] E] //=; cbn.
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
(* clean and simplify this section *)

Lemma rem_parr_ps_correct : correct rem_parr_ps.
Proof. by refine (add_node_parr_correct' _ (iso_correct rem_parr_iso (p_correct G))). Qed.

Lemma terminal_parr_is_sequentializing : sequentializing v.
Proof.
  rewrite /sequentializing V.
  exists {| p_correct := rem_parr_ps_correct |}.
  exact (iso_sym rem_parr_iso).
Qed.

End Sequentializing_parr. (* TODO simplify all this, timeouts *)

(*
Definition rem_cut_graph_1 {G : proof_structure} {v : G} (H : vlabel v = cut) :=
  induced (setT :\ v).

(* Add two new conclusions *)
Lemma rem_cut_graph_helper {G : proof_structure} {v : G} (H : vlabel v = cut) :
  {'(e, f) & edges_at_in v = [set e; f] /\ e <> f /\ source e \in [set: G] :\ v /\ source f \in [set: G] :\ v}.
Proof.
  assert (C : exists e, [exists f, (e != f) && (edges_at_in v == [set e; f])]).
  { assert (C := pre_proper_cut H).
    revert C => /eqP/cards2P[e [f [? ?]]].
    exists e. apply /existsP. exists f. apply /andP. split; trivial. by apply /eqP. }
  revert C => /sigW[e] /existsP/sigW[f /andP[/eqP-? /eqP-In]].
  exists (e, f). splitb; trivial; [set a := e | set a := f].
  all: rewrite !in_set andb_true_r; apply /eqP.
  all: enough (v = target a) as -> by apply no_selfloop.
  all: enough (A : a \in edges_at_in v) by by revert A; rewrite in_set => /eqP-->.
  all: rewrite In !in_set; caseb.
Qed.

Definition rem_cut_graph {G : proof_structure} {v : G} (H : vlabel v = cut) : base_graph.
Proof.
  destruct (rem_cut_graph_helper H) as [[e f] [_ [_ [E F]]]].
  exact(@add_concl_graph _
    (@add_concl_graph _ (rem_cut_graph_1 H) (Sub (source e) E) c (flabel e))
      (inl (Sub (source f) F)) c (flabel f)).
Defined.

Definition splitting_cc (G : proof_net) (v : G) : bool :=
  match vlabel v as V return vlabel v = V -> bool with
  | ax => fun _ => terminal v
  | ⊗ => fun H => uconnected_nb (@switching_left _ (rem_node_graph (or_introl H))) == 2
  | ⅋ => fun H => uconnected_nb (@switching_left _ (rem_node_graph (or_intror H))) == 1
  | cut => fun H => uconnected_nb (@switching_left _ (rem_cut_graph H)) == 2
  | c => fun _ => false
  end Logic.eq_refl.

(* puis définir les graphes avec induced_sub S pour S dans 
equivalence_partition (is_uconnected f) [set: G] et là ça devient galère,
faire des vues pour se retrouver avec des il existe equi = [S S'] (il existe sur
set de finset, donc ok je pense) puis définir les Gi à partir de là,
montrer qu'ils sont uconnected_nb = 1, puis finalement que
G iso à add_node Gi *)*)



Lemma utree_switching_left (G : proof_net) :
  utree (@switching_left G).
Proof. split; [apply uacyclic_swithching_left, G | apply uconnected_from_nb1, G]. Qed.

Lemma partition_terminal_ccl (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  terminal v ->
  forall x, utree_part (@switching_left_sinj _ G) (utree_switching_left G) v x = Some (ccl_tens V) ->
  pblock (preim_partition (utree_part (@switching_left_sinj _ G) (utree_switching_left G) v) [set: G]) x
    = [set target (ccl_tens V)].
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  rewrite (terminal_tens_parr (or_introl V)) => /eqP-C.
  intros x X. apply /setP => y.
  assert (Spart := preim_partitionP (utree_part F T v) [set: G]).
  revert Spart => /andP[/eqP-Cov /andP[Triv _]].
  rewrite in_set -eq_pblock // ?Cov {Cov Triv} // preim_partition_pblock_eq // X {X}.
  destruct (eq_comparable y (target (ccl_tens V))) as [? | Y].
  - subst y. rewrite eq_refl. apply /eqP.
    unfold utree_part. destruct (utree_unique_path F T v (target (ccl_tens V))) as [P Pu].
    assert (S : supath switching_left v (target (ccl_tens V)) [:: forward (ccl_tens V)]).
    { rewrite /supath /= in_cons negb_orb ccl_e. splitb.
      by rewrite /switching_left C. }
    specialize (Pu {| upvalK := S |}). by subst P.
  - transitivity false; last by (symmetry; apply /eqP).
    apply /eqP.
    unfold utree_part. destruct (utree_unique_path F T v y) as [[p P] _].
    destruct p as [ | (e1, b1) p]; first by []. cbnb.
    destruct (eq_comparable e1 (ccl_tens V)); last by apply nesym.
    subst e1. exfalso.
    rewrite supath_cons in P. revert P => /andP[/andP[/andP[P1 /eqP-Vb1] U1] /eqP-N1].
    assert (b1 = true).
    { destruct b1; trivial. exfalso. destruct T as [A _].
      contradict Vb1. simpl.
      apply nesym in N1. simpl in N1.
      rewrite -[in RHS](ccl_e (or_introl V)).
      by apply nesym, (uacyclic_loop A). }
    subst b1. clear Vb1. simpl in *.
    destruct p as [ | e2 p].
    { clear - P1 Y. revert P1. rewrite /supath /=. introb. }
    rewrite supath_cons in P1. revert P1 => /andP[/andP[/andP[_ /eqP-Vb2] _] _].
    clear - U1 Vb2 C.
    destruct e2 as (e2, []); simpl in Vb2.
    + contradict Vb2. by apply no_source_c.
    + revert U1. rewrite map_cons in_cons => /norP[U1 _].
      contradict U1. apply /negP/negPn/eqP.
      simpl. f_equal.
      apply one_target_c; by rewrite Vb2.
Qed.

Lemma partition_terminal_utree_part (G : proof_net) (v : G) (V : vlabel v = ⊗) (x : G) :
  utree_part (@switching_left_sinj _ G) (utree_switching_left G) v x
    \in [set None; Some (left_tens V); Some (right_tens V); Some (ccl_tens V)].
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  unfold utree_part. destruct (utree_unique_path F T v x) as [[[ | e p] P] _].
  { by rewrite !in_set. }
  rewrite supath_cons in P. revert P => /andP[/andP[/andP[_ /eqP-EV] _] _].
  destruct e as (e, []); simpl in EV.
  - assert (E := ccl_eq (or_introl V) EV). subst e.
    rewrite !in_set. caseb.
  - enough (E : e \in [set left_tens V; right_tens V]).
    { revert E. rewrite !in_set => /orP[/eqP--> | /eqP-->]; caseb. }
    by rewrite -right_set in_set EV.
Qed.

Lemma partition_terminal_utree_part_ccl (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  terminal v ->
  utree_part (@switching_left_sinj _ G) (utree_switching_left G) v (target (ccl_tens V))
    = Some (ccl_tens V).
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  rewrite (terminal_tens_parr (or_introl V)) => /eqP-C.
  unfold utree_part. destruct (utree_unique_path F T v (target (ccl_tens V))) as [P Pu].
  assert (S : supath switching_left v (target (ccl_tens V)) [:: forward (ccl_tens V)]).
  { rewrite /supath /= in_cons negb_orb ccl_e /switching_left C. splitb. }
  specialize (Pu {| upvalK := S |}). by subst P.
Qed.

Lemma partition_terminal_utree_part_left (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  utree_part (@switching_left_sinj _ G) (utree_switching_left G) v (source (left_tens V))
    = Some (left_tens V).
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  unfold utree_part. destruct (utree_unique_path F T v (source (left_tens V))) as [P Pu].
  assert (S : supath switching_left v (source (left_tens V)) [:: backward (left_tens V)]).
  { rewrite /supath /= in_cons negb_orb left_e /switching_left left_e V. splitb. }
  specialize (Pu {| upvalK := S |}). by subst P. (* TODO tout simplifier comme ça ! *)
Qed.

Lemma partition_terminal_utree_part_right (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  utree_part (@switching_left_sinj _ G) (utree_switching_left G) v (source (right_tens V))
    = Some (right_tens V).
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  unfold utree_part. destruct (utree_unique_path F T v (source (right_tens V))) as [P Pu].
  assert (S : supath switching_left v (source (right_tens V)) [:: backward (right_tens V)]).
  { rewrite /supath /= in_cons negb_orb right_e /switching_left right_e V. splitb. }
  specialize (Pu {| upvalK := S |}). by subst P.
Qed.

Lemma partition_terminal_eq (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  terminal v ->
  preim_partition (utree_part (@switching_left_sinj _ G) (utree_switching_left G) v) [set: G] =
  [set pblock (preim_partition (utree_part (@switching_left_sinj _ G) (utree_switching_left G) v) [set: G])
         (source (left_tens V));
       pblock (preim_partition (utree_part (@switching_left_sinj _ G) (utree_switching_left G) v) [set: G])
         (source (right_tens V));
       [set v]; [set target (ccl_tens V)]].
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  intro VT.
  rewrite [in LHS]preim_partition_eq.
  apply /setP => P.
  symmetry.
  destruct (P \in [set pblock (preim_partition (utree_part F T v) [set: G]) x
    | x in [set: G]]) eqn:Pin.
  - revert Pin => /imsetP[x _ ?]. subst P.
    assert (Imx := partition_terminal_utree_part V x).
    revert Imx. rewrite !in_set => /orP[/orP[/orP[/eqP-X | /eqP-X] | /eqP-X] | /eqP-X].
    + apply utree_part_None in X. subst x.
      rewrite utree_part_v. caseb.
    + enough (pblock (preim_partition (utree_part F T v) [set: G]) x =
              pblock (preim_partition (utree_part F T v) [set: G]) (source (left_tens V)))
        as -> by caseb.
      apply /eqP. by rewrite preim_partition_pblock_eq // X partition_terminal_utree_part_left.
    + enough (pblock (preim_partition (utree_part F T v) [set: G]) x =
              pblock (preim_partition (utree_part F T v) [set: G]) (source (right_tens V)))
        as -> by caseb.
      apply /eqP. by rewrite preim_partition_pblock_eq // X partition_terminal_utree_part_right.
    + rewrite (partition_terminal_ccl VT X). caseb.
  - revert Pin => /negP/negP-Pin.
    apply /negP/negP.
    rewrite !in_set !negb_orb -(utree_part_v F)
      -(partition_terminal_ccl VT (partition_terminal_utree_part_ccl V VT)).
    splitb.
    all: apply /eqP => ?; subst P.
    all: contradict Pin; apply /negP/negPn.
    all: by apply imset_f.
Qed.
(* TODO this is a general lemma on trees, prove it purely in the graph part *)
(* généraliser : dans utree_part, un pblock par arete (la target / source non v) + pblock de v, qui est lui même *)


(* In the switching graph without any right premise, there is a partition separating the tree into
   the vertices on the left of v, and on its right *)
Lemma partition_terminal (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  terminal v ->
  {'(Sl, Sr) : {set G} * {set G} & partition [set Sl; Sr; [set v]; [set target (ccl_tens V)]] [set: G] /\
    uconnected (@switching_left (induced Sl)) /\ uconnected (@switching_left (induced Sr)) /\
    source (left_tens V) \in Sl /\ source (right_tens V) \in Sr}.
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  intro VT.
  assert (Spart := preim_partitionP (utree_part F T v) [set: G]).
  revert Spart => /andP[/eqP-Cov _].
  exists (pblock (preim_partition (utree_part F T v) [set: G]) (source (left_tens V)),
          pblock (preim_partition (utree_part F T v) [set: G]) (source (right_tens V))).
  split; [ | split; [ | split; [ | split]]]; trivial.
  - rewrite -(partition_terminal_eq V VT). apply tree_partition.
  - apply (@uconnected_utree_part _ _ _ _ _ _ _ _ F T v
      (@switching_left_induced_None_to _ _ _) (@switching_left_induced_eq_to _ _ _)).
    rewrite {2}(partition_terminal_eq V VT) !in_set. caseb.
  - apply (@uconnected_utree_part _ _ _ _ _ _ _ _ F T v
      (@switching_left_induced_None_to _ _ _) (@switching_left_induced_eq_to _ _ _)).
    rewrite {2}(partition_terminal_eq V VT) !in_set. caseb.
  - by rewrite mem_pblock Cov.
  - by rewrite mem_pblock Cov.
Qed.

(* We can do a case study on this, but not on sequentializing : Type *)
Definition splitting_tens_prop (G : proof_net) (v : G) (V : vlabel v = ⊗) (T : terminal v) :=
  let (SS, _) := (partition_terminal V T) in let (Sl, Sr) := SS in
  forall (p : G) (P : vlabel p = ⅋), (p \in Sl -> source (right_parr P) \in Sl)
                                  /\ (p \in Sr -> source (right_parr P) \in Sr).


Definition splitting_tens_bool (G : proof_net) (v : G) (V : vlabel v = ⊗) (T : terminal v) :=
  let (SS, _) := (partition_terminal V T) in let (Sl, Sr) := SS in
  [forall p : G, if @boolP (vlabel p == ⅋) is AltTrue P then ((p \in Sl) ==> (source (right_parr (eqP P)) \in Sl))
                                  && ((p \in Sr) ==> (source (right_parr (eqP P)) \in Sr)) else true].

Lemma splitting_tensP (G : proof_net) (v : G) (V : vlabel v = ⊗) (T : terminal v) :
  reflect (splitting_tens_prop V T) (splitting_tens_bool V T).
Proof.
  unfold splitting_tens_bool, splitting_tens_prop.
  destruct (partition_terminal V T) as [[Sl Sr] _].
  apply (iffP idP).
  - move => /forallP H p P.
    specialize (H p).
    revert H.
    case: {-}_ /boolP => P'.
    2:{ contradict P; by apply /eqP. }
    assert (eqP P' = P) as -> by apply eq_irrelevance.
    move => /andP[/implyP-? /implyP-?]. by split.
  - move => H.
    apply /forallP => p.
    case: {-}_ /boolP => P' //.
    specialize (H p (eqP P')). destruct H.
    apply /andP. split; by apply /implyP.
Qed.

Lemma splitting_tens_prop_is_sequentializing (G : proof_net) (v : G) (V : vlabel v = ⊗) (T : terminal v) :
  splitting_tens_prop V T -> sequentializing v.
Proof.
(* Taking induced of Sl (resp Sr).
Adding a concl on source (left_tens V).
This graph is correct: acyclicity is preserved by induced (lemma uacyclic_induced);
connectivity by hypothesis (Sl and Sr connected).
This graph is a proof structure: heavy, but should not be too hard (but
we need to add some concl edge ...).
Difficult part: G is isomorphic to add_tens ... with the usual problems of timeout
from Coq in this case, how to escape it ?
Should use an intermediate lemma of the form "there is no edges between Sl and Sr".
And of course, this will be divided across plenty of lemmas. *)
(* Admitted for now, to check that this is a good notion of splitting,
before doing this no-fun proof *)
Admitted.

Lemma sequentializing_tens_is_splitting_prop (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  sequentializing v -> {T : terminal v | splitting_tens_prop V T}.
Proof.
(* same as the proof above, but normally in a easier way (well, we still have an iso to
manipulate); by contradiction ? *)
Admitted.

(* A tensor is non-splitting because there is some ⅋ with its right edge in the other part
  of the partition *)
Lemma non_splitting_tens (G : proof_net) (v : G) (V : vlabel v = ⊗) (T : terminal v) :
  ~(splitting_tens_prop V T) -> {p : {p : G | vlabel p = ⅋} &
  let (SS, _) := (partition_terminal V T) in let (Sl, Sr) := SS in
  (projT1 p \in Sl /\ source (right_parr (projT2 p)) \in Sr) \/
  (projT1 p \in Sr /\ source (right_parr (projT2 p)) \in Sl)}.
Proof.
  move => /splitting_tensP.
  unfold splitting_tens_bool.
  destruct (partition_terminal V T) as [[Sl Sr] [Sp _]].
  apply cover_partition in Sp.
  move => /forallPn/sigW[p P].
  revert P. case: {-}_ /boolP => P' //.
  set (P := eqP P'). clearbody P. clear P'.
  rewrite negb_and => H.
  wlog: Sl Sr Sp H / ~~ ((p \in Sl) ==> (source (right_parr P) \in Sl)).
  { elim: (orb_sum H) => H'.
    - by move => /(_ Sl Sr Sp H H').
    - move => /(_ Sr Sl _ _ H').
      assert ([set Sr; Sl; [set v]; [set target (ccl_tens V)]] =
        [set Sl; Sr; [set v]; [set target (ccl_tens V)]]) as ->.
      { apply /setP => x. rewrite !in_set. f_equal. f_equal. by rewrite orb_comm. }
      rewrite orb_comm => /(_ Sp H) [pw Pw].
      exists pw. destruct Pw as [? | ?]; [by right | by left]. }
  clear H. rewrite negb_imply => /andP[In S].
  exists (exist _ p P). simpl.
  assert (Hr : ssrfun.svalP (exist (fun p => vlabel p = ⅋) p P) = P) by apply eq_irrelevance.
  rewrite Hr {Hr}.
  left. split; trivial.
  assert (In2 : source (right_parr P) \in cover [set Sl; Sr; [set v]; [set target (ccl_tens V)]])
    by by rewrite Sp in_set.
  revert In2.
  rewrite /cover !bigcup_setU !bigcup_set1 !in_set.
  move => /orP[/orP[/orP[In2 | //] | /eqP-In2] | /eqP-In2].
  - by rewrite In2 in S.
  - assert (H := terminal_source T In2). by rewrite right_e P in H.
  - contradict In2. apply no_source_c, (terminal_source T), ccl_e.
Qed.

Lemma correctness_parr (G : proof_net) (v : G) (V : vlabel v = ⊗) (T : terminal v)
  (NS : ~(splitting_tens_prop V T)) :
  let (P, _) := (non_splitting_tens NS) in let (p, P) := P in
  {'(k, k') : Supath switching v p * Supath switching v p &
  upath_disjoint switching k k'}.
Proof.
  destruct (non_splitting_tens NS) as [[p P] HP].
  destruct (partition_terminal V T) as [[Sl Sr] [Sp S]]. simpl in HP.
  assert (Hr : ssrfun.svalP (exist (fun p => vlabel p = ⅋) p P) = P) by apply eq_irrelevance.
  rewrite Hr {Hr} in HP.
  destruct S as [Ul [Ur [Inl Inr]]].
  specialize (Ul (Sub (source (left_tens V)) Inl)).
  specialize (Ur (Sub (source (right_tens V)) Inr)).
  assert (HP' : ((p \in Sl) && (source (right_parr P) \in Sr)) ||
     ((p \in Sr) && (source (right_parr P) \in Sl))).
  { destruct HP as [[? ?] | [? ?]]; apply /orP; [left | right]; by apply /andP. }
(* Do a wlog here, by generalizing Inl and Inr with a || ? seems hard du to Ul and Ur *)
  clear HP. elim: (orb_sum HP') => {HP'} /andP[Pin Spin].
  - specialize (Ul (Sub p Pin)).
    specialize (Ur (Sub (source (right_parr P)) Spin)).
    revert Ul => /sigW[MuL _].
    revert Ur => /sigW[MuR _].
    assert (KL := supath_from_induced_switching_left MuL). simpl in KL.
    assert (KR := supath_from_induced_switching_left MuR). simpl in KR.
    apply supath_switching_from_leftK in KL, KR.
    assert (SlvMuL : switching (left_tens V) \notin
      [seq switching b.1 | b <- [seq (val a.1, a.2) | a <- upval MuL]]).
    { rewrite {1}/switching left_e V /= -map_comp.
      apply /mapP. move => [[[a A] _] _ /= SA].
      assert (a = left_tens V).
      { revert SA. move => /eqP. unfold switching. case_if. }
      clear SA. subst a.
      clear - Sp Inl A.
      revert A. rewrite in_set left_e => /andP[_ Vin].
assert ([disjoint Sl & Sr] /\ [disjoint [set v] & Sl] /\ [disjoint [set target (ccl_tens V)] & Sl]
/\ [disjoint [set v] & Sr] /\ [disjoint [set target (ccl_tens V)] & Sr]
 /\ [disjoint [set v] & [set target (ccl_tens V)]]).
{ (* TODO do it for all pairs, in a(some) lemma(s) *) admit. }
rewrite !disjoints1 !in_set in _H.
      assert (T := partition_trivIset Sp). (* TODO lemma to prove all elems here are not only trivIset, but disjoint (even on the tree part) *)
      revert T => /trivIsetP /(_ Sl [set v]).
      rewrite !in_set 2!eq_refl orb_true_r /=.
      move => /(_ is_true_true is_true_true).
      assert (SV : Sl != [set v]).
      { apply /eqP => ?. subst Sl.
        contradict Inl. apply /negP.
        rewrite !in_set. apply /eqP.
        rewrite -[in RHS](left_e (or_introl V)).
        apply no_selfloop. }
      move => /(_ SV) {SV}.
      rewrite disjoint_sym disjoints1.
      by apply /negP/negPn. }
(* now: concatenate left and right of v to k and k' respectively, and prove they are disjoint *)
    assert (KL' : supath switching v p (backward (left_tens V) ::
      [seq (val a.1, a.2) | a <- upval MuL])).
    { by rewrite supath_cons KL left_e eq_refl !andb_true_r /=. }
    assert (KR' : supath switching v p (rcons (backward (right_tens V) ::
      [seq (val a.1, a.2) | a <- upval MuR]) (forward (right_parr P)))).
    { rewrite supath_rcons supath_cons KR !right_e !eq_refl map_cons in_cons !andb_true_r /=.
      splitb.
      - admit. (* idem before *)
      - by rewrite /switching !right_e P V.
      - admit. (* idem before *) }
    exists ({| upvalK := KL' |}, {| upvalK := KR' |}). simpl.
    unfold upath_disjoint.
    rewrite !map_cons map_rcons.
    rewrite disjoint_cons disjoint_sym disjoint_cons disjoint_rcons.
    rewrite in_cons in_rcons /=.
    splitb.
    + rewrite /switching left_e right_e V. cbn.
      apply /eqP. apply left_neq_right.
    + by rewrite /switching left_e right_e V P.
    + (* similar to the proof of SlvMuL *) admit.
    + (* similar to what is above *) admit.
    + (* ok as this edge go from Sr to Sl *) admit.
    + (* ok as they are in the disjoint Sl and Sr *) admit.
  - (* almost exactly the proof above - try to generalize *) admit.
Admitted.

Lemma case_todo_properly (G : proof_net) : {v : G & sequentializing v} + forall (v : G), (sequentializing v -> False).
Proof.
Admitted.

(* And then, descending path, followed by critical path *)


(* END NEW TRY *)

(* OLD TRY
Lemma terminal_parr_is_splitting_cc (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal v -> splitting_cc v.
Proof.
  intros V T.
  unfold splitting_cc. generalize (erefl (vlabel v)). rewrite {2 3}V => V'.
  assert (V = V') by apply eq_irrelevance. subst V'.
  enough (C : correct (rem_node_graph (or_intror V))) by by apply /eqP; destruct C.
  unfold rem_node_graph.
  destruct (rem_node_sources_stay (or_intror V)) as [e f].
  apply add_concl_correct, correct_to_weak, add_concl_correct. split.
  { apply uacyclic_induced, p_correct. }
  intros [x X] [y Y].
  destruct (correct_to_weak (p_correct G)) as [_ C].
  revert C => /(_ x y)/sigW[[p P] _].
  enough ({q : Supath switching_left (Sub x X : rem_node_graph_1 (or_intror V)) (Sub y Y) &
    p = [seq (val a.1, a.2) | a <- upval q]}) as [q _] by by exists q.
  revert x X P. induction p as [ | a p IH] => x X; rewrite /supath /=.
  { introb. replace Y with X by apply eq_irrelevance. by exists (supath_nil _ _). }
  rewrite in_cons => /andP[/andP[/andP[/eqP-? W] /andP[u U]] /norP[n N]]; subst x.
  destruct (utarget a \in [set: G] :\ v :\ target (ccl_parr V)) eqn:A.
  - destruct (IH _ A) as [q Hq].
    { splitb. }
    assert (Ain : a.1 \in edge_set ([set: G] :\ v :\ target (ccl_parr V))).
    { rewrite in_set. destruct a as [a []]; splitb. }
    assert (PA : supath switching_left (Sub (usource a) X : rem_node_graph_1 (or_intror V))
      (Sub (utarget a) A) [:: (Sub a.1 Ain, a.2)]).
    { rewrite /supath /= in_cons orb_false_r. splitb; try by cbnb.
      revert n. rewrite /switching_left /=. case_if. }
    enough (D : upath_disjoint switching_left {| upvalK := PA |} q).
    { exists (supath_cat D). cbn. rewrite Hq. f_equal. simpl. by destruct a. }
    rewrite /= /upath_disjoint disjoint_has /= orb_false_r.
    revert u. subst p.
    destruct q as [q Q]. rewrite -map_comp /=. clear.
    induction q as [ | c q IH]; trivial.
    rewrite /= !in_cons => /norP[k K]. apply /norP. rewrite IH //. splitb.
    revert k. rewrite /switching_left /=. case_if.
  - clear IH.
    assert (Vc : vlabel (target (ccl_parr V)) = c).
    { revert T. clear. rewrite (terminal_tens_parr (or_intror V)). apply /eqP. }
    assert (Ca : a = forward (left_parr V)).
    { clear - X A n Vc.
      revert A. rewrite !in_set andb_true_r => /nandP[/negPn/eqP-A | /negPn/eqP-A].
      - exfalso.
        destruct a as [a []].
        + assert (a = ccl_parr V) by by apply one_target_c.
          subst a.
          contradict X; apply /negP.
          rewrite !in_set /= ccl_e. caseb.
        + contradict A. simpl.
          by apply no_source_c.
      - destruct a as [a []].
        + simpl in A. f_equal.
          revert n. rewrite /switching_left /= A V /=. case_if.
          by apply left_eq.
        + assert (a = ccl_parr V) by by apply ccl_eq.
          subst a.
          contradict X; apply /negP.
          rewrite !in_set /=. caseb. }
    subst a.
    assert (Cp : p = [::] \/ p = [:: forward (ccl_parr V)]).
    { destruct p as [ | s p]; auto. right.
      assert (s = forward (ccl_parr V)).
      { revert W => /= /andP[/eqP-S W].
        rewrite left_e in S.
        destruct s as [s []]; simpl in *.
        - apply /eqP. cbn. rewrite andb_true_r. apply /eqP.
          by apply ccl_eq.
        - revert u N. rewrite !in_cons => /norP[S1 _] /norP[S2 _]. revert S1 S2.
          rewrite /switching_left left_e left_l S V /=.
          case_if.
          enough (left_parr V = s) by by [].
          symmetry. by apply left_eq. }
      subst s.
      destruct p as [ | r p]; trivial.
      exfalso. revert U W. clear - Vc.
      rewrite /= !in_cons => /andP[/norP[U _] _] /andP[_ /andP[/eqP-W _]].
      assert (r = backward (ccl_parr V)).
      { clear - W Vc.
        destruct r as [r []].
        - revert W. cbnb => W. contradict W.
          by apply no_source_c.
        - revert W. cbnb => W.
          apply /eqP. cbn. splitb. apply /eqP.
          by apply one_target_c. }
      subst r.
      contradict U. by apply /negP/negPn/eqP. }
    contradict Y. apply /negP. clear -Cp W.
    rewrite !in_set.
    revert W. destruct Cp; subst p; simpl.
    + move => /eqP-?; subst y. rewrite left_e. caseb.
    + move => /andP[_ /eqP-?]. subst y. caseb.
Qed.

Lemma splitting_cc_parr_is_sequentializing (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal v -> splitting_cc v -> sequentializing v.
Proof.
  intros V T.
  unfold splitting_cc. generalize (erefl (vlabel v)). rewrite {2 3}V => V' S.
  assert (V = V') by apply eq_irrelevance. subst V'.
  rewrite /sequentializing V.
  assert (C : correct (rem_node_graph (or_intror V))).
  { split; [ | by apply /eqP].
    apply union_edge_uacyclic; last by apply unit_graph_uacyclic.
    apply union_edge_uacyclic; last by apply unit_graph_uacyclic.
    apply uacyclic_induced, p_correct. }
  exists {| ps_of := rem_node_ps (or_intror V) T ; p_correct := C |}.
Abort.
(*
  assert (h := rem_node_iso (or_intror V) T).
  rewrite {1}V in h.
  apply h.
Qed.
*)

(* tenseur scindant ici, avec cut ... TODO traiter cut comme des tens ? *)


Lemma splitting_cc_is_sequentializing (G : proof_net) (v : G) :
  splitting_cc v -> sequentializing v.
Proof.
Admitted.

Lemma terminal_parr_is_sequentializing (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal v -> sequentializing v.
Proof. intros. by apply splitting_cc_is_sequentializing, terminal_parr_is_splitting_cc. Qed.
*)

Lemma has_sequentializing (G : proof_net) :
  {v : G & sequentializing v}.
Proof.
(* utiliser has_terminal, se ramener au cas où il n'y a que des cut / tens term
puis tenseur scindant *)
Admitted.

(* TODO admettre lemme tenseur scindant puis sequantialisation directement *)
(* ax : pas iso a G mais ps p iso à ax exp G *)
(* TODO ne séquentializer que des réseaux atomiques ! *)
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

(** ** Sequentialization *)
(* many things to do: spliting tens / cut, blocking parr, always a
  terminal parr or a splitting *)
(* function to turn a ps into a sequential proof *)
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
