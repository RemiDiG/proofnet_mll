(* Sequentialisation - Definition of a sequentializing vertex *)
(* From a Proof Net, return a LL proof of the same sequent *)

From Coq Require Import Bool.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden".
From GraphTheory Require Import mgraph setoid_bigop structures.

From Yalla Require Export mll_prelim mll_def mll_basic mll_seq_to_pn.

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



Definition sequentializing {G : proof_net} (v : G) : Type :=
  match vlabel v with
  | ax => {A & G ≃ ax_pn A}
  | ⊗ => {'(G0, G1) : proof_net * proof_net & G ≃ add_node_ps_tens G0 G1}
  | ⅋ => {G0 : proof_net & G ≃ add_node_ps_parr G0}
  | cut => {'(G0, G1) : proof_net * proof_net & G ≃ add_node_ps_cut G0 G1}
  | c => void (* a conclusion node is never sequentializing *)
  end.

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

End Rem_node. (* TODO move this to the file with parr if not used for tens *)

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


Lemma splitting_cc_is_sequentializing (G : proof_net) (v : G) :
  splitting_cc v -> sequentializing v.
Proof.
Admitted.

Lemma terminal_parr_is_sequentializing (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal v -> sequentializing v.
Proof. intros. by apply splitting_cc_is_sequentializing, terminal_parr_is_splitting_cc. Qed.
*)

End Atoms.
