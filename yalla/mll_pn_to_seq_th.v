(* Sequentialisation - Prove the theorem *)
(* From a Proof Net, return a LL proof of the same sequent *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export mll_prelim graph_more upath mgraph_tree mll_def mll_basic mll_seq_to_pn
  mll_pn_to_seq_def mll_pn_to_seq_ax mll_pn_to_seq_parr mll_pn_to_seq_tens mll_pn_to_seq.

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

Lemma uwalk_to_simple_upath {Lv Le : Type} {G : graph Lv Le} (s t : G) (p : upath) :
  uwalk s t p -> {q : Simple_upath G | upath_source s q = s /\ upath_target s q = t
  (*/\ {subset supval q <= p}*)}.
Proof.
(* TODO similar to uconnected_simpl *)
  revert s t. induction p as [ | e p IH] => s t.
  { move => /= /eqP-<-. by exists {| supval := [::] ; supvalK := simple_upath_nil G |}. }
  move => /= /andP[/eqP-? W]. subst s.
  move: IH => /(_ _ _ W) {W} [[q simple_q] /= [source_q target_q]].
  case/boolP: ((e.1 != (head e q).1) && (usource e \notin [seq usource _a | _a <- q]) &&
    (utarget e != t)).
  - move => H.
    enough (K : simple_upath (e :: q)) by by exists {| supval := _ ; supvalK := K |}.
    rewrite simple_upath_cons simple_q /= source_q eq_refl andb_true_r.
    destruct q as [ | eq q]; first by [].
    simpl in *.
    by rewrite target_q.
  - rewrite !negb_andb !negb_involutive.
    have [/eqP-t_eq | t_neq] := boolP (utarget e == t).
    + move=> _.
      by exists {| supval := [:: e] ; supvalK := simple_upath_edge e |}.
    + rewrite orb_false_r.
      have [se_in | se_nin] := boolP (usource e \in [seq usource a | a <- q]).
      * move=> _.
        move: se_in. rewrite in_elt_sub => /existsP/sigW[[n N] /= /eqP-sources_q].
        rewrite -{1}(cat_take_drop n [seq usource a | a <- q]) in sources_q.
        apply cat_eq_l in sources_q.
        assert (simple_drop : simple_upath (drop n q)).
        { move: simple_q. rewrite -{1}(cat_take_drop n q). by apply simple_upath_suffix. }
        exists {| supval := _ ; supvalK := simple_drop |}.
        rewrite /= !map_drop sources_q /=. split; trivial.
        move: target_q.
        rewrite -{1}(cat_take_drop n q) map_cat last_cat map_drop -source_q.
        clear source_q simple_drop sources_q t_neq.
        revert n N. generalize e. clear e.
        induction q as [ | eq q IH]; first by []; move => e n N /=.
        destruct n as [ | n].
        { by rewrite drop0 take0 /=. }
        move: simple_q. rewrite simple_upath_cons => /andP[/andP[/andP[/andP[simple_q _] /eqP-e_te_eq] _] _].
        rewrite /= e_te_eq /= => H. simpl in N.
        rewrite -(IH simple_q eq n); [ | clear -N; simpl in *; lia | by []].
        clear IH simple_q e_te_eq H.
        revert q N. induction n as [ | n IH] => q N; destruct q; try by [].
        simpl in *. apply IH. lia.
      * rewrite orb_false_r => /eqP-e1_eq.
        destruct q as [ | [eq b'] q].
        { by exists {| supval := [:: e] ; supvalK := simple_upath_edge e |}. }
        simpl in e1_eq. subst eq.
        move: simple_q. rewrite simple_upath_cons => /andP[/andP[/andP[/andP[simple_q _] /eqP-e_ta] _] _].
        exists {| supval := q ; supvalK := simple_q |}.
        simpl in *.
        destruct e as [e b].
        assert (b' = ~~ b).
        { move: se_nin. clear. rewrite in_cons => /norP[/eqP-? _].
          by destruct b, b'. }
        subst b'.
        by rewrite -e_ta target_q.
Qed.

Lemma splitting_terminal_tens_is_sequentializing {G : proof_net} {v : G} :
  vlabel v = ⊗ -> splitting bridge v -> terminal v ->
  sequentializing v.
Proof.
  move => vlabel_v splitting_v terminal_v.
  apply (@splitting_tens_prop_is_sequentializing _ _ _ vlabel_v terminal_v).
(**)
  hnf. move => p vlabel_p. split.
  - move => p_in_left.
    assert (In : source (right_parr vlabel_p) \in setT) by by rewrite in_set.
    rewrite -(cover_partition (partition_terminal vlabel_v terminal_v))
      /cover !bigcup_setU !bigcup_set1 !in_set in In.
    revert In => /orP[/orP[/orP[-> // | In] | /eqP-In] | /eqP-In]; exfalso.
    + destruct (@uconnected_Sl _ _ _ vlabel_v terminal_v
        (Sub (source (left_tens vlabel_v)) (source_left_Sl vlabel_v))
        (Sub p p_in_left)) as [p1 _].
      destruct (@uconnected_Sr _ _ _ vlabel_v terminal_v
        (Sub (source (right_tens vlabel_v)) (source_right_Sr vlabel_v))
        (Sub (source (right_parr vlabel_p)) In)) as [p2 _].
  (* TODO et là en déduire des chemins simples avec le lemme précédent,
puis dire disjoint, puis les concatener pour contredire splitting_v *)
      admit.
    + (* contredit terminal v *) admit.
    + (* contredit terminal v *) admit.
  - (*idem ci-dessus, en inversant Sl et Sr *) admit.
(**)
(* TODO se passer de cet intermédiaire splitting_tens_prop
maintenant qu'on est plus sur les parr *)
Admitted.

Lemma splitting_terminal_cut_is_sequentializing {G : proof_net} {v : G} :
  vlabel v = cut -> splitting bridge v -> terminal v ->
  sequentializing v.
Proof.
Admitted.
(* TODO tens idem cut *)

Lemma splitting_terminal_is_sequentializing (G : proof_net) (v : G) :
  splitting bridge v -> terminal v -> sequentializing v.
Proof.
  move => splitting_v terminal_v.
  destruct (vlabel v) eqn:vlabel_v.
  - by apply terminal_ax_is_sequentializing.
  - by apply splitting_terminal_tens_is_sequentializing.
  - by apply terminal_parr_is_sequentializing.
  - by apply splitting_terminal_cut_is_sequentializing.
  - contradict terminal_v.
    by rewrite /terminal vlabel_v.
Qed.

Lemma has_sequentializing (G : proof_net) :
  {v : G & sequentializing v}.
Proof.
  destruct (@exists_terminal_splitting _ G) as [v V].
  revert V => /andP[splitting_v terminal_v].
  exists v. by apply splitting_terminal_is_sequentializing.
Qed.

(** ** Sequentialization Theorem *)
Theorem sequentialize (G : proof_net) : { p : ll (sequent G) & ps p ≃d G }.
Proof.
  revert G.
  enough (Hm : forall n (G : proof_net), #|edge G| = n -> { p : ll (sequent G) & ps p ≃d G })
    by by intro G; apply (Hm #|edge G|).
  intro n; induction n as [n IH] using lt_wf_rect; intros G ?; subst n.
  destruct (@has_sequentializing G) as [v V].
  unfold sequentializing in V. destruct (vlabel v); try by [].
  - destruct V as [A h].
    set pi := ax_r A : ⊢ sequent (ax_graph_data A).
    exists (ex_r pi (sequent_iso_perm h)).
    symmetry. exact (iso_to_isod h).
  - destruct V as [[G0 G1] h].
    assert (C : mll_def.correct (add_node_ps_tens G0 G1)) by apply (iso_correct (iso_sym h)), p_correct.
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
    assert (C : mll_def.correct (add_node_ps_parr G0)) by apply (iso_correct (iso_sym h)), p_correct.
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
    assert (C : mll_def.correct (add_node_ps_cut G0 G1)) by apply (iso_correct (iso_sym h)), p_correct.
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
Qed.
(* TODO voir derniere quest exam et focalisation + seqpn *)


(* Possible things to prove: same number of cuts... *)
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