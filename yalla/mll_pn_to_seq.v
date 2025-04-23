(* Sequentialisation *)
(* A Proof Net contains a terminal and splitting vertex *)

From Coq Require Import Bool.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From GraphTheory Require Import mgraph setoid_bigop.

From Yalla Require Export mll_prelim graph_more upath supath simple_upath mll_def mll_basic yeo.

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
Notation proof_structure := (@proof_structure atom). (* TODO temp *)
Notation proof_net := (@proof_net atom).

Lemma supath_is_simple_upath {G : proof_structure} {I : eqType} (f : edge G -> option I)
  (v : G) (p : upath) :
  supath f v v p -> simple_upath p.
Proof.
  rewrite /supath /simple_upath map_comp .
  move=> /andP[/andP[uwalk_p uniq_p] _].
  apply map_uniq in uniq_p.
  destruct p as [ | e p]; first by [].
  assert (upath_source (utarget e) (e :: p) = v /\ upath_target (utarget e) (e :: p) = v) as [s_v t_v].
  { by elim (uwalk_endpoint uwalk_p) => /= -> ->. }
  rewrite s_v t_v eq_refl uwalk_p uniq_p orb_true_r !andb_true_l.
  apply/(uniqP (usource e)) => i j.
  rewrite size_map => i_lt j_lt.
  rewrite !(nth_map e) // => si_eq_sj.
  destruct (eq_comparable i j) as [-> | i_neq_j]; first by reflexivity.
  exfalso.
  wlog {i_neq_j} i_lt_j : i j i_lt j_lt si_eq_sj / i < j.
  { clear uwalk_p uniq_p s_v t_v => Wlog.
    case/boolP: (i < j) => ij.
    - by apply (Wlog i j).
    - apply (Wlog j i); try by []. lia. }
  wlog {i_lt} i_eq_0 : v e p uwalk_p uniq_p s_v t_v i j i_lt j_lt si_eq_sj i_lt_j / i = 0.
  { move=> Wlog.
    assert (ep_eq := take_nth_drop e i_lt).
    rewrite ep_eq in uwalk_p.
    apply uwalk_turns in uwalk_p.
    rewrite cat_cons in uwalk_p.
    refine (Wlog _ _ _ uwalk_p _ _ _ 0 (j - i) _ _ _ _ _); clear Wlog; try by [].
    - move: uniq_p. clear - ep_eq.
      rewrite {1}ep_eq /= !map_cat !cat_uniq /= mem_cat !negb_orb has_sym /=. lia.
    - by elim (uwalk_endpoint uwalk_p) => _.
    - clear - ep_eq j_lt.
      move: j_lt.
      rewrite {1}ep_eq /= !size_cat /= /in_mem /=. lia.
    - rewrite ep_eq in si_eq_sj.
      move: si_eq_sj.
      rewrite nth0 !nth_cat.
      rewrite /in_mem /= in i_lt.
      rewrite size_take i_lt /=.
      replace (i < i)%N with false by lia.
      replace (j < i)%N with false by lia.
      replace (i - i) with 0 by lia.
      rewrite nth0 /=.
      move=> ->.
      rewrite -cat_cons nth_cat /= size_drop.
      replace (j - i < (size (e :: p) - (i + 1)).+1)%N with true.
      2:{ move: j_lt. rewrite /in_mem /=. lia. }
      apply (@f_equal _ _ (fun a => usource a)), nth_eq.
      rewrite /= size_drop. move: j_lt. rewrite /in_mem /=. lia.
    - lia. }
  subst i.
  assert (j_lt' : (j - 1 + 1 < size (e :: p))%N).
  { move: j_lt i_lt_j. clear.  rewrite /in_mem /=. lia. }
  assert (ep_eq := take_nth_drop2 e j_lt').
  clear j_lt'.
  replace (j - 1 + 1) with j in ep_eq by lia.
  replace (j - 1 + 2) with (j + 1) in ep_eq by lia.
  rewrite /= in si_eq_sj.
  assert (j1_lt : j + 1 \in gtn (size (e :: p))).
  { destruct (eq_comparable (j + 1) (size (e :: p))) as [j1_eq | j1_neq];
    last first.
    { move: j1_neq j_lt. clear. rewrite /in_mem /=. lia. }
    exfalso.
    rewrite j1_eq drop_size in ep_eq.
    move: t_v. rewrite ep_eq /= map_cat /= last_cat /=.
    move: s_v => /= <-.
    rewrite si_eq_sj. clear.
    destruct (nth e (e :: p) j) as [? []]; simpl.
    - apply nesym, no_loop.
    - apply no_loop. }
  destruct (drop (j + 1) (e :: p)) as [ | dp lp _] eqn:dp_eq using last_ind.
  { contradict dp_eq. by rewrite (drop_nth e j1_lt). }
  destruct (take (j - 1) (e :: p)) as [ | hp tp ] eqn:tp_eq.
  { have : size (take (j - 1) (e :: p)) = 0 by rewrite tp_eq.
    rewrite size_take.
    replace (j - 1 < size (e :: p))%N with true. 2:{ symmetry. move: j1_lt. clear. rewrite /in_mem /=. lia. }
    destruct j as [ | [ | j]] => //=.
    move: si_eq_sj ep_eq j1_lt.
    rewrite /= nth0 -dp_eq /= drop1.
    destruct p as [ | ep p] => //=.
    move: uwalk_p => /= /andP[_ /andP[/eqP-> _]] F.
    contradict F.
    destruct e as [e []]; [ | apply nesym]; apply no_loop. }
  assert (hp = e).
  { rewrite cat_cons in ep_eq. by inversion ep_eq. }
  subst hp.
  assert (tjm1_sj : utarget (nth e (e :: p) (j - 1)) = usource (nth e (e :: p) j)).
  { replace j with (j - 1).+1 by lia.
    replace ((j - 1).+1 - 1) with (j - 1) by lia.
    symmetry. apply (uwalk_nth uwalk_p).
    move: j_lt i_lt_j. clear. rewrite /in_mem /=. lia. }
  assert (tlp : utarget lp = v).
  { move: t_v. by rewrite ep_eq /= map_cat /= map_rcons last_cat /= last_rcons. }
  assert (se : usource e = v) by by [].
  rewrite /uendpoint in tjm1_sj tlp se si_eq_sj.
  move: uniq_p.
  rewrite ep_eq map_cat /= map_rcons cat_uniq /= rcons_uniq /= !in_cons !in_rcons has_rcons
    !negb_orb mem_cat /= !in_cons in_rcons !negb_orb.
  move=> /andP[/andP[_ /andP[hp_jm1 /andP[hp_j /andP[hp_lp _]]]]
    /andP[_ /andP[_ /andP[/andP[jm1_j /andP[jm1_lp _]] /andP[/andP[j_lp _] _]]]]].
  assert (S : [set e.1; (nth e (e :: p) (j - 1)).1; (nth e (e :: p) j).1; lp.1] \subset
    edges_at v).
  { apply/subsetP => a.
    rewrite !in_set !in_set1 /incident => /orP[/orP[/orP[/eqP-? | /eqP-?] | /eqP-?] | /eqP-?];
    subst a; apply/existsP.
    - exists (~~ e.2). by rewrite se.
    - exists (nth e (e :: p) (j - 1)).2. by rewrite tjm1_sj -si_eq_sj se.
    - exists (~~ (nth e (e :: p) j).2). by rewrite -si_eq_sj se.
    - exists lp.2. by rewrite tlp. }
  assert (card4 : #|[set e.1; (nth e (e :: p) (j - 1)).1; (nth e (e :: p) j).1; lp.1]| = 4).
  { by rewrite !cardsU !cards1 set1I setIC set1I setIC set1I !in_set !in_set1
      (negPf hp_jm1) eq_sym (negPf hp_j) eq_sym (negPf jm1_j) eq_sym (negPf hp_lp)
      eq_sym (negPf jm1_lp) eq_sym (negPf j_lp) /= cards0. }
  assert (F : #|edges_at v| >= 4).
  { rewrite -card4. apply (subset_leq_card S). }
  contradict F. clear.
  rewrite card_edges_at.
  destruct (vlabel v); lia.
Qed.

Section InstantiateCusp.

Context {G : base_graph}.

Definition switching_Color : eqType :=
  ((edge G * bool) + vertex G)%type.

(* Each edge has its own color, except premises of ⅋ that share the same color *)
Definition switching_coloring (e : edge G * bool) : switching_Color :=
  if e.2 && (vlabel (target e.1) == ⅋) then inr (target e.1)
  else inl e.

Lemma eq_switching_is_cusp (e f : edge G) :
  switching e = switching f -> cusp switching_coloring (forward e) (backward f).
Proof.
  rewrite /cusp /switching_coloring /switching /= => /eqP.
  case_if.
Qed.

(* Both notions of correctness coincides *)
(* TODO only proof_net -> cusp_acyclic as connexity in more, or use cusp_acyclic as criterion from the beginning! *)
Lemma correct_is_correct :
  uacyclic (@switching _ G) -> cusp_acyclic switching_coloring.
Proof.
(* By contradiction, a simple path p has no cusp but its edges are not unique by switching. *)
  move=> U.
  rewrite /cusp_acyclic. apply/forallP. move=> [p P] /=.
  apply/implyP => cusp_free_p.
  destruct p as [ | e p]; first by [].
  apply/implyP => /eqP-cyclic_p. apply/negPn/negP => no_cusp.
  enough (P' : supath switching (head (usource e) [seq usource a | a <- e :: p])
    (head (usource e) [seq usource a | a <- e :: p]) (e :: p)).
  { by move: U => /(_ _ (Sub _ P')). }
  clear U.
  rewrite /supath switching_None andb_true_r.
  apply/andP. split.
  { have := uwalk_of_simple_upath P (usource e).
    by move: cyclic_p => /= <-. }
  clear cyclic_p.
  apply/(uniqP (switching e.1)) => i j.
  rewrite size_map !inE => i_lt j_lt.
  rewrite !(nth_map e) // => cusp_nth.
  case/boolP: (i == j) => /eqP-i_neq_j //. exfalso.
(* The equality on switching yields a cusp. *)
  apply eq_switching_is_cusp in cusp_nth.
  move: cusp_nth. rewrite /cusp /switching_coloring /= => parr_i_j.
  wlog {i_neq_j} i_lt_j : i j i_lt j_lt parr_i_j / i < j.
  { clear P cusp_free_p no_cusp => Wlog.
    case/boolP: (i < j) => ij.
    - by apply (Wlog i j).
    - apply (Wlog j i); try by [].
      + by rewrite (eqP parr_i_j).
      + clear - ij i_neq_j. lia. }
   assert (target_i_j : target (nth e (e :: p) i).1 = target (nth e (e :: p) j).1).
   { move: parr_i_j. case_if. }
(* But (nth e p i).1 and (nth e p j).1 share the same target,
   thus they are consecutive (modulo p), contradicting cusp-freeness. *)
  have /orP[/andP[/andP[/eqP-? i2] j2] | /andP[/andP[/andP[/eqP-? /eqP-?] i2] j2]] :=
    @same_target_are_consecutive _ _ _ (e :: p) e i j P i_lt j_lt i_lt_j target_i_j.
  - subst j. clear i_lt i_lt_j P no_cusp.
    contradict cusp_free_p. apply/negP.
    rewrite (take_nth_drop2 e j_lt) nb_cusps_cat /=.
    enough (cusp switching_coloring (nth e (e :: p) i)
      (nth e (e :: p) (i + 1))) as -> by lia.
    rewrite /cusp /switching_coloring /=.
    by destruct (nth e (e :: p) i) as [ei []], (nth e (e :: p) (i + 1)) as [ej []].
  - subst i j. clear i_lt j_lt P cusp_free_p.
    rewrite nth_last in target_i_j, j2. simpl in *.
    destruct e as [e []]; first by []. clear i2. simpl in *.
    destruct p as [ | ep p]; first by []. clear i_lt_j. simpl in *.
    contradict no_cusp. apply/negP/negPn.
    rewrite /cusp /switching_coloring /=.
    move: parr_i_j. rewrite -target_i_j -last_nth j2. case_if.
Qed.

End InstantiateCusp.

Lemma correct_is_correct_bis {G : proof_structure} : (* TODO should be useless once uacyclic no longer used *)
  @cusp_acyclic _ _ G _ switching_coloring -> uacyclic (@switching _ G).
Proof.
  move=> C v [p supath_p].
  apply val_inj.
  assert (simple_p := supath_is_simple_upath supath_p).
  move: C => /forallP/(_ (Sub p simple_p)) /=.
  move: supath_p => /andP[/andP[uwalk_p uniq_p] _].
  assert (nb_cusps switching_coloring p == 0) as ->.
  { case/boolP: (nb_cusps switching_coloring p == 0) => // nb_p.
    destruct (not_cusp_free_has_first_cusp nb_p) as [p1 [p2 [e1 [e2 [? [B _]]]]]].
    subst p.
    assert (H : e1 <> e2).
    { apply map_uniq in uniq_p.
      move: uniq_p. rewrite cat_uniq /= in_cons. introb. }
    contradict uniq_p. apply/negP.
    refine (not_uniq_map _ _ H _).
    - by rewrite mem_cat !in_cons eq_refl !orb_true_r.
    - by rewrite mem_cat !in_cons eq_refl !orb_true_r.
    - apply/eqP. move : B. rewrite /cusp /switching_coloring /switching.
      destruct e1 as [e1 []], e2 as [e2 []]; case_if. }
  rewrite /=. destruct p as [ | e p]; first by [].
  elim (uwalk_endpoint uwalk_p) => /= W1 W2.
  rewrite W1 W2 eq_refl /= => Cel.
  assert (H : e <> last e p).
  { apply map_uniq in uniq_p.
    destruct p as [ | p e' _] using last_ind.
    - move: uwalk_p => /= /andP[/eqP-S /eqP-T].
      rewrite -T in S.
      contradict S.
      destruct e as [? []]; [ | apply nesym]; apply no_loop.
    - rewrite last_rcons => ?. subst e'.
      contradict uniq_p. apply/negP.
      by rewrite /= in_rcons eq_refl. }
  contradict uniq_p. apply/negP.
  refine (not_uniq_map _ _ H _).
  - by rewrite in_cons eq_refl.
  - apply mem_last.
  - apply/eqP. move: Cel. rewrite /cusp /switching_coloring /switching.
    destruct p as [ | p e' _] using last_ind; first by [].
    move: W2. rewrite /= map_rcons !last_rcons -W1.
    destruct e as [e []], e' as [e' []]; case_if.
Qed.

Section Sequentializable.

Context {G : proof_net}.

Fact is_correct_cusp : @cusp_acyclic _ _ G _ switching_coloring.
Proof. apply correct_is_correct. by destruct (p_correct G). Qed.

(* Parameter E = all forward edges towards tens, parr and cut, as well as
   all backward edges towards terminal ax. *)
Definition E_sequentialization : {set edge G * bool} :=
  [set e | e.2 && (vlabel (utarget e) \in [:: ⊗ ; ⅋ ; cut])] :|:
  [set e | ~~e.2 && (vlabel (utarget e) == ax) && (terminal (utarget e))].

(* A vertex v which is maximal is terminal.
   Or by contrapose, a non-terminal element cannot be maximal. *)
Lemma no_terminal_is_no_max (e : edge G * bool) :
  e \in E_sequentialization ->
  ~~ terminal (utarget e) -> exists f, ordering switching_coloring e f /\
  f \in E_sequentialization.
Proof.
  rewrite !in_set !in_cons in_nil /= orb_false_r => /orP[/andP[e2 vlabelte] |
    /andP[/andP[e2 vlabelse] terminal_se]] not_terminal_e; last first.
  { by rewrite terminal_se in not_terminal_e. }
  destruct e as [e []]; last by []. clear e2.
  apply not_terminal in not_terminal_e as [f [sf_is_te tf_not_c]];
    last by move: vlabelte => /orP[/eqP--> | /orP[/eqP--> | /eqP-->]].
  exists (forward f). split; last first.
  { rewrite !in_set !in_cons in_nil /uendpoint /= !orb_false_r.
    destruct (vlabel (target f)) eqn:vlabel_tf; try by [].
    by have := (@no_target_ax _ _ _ vlabel_tf f). }
  apply/existsP. exists (Sub [:: forward f] (simple_upath_edge _)).
  rewrite /ordering_path /pre_ordering_path /= /uendpoint {2}sf_is_te !eq_refl !andb_true_r.
  repeat (apply/andP; split).
  - apply/eqP. apply no_loop.
  - rewrite /cusp /switching_coloring /=.
    assert (e_neq_f : e <> f).
    { move=> ?. subst f.
      contradict sf_is_te. apply no_loop. }
    destruct (vlabel (target e)) eqn:vlabel_e => //=; cbn; by rewrite andb_false_r.
  - (* By correctness *)
    apply/forallP. move=> g. apply/forallP. move=> [p P] /=.
    apply/implyP => /andP[/andP[/andP[/andP[p_open p_cusp_free] /eqP-sp_is_tf] no_cusp_f_p] /eqP-?]. subst g.
    rewrite disjoint_sym disjoint_cons disjoint_nil andb_true_r.
    apply/negP => sf_in_targets_p.
  (* Up to taking a prefix of p, exactly the endpoints of p are in both e and p *)
    wlog {sf_in_targets_p} sf_is_tp : p P p_open p_cusp_free sp_is_tf
      no_cusp_f_p / (source f = upath_target (target e) p).
    { move {tf_not_c} => Wlog.
      move: sf_in_targets_p => /mapP[a a_in_p v_eq_ta].
      assert (H : (fun b => source f == utarget b) a) by by apply/eqP.
      destruct (in_elt_sub_fst H a_in_p) as [[n N] [a' [p_eq [sf_eq_ta' a'_fst]]]].
      move: sf_eq_ta' => {H} /eqP-sf_eq_ta'.
      rewrite -cat_rcons in p_eq.
      apply (Wlog (rcons (take (Ordinal N) p) a')); clear Wlog.
      - rewrite p_eq in P. by apply simple_upath_prefix in P.
      - rewrite !map_rcons head_rcons last_rcons.
        destruct p as [ | ep p]; first by [].
        destruct n as [ | n].
        + simpl in p_eq. inversion p_eq. subst ep.
          destruct a' as [a' []]; apply/eqP; [ | apply nesym]; apply no_loop.
        + rewrite /= /uendpoint in sp_is_tf sf_eq_ta'. rewrite /= sp_is_tf -sf_eq_ta'.
          apply/eqP. apply nesym, no_loop.
      - move: p_cusp_free. rewrite {1}p_eq nb_cusps_cat. clear. simpl. lia.
      - rewrite -sp_is_tf. by rewrite {5}p_eq map_cat !map_rcons head_cat !head_rcons.
      - move: no_cusp_f_p. by rewrite {1}p_eq head_cat !head_rcons.
      - by rewrite /= map_rcons last_rcons sf_eq_ta'. }
  (* The path f :: p contradicts correctness. *)
    assert (FP : simple_upath (forward f :: p)).
    { rewrite simple_upath_cons P /=.
      destruct p as [ | ep p]; first by rewrite /= eq_refl.
      rewrite sp_is_tf eq_refl /= andb_true_r.
      move: sf_is_tp p_open => /= sf_is_tp p_open.
      rewrite /uendpoint sf_is_tp in_cons negb_orb (eq_sym _ (usource ep)) p_open /=.
      move: P. rewrite /simple_upath /= eq_refl /= in_cons negb_orb.
      rewrite eq_sym in p_open. rewrite (negPf p_open) orb_false_r /=.
      move=> /andP[/andP[/andP[_ ->] _] _].
      rewrite andb_true_r -sf_is_tp.
      apply/andP; split.
      - apply/eqP => ?. subst f.
        simpl in *.
        destruct ep as [ep []]; simpl in *.
        + contradict sp_is_tf. apply no_loop.
        + contradict no_cusp_f_p. apply/negP/negPn. by rewrite /cusp.
      - apply/eqP. apply nesym, no_loop. }
    have /forallP/(_ (Sub _ FP)) /= H := is_correct_cusp.
    contradict H. apply/negP.
    rewrite /uendpoint !negb_imply sf_is_tp.
    repeat (apply/andP; split).
    + rewrite (eqP p_cusp_free).
      destruct p as [ | ep p]; first by [].
      by rewrite (negPf no_cusp_f_p).
    + destruct p as [ | ep p]; last by [].
      contradict p_open. by rewrite eq_refl.
    + rewrite /cusp /switching_coloring /=.
      destruct p as [ | p ep _] using last_ind; first by [].
      move: sf_is_tp. rewrite /= map_rcons !last_rcons => sf_is_tp.
      rewrite sp_is_tf map_rcons last_rcons in p_open.
      case:ifP => //= _.
      cbn. destruct ep as [ep []]; cbn; rewrite ?andb_true_r ?andb_false_r //.
      apply/eqP => ?. subst f.
      have := uniq_fst_simple_upath FP.
      by rewrite /= map_rcons in_rcons eq_refl.
Qed.

Lemma E_sequentialization_non_empty :
  { e | e \in E_sequentialization }.
Proof.
  apply/sigW.
  destruct (has_ax G) as [v vlabel_v].
  destruct (terminal v) eqn:terminal_v.
  - destruct (p_ax vlabel_v) as [el [? [el_in_edges_out_v [? ?]]]].
    exists (backward el).
    rewrite /E_sequentialization !in_set /=.
    move: el_in_edges_out_v. rewrite in_set /uendpoint => /eqP-->.
    by rewrite vlabel_v eq_refl terminal_v.
  - edestruct (@not_terminal _ G v) as [e [source_e_is_v target_e_not_c]];
      rewrite ?vlabel_v ?terminal_v //.
    exists (forward e).
    rewrite /E_sequentialization !in_set !in_cons in_nil /uendpoint /= !orb_false_r.
    destruct (vlabel (target e)) eqn:vlabel_target_e; try by [].
    by have := @no_target_ax _ _ _ vlabel_target_e e.
Qed.

Theorem exists_terminal_splitting :
  { v : G | splitting switching_coloring v && terminal v }.
Proof.
  apply/sigW.
  destruct E_sequentialization_non_empty as [e e_in_E].
  induction (e : Datatypes_prod__canonical__Order_FinPOrder switching_coloring)
    as [f IH] using (well_founded_ind gt_wf).
(* TODO ugly type annotation *)
  clear e.
  case/boolP: [exists g, (f < g) && (g \in E_sequentialization)].
  - move=> /existsP[g /andP[gf gE]]. exact (IH g gf gE).
  - move=> /existsPn-Fmax.
    exists (utarget f).
    apply/andP; split.
    + apply (@ParametrizedYeo _ _ _ _ _ E_sequentialization is_correct_cusp); try by [].
      * move=> [e eb].
        rewrite /cusping /cusp /switching_coloring => /existsP[g /andP[eg_cusp e_neq_g]].
        left.
        move: eg_cusp. case:ifP.
        ** destruct eb => //= vlabel_te _.
           by rewrite /E_sequentialization !in_set !in_cons vlabel_te /= orb_true_r.
        ** destruct g as [g gb].
           case:ifP => //= H1 H2 /eqP-eg.
           inversion eg. subst e eb.
           contradict e_neq_g. by apply/negP/negPn.
      * move=> e fe.
        move: Fmax => /(_ e).
        by rewrite fe.
    + apply/negPn/negP => not_terminal_f.
      destruct (no_terminal_is_no_max e_in_E not_terminal_f) as [g [fg g_in_E]].
      move: Fmax => /(_ g).
      by rewrite g_in_E /Order.lt /= fg.
Qed.

End Sequentializable.

End Atoms.
