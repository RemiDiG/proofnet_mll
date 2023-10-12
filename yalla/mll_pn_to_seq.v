(* Sequentialisation *)
(* A Proof Net contains a terminal and splitting vertex *)

From Coq Require Import Bool.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
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

Lemma set1I {T : finType} (x : T) (S : {set T}) :
  [set x] :&: S = if x \in S then [set x] else set0.
Proof.
  apply/setP => y.
  rewrite in_set in_set1.
  case/boolP: (y == x) => [/eqP--> | y_x] /=;
  case:ifP.
  - by rewrite in_set1 eq_refl.
  - by rewrite in_set0.
  - by rewrite in_set1 (negPf y_x).
  - by rewrite in_set0.
Qed. (* TODO in prelim *)

Lemma nth_eq {T : Type} (x y : T) (s : seq T) (n : nat) :
  n < size s -> nth x s n = nth y s n.
Proof.
  move: s. induction n as [ | n IH] => s; destruct s => //= n_lt.
  apply IH. lia.
Qed.


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

Section InstantiateBridge.

Context {G : base_graph}.

(** We instanciate previous notions. *)
(* Bridges - pairs of edges targettting the same ⅋ *)
Definition bridge (v : G) : rel (edge G) :=
  fun e1 e2 => (target e1 == v) && (target e2 == v) && (vlabel v == ⅋).

Lemma bridge_sym : local_symmetric bridge.
Proof. move=> v e1 e2 _ _. rewrite /bridge. lia. Qed.

Lemma bridge_trans : local_transitive bridge.
Proof. move=> v e1 e2 e3 _ _ _. rewrite /bridge. lia. Qed.

Definition T : finType :=
  { x : G * (option (edge G)) | (vlabel x.1 != c) &&
    match x.2 with | None => true | Some e => target e == x.1 end }.

Definition v_of_t (u : T) : G :=
  match u with
  | exist (u, _) _ => u
  end.

Definition e_of_t (u : T) : option (edge G * bool) :=
  match u with
  | exist (_, Some e) _ => Some (forward e)
  | exist (_, None)   _ => None
  end.

Definition seq_finPOrderType : finPOrderType tt :=
  T_finPOrderType_bridge bridge v_of_t e_of_t.

Lemma t_of_b_helper (e : edge G * bool) (e' : edge G) :
  bridge (utarget e) e.1 e' ->
  (vlabel (target e.1) != c) && (target e.1 == target e.1).
Proof. by move=> /andP[/andP[/eqP--> _] /eqP-->] /=. Qed.

Definition t_of_b (e : edge G * bool) e' (B : bridge (utarget e) e.1 e') (N : e.1 <> e') : T :=
  Sub (target e.1, Some e.1) (t_of_b_helper B).

Lemma eq_switching_is_bridge (e f : edge G) :
  switching e = switching f -> e <> f -> bridge (target e) e f.
Proof.
  rewrite /bridge /switching eq_refl /=.
  case/boolP: (target f == target e) => /eqP-T /=.
  - rewrite T.
    case: ifP => // _ F. by inversion F.
  - case: ifP; case: ifP => ? ? F; inversion F; last by [].
    by contradict T.
Qed.

(* Both notions of correctness coincides *)
(* TODO only proof_net -> correct bridge as connexity in more, or use correct bridge as criterion from the beginning! *)
Lemma correct_is_correct :
  uacyclic (@switching _ G) -> correct bridge.
Proof.
(* By contradiction, a simple path p has no bridge but its edges are not unique by switching. *)
  move=> U.
  rewrite /correct. apply/forallP. move=> [p P] /=.
  apply/implyP => bridge_free_p.
  destruct p as [ | e p]; first by [].
  apply/implyP => /eqP-cyclic_p. apply/negPn/negP => no_bridge.
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
  rewrite !(nth_map e) // => bridge_nth.
  case/boolP: (i == j) => /eqP-i_neq_j //. exfalso.
(* The equality on switching yields a bridge. *)
  apply eq_switching_is_bridge in bridge_nth; last first.
  { move=> F.
    apply uniq_fst_simple_upath in P.
    move: P => /uniqP => /(_ e.1)/(_ i j).
    rewrite size_map !(nth_map e) // => P.
    contradict i_neq_j. by apply P. }
  move: bridge_nth. rewrite /bridge eq_refl /= eq_sym => /andP[/eqP-target_i_j parr_i_j].
  wlog {i_neq_j} i_lt_j : i j i_lt j_lt target_i_j parr_i_j / i < j.
  { clear P bridge_free_p no_bridge => Wlog.
    case/boolP: (i < j) => ij.
    - by apply (Wlog i j).
    - apply (Wlog j i); try by [].
      + by rewrite -target_i_j parr_i_j.
      + clear - ij i_neq_j. lia. }
(* But (nth e p i).1 and (nth e p j).1 share the same target,
   thus they are consecutive (modulo p), contradicting bridge_freeness. *)
  have /orP[/andP[/andP[/eqP-? i2] j2] | /andP[/andP[/andP[/eqP-? /eqP-?] i2] j2]] :=
    @same_target_are_consecutive _ _ _ (e :: p) e i j P i_lt j_lt i_lt_j target_i_j.
  - subst j. clear i_lt i_lt_j P no_bridge.
    contradict bridge_free_p. apply/negP.
    rewrite (take_nth_drop2 e j_lt) nb_bridges_cat /=.
    enough (bridge (utarget (nth e (e :: p) i)) (nth e (e :: p) i).1
      (nth e (e :: p) (i + 1)).1) as -> by lia.
    destruct (nth e (e :: p) i) as [ei []], (nth e (e :: p) (i + 1)) as [ej []] => //=.
    by rewrite /bridge parr_i_j target_i_j eq_refl.
  - subst i j. clear i_lt j_lt P bridge_free_p.
    rewrite nth_last in target_i_j, j2. simpl in *.
    destruct e as [e []]; first by []. clear i2. simpl in *.
    destruct p as [ | ep p]; first by []. clear i_lt_j. simpl in *.
    contradict no_bridge. apply/negP/negPn.
    by rewrite /bridge -target_i_j parr_i_j !eq_refl.
Qed.

End InstantiateBridge.

Lemma correct_is_correct_bis {G : proof_structure} : (* TODO should be useless once uacyclic no longer used *)
  @correct _ _ G bridge -> uacyclic (@switching _ G).
Proof.
  move=> C v [p supath_p].
  apply val_inj.
  assert (simple_p := supath_is_simple_upath supath_p).
  move: C => /forallP/(_ (Sub p simple_p)) /=.
  move: supath_p => /andP[/andP[uwalk_p uniq_p] _].
  assert (nb_bridges bridge p == 0) as ->.
  { case/boolP: (nb_bridges bridge p == 0) => // nb_p.
    destruct (not_bridge_free_has_first_bridge nb_p) as [p1 [p2 [e1 [e2 [? [B _]]]]]].
    subst p.
    move : B. rewrite /bridge => /andP[/andP[/eqP-T1 /eqP-T2] V].
    assert (H : e1 <> e2).
    { apply map_uniq in uniq_p.
      move: uniq_p. rewrite cat_uniq /= in_cons. introb. }
    contradict uniq_p. apply/negP.
    refine (not_uniq_map _ _ H _).
    - by rewrite mem_cat !in_cons eq_refl !orb_true_r.
    - by rewrite mem_cat !in_cons eq_refl !orb_true_r.
    - by rewrite /switching T1 T2 V. }
  destruct p as [ | e p]; first by [].
  elim (uwalk_endpoint uwalk_p) => /= -> ->.
  rewrite eq_refl /= => /andP[/andP[/eqP-Te /eqP-Tl] V].
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
  - by rewrite /switching Te Tl V.
Qed.

Section Sequentializable.

Context {G : proof_net}.

Notation bridge := (@bridge G).
Notation seq_finPOrderType := (@seq_finPOrderType G).

Fact is_correct_bridge : correct bridge.
Proof. apply correct_is_correct. by destruct (p_correct G). Qed.

(* A vertex v which is maximal is terminal.
   Or by contrapose, a non-terminal element cannot be maximal. *)
Lemma no_terminal_is_no_max (v : seq_finPOrderType) :
  ~~ terminal (v_of_t v) -> exists U, v < U.
Proof.
  move=> not_terminal_v.
  destruct v as [[v f] V]. simpl in *.
  apply not_terminal in not_terminal_v as [e [se_is_v te_not_c]]; last first.
  { by move: V => /= /andP[/eqP-? _]. }
  assert (H : (vlabel (target e) != c) && (target e == target e)).
  { rewrite eq_refl andb_true_r. by apply/eqP. }
  exists (exist _ (target e, Some e) H).
  apply/existsP. exists (Sub [:: forward e] (simple_upath_edge _)).
  rewrite /pre_ordering /Psource /Ptarget /= se_is_v /= !eq_refl !andb_true_r /= {H}.
  move: V => /andP[/eqP-v_not_c vf].
  assert (te_neq_v : v <> target e).
  { move=> v_eq.
    contradict se_is_v. rewrite v_eq.
    apply no_loop. }
  repeat (apply/andP; split).
  - by apply/eqP.
  - destruct f as [f | ]; last by [].
    rewrite /= /bridge (eqP vf) eq_refl /= negb_andb.
    apply/andP. split.
    + apply/orP. left.
      apply/eqP. by apply nesym.
    + apply/eqP => ?. subst f.
      contradict te_neq_v. symmetry. by apply/eqP.
  - (* By correctness *)
    apply/forallP. move=> [p P] /=. apply/implyP => /eqP-Pnc.
    apply/implyP => /eqP-sp_eq_te.
    apply/implyP => /andP[/eqP-bridge_free_p /andP[no_bridge_p_e /eqP-fst_p_not_e]].
    rewrite disjoint_sym disjoint_cons disjoint_nil andb_true_r.
    apply/negP => v_in_targets_p.
(* Up to taking a prefix of p, exactly the endpoints of p are in both e and p *)
    wlog {v_in_targets_p} v_eq_target_p : p P Pnc sp_eq_te fst_p_not_e
      bridge_free_p no_bridge_p_e / (v = upath_target (target e) p).
    { move {te_not_c v_not_c vf} => Wlog.
      move: v_in_targets_p => /mapP[a a_in_p v_eq_ta].
      assert (H : (fun b => v == utarget b) a) by by apply/eqP.
      destruct (in_elt_sub_fst H a_in_p) as [[n N] [a' [p_eq [v_eq_ta' a'_fst]]]].
      move: v_eq_ta' => {H} /eqP-v_eq_ta'.
      rewrite -cat_rcons in p_eq.
      apply (Wlog (rcons (take (Ordinal N) p) a')); clear Wlog.
      - rewrite p_eq in P. by apply simple_upath_prefix in P.
      - rewrite !map_rcons head_rcons last_rcons.
        destruct p as [ | ep p]; first by [].
        destruct n as [ | n].
        + simpl in *. inversion p_eq. subst ep.
          destruct a' as [a' []]; [ | apply nesym]; apply no_loop.
        + move=> /= Ta'.
          simpl in sp_eq_te.
          contradict te_neq_v. by rewrite v_eq_ta' -Ta' sp_eq_te.
      - move: sp_eq_te. by rewrite {1}p_eq map_cat !map_rcons head_cat !head_rcons.
      - move: fst_p_not_e. by rewrite {1}p_eq head_cat !head_rcons.
      - move: bridge_free_p. rewrite {1}p_eq nb_bridges_cat. clear. simpl. lia.
      - move: no_bridge_p_e. by rewrite {1}p_eq head_cat !head_rcons.
      - by rewrite /= map_rcons last_rcons v_eq_ta'. }
(* The path e :: p contradicts correctness. *)
    assert (EP : simple_upath (forward e :: p)).
    { rewrite simple_upath_cons P /= se_is_v -{1}sp_eq_te.
      destruct p as [ | ep p]; first by [].
      move: fst_p_not_e Pnc => /= /eqP-fst_p_not_e /eqP-Pnc.
      rewrite eq_refl eq_sym fst_p_not_e Pnc andb_true_r v_eq_target_p
        in_cons negb_orb eq_sym Pnc /=.
      move: P. rewrite /simple_upath /= eq_refl /= in_cons negb_orb.
      rewrite eq_sym in Pnc. rewrite (negPf Pnc) orb_false_r /=.
      by move=> /andP[/andP[/andP[_ ->] _] _]. }
    have /forallP/(_ (Sub _ EP)) /= H := is_correct_bridge.
    contradict H. apply/negP.
    rewrite !negb_imply se_is_v v_eq_target_p eq_refl /=.
    apply/andP. split.
    + rewrite /= bridge_free_p.
      destruct p as [ | ep p]; first by [].
      by rewrite (negPf no_bridge_p_e).
    + rewrite /bridge !negb_andb.
      apply/orP. left. apply/orP. left.
      move: v_eq_target_p => /= <-.
      apply/eqP. by apply nesym.
Qed.

Theorem exists_terminal_splitting :
  { v : G | splitting bridge v && terminal v }.
Proof.
  apply/sigW.
  assert (u : seq_finPOrderType).
  { have [u /eqP-U] := exists_node G.
    exists (u, None). by rewrite U. }
  induction u as [u IH] using (well_founded_ind gt_wf).
  case/boolP: (splitting bridge (v_of_t u) && terminal (v_of_t u)) => split_u.
  { by exists (v_of_t u). }
  enough (exists v, (u : seq_finPOrderType) < v) as [v ?]
    by by apply (IH v).
  move: split_u => /nandP[split_u | term_u]; [ | exact (no_terminal_is_no_max term_u)].
  refine (@no_splitting_is_no_max _ _ _ _ bridge_sym bridge_trans _ v_of_t e_of_t
    _ t_of_b _ _ is_correct_bridge split_u).
  - move=> [e []] e' //= /andP[/andP[/eqP-F _] _].
    contradict F. apply nesym, no_loop.
  - by move=> [[? [? | ]] //= /andP[_ ->]].
Qed.

End Sequentializable.

End Atoms.
