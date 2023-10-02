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
Notation proof_net := (@proof_net atom).

Section InstantiateBridge.

Context {G : base_graph}.

(** We instanciate previous notions. *)
(* Bridges - pairs of edges targettting the same ⅋ *)
Definition bridge (v : G) : rel (edge G) :=
  fun e1 e2 => (target e1 == v) && (target e2 == v) && (vlabel v == ⅋).

Lemma bridge_sym : local_symmetric bridge.
Proof. move=> v e1 e2 _ _. rewrite /bridge. lia. Qed.

Lemma bridge_trans : local_transitive bridge.
Proof.
  move=> v e1 e2 e3 _ _ _.
  rewrite /bridge.
  by move=> /andP[/andP[-> _] _] /andP[/andP[_ ->] ->].
Qed.

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
  | exist (_, None) _ => None
  end.

Definition vertex_finPOrderType3 : finPOrderType tt :=
  vertex_finPOrderType2 bridge v_of_t e_of_t.

Lemma t_of_b_helper (e : edge G * bool) (e' : edge G) :
  bridge (utarget e) e.1 e' -> e.1 <> e' ->
  (vlabel (target e.1) != c) && (target e.1 == target e.1).
Proof. by move => /andP[/andP[/eqP--> _] /eqP-->] /=. Qed.

Definition t_of_b (e : edge G * bool) e' (B : bridge (utarget e) e.1 e') (N : e.1 <> e') : T :=
  Sub (target e.1, Some e.1) (t_of_b_helper B N).

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
  case/boolP: (i == j) => /eqP-i_neq_j //.
  exfalso.
  apply eq_switching_is_bridge in bridge_nth; last first.
  { move=> F.
    apply uniq_fst_simple_upath in P.
    move: P => /uniqP => /(_ e.1)/(_ i j).
    rewrite size_map => P.
    contradict i_neq_j. apply P; clear P; try by [].
    by rewrite !(nth_map e). }
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
  - subst j. clear i_lt i_lt_j.
    contradict bridge_free_p. apply/negP.
    assert (ep_eq : e :: p = take i (e :: p) ++
      [:: nth e (e :: p) i; nth e (e :: p) (i + 1)] ++ drop (i + 2) (e :: p)).
    { clear - j_lt.
      move: i j_lt.
      set p' := e :: p. clearbody p'. clear p.
      induction p' as [ | e' p IH] => i //= j_lt.
      destruct i as [ | i].
      + rewrite /= nth0 drop1. by destruct p.
      + by rewrite {1}(IH i). } (* TODO lemma for this *)
    rewrite ep_eq !nb_bridges_cat /=.
    enough (bridge (utarget (nth e (e :: p) i)) (nth e (e :: p) i).1
      (nth e (e :: p) (i + 1)).1) as -> by lia.
    move: i2 j2.
    destruct (nth e (e :: p) i) as [ei []], (nth e (e :: p) (i + 1)) as [ej []]
      => //= _ _.
    by rewrite /bridge parr_i_j target_i_j eq_refl.
  - subst i j.
    rewrite nth_last in target_i_j, j2. simpl in *.
    destruct p as [ | ep p]; first by []. simpl in *.
    assert (no_bridge' : ~~ bridge (utarget e) e.1 ep.1).
    { clear - bridge_free_p. lia. }
    clear bridge_free_p.
    destruct e as [e []]; first by []; simpl in *.
    contradict no_bridge. apply/negP/negPn.
    by rewrite /bridge -target_i_j parr_i_j !eq_refl.
Qed.

End InstantiateBridge.

Section Sequentializable.

Context {G : proof_net}.

Notation bridge := (@bridge G).
Notation vertex_finPOrderType3 := (@vertex_finPOrderType3 G).

Fact is_correct_bridge : correct bridge.
Proof. apply correct_is_correct. by destruct (p_correct G). Qed.

(* A vertex v which is maximal is terminal.
   Or by contrapose, a non-terminal element cannot be maximal. *)
Lemma no_terminal_is_no_max (v : vertex_finPOrderType3) :
  ~~ terminal (v_of_t v) -> exists U, (v : vertex_finPOrderType3) < U.
Proof.
  move=> not_terminal_v.
  destruct v as [[v f] V]. simpl in *.
  apply not_terminal in not_terminal_v as [e [se_is_v te_not_c]]; last first.
  { clear not_terminal_v. by move: V => /= /andP[/eqP-? _]. }
  assert (H : (vlabel (target e) != c) && (target e == target e)).
  { rewrite eq_refl andb_true_r. by apply /eqP. }
  exists (exist _ (target e, Some e) H).
  apply /existsP. exists (Sub [:: forward e] (simple_upath_edge _)).
  rewrite /pre_ordering /Psource /Ptarget /= se_is_v /= !eq_refl !andb_true_r /= {H}.
  move: V => /andP[/eqP-v_not_c vf].
  assert (te_neq_v : v <> target e).
  { move=> v_eq.
    contradict se_is_v. rewrite v_eq.
    apply no_selfloop. }
  repeat (apply /andP; split).
  - by apply /eqP.
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
      revert v_in_targets_p => /mapP[a a_in_p v_eq_ta].
      assert (H : (fun b => v == utarget b) a) by by apply /eqP.
      destruct (in_elt_sub_fst H a_in_p) as [[n N] [a' [p_eq [v_eq_ta' a'_fst]]]].
      revert v_eq_ta' => {H} /eqP-v_eq_ta'.
      rewrite -cat_rcons in p_eq.
      apply (Wlog (rcons (take (Ordinal N) p) a')); clear Wlog.
      - rewrite p_eq in P. by apply simple_upath_prefix in P.
      - rewrite !map_rcons head_rcons last_rcons.
        destruct p as [ | ep p]; first by [].
        destruct n as [ | n].
        + simpl in *. inversion p_eq. subst ep.
          destruct a' as [a' []]; [ | apply nesym]; apply no_selfloop.
        + move => /= Ta'.
          simpl in sp_eq_te.
          contradict te_neq_v. by rewrite v_eq_ta' -Ta' sp_eq_te.
      - revert sp_eq_te. by rewrite {1}p_eq map_cat !map_rcons head_cat !head_rcons.
      - revert fst_p_not_e. by rewrite {1}p_eq head_cat !head_rcons.
      - revert bridge_free_p. rewrite {1}p_eq nb_bridges_cat. clear. simpl. lia.
      - revert no_bridge_p_e. by rewrite {1}p_eq head_cat !head_rcons.
      - by rewrite /= map_rcons last_rcons v_eq_ta'. }
(* The path e :: p contradicts correctness. *)
    assert (EP : simple_upath (forward e :: p)).
    { rewrite simple_upath_cons P /= se_is_v -{1}sp_eq_te.
      destruct p as [ | ep p]; first by [].
      revert fst_p_not_e Pnc => /= /eqP-fst_p_not_e /eqP-Pnc.
      rewrite /= eq_refl eq_sym fst_p_not_e Pnc /= andb_true_r v_eq_target_p.
      rewrite /= in_cons negb_orb eq_sym Pnc /=.
      revert P. rewrite /simple_upath /= eq_refl /= in_cons negb_orb.
      move => /andP[/andP[/andP[_ /orP[/andP[_ -> //] | F]] _] _].
      by rewrite eq_sym F in Pnc. }
    have /forallP/(_ (Sub _ EP)) /= H := is_correct_bridge.
    contradict H. apply/negP.
    rewrite !negb_imply se_is_v v_eq_target_p /= eq_refl /=.
    apply/andP. split.
    + rewrite /= bridge_free_p.
      destruct p as [ | ep p]; first by []. simpl.
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
  assert (u : vertex_finPOrderType3).
  { destruct (has_ax G) as [u U].
    exists (u, None). by rewrite U. }
  induction u as [u IH] using (well_founded_ind gt_wf).
  case/boolP: (splitting bridge (v_of_t u) && terminal (v_of_t u)) => split_u.
  { by exists (v_of_t u). }
  enough (exists v, (u : vertex_finPOrderType3) < v) as [v ?]
    by by apply (IH v).
  move: split_u => /nandP[split_u | term_u]; [ | exact (no_terminal_is_no_max term_u)].
  refine (@no_splitting_is_no_max _ _ _ _ bridge_sym bridge_trans _ v_of_t e_of_t
    _ t_of_b _ _ is_correct_bridge split_u).
  - move=> [e []] e' //=.
    rewrite /bridge => /andP[/andP[/eqP-F _] _].
    contradict F. apply nesym, no_selfloop.
  - by elim => [[? [? | ]] //= /andP[_ ->]].
Qed.

End Sequentializable.

End Atoms.
