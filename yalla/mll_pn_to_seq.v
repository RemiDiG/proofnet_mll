(* Sequentialisation *)
(* A Proof Net contains a terminal and splitting vertex *)

From Coq Require Import Bool.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import mgraph setoid_bigop.

From Yalla Require Export mll_prelim graph_more upath simple_upath mll_def mll_basic yeo.

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
Definition bridge : rel (edge G) :=
  fun e1 e2 => (e1 == e2) || (target e1 == target e2) && (vlabel (target e1) == ⅋).

Lemma bridge_refl : reflexive bridge.
Proof. move => e. by rewrite /bridge eq_refl. Qed.

Lemma bridge_sym : symmetric bridge.
Proof.
  move => e1 e2.
  rewrite /bridge eq_sym (eq_sym (target _)).
  f_equal.
  by case/boolP: (target e2 == target e1) => // /eqP-->.
 Qed.

Lemma bridge_trans : transitive bridge.
Proof.
  move => e1 e2 e3.
  rewrite /bridge.
  move => /orP[/eqP--> // | /andP[T12 V2]] /orP[/eqP-? | /andP[/eqP-T23 ?]].
  - subst e3. by rewrite T12 V2 orb_true_r.
  - by rewrite -T23 T12 V2 orb_true_r.
Qed.

Definition T : finType :=
  [finType of { x : G * (option (edge G)) |
    (vlabel x.1 != c) &&
    match x.2 with | None => true | Some e => target e == x.1 end }].

Definition v_of_t (u : T) : G :=
  match u with
  | exist (u, _) _ => u
  end.

Definition e_of_t (u : T) : option (edge G) :=
  match u with
  | exist (_, e) _ => e
  end.

Definition Psource (u : T) (p : upath) : bool :=
  match u, p with
  | exist (_, Some eu) _, e :: _ => (head e p).1 != eu
  | _, _ => true
  end.

Definition Ptarget (u : T) (p : upath) : bool :=
  match u, p with
  | exist (_, Some eu) _, e :: _ => (last e p).1 == eu
  | _, _ => false
  end.

Lemma Psource_cat u v p q :
  Psource u p -> Ptarget v p -> Psource v q -> Psource u (p ++ q).
Proof. by destruct u as [[u [e | ]] ?], v as [[v [f | ]] ?], p. Qed.

Lemma Ptarget_cat u v w p q :
  Psource u p -> Ptarget v p -> Psource v q -> Ptarget w q -> Ptarget w (p ++ q).
Proof.
  rewrite /Psource /Ptarget.
  destruct v as [[v [ev | ]] ?], w as [[w [ew | ]] ?], p, q => //=.
  by rewrite last_cat.
Qed.

Definition vertexCol3_finPOrderType :=
  vertexCol2_finPOrderType bridge_refl bridge_sym bridge_trans v_of_t e_of_t Psource_cat Ptarget_cat.

Lemma t_of_v_e_helper (e : edge G * bool) (e' : edge G) :
  bridge e.1 e' -> e.1 <> e' ->
  (vlabel (target e.1) != c) && (target e.1 == target e.1).
Proof. by move => /orP[/eqP-? // | /andP[_ /eqP-->]] /=. Qed.

Definition t_of_v_e (e : edge G * bool) e' :
  bridge e.1 e' -> e.1 <> e' -> T :=
  fun B N => exist _ (target e.1, Some e.1) (t_of_v_e_helper B N).

Lemma eq_switching_is_bridge (e f : edge G) :
  switching e = switching f -> bridge e f.
Proof.
  rewrite /bridge /switching.
  case/boolP: (e == f) => //= /eqP-?.
  case/boolP: (target e == target f) => /eqP-T.
  - rewrite T.
    case: ifP => // _ F. by inversion F.
  - case: ifP; case: ifP => _ _ F; by inversion F.
Qed.

(* Both notions of correctness coincides *)
(* TODO only proof_net -> correct bridge as connexity in more, or use correct bridge as criterion from the beginning! *)
Lemma correct_is_correct :
  uacyclic (@switching _ G) -> correct bridge.
Proof.
  move => U.
  rewrite /correct. apply /forallP. move => [p P] /=.
  apply /implyP => bridge_free_p. apply /forallP => e.
  apply /implyP => /eqP-cyclic_p. apply /negPn/negP => no_bridge.
  enough (P' : supath switching (head (usource e) [seq usource a | a <- p])
    (head (usource e) [seq usource a | a <- p]) p).
  { rewrite /uacyclic in U.
    specialize (U _ {| upval := _ ; upvalK := P' |}).
    destruct p; last by [].
    by rewrite bridge_refl in no_bridge. }
  rewrite {U} /supath switching_None andb_true_r.
  apply /andP; split.
  { assert (W := uwalk_of_simple_upath P (usource e)).
    revert W. by rewrite /= -cyclic_p. }
  clear cyclic_p.
  apply /(uniqP (switching e.1)). move => i j.
  rewrite size_map !inE => i_lt j_lt.
  rewrite !(nth_map e) // => bridge_nth.
  case/boolP: (i == j) => /eqP-i_neq_j //.
  exfalso.
  apply eq_switching_is_bridge in bridge_nth.
  wlog {i_neq_j} i_lt_j : i j i_lt j_lt bridge_nth / i < j.
  { clear P bridge_free_p no_bridge => Wlog.
    case/boolP: (i < j) => ij.
    - by apply (Wlog i j).
    - apply (Wlog j i); try by [].
      + by rewrite bridge_sym.
      + clear - ij i_neq_j. lia. }
(* But (nth e p i).1 and (nth e p j).1 share the same target,
   thus they are consecutive (modulo p), contradicting bridge_freeness. *)
  assert (consec : (j == i + 1) || (i == 0) && (j == (size p).-1)).
  { apply (@same_target_are_consecutive _ _ _ p e); try by [].
    revert bridge_nth. by rewrite /bridge => /orP[/eqP--> | /andP[/eqP--> _]]. }
  revert consec => /orP[/eqP-? | /andP[/eqP-? /eqP-?]]; subst.
  - clear no_bridge i_lt i_lt_j.
    contradict bridge_free_p. apply /negP.
    revert i j_lt e bridge_nth. induction p as [ | a p IH] => //=
      i i_lt e bridge_nth.
    destruct i as [ | i].
    + rewrite /= nth0 in bridge_nth.
      destruct p; first by [].
      rewrite bridge_nth. lia.
    + enough (nb_bridges bridge p != 0) by lia.
      refine (IH _ i _ e _); try by [].
      revert P. by rewrite simple_upath_cons => /andP[/andP[/andP[/andP[-> _] _] _] _].
  - rewrite nth0 nth_last in bridge_nth.
    by rewrite bridge_nth in no_bridge.
Qed.

Lemma bridges_are_forward (o o1 o2 : upath) e1 e2 :
  o = o1 ++ [:: e1; e2] ++ o2 -> 
  simple_upath o -> ~~ bridge (head e1 o).1 (last e1 o).1 ->
  bridge e1.1 e2.1 ->
  e1.2.
Proof.
  move => Oeq O Bv B12.
  rewrite /bridge in B12.
  revert B12 => /orP[E1E2 | /andP[/eqP-B12 /eqP-V12]].
  { apply uniq_fst_simple_upath in O.
    contradict O. apply /negP.
    by rewrite Oeq !map_cat !cat_uniq /= in_cons E1E2 /= !andb_false_r. }
  destruct e1 as [e1 []] => //=.
  destruct e2 as [e2 []]; simpl in B12; last first.
  { apply uniq_usource_simple_upath in O.
    contradict O. apply /negP.
    by rewrite Oeq !map_cat !cat_uniq /= in_cons B12 eq_refl /= !andb_false_r. }
  destruct o1 as [ | o1 e11 _] using last_ind; last first.
  { assert (T11 : target e1 = utarget e11).
    { assert (W := uwalk_of_simple_upath O (usource e11)).
      rewrite Oeq in W.
      apply uwalk_sub_middle in W.
      by rewrite /= map_rcons last_rcons in W. }
    apply uniq_utarget_simple_upath in O.
    contradict O. apply /negP.
    by rewrite Oeq !map_cat !cat_uniq !map_rcons !rcons_uniq /= !in_cons !in_rcons
      -!T11 !B12 eq_refl /= !negb_orb !andb_false_r. }
  simpl in Oeq.
  destruct o2 as [ | e22 o2]; last first.
  { assert (S22 : target e2 = usource e22).
    { assert (W := uwalk_of_simple_upath O (usource e22)).
      replace o with ([:: backward e1; forward e2] ++ e22 :: o2) in W.
      by apply uwalk_sub_middle in W. }
    apply uniq_usource_simple_upath in O.
    contradict O. apply /negP.
    by rewrite Oeq /= !in_cons -!S22 B12 eq_refl /= !negb_orb !andb_false_r. }
  by rewrite Oeq /= /bridge negb_orb -!B12 V12 !eq_refl /= andb_false_r in Bv.
Qed.

End InstantiateBridge.

Section Sequentializable.

Context {G : proof_net}.

Notation bridge := (@bridge G).
Notation vertexCol3_finPOrderType := (@vertexCol3_finPOrderType G).

Fact is_correct_bridge : correct bridge.
Proof. apply correct_is_correct. by destruct (p_correct G). Qed.

(* A vertex v which is maximal is terminal.
   Or by contrapose, a non-terminal element cannot be maximal. *)
Lemma no_terminal_is_no_max (v : vertexCol3_finPOrderType) :
  ~~ terminal (v_of_t v) -> exists U, (v : vertexCol3_finPOrderType) < U.
Proof.
  move => not_terminal_v.
  destruct v as [[v f] V]. simpl in *.
  apply not_terminal in not_terminal_v as [e [se_is_v te_not_c]]; last first.
  { clear not_terminal_v. by revert V => /= /andP[/eqP-? _]. }
  assert (H : (vlabel (target e) != c) && (target e == target e)).
  { rewrite eq_refl andb_true_r. by apply /eqP. }
  exists (exist _ (target e, Some e) H).
  apply /existsP. exists {| supval := [:: forward e] ; supvalK := simple_upath_edge _ |}.
  rewrite /pre_ordering /Psource_bis /Psource /Ptarget_bis /Ptarget /=
    se_is_v /= !eq_refl bridge_refl !andb_true_r /= {H}.
  revert V => /andP[/eqP-v_not_c vf'].
  assert (vf : match f with | Some f => target f = v | None => True end).
  { destruct f; last by []. by apply /eqP. }
  clear vf'.
  assert (te_neq_v : v <> target e).
  { move => v_eq.
    contradict se_is_v. rewrite v_eq.
    apply no_selfloop. }
  repeat (apply /andP; split).
  - by apply /eqP.
  - destruct f as [f | ]; last by [].
    apply /eqP => ?. subst f.
    contradict vf. by apply nesym.
  - destruct f as [f | ]; last by [].
    rewrite /bridge negb_orb negb_andb.
    apply /andP; split.
    + apply /eqP => ?. subst f.
      contradict vf. by apply nesym.
    + apply /orP; left. apply /eqP => TeTf.
      contradict vf. rewrite -TeTf. by apply nesym.
  - (* By correctness *)
    apply /forallP. move => [p P] /=. apply /implyP => /eqP-Pnc.
    apply /implyP => /eqP-sp_eq_te.
    apply /implyP => /andP[/andP[fst_p_not_e' /eqP-bridge_free_p] no_bridge_p_e].
    assert (fst_p_not_e : (head (forward e) p).1 <> e).
    { apply /eqP. by destruct p. }
    clear fst_p_not_e'.
    rewrite disjoint_sym disjoint_cons disjoint_nil andb_true_r.
    apply /negP => v_in_targets_p.
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
    assert (is_correct := is_correct_bridge).
    revert is_correct => /forallP/(_ {| supval := _ ; supvalK := EP |}) /= H.
    contradict H. apply /negP.
    rewrite negb_imply negb_forall negb_imply se_is_v v_eq_target_p /= eq_refl /=.
    apply /andP; split.
    { rewrite /= bridge_free_p.
      destruct p as [ | ep p]; first by []. simpl.
      enough (~~ bridge e ep.1) by lia.
      by rewrite bridge_sym. }
    apply /existsP. exists (forward e).
    rewrite /bridge negb_orb negb_andb.
    apply /andP; split.
    { destruct p as [ | ep p]; first by [].
      apply /eqP. move => /= ?. subst e.
      apply uniq_fst_simple_upath in EP.
      contradict EP. apply /negP.
      by rewrite /= !negb_andb -last_map mem_last. }
    destruct p as [ | p ep _ ] using last_ind; first by [].
    revert v_eq_target_p. rewrite /= map_rcons !last_rcons => v_eq_target_p.
    destruct ep as [ep []].
    { rewrite -v_eq_target_p -se_is_v eq_sym.
      apply /orP. left. apply /eqP. apply no_selfloop. }
    simpl in v_eq_target_p.
    destruct p as [ | p ep2 _] using last_ind.
    * simpl in *.
      revert no_bridge_p_e.
      rewrite /bridge negb_orb negb_andb (eq_sym (target _)) => /andP[_ no_bridge_p_e].
      revert no_bridge_p_e.
      by case/boolP: (target e == target ep) => // /eqP-->.
    * apply /orP. left. apply /eqP. move => /= F.
      assert (W := uwalk_of_simple_upath P v).
      revert W. rewrite !uwalk_rcons -{}F /= => /andP[/andP[_ /eqP-W] _].
      apply uniq_utarget_simple_upath in EP. contradict EP. apply /negP.
      by rewrite /= !map_rcons !rcons_uniq !in_rcons W eq_refl orb_true_r /=.
Qed.

Theorem exists_terminal_splitting :
  exists (v : G), splitting bridge v && terminal v.
Proof.
  assert (u : vertexCol3_finPOrderType).
  { destruct (has_ax G) as [u U].
    exists (u, None). by rewrite U. }
  induction u as [u IH] using (well_founded_ind gt_wf).
  case/boolP: (splitting bridge (v_of_t u) && terminal (v_of_t u)) => split_u.
  { by exists (v_of_t u). }
  enough (exists v, (u : vertexCol3_finPOrderType) < v) as [v ?]
    by by apply (IH v).
  revert split_u => /nandP[split_u | term_u]; [ | exact (no_terminal_is_no_max term_u)].
  apply (no_splitting_is_no_max (t_of_v_e := t_of_v_e)); try by [].
  - move => [[v [e | ]] V] //= p.
    rewrite /Psource /=.
    destruct p; first by [].
    move => /= /negP-B. apply /eqP => ?. subst e.
    contradict B. by rewrite bridge_refl.
  - move => e _ p _ _ /=.
    destruct (rcons p e) eqn:F.
    { contradict F. apply rcons_nil. }
    by rewrite -{}F last_rcons.
  - move => o o1 o2 e1 e2 ? ? Oeq * /=.
    assert e1.2 by by apply (bridges_are_forward Oeq).
    by destruct e1 as [e1 []].
  - exact is_correct_bridge.
Qed.

End Sequentializable.

End Atoms.
