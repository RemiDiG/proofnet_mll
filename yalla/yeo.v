(* Proof of Yeo's Theorem and bungee jumping lemma *)

From Coq Require Import Bool.
From HB Require Import structures.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From GraphTheory Require Import preliminaries mgraph.
From Yalla Require Import mll_prelim graph_more upath simple_upath.

Import EqNotations.
Import Order.POrderTheory. (* Theory of partial ordered finite sets *)
Open Scope order_scope.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section GeneralizedYeo.
(* TODO work in pogress: state and prove our generalized Yeo, then use it for sequentialization *)
(** We consider a locally edge-colored multigraph G.
    There is no label on vertices nor on edges (more accurately, their labels
    are irrelevant and we could put Lv and Le to be unit).
    We color each pair made of an edge and a direction.
    The color type has decidable equality. *)(* TODO define graph without Lv and Le, with a coercion to these? *)
Variables (Lv Le : Type) (G : graph Lv Le) (Color : eqType) (c : edge G * bool -> Color).

(* A cusp is a pair of directed edges with the same color *)
Definition cusp : rel (edge G * bool) :=
  fun e1 e2 => c e1 == c (reversed e2).

(* Number of cusps in a path, made by couple of successive edges (not
   counting the one made by the last and first edges in the case of a cycle). *)
Fixpoint nb_cusps (p : @upath _ _ G) : nat :=
  match p with
  | [::] => 0
  | e :: p => nb_cusps p + if p is [::] then 0 else cusp e (head e p)
  end.

Lemma nb_cusps_rcons e (p : upath) :
  nb_cusps (rcons p e) = nb_cusps p +
    if p is [::] then 0 else cusp (last e p) e.
Proof.
  induction p as [ | e' p IH]; first by [].
  rewrite /= {}IH.
  destruct (rcons p e) eqn:F.
  { contradict F. apply rcons_nil. } (* TODO would be great for this to be solved by done...
but I can't manage to do it with just Hint Resolve rcons_nil : core. *)
  destruct p; simpl.
  - by inversion F.
  - inversion F. clear F. subst. lia.
Qed.

Lemma nb_cusps_upath_rev (p : @upath _ _ G) :
  nb_cusps (upath_rev p) = nb_cusps p.
Proof.
  induction p as [ | [e1 b1] p IH] => //=.
  rewrite nb_cusps_rcons {}IH /=. f_equal.
  destruct p; first by [].
  rewrite last_rcons /=.
  destruct (rcons _ _) eqn:F.
  { contradict F. apply rcons_nil. }
  by rewrite /cusp /= negb_involutive eq_sym.
Qed.

Lemma nb_cusps_cat (p q : upath) :
  nb_cusps (p ++ q) = nb_cusps p + nb_cusps q +
    match p, q with | ep :: _, eq :: _ =>
    cusp (last ep p) (head eq q) | _, _ => 0 end.
Proof.
  move: p. induction q as [ | eq q IHq] => p.
  { rewrite /= cats0. destruct p; lia. }
  rewrite -cat_rcons {}IHq /= nb_cusps_rcons.
  destruct (rcons p eq) eqn:F.
  { contradict F. apply rcons_nil. }
  rewrite -{}F last_rcons.
  destruct p, q; simpl; lia.
Qed.

(* For colors, this corresponds to alternating paths. *)
Notation cusp_free p := (nb_cusps p == 0).

Lemma not_cusp_free_has_first_cusp (p : upath) :
  ~~ cusp_free p -> exists p1 p2 e1 e2,
  p = p1 ++ [:: e1; e2] ++ p2 /\ cusp e1 e2 /\ cusp_free (rcons p1 e1).
Proof.
  induction p as [ | e [ | e' p] IH] => // not_cusp_free_e_e'_p.
  case/boolP: (cusp e e') => cusp_e_e'.
  { by exists [::], p, e, e'. }
  case/boolP: (cusp_free (e' :: p)) => not_cusp_free_e'_p.
  { contradict not_cusp_free_e_e'_p. apply/negP/negPn.
    move: not_cusp_free_e'_p. simpl. lia. }
  clear not_cusp_free_e_e'_p.
  destruct (IH not_cusp_free_e'_p) as [p1 [p2 [e1 [e2 [e'_p_eq [B cusp_free_p1_e1]]]]]].
  clear IH not_cusp_free_e'_p. rewrite e'_p_eq.
  exists (e :: p1), p2, e1, e2.
  rewrite {}B /= (eqP cusp_free_p1_e1) {cusp_free_p1_e1}. repeat split.
  destruct (rcons p1 e1) eqn:P1eq; first by [].
  rewrite -{}P1eq.
  replace (head e (rcons p1 e1)) with (head e (p1 ++ [:: e1; e2] ++ p2))
    by by rewrite -cat_rcons head_cat !head_rcons.
  by rewrite -{}e'_p_eq /= (negPf cusp_e_e').
Qed.

Lemma cusp_free_cat (p q : upath) :
  cusp_free (p ++ q) ->
  cusp_free p /\ cusp_free q.
Proof. rewrite nb_cusps_cat. lia. Qed.

(** A graph is cusp_acyclic if all its simple cusp-free cycles have their first and last edges
   making a cuqp; i.e. it has no non-empty simple cuqp-free cycle, if we count as a possible cusp
   also the first and last edges of a cycle. *)
(* TODO rename all bridges into cusps *)
Definition cusp_acyclic : bool :=
  [forall p : Simple_upath G, (cusp_free (val p)) ==>
    match val p with | [::] => true | e :: _ =>
    (upath_source (usource e) (val p) == upath_target (usource e) (val p)) ==>
    cusp (last e (val p)) (head e (val p)) end].
(* TODO def cyclic upath/simple_upath to simplify? *)

(* Take G an edge-colored graph and o a simple cycle such that its first and
  last edges are not a cusp, with a minimal number of bridges (with respect
  to all such cycles with the same source), and containing a bridge, of color
  d and pier k.
  If there is an alternating simple non-cyclic path r starting from k with an
  edge not colored d, with r intersecting o (other than in k), then G is not
  cusp_acyclic. *)
(* TODO "upath_target (usource e1) r \in [seq usource e | e <- o]" replaced
  with "~~ [disjoint [seq utarget e | e <- r] & [seq usource e | e <- o]]":
  this leads to less wlog to do, and is coherent with the ordering:
  to adapt in the journal's text *)
Lemma bungee_jumping (o o1 o2 : upath) e1 e2 r :
(* Let o be a simple cycle *)
  simple_upath o -> upath_source (usource e1) o = upath_target (usource e1) o ->
(* whose first and last edges are not a bridge, *)
  ~~ cusp (last e1 o) (head e1 o) ->
(* with o having a minimal number of bridges among such cycles, with the same source. *)
  (forall p, p <> [::] -> simple_upath p -> upath_source (usource e1) p = upath_source (usource e1) o ->
    upath_source (usource e1) p = upath_target (usource e1) p ->
    ~~ cusp (last e1 p) (head e1 p) -> nb_cusps p >= nb_cusps o) ->
(* Take e1 e2 a bridge of o *)
  o = o1 ++ [:: e1; e2] ++ o2 -> cusp e1 e2 ->
(* and r an alternating simple non-cyclic path starting from the pier of this bridge *)
  upath_source (usource e1) r = utarget e1 -> cusp_free r -> simple_upath r ->
  upath_source (usource e1) r <> upath_target (usource e1) r ->
(* with a different color than the bridge, and from another edge *)
  ~~ cusp e1 (head e1 r) ->
  (head e1 r).1 <> e1.1 -> (head e1 r).1 <> e2.1 -> (* TODO this last hypothesis may be unneeded *)
(* and not vertex-disjoint with o (other than in the source of r). *)
  ~~ [disjoint [seq utarget e | e <- r] & [seq usource e | e <- o]] ->
(* Then G is not cusp_acyclic. *)
  ~~ cusp_acyclic.
Proof.
  move=> Os Oc Onb Omin Oeq B12 Rso Ra Rs Rnc Rc Re1 Re2 Rta.
(* Up to taking a prefix of r, exactly the endpoints of r are in both o and r *)
  wlog {Rta} [Rfst Rta] : r Rso Ra Rs Rnc Rc Re1 Re2 / (forall u, u \in [seq utarget e | e <- r] ->
    u \in [seq usource e | e <- o] -> u = upath_target (usource e1) r) /\
    upath_target (usource e1) r \in [seq usource e | e <- o].
  { move=> {Oc Os Onb Omin Oeq o1 o2 B12} Wlog.
    move: Rta => /disjointP-Rta.
    assert (Rta' : ~~[forall x, (x \in [seq utarget _e | _e <- r]) ==>
       (x \in [seq usource _e | _e <- o]) ==> false]).
    { clear - Rta.
      apply/negP => Rta'.
      contradict Rta => x Xr Xo.
      by move: Rta' => /forallP/(_ x)/implyP/(_ Xr)/implyP/(_ Xo). }
    move: Rta' => {Rta} /forallPn/sigW[u U].
    move: U. rewrite !negb_imply andb_true_r
      => /andP[/mapP-[a a_in_r ?] target_a_in_sources_o]. subst u.
    assert (Rta' : (utarget a \in [seq usource e | e <- o]) &&
      (upath_source (usource e1) r != utarget a)).
    { rewrite target_a_in_sources_o /=.
      apply/eqP => F.
      contradict Rnc.
      apply (simple_upath_source_in_targets Rs).
      by rewrite /= F (map_f (fun _ => _)). }
    destruct (@in_elt_sub_fst _ r (fun e => (utarget e \in [seq usource e | e <- o]) &&
      (upath_source (usource e1) r != utarget e)) a Rta' a_in_r) as [[n N] [e [Req [Ein Efst]]]].
    move: Ein Req => /andP[Ein /eqP-Rnc'] /= Req {Rta' a a_in_r target_a_in_sources_o Rnc}.
    assert (Rs' : simple_upath (rcons (take n r) e)).
    { clear - Rs Req.
      rewrite {}Req -cat_rcons in Rs.
      by apply simple_upath_prefix in Rs. }
    apply (Wlog (rcons (take n r) e)); clear Wlog; try by [].
    - move: Rso. by rewrite {1}Req /= map_cat head_cat map_rcons head_rcons.
    - clear - Ra Req. rewrite {}Req -cat_rcons in Ra.
      by destruct (cusp_free_cat Ra) as [-> _].
    - clear - Rnc' Req.
      move: Rnc'. by rewrite {1}Req /= -cat_rcons map_cat !map_rcons !head_cat !head_rcons last_rcons.
    - rewrite head_rcons head_take. destruct n, r; try by [].
      by rewrite Req in Rc.
    - clear - Re1 Req. move: Re1. by rewrite {1}Req head_cat head_rcons.
    - clear - Re2 Req. move: Re2. by rewrite {1}Req head_cat head_rcons.
    - rewrite /= map_rcons last_rcons Ein. split; last by [].
      clear - Efst Req Rs' => u.
      rewrite /= mem_rcons in_cons => /orP[/eqP--> // | /mapP[a Ain ?]] UinO.
      subst u. contradict UinO. apply/negP.
      move: Efst => /(_ a Ain) /nandP[-> // | /negPn/eqP-Ta].
      exfalso.
      assert (a = e).
      { replace e with (last a (rcons (take n r) e)) by by rewrite last_rcons.
        apply back_source_is_last; try by [].
        - by rewrite -Ta {1}Req /= map_cat head_cat map_rcons head_rcons.
        - by rewrite mem_rcons in_cons Ain orb_true_r. }
      subst a.
      assert (U := uniq_fst_simple_upath Rs').
      contradict U. apply/negP.
      by rewrite map_rcons rcons_uniq map_f. }
(* By symmetry, up to reversing o, upath_target (usource e1) r is in o2 the second half of the cycle,
   and if it is the source of o then its last edge does not make a cusp with the first edge of o. *)
(* This stronger hypothesis replaces the weaker Rta. *)
  wlog {Rta} Rta : o o1 o2 e1 e2 r Os Oc Onb Omin Oeq B12 Rso Ra Rs Rnc Rc Re1 Re2 Rfst /
    upath_target (usource e1) r \in [seq usource e | e <- o2] \/
    (upath_target (usource e1) r = upath_source (usource e1) o /\
    ~~ cusp (last e1 r) (head e1 o)).
  { move=> Wlog.
(* Some equalities on endpoints of the paths *)
    assert (Onil : o <> [::]) by by destruct o, o1.
    assert (Ow := @uwalk_of_simple_upath _ _ _ _ Os (usource e1)). rewrite Oeq in Ow.
    assert (O1e1 := uwalk_sub_middle Ow).
    move: Ow. rewrite 2!uwalk_cat =>/andP[O1w /andP[E1E2 _]].
    rewrite {}O1e1 in O1w.
    move: O1w E1E2. rewrite /= !map_cat !head_cat !eq_refl andb_true_r /= => O1w /andP[_ /eqP-E1E2].
    assert (Omem : [seq utarget e | e <- o] =i [seq usource e | e <- o]).
    { apply eq_mem_sym, (@mem_usource_utarget_cycle _ _ _ (upath_source (usource e1) o)).
      rewrite {2}Oc. by apply uwalk_of_simple_upath. }
(* If the target of r is the source of o, and does not make a bridge with it, or
   if the target of r is in o2 and not the source of o, then apply Wlog to o. *)
    destruct ((upath_target (usource e1) r == upath_source (usource e1) o) &&
      (~~ cusp (last e1 r) (head e1 o)) ||
      (last (usource e1) [seq utarget e | e <- r] \in [seq usource e | e <- o2])) eqn:Rta'.
    { apply (Wlog o o1 o2 e1 e2 r); try by [].
      move: Rta' => /orP[/andP[/eqP-? ?] | ?]; [by right | by left]. }
   move: Rta' => /norP[Rta1 Rta2]. rewrite negb_andb negb_involutive in Rta1.
(* The target of r cannot be the source of e2, which is the the source of the non-cyclic r. *)
    case/boolP: (last (usource e1) [seq utarget e | e <- r] == usource e2) => /eqP-Rta3.
    { contradict Rnc. by rewrite Rso -E1E2 -Rta3. }
(* Thus, the target of r is in (rcons o1 e1). *)
    move: Rta. rewrite Oeq -cat_rcons !map_cat !mem_cat /= !in_cons.
    move: Rta2 Rta3 => /negPf--> /eqP/negPf-->.
    rewrite !orb_false_r => Rta.
(* In this case, we apply Wlog to the cycle o reversed. *)
    apply (Wlog (upath_rev o) (upath_rev o2) (upath_rev o1) (reversed e2) (reversed e1) r);
      clear Wlog; try by [].
    - by rewrite simple_upath_rev.
    - rewrite uendpoint_reversed /= 2!map_uendpoint_upath_rev head_rev last_rev.
      by destruct o.
    - rewrite head_upath_rev last_upath_rev.
      move: Onb. rewrite /cusp /= !negb_involutive -!surjective_pairing eq_sym.
      by destruct o.
    - move=> p Ps.
      move: Omin => /(_ p Ps).
      rewrite upath_endpoint_rev Oc nb_cusps_upath_rev.
      by destruct o, p.
    - by rewrite Oeq !upath_rev_cat /= -catA -cat1s -catA !cat1s.
    - move: B12. by rewrite /cusp /= negb_involutive -surjective_pairing eq_sym.
    - move: Rso. rewrite 2!uendpoint_reversed E1E2. by destruct r.
    - move: Rnc. rewrite uendpoint_reversed. by destruct r.
    - move: B12 Rc. rewrite /cusp /= => /eqP-->. by destruct r.
    - by destruct r.
    - by destruct r.
    - move=> u.
      rewrite map_uendpoint_upath_rev mem_rev Omem.
      replace (upath_target (usource (reversed e2)) r) with
        (upath_target (usource e1) r) by by destruct r.
      apply Rfst.
    - move: Rta.
      rewrite upath_endpoint_rev.
      replace (upath_endpoint (~~ false) (usource (reversed e2)) o)
        with (upath_source (usource e1) o) by by destruct o.
      rewrite !map_uendpoint_upath_rev !uendpoint_reversed mem_rev /= map_rcons mem_rcons
        (mem_usource_utarget_uwalk O1w) in_cons (last_eq _ (usource e1)); last by destruct r.
      replace (head (usource e1) [seq usource e | e <- o1]) with
        (head (usource e1) [seq usource e | e <- o]) by by rewrite Oeq map_cat head_cat.
      move=> /orP[/eqP-Rta | ->]; [right | by left]. split; first by [].
      rewrite head_upath_rev /= !(last_eq _ e1) //; [ | by destruct r].
      rewrite /= Rta eq_refl /= in Rta1.
      move: Rta1 Onb.
      rewrite /cusp negb_involutive /=.
      destruct r as [ | r [er br] _] using last_ind; first by [].
      rewrite !last_rcons -surjective_pairing.
      destruct o => //= /eqP-->.
      by rewrite eq_sym. }
(* As r ends in o2, we separate o2 in o21 before the target of r and o22 after,
   and r ends on the source of o (without a bridge) if o22 is empty. *)
  assert (exists o21 o22, o2 = o21 ++ o22 /\
    upath_source (upath_target (utarget e2) o21) o22 = upath_target (usource e1) r /\
    if o22 == [::] then ~~ cusp (last e1 r) (head e1 o) else true)
    as [o21 [o22 [O2eq [O2so Bnro]]]].
  { destruct Rta as [Rta | [RtOs ->]].
    - move: Rta => /mapP[e Eo2 ->].
      rewrite in_elt_sub in Eo2. move: Eo2 => /existsP[[n N] /= /eqP-Eo2].
      exists (take n o2), (drop n o2).
      rewrite cat_take_drop. split; trivial.
      rewrite -{1}(cat_take_drop n o2) in Eo2.
      apply cat_eq_l in Eo2.
      by rewrite Eo2.
    - exists o2, [::].
      rewrite cats0 eq_refl. repeat (split; trivial).
      by rewrite RtOs Oc Oeq /= map_cat last_cat. }
  subst o2. clear Rta.
(* Some equalities on endpoints of the paths, almost copy-pasted from above TODO without copy-paste *)
  assert (Ow := @uwalk_of_simple_upath _ _ _ _ Os (usource e1)). rewrite Oeq in Ow.
  assert (O1e1 := uwalk_sub_middle Ow). rewrite /= map_cat head_cat /= in O1e1.
  move: Ow. rewrite 2!uwalk_cat =>/andP[_ /andP[E1E2w O2w]].
  move: E1E2w. rewrite /= eq_refl andb_true_r => /andP[_ /eqP-E1E2].
  apply uwalk_sub_middle in O2w. rewrite /= !map_cat !last_cat /= map_cat last_cat in O2w.
  assert (Omem : [seq utarget e | e <- o] =i [seq usource e | e <- o]).
  { apply eq_mem_sym, (@mem_usource_utarget_cycle _ _ _ (upath_source (usource e1) o)).
    rewrite {2}Oc. by apply uwalk_of_simple_upath. }
(* No edge of r belongs to o. *)
  assert (Dro : [disjoint [seq e.1 | e <- r] & [seq e.1 | e <- o]]). (* TODO lemma? *)
  { clear Oc Onb Omin Ra Rnc Bnro.
    apply/disjointP => e Er Eo.
    assert (Rfst' : forall u, u \in [seq utarget e | e <- r] ->
      u \in [seq usource e | e <- o] -> u = upath_target u r).
    { move=> u Ur Uo. rewrite (Rfst u Ur Uo). by destruct r. }
    destruct (disjoint_or_edge Omem Rs Rfst' Er Eo) as [b ?]. clear Rfst'. subst r.
    apply in_map_fst in Eo as [b' Eo].
    assert (E22 : utarget (e, b') = utarget e1 \/ usource (e, b') = utarget e1). (* TODO lemma for this, I think I use it elsewhere *)
    { rewrite -Rso. clear. by destruct b, b'; auto. }
    clear Rso. destruct E22 as [E22 | E22].
    - assert (U := uniq_utarget_simple_upath Os).
      contradict U. apply/negP.
      apply (@not_uniq_map _ _ _ _ (e, b') e1); try by [].
      + by rewrite Oeq !mem_cat !in_cons eq_refl !orb_true_r.
      + move=> ?. by subst e1.
    - rewrite -E1E2 in E22.
      assert (U := uniq_usource_simple_upath Os).
      contradict U. apply/negP.
      apply (@not_uniq_map _ _ _ _ (e, b') e2); try by [].
      + by rewrite Oeq !mem_cat !in_cons eq_refl !orb_true_r.
      + move=> ?. by subst e2. }
(* The following cycle, p, has the needed properties to use the minimality of o. *)
  set p := o1 ++ e1 :: r ++ o22.
  assert (Pnil : p <> [::]) by by destruct o1.
  assert (Ps : simple_upath p).
  { rewrite /p.
    enough (simple_upath (e1 :: r ++ o22)).
    { case/boolP: (o1 == [::]) => /eqP-?; first by subst o1.
      apply simple_upath_cat; try by [].
      - rewrite Oeq in Os. by apply simple_upath_prefix in Os.
      - rewrite -O1e1. apply/eqP. by destruct o1.
      - apply uniq_usource_simple_upath in Os.
        move: Os.
        rewrite Oeq !map_cat !cat_uniq /= !has_cat !negb_orb /= -!disjoint_has !andb_true_r.
        move=> /andP[_ /andP[/andP[E1O1 /andP[E2O1 /andP[_ Do22o1]]] _]].
        rewrite disjoint_sym disjoint_cons map_cat disjoint_cat {}E1O1 {}Do22o1 /= andb_true_r.
        apply /disjointP => v Vr Vo1.
        assert (Vr': v \in (upath_target (usource e1) r) :: [seq usource e | e <- r])
          by by rewrite in_cons Vr orb_true_r.
        rewrite (@mem_usource_utarget_uwalk _ _ _ (upath_source (usource e1) r)) in Vr';
          last by apply (@uwalk_of_simple_upath _ _ _ _ Rs (usource e1)).
        move: Vr'. rewrite /= in_cons => /orP[/eqP-? | Vr'].
        + subst v.
          by rewrite E1E2 -Rso Vo1 in E2O1.
        + assert (v = upath_target (usource e1) r).
          { apply Rfst; try by [].
            by rewrite Oeq map_cat mem_cat Vo1. }
          subst v. clear - Vr Rs Rnc.
          contradict Rnc.
          by apply simple_upath_target_in_sources.
      - assert (upath_target (usource e1) (e1 :: r ++ o22) = upath_target (usource e1) o) as ->.
        { destruct o22.
          - move: O2so. rewrite cats0 /= Oeq !map_cat !last_cat /= => ->.
            by destruct r.
          - by rewrite Oeq /= !map_cat !last_cat /= !map_cat !last_cat. }
        rewrite -Oc Oeq.
        apply /negP => F.
        assert (E : upath_source (usource e1) o1 = upath_target (usource e1) o1).
        { destruct o1; first by [].
          apply simple_upath_source_in_targets; last by [].
          rewrite Oeq in Os. by apply simple_upath_prefix in Os. }
        move: E.
        clear - F Os Oeq.
        rewrite {}Oeq -cat_rcons in Os. apply simple_upath_prefix in Os.
        move: Os. rewrite simple_upath_rcons => /andP[_ /orP[/eqP-? | /eqP-?]].
        + by subst o1.
        + by destruct o1.
      - rewrite Oeq -cat_rcons /= in Os.
        apply simple_upath_prefix in Os.
        rewrite simple_upath_rcons in Os.
        move: Os => /andP[/andP[/andP[/andP[_ Os] _] _] _].
        destruct o1; by rewrite // eq_sym. }
    rewrite simple_upath_cons. apply /andP; split; [apply /andP; split | ];
      [apply /andP; split | | ]; [apply /andP; split | | | ].
    - case/boolP: (o22 == [::]) => /eqP-O22nil; first by (subst o22; rewrite cats0).
      apply simple_upath_cat; try by [].
      + rewrite Oeq !catA in Os. by apply simple_upath_suffix in Os.
      + destruct o22, r; by apply /eqP.
      + apply /disjointP => [v Vr Vo22].
        case/boolP: (v == upath_source (usource e1) r) => [/eqP-? | Vsr].
        * subst v.
          rewrite Rso -E1E2 in Vo22.
          apply uniq_usource_simple_upath in Os.
          contradict Os. apply /negP.
          by rewrite Oeq !map_cat !cat_uniq /= !has_cat (has_sym [:: usource e1; usource e2]
            [seq usource _e | _e <- o22]) /= Vo22 !orb_true_r !andb_false_r.
        * assert (Vint : (v \in [seq usource e | e <- r]) && (v != upath_source v r)).
          { rewrite Vr /= (head_eq _ (usource e1)) ?Vsr //. by destruct r. }
          rewrite (mem_usource_utarget_simple_upath_internal Rs) in Vint.
          move: Vint => /andP[Vrt /eqP-Vrta].
          contradict Vrta.
          replace (upath_target v r) with (upath_target (usource e1) r) by by destruct r.
          apply Rfst; first by [].
          by rewrite Oeq !map_cat !mem_cat Vo22 !orb_true_r.
      + destruct o22 as [ | e22 o22]; first by [].
        replace (upath_target (usource e22) (e22 :: o22)) with (upath_target (usource e1) o)
          by by rewrite Oeq /= map_cat /= map_cat last_cat /= last_cat.
        rewrite -Oc.
        apply /negP => F.
        assert (F' : upath_source (usource e1) o = upath_target (usource e1) r).
        { apply Rfst; first by []. rewrite mem3_head //; by destruct o, o1. }
        rewrite -O2so Oc in F'.
        assert (F'' : upath_source (usource e1) (e22 :: o22) = upath_target (usource e1) (e22 :: o22)).
        { move: F'. by rewrite Oeq /= map_cat /= map_cat last_cat /= last_cat. }
        contradict F''.
        apply (@simple_cat_not_cyclic _ _ _ (o1 ++ [:: e1; e2] ++ o21) (e22 :: o22)); trivial.
        * by rewrite -!catA -Oeq Os.
        * by destruct o1.
      + destruct o22, r as [ | er r]; try by [].
        apply/eqP. move=> /= F.
        move: Dro => /disjointP/(_ (last e2 (er :: r)).1)-Dro. apply Dro.
        * by apply map_f, mem3_last.
        * rewrite F. apply map_f.
          by rewrite Oeq !mem_cat !in_cons eq_refl !orb_true_r.
    - destruct r => //=.
      apply /eqP => E1r.
      move: Dro => /disjointP/(_ e1.1)-Dro. apply Dro.
      + by rewrite E1r /= in_cons eq_refl.
      + by rewrite Oeq !map_cat !mem_cat /= in_cons eq_refl orb_true_r.
    - rewrite -Rso. by destruct r.
    - rewrite map_cat mem_cat negb_orb. apply /andP; split.
      + apply /negP => E1r.
        assert (Hr : usource e1 != upath_source (usource e1) r).
        { rewrite Rso -E1E2.
          apply /eqP => F.
          assert (U := uniq_usource_simple_upath Os). contradict U. apply /negP.
          by rewrite Oeq !map_cat !cat_uniq /= !in_cons F eq_refl !andb_false_r. }
        assert (E1r' : (usource e1 \in [seq usource e | e <- r]) &&
          (usource e1 != upath_source (usource e1) r))
          by by rewrite Hr E1r.
        clear Hr E1r.
        rewrite (mem_usource_utarget_simple_upath_internal Rs) in E1r'.
        move: E1r' => /andP[E1r /eqP-E1rt].
        contradict E1rt.
        apply (Rfst _ E1r).
        by rewrite Oeq !map_cat !mem_cat in_cons eq_refl orb_true_r.
      + apply /negP => F.
        assert (U := uniq_usource_simple_upath Os). contradict U. apply /negP.
        by rewrite Oeq !map_cat !cat_uniq !has_cat (has_sym [:: usource e1; usource e2]
          [seq usource e | e <- o22]) /= F !orb_true_r !andb_false_r.
    - apply /orP. right. apply /eqP.
      replace (upath_source (utarget e1) (r ++ o22)) with (upath_source (usource e1) r)
        by by destruct r.
      replace (upath_target (utarget e1) (r ++ o22)) with
        (upath_target (upath_target (utarget e1) r) o22) by by rewrite /= map_cat last_cat.
      destruct o22 as [ | o22 e22 _] using last_ind.
      { by destruct r. }
      rewrite Rso /= map_rcons last_rcons => F.
      assert (U := uniq_utarget_simple_upath Os).
      contradict U. apply /negP.
      by rewrite Oeq !map_cat !map_rcons !cat_uniq !rcons_uniq !has_cat !has_rcons /=
        !in_cons F eq_refl orb_true_r !andb_false_r. }
  assert (Pso : upath_source (usource e1) p = upath_source (usource e1) o).
  { rewrite /p Oeq. by destruct o1. }
  assert (Pc : upath_source (usource e1) p = upath_target (usource e1) p).
  { move: O2so.
    rewrite Pso Oc /p Oeq /= !map_cat /= !map_cat !last_cat /= !last_cat.
    by destruct o22, r. }
  assert (Pnb : ~~ cusp (last e1 p) (head e1 p)).
  { move: Bnro Onb O2so. rewrite /p Oeq !head_cat !last_cat /= last_cat.
    by destruct o22. }
(* By minimality of o, the last edge of r and the first of o22 makes a bridge,
   o1 is bridge-free and we know some bridge-free points *)
  specialize (Omin _ Pnil Ps Pso Pc Pnb).
  rewrite Oeq !nb_cusps_cat /= B12 /= nb_cusps_cat {p Pnil Pso Pc Ps Pnb} in Omin.
  move: Ra => /eqP-Ra. rewrite Ra in Omin. (* TODO Ra in Prop? *)
  assert (Omin' : 1 + nb_cusps o21 +
    match o21 with | [::] => 0 | ep :: _ =>
      match o22 with | [::] => 0 | eq :: _ => cusp (last ep o21) (head eq o22) end end +
    match o21 ++ o22 with | [::] => 0 | eq :: _ => cusp e2 (head eq (o21 ++ o22)) end <=
    cusp e1 (head e1 r) +
    match o22 with | [::] => 0 | eq :: _ => cusp (last e1 r) (head eq o22) end).
  { move: Omin. destruct r; first by []. clear. simpl. lia. }
  clear Omin.
  replace (cusp e1 (head e1 r)) with false in Omin'; last first.
  { clear - Rc. symmetry. by apply /negP/negP. }
  assert (nb_cusps o21 = 0 /\
    match o21 with | [::] => true | _ :: _ =>
      match o22 with | [::] => true | _ :: _ => ~~ cusp (last e1 o21) (head e1 o22) end end /\
    match o21 ++ o22 with | [::] => true | _ :: _ => ~~ cusp e2 (head e1 (o21 ++ o22)) end /\
    match o22 with | [::] => false | _ :: _ => cusp (last e1 r) (head e1 o22) end)
    as [O21a [Bno21o22 [Bne2o2122 Be1o22]]].
  { move: Omin'. destruct r; first by []. clear. destruct o22, o21; simpl; lia. }
  clear Omin'.
(* Thanks to the bridge-freeness hypotheses given by the minimality of o,
   r ++ upath_rev (e2 :: o21) contradicts cusp_acyclicity. *)
  assert (S : simple_upath (r ++ upath_rev (e2 :: o21))).
  { apply simple_upath_cat; try by [].
    - rewrite simple_upath_rev.
      rewrite Oeq -cat_rcons -cat_cons in Os.
      by apply simple_upath_suffix, simple_upath_prefix in Os.
    - destruct (upath_rev (e2 :: o21)) eqn:R; first by []; rewrite -{}R.
      rewrite upath_endpoint_rev.
      move: O2so. destruct r; first by []. move=> /= <-.
      apply/eqP. by destruct o21, o22.
    - rewrite map_uendpoint_upath_rev disjoint_sym disjoint_rev.
      apply /disjointP => u Uo Ur.
      assert (Uo' : u \in [seq usource e | e <- o])
        by by rewrite -Omem Oeq !cat_cons /= -cat_rcons -cat_cons !map_cat !mem_cat Uo orb_true_r.
      assert (Ur' : u \in upath_target (usource e1) r :: [seq usource _e | _e <- r])
        by by rewrite in_cons Ur orb_true_r.
      rewrite (mem_usource_utarget_uwalk (uwalk_of_simple_upath Rs _)) in_cons in Ur'.
      move: Ur' => /orP[/eqP-? | Ur'].
      + subst u.
        rewrite Rso in Uo.
        rewrite Oeq !cat_cons /= -!cat_cons in Os.
        apply simple_upath_suffix, simple_upath_prefix in Os.
        move: Os. rewrite simple_upath_cons
          => /andP[/andP[/andP[/andP[E2O21s _] /eqP-E1ta] _] /orP[// | /eqP-E2O2nc]].
        contradict E2O2nc.
        apply (simple_upath_source_in_targets E2O21s).
        by rewrite /= E1E2.
      + specialize (Rfst _ Ur' Uo'). subst u.
        contradict Rnc.
        by apply simple_upath_target_in_sources.
    - destruct (upath_rev (e2 :: o21)) eqn:R; first by []. rewrite -{}R.
      rewrite upath_endpoint_rev /=.
      apply /negP => F.
      contradict Rnc.
      apply (simple_upath_source_in_targets Rs).
      by rewrite Rso -E1E2 F.
    - destruct r as [ | er r], (upath_rev (e2 :: o21)) eqn:R; try by [].
      apply/eqP => F.
      move: Dro => /disjointP/(_ (last e1 (er :: r)).1)-Dro. apply Dro.
      + by apply map_f, mem3_last.
      + rewrite F Oeq.
        replace (o1 ++ [:: e1; e2] ++ o21 ++ o22) with
          (o1 ++ e1 :: (upath_rev (upath_rev (e2 :: o21))) ++ o22)
          by by rewrite upath_rev_inv.
        by rewrite {}R !map_cat /= map_cat map_rcons mem_cat in_cons mem_cat
          in_rcons eq_refl !orb_true_r. }
  rewrite /cusp_acyclic. apply/forallPn.
  exists (Sub _ S).
  rewrite negb_imply. apply/andP; split.
  - rewrite nb_cusps_cat nb_cusps_upath_rev /= Ra O21a.
    replace (0 + match o21 with | [::] => 0 | _ :: _ => cusp e2 (head e2 o21) end)
      with 0 by (clear - Bne2o2122; destruct o21; simpl in *; lia).
    assert (Hr : match r with | [::] => 0 | ep :: _ =>
      match rcons (upath_rev o21) (reversed e2) with
      | [::] => 0 | eq :: _ => cusp (last ep r) (head eq (rcons (upath_rev o21) (reversed e2))) end end =
      cusp (last e1 r) (head e2 (rcons (upath_rev o21) (reversed e2)))).
    { destruct r, (rcons (upath_rev o21) (reversed e2)) eqn:F; try by [].
      contradict F. apply rcons_nil. }
    rewrite {}Hr head_rcons head_upath_rev /= negb_involutive -surjective_pairing /=.
    enough (E : ~~ cusp (last e1 r) (reversed (last e2 o21))) by (clear - E; lia).
    apply/negP => B.
    destruct o22 as [ | e22 o22]; first by [].
    move: B Be1o22. rewrite /cusp /= negb_involutive -surjective_pairing => /eqP--> BF.
    clear - Bno21o22 Bne2o2122 BF.
    destruct o21 as [ | e21 o21]; simpl in *.
    + contradict Bne2o2122. by apply/negP/negPn.
    + contradict Bno21o22. by apply/negP/negPn.
  - rewrite /=. destruct r; first by [].
    rewrite /= negb_imply. simpl in *.
    move: Rso.
    rewrite /= !map_cat !map_rcons map_uendpoint_upath_rev !last_cat !last_rcons /= uendpoint_reversed E1E2 => Rso.
    rewrite Rso eq_refl /=.
    apply/negP => B. contradict Rc. apply/negP/negPn.
    move: B B12. by rewrite /cusp => /eqP--> /eqP-->.
Qed.
(* TODO surely possible to simplify *)
(* TODO then define the ordering, prove it is an ordering, and then that no splitting => no max thanks to bungee_jumping, then use it instead of work done below in this file *)

(* Given two edges * bool e and f , we write e ↱^p f if p is a simple open cusp-free path
   from t(e) to t(f) such that e does not make a cusp with the first edge of p and the last edge of p is f.
   We simply write e ↱ f whenever such a path exists.
   We then write e ◁^p f when e ↱^p f and for all edge g and path q such that f ↱^q g, p and q have only
   t(f) as a common vertex. Again, we may simply write e ◁ f whenever such a path exists.
*)
(* TODO with an option type for the case with a graph with no edges? *)
Definition pre_ordering_path (e f : edge G * bool) (p : Simple_upath G) : bool :=
  (upath_source (utarget e) (val p) != upath_target (utarget e) (val p)) &&
  (cusp_free (val p)) &&
  (upath_source (utarget e) (val p) == utarget e) && (~~ cusp e (head e (val p))) &&
  (last e (val p) == f).

Definition ordering_path (e f : edge G * bool) (p : Simple_upath G) : bool :=
  (pre_ordering_path e f p) &&
  [forall g : edge G * bool, [forall q : Simple_upath G,
  pre_ordering_path f g q ==>
  [disjoint [seq utarget e | e <- val q] & [seq usource e | e <- val p]]]].

Definition ordering (e f : edge G * bool) : bool :=
  [exists p, ordering_path e f p].

Lemma pre_ordering_path_irrefl (e : edge G * bool) (p : Simple_upath G) :
  ~~pre_ordering_path e e p.
Proof.
  destruct p as [p P].
  rewrite /pre_ordering_path /=.
  destruct p as [ | p f _] using last_ind.
  - by rewrite /= eq_refl.
  - rewrite !map_rcons head_rcons !last_rcons.
    apply/negP => /andP[/andP[/andP[HF HE] _] /eqP-?].
    subst f. by rewrite HE in HF.
Qed.

Lemma ordering_irrefl : irreflexive ordering.
Proof.
  hnf => e. apply/existsPn => p.
  by rewrite /ordering_path negb_andb pre_ordering_path_irrefl.
Qed.

(* Let e, f and g be edges and let p and q be paths. If e ◁^p f and f ↱^q g then e ↱^pq g. *)
Lemma ordering_preordering_transitive (e f g : edge G * bool) (p q : Simple_upath G) :
  ordering_path e f p -> pre_ordering_path f g q ->
  { PQ : simple_upath (val p ++ val q) | pre_ordering_path e g (exist (fun q : upath => simple_upath q) _ PQ) }.
Proof.
  rewrite /ordering_path.
  move=> /andP[Op /forallP/(_ g)/forallP/(_ q)/implyP-Hp] Oq.
  specialize (Hp Oq).
  destruct p as [p P], q as [q Q].
  enough (Spq : simple_upath (p ++ q)).
  { exists Spq.
    move: Op Oq Hp.
    rewrite /ordering_path /pre_ordering_path /= !map_cat !head_cat !last_cat.
    destruct p as [ | ep p]; first by rewrite eq_refl.
    destruct q as [ | q eq _] using last_ind; first by rewrite eq_refl.
    rewrite /= !map_rcons !last_rcons disjoint_rcons in_cons negb_orb.
    move=> /andP[/andP[/andP[/andP[_ Cp] ->] ->] /eqP-?] /andP[/andP[/andP[/andP[_ /eqP-Cq] _] Cfq] ->] /andP[/andP[Depeq _] _].
    subst f.
    rewrite eq_sym Depeq /= nb_cusps_cat Cq.
    destruct p.
    - rewrite /=. destruct (rcons q eq) eqn:F; first by [].
      move: Cfq. rewrite -F /=. clear. lia.
    - move: Cp Cfq Cq. rewrite /=. destruct (rcons q eq) as [ | eeq ?] eqn:F.
      + contradict F. apply rcons_nil.
      + rewrite -F /=.
        rewrite (@head_eq _ _ eeq (rcons q eq)); last by apply rcons_nil.
        clear. lia. }
  apply (@simple_disjoints_are_cat_simple _ _ _ (utarget f)); trivial.
  - move: Op. rewrite /pre_ordering_path /=.
    destruct p; first by rewrite eq_refl.
    by move=> /= /andP[/andP[/andP[/andP[/eqP-? _] _] _] _].
  - move: Oq. rewrite /pre_ordering_path /=.
    destruct q; first by rewrite eq_refl.
    by move=> /= /andP[/andP[/andP[/andP[/eqP-? _] _] _] _].
  - move: Op Oq. rewrite /pre_ordering_path /=.
    destruct p as [ | p ep _] using last_ind; first by rewrite eq_refl.
    destruct q; first by rewrite eq_refl.
    rewrite /= !map_rcons !last_rcons.
    by move=> /andP[_ /eqP-->] /andP[/andP[/andP[_ /eqP-->] _] _].
Qed.

Lemma ordering_transitive : transitive ordering.
Proof.
  move=> f e g /existsP[p Op] /existsP[q Oq].
  apply/existsP.
  assert ({ PQ : simple_upath (val p ++ val q) |
    pre_ordering_path e g (exist (fun q : upath => simple_upath q) _ PQ) })
    as [PQ Opq].
  { apply (@ordering_preordering_transitive e f g p q Op). by move: Oq => /andP[-> _]. }
  exists (exist (fun h : upath => simple_upath h) _ PQ).
  rewrite /ordering_path Opq /=.
  apply/forallP => h. apply/forallP => r. apply/implyP => Or.
  rewrite map_cat disjoint_sym disjoint_cat.
  apply/andP; split.
  - destruct (ordering_preordering_transitive Oq Or) as [QR Oqr].
    move: Op. rewrite /ordering_path => /andP[_ /forallP/(_ h)/forallP
      /(_ (exist (fun q : upath => simple_upath q) _ QR))/implyP/(_ Oqr)].
  rewrite /= map_cat disjoint_cat => /andP[_ ?]. by rewrite disjoint_sym.
  - move: Oq. rewrite /ordering_path => /andP[_ /forallP/(_ h)/forallP/(_ r)/implyP/(_ Or)].
    by rewrite disjoint_sym.
Qed.

(* We consider T as a finite partial ordered type. *)
HB.instance Definition _ := @Order.Lt_isPOrder.Build
  tt (edge G * bool)%type ordering ordering_irrefl ordering_transitive.
  (*
Definition T_finPOrderType : Type := (edge G * bool). (* TODO Define T so that this trick is unneeded *)
HB.instance Definition _ := Finite.on T_finPOrderType. (* To prevent delta-expansion *)
HB.instance Definition _ := @Order.Lt_isPOrder.Build
  tt T_finPOrderType ordering ordering_irrefl ordering_transitive.
  (* TODO warnings + do not use T *)*)


(* We are looking for a splitting vertex, one such that any simple cycle starting from it
   has its first and last edges making a bridge. *)
Definition splitting (v : G) : bool :=
  [forall p : Simple_upath G, (upath_source v (val p) == v) ==> (upath_target v (val p) == v) ==>
  (match p with
  | exist [::] _ => true
  | exist (e :: p') _ => cusp (last e p') e end)].

(* A cusping edge is an edge in some cusp *)
Definition cusping (e : edge G * bool) : bool :=
  [exists f, (cusp e f) && (e != reversed f)].

(* A vertex v which is the utarget of a maxiaml edge is splitting.
   Or by contrapose, a non-splitting element cannot be the utarget of a maximal edge. *)
Lemma no_splitting_is_no_max (e : edge G * bool) :
  cusp_acyclic -> ~~ splitting (utarget e) ->
  exists f, e < f /\ cusping f.
Proof.
(* Take v a non-splitting vertex: it is in a simple cycle o starting from it whose first
   and last edges do not make a bridge. *)
  move=> C /forallPn[[o O] /= ].
  rewrite !negb_imply => /andP[/eqP-Oso /andP[/eqP-Ota Bv']].
  assert (Onil : o <> [::]) by by destruct o.
  assert (e_base : edge G * bool) by by destruct o.
  assert (Bv : ~~ cusp (last e_base o) (head e_base o)) by by destruct o.
  clear Bv'.
(* Without loss of generality, we can take o to have a minimal number of bridges among all
   such cycles. *)
  wlog Omin : o O Oso Ota Onil Bv / forall p, simple_upath p ->
    upath_source (utarget e) p = upath_source (utarget e) o ->
    upath_source (utarget e) p = upath_target (utarget e) p ->
    p <> [::] ->
    ~~ cusp (last e_base p) (head e_base p) ->
  nb_cusps p >= nb_cusps o.
  { move=> Wlog.
    set PropMin := fun (p : Simple_upath G) =>
      (upath_source (utarget e) (val p) == upath_source (utarget e) o) &&
      (upath_source (utarget e) (val p) == upath_target (utarget e) (val p)) &&
      (val p != [::]) && ~~ cusp (last e_base (val p)) (head e_base (val p)).
    assert (PropMino : PropMin (Sub o O)).
    { repeat (apply /andP; split); try by [].
      - by rewrite /= Oso Ota.
      - by apply/eqP. }
    move: PropMino => /(@arg_minnP _ (Sub o O : Simple_upath G) PropMin (fun p => nb_cusps (val p)))-[[o' O']
      /andP[/=/andP[/andP[/eqP-O'so /eqP-O'c] /eqP-O'nil] O'b] O'min].
    apply (Wlog o'); try by [].
    - by rewrite O'so Oso.
    - by rewrite -O'c O'so Oso.
    - move=> p P Pso Pc Pnil Pb.
      apply (O'min (Sub _ P)).
      rewrite /PropMin Pb -Pc Pso /= {1}O'so O'c !eq_refl /= andb_true_r.
      by apply /eqP. }
(* Still without loss of generality, up to reversing o, it does not start with
   an edge colored as e. This is possible as its first and last
   edges have different colors. *)
  wlog Ostart : o O Oso Ota Onil Bv Omin / ~~ cusp e (head e_base o).
  { move=> Wlog.
    case/boolP: (~~ cusp e (head e_base o)).
    { move=> ?. by apply (Wlog o). }
    rewrite negb_involutive => Oend.
    assert (last_head : utarget (last (reversed e_base) o) = usource (head e_base o))
      by by rewrite (@cyclic_source_eq_target _ _ _ _ (utarget e) _ e_base Onil) //= Oso Ota.
    apply (Wlog (upath_rev o)); clear Wlog.
    - by rewrite simple_upath_rev.
    - by rewrite map_uendpoint_upath_rev head_rev.
    - by rewrite map_uendpoint_upath_rev last_rev.
    - apply/eqP. rewrite upath_rev_nil. by apply/eqP.
    - move: Bv. rewrite head_upath_rev last_upath_rev /cusp /= negb_involutive eq_sym -surjective_pairing.
      by destruct o.
    - rewrite nb_cusps_upath_rev upath_endpoint_rev.
      by replace (upath_endpoint (~~ false) (utarget e) o) with (upath_source (utarget e) o)
       by by rewrite /= Oso Ota.
    - move: Oend Bv.
      rewrite head_upath_rev /cusp /= negb_involutive -surjective_pairing.
      destruct o as [ | eo o]; first by [].
      move=> /= /eqP-->. by rewrite eq_sym. }
(* By cusp_acyclicity, this cycle o cannot be cusp-free. *)
  case/boolP: (cusp_free o) => Oa.
  { contradict C. apply/negP/forallPn.
    exists (Sub _ O).
    rewrite /= negb_imply Oa /=.
    destruct o as [ | eo o]; first by [].
    by rewrite negb_imply (head_eq _ (utarget e)) ?(last_eq _ (utarget e)) // Oso Ota eq_refl. }
(* So, it has a cusp. We take the first one, following o. *)
  destruct (not_cusp_free_has_first_cusp Oa) as [o1 [o2 [e1 [e2 [Oeq [B12 Bfst]]]]]].
(* By bungee jumping, e < e1. *)
  exists e1. split; last first.
  { apply/existsP. exists e2.
    rewrite B12 /=. apply/eqP => ?. subst e1.
    have := uniq_fst_simple_upath O.
    by rewrite Oeq !map_cat !cat_uniq /= in_cons eq_refl /= !andb_false_r. }
  assert (O1 : simple_upath (rcons o1 e1)).
  { rewrite Oeq -cat_rcons in O.
    by apply simple_upath_prefix in O. }
  apply/existsP. exists (Sub _ O1).
  rewrite /ordering_path /pre_ordering_path /= Bfst !last_rcons !eq_refl !andb_true_r.
  repeat (apply /andP; split).
  - rewrite Oeq -!cat_rcons in O.
    apply simple_upath_prefix in O.
    move: O. rewrite simple_upath_rcons => /andP[_ /orP[/eqP-F | O]].
    { contradict F. apply rcons_nil. }
    move: O. by rewrite /= !map_rcons !head_rcons !last_rcons.
  - by rewrite -Oso Oeq -cat_rcons map_cat head_cat !map_rcons !head_rcons.
  - move: Ostart.
    rewrite Oeq. by destruct o1.
  - (* This is where we use the bungee jumping lemma. *)
    apply/forallP => f. apply/forallP => q.
    apply/implyP => /andP[/andP[/andP[/andP[Oq Cq] /eqP-Hq] Ce1q] /eqP-?]. subst f.
    apply/negPn/negP => ND.
    contradict C. apply/negP.
    apply (@bungee_jumping o o1 o2 e1 e2 (val q)); try by [].
    + rewrite /= (head_eq _ (utarget e)) ?(last_eq _ (utarget e)) ?Oso ?Ota //; by destruct o.
    + by destruct o.
    + move=> [// | ? ?] _ P Po Pc Pnb.
      apply Omin; try by []. by destruct o.
    + move: Hq. destruct q as [[ | ? ?] ?]; last by [].
      contradict Oq. apply/negP. by rewrite /= eq_refl.
    + by destruct q.
    + apply/eqP. move: Oq. destruct q as [[ | ? ?] ?]; last by [].
      by rewrite /= !eq_refl.
    + destruct q as [[ | [eq bq] q] Q]; first by rewrite eq_refl in Oq.
      simpl in *.
      move=> ?. subst eq.
      destruct e1 as [e1 b1].
      destruct (eq_or_eq_negb b1 bq); subst bq.
      * rewrite simple_upath_cons in Q.
        destruct q.
        ** by rewrite Hq eq_refl in Oq.
        ** move: Q. rewrite in_cons negb_orb => /andP[/andP[/andP[_ /eqP-F1] /andP[/eqP-F2 _]] _].
           by rewrite Hq in F2.
      * contradict Ce1q. apply/negP/negPn. by rewrite /cusp /= negb_involutive.
    + destruct q as [[ | [eq bq] q] Q]; first by rewrite eq_refl in Oq.
      simpl in *.
      move=> ?. subst eq.
      destruct e2 as [e2 b2].
      destruct (eq_or_eq_negb b2 bq); subst bq.
      * contradict Ce1q. by apply/negP/negPn.
      * simpl in *. rewrite /uendpoint /= negb_involutive in Hq.
        apply uniq_utarget_simple_upath in O.
        move: O. by rewrite Oeq map_cat cat_uniq /= in_cons !negb_orb /uendpoint Hq eq_refl /= !andb_false_r.
    + by rewrite Oeq disjoint_sym -cat_rcons map_cat disjoint_cat disjoint_sym negb_andb ND.
Qed.

(* In a cusp_acyclic graph, take E a set containing or dominating all cusping edges.
   Then any maximal element of E has a splitting target. *)
Theorem ParametrizedYeo (E : {set edge G * bool}) :
  cusp_acyclic ->
  (forall e, cusping e -> e \in E \/ exists f, f \in E /\ e < f) ->
  forall e, e \in E -> (forall f, e < f -> f \notin E) -> splitting (utarget e).
Proof.
  move=> C Ehyp e Ein Emax.
  apply/negPn/negP => NS.
  destruct (no_splitting_is_no_max C NS) as [f [EF F]].
  move: Ehyp => /(_ _ F)[Fin | [g [Gin FG]]].
  - contradict Fin. apply/negP. exact (Emax _ EF).
  - contradict Gin. apply/negP. apply Emax. exact (lt_trans EF FG).
Qed.

Theorem LocalYeo : cusp_acyclic -> G -> exists v, splitting v.
Proof.
  (* If G has an edge, apply ParameterizedYeo; otherwise any vertex is splitting *)
  move=> C v.
  case: (set_0Vmem [set: edge G]) => [Noedge | [e _]].
  - exists v. apply/forallP; move=> [[ | e ?] ?].
    + by rewrite eq_refl.
    + enough (F : e.1 \in set0).
      { contradict F. by rewrite in_set. }
      by rewrite -Noedge in_set.
  - induction (forward e) as [f IH] using (well_founded_ind gt_wf).
    clear e.
    case/boolP: [exists g, f < g].
    + move=> /existsP[g gf]. exact (IH g gf).
    + move=> /existsPn-Fmax.
      exists (utarget f).
      apply (@ParametrizedYeo setT); try by [].
      * move=> e _. rewrite in_set. by left.
      * move=> e fe. contradict fe. apply/negP. apply Fmax.
Qed.

End GeneralizedYeo.

Section Yeo.

(** We consider an edge-colored multigraph G.
    There is no label on vertices (more accurately, they are all labeled by
    tt : unit) and the labels of edges belong to the type Colors,
    which has decidable equality (for we need to compare colors). *)
Variables (Colors : eqType) (G : graph unit Colors).

Theorem Yeo : cusp_acyclic (fun (e : edge G * bool) => elabel e.1) -> G ->
  exists (v : G), splitting (fun e => elabel e.1) v.
Proof. exact: @LocalYeo _ _ G Colors (fun e => elabel e.1). Qed.

End Yeo.

(* TODO everywhere - use case/boolP: b *)
(* TODO remove all useless by by in all files *)
(* TODO uwalk without s and t should simplify *)
(* TODO uwalk_cat; but with empty lists problem? *)
(* TODO mem_usource_utarget_simple_upath_internal to use more *)
(* TODO prevent simpl of upath_endpoint? *)
(* TODO general lemma for uwalk last? *)
