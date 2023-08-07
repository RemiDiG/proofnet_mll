(* Proof of Yeo's Theorem *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph (* structures *) (* bij *) (* setoid_bigop *).
From Yalla Require Import mll_prelim graph_more simple_upath.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(** Edge-colored multigraphs *)
Set Primitive Projections.
Record ecgraph (Lv Le : Type) (Lc : eqType) : Type :=
  Ecgraph {
    mgraph :> graph Lv Le;
    c : edge mgraph -> Lc; (* Decidable equality of colors *)
  }.
Unset Primitive Projections.
(* TODO Lc as Le? or even no Le? so all in graph, no ecgraph *)


Section Yeo.

Variables (Lv Le : Type) (Lc : eqType) (G : ecgraph Lv Le Lc).

(* A bridge is two edges of the same color *)
Notation bridge e1 e2 :=
  ((c e1) == (c e2)).

Lemma bridge_sym (e1 e2 : edge G) :
  bridge e2 e1 = bridge e1 e2.
Proof. by []. Qed.

Lemma never_two_bridges_without_three (e1 e2 e3 : edge G) :
  bridge e1 e2 -> bridge e2 e3 -> bridge e1 e3.
Proof. by move => /eqP-->. Qed.

Fixpoint nb_bridges (p : @upath _ _ G) : nat :=
  match p with
  | [::] | [:: _] => 0
  | e1 :: (e2 :: _) as p' => (bridge e1.1 e2.1) + nb_bridges p'
  end.

Lemma nb_bridges_cons e (p : upath) :
  nb_bridges (e :: p) = nb_bridges p + (match p with | [::] => 0 | e' :: _ => bridge e.1 e'.1 end).
Proof. destruct p; simpl; lia. Qed. (* TODO as definition instead? *)

Lemma nb_bridges_rcons e (p : upath) :
  nb_bridges (rcons p e) = nb_bridges p + (match p with | [::] => 0 | _ :: _ => bridge (last e p).1 e.1 end).
Proof.
  induction p as [ | e' p IH]; first by [].
  rewrite rcons_cons /= {}IH.
  destruct (rcons p e) as [ | e0 p0] eqn:F.
  { contradict F. apply rcons_nil. }
  destruct p as [ | e'' p].
  { inversion F. subst. simpl. lia. }
  rewrite rcons_cons in F. inversion F. subst e0 p0. clear F.
  rewrite (last_eq e e') //. lia.
Qed.

Lemma nb_bridges_upath_rev (p : @upath _ _ G) :
  nb_bridges (upath_rev p) = nb_bridges p.
Proof.
  induction p as [ | (e, b) p IH]; first by [].
  rewrite /= nb_bridges_rcons {}IH.
  destruct p as [ | (e', b') p]; first by []. simpl.
  destruct (rcons _ _) as [ | e0 p0] eqn:F.
  { contradict F. apply rcons_nil. }
  rewrite /= (bridge_sym e).
  enough (e' = (last e0 p0).1) as -> by lia.
  change (last e0 p0) with (last e0 (e0 :: p0)).
  by rewrite -F last_rcons.
Qed.

Lemma nb_bridges_cat (p q : upath) :
  nb_bridges (p ++ q) = nb_bridges p + nb_bridges q +
  (match p, q with | ep :: _, eq :: _ => bridge (last ep p).1 eq.1 | _, _ => 0 end).
Proof.
  revert p. induction q as [ | eq q IHq] => p.
  { rewrite /= cats0. destruct p; lia. }
  rewrite -cat_rcons (IHq _) {IHq} nb_bridges_cons nb_bridges_rcons.
  destruct (rcons p eq) eqn:F.
  { contradict F. apply rcons_nil. }
  rewrite -F last_rcons.
  destruct p; simpl; lia.
Qed.

(* TODO rename bridge_free? *)
Definition alternating (p : upath) : bool :=
  nb_bridges p == 0.

Lemma not_alternating_has_bridge (p : upath) :
  ~~ alternating p -> exists p1 p2 e1 e2,
  p = p1 ++ [:: e1; e2] ++ p2 /\ bridge e1.1 e2.1.
Proof.
  rewrite /alternating. induction p as [ | e p IH]; first by [].
  rewrite nb_bridges_cons.
  destruct (nb_bridges p == 0) eqn:Pb.
  - clear IH. revert Pb => /eqP-->.
    destruct p as [ | e' p]; first by [].
    move => B. exists [::], p, e, e'. split; [by [] | lia].
  - move => _.
    destruct IH as [p1 [p2 [e1 [e2 [Peq B]]]]]; first by [].
    subst p. by exists (e :: p1), p2, e1, e2.
Qed.

Lemma alternating_cat (p q : upath) :
  alternating (p ++ q) ->
  alternating p /\ alternating q.
Proof. rewrite /alternating nb_bridges_cat. lia. Qed.

(* A graph is correct if it all its simple alternating cycles have their first and last edges
   making a bridge; i.e. it has no simple bridge-free cycle, if we count as a possible bridge
   also the first and last edges of a cycle. *)
Definition correct : bool :=
  [forall p : Simple_upath G, (alternating p) ==>
  [forall e, (upath_source (usource e) p == upath_target (usource e) p) ==>
  bridge (head e (supval p)).1 (last e (supval p)).1]].
(* TODO def cyclic upath/simple_upath to simplify *)

(* useless
Lemma loop_incorrect (e : edge G) :
  source e == target e -> incorrect.
Proof.
  move => E.
  rewrite /incorrect. exists [:: forward e].
  by rewrite simple_upath_edge.
Qed.
*)

(* TODO general lemma for uwalk last ? *)

(* useless?
Lemma eq_edge_fst (e1 e2 : edge G * bool) :
  e1.1 = e2.1 ->
  utarget e1 = utarget e2 \/ usource e1 = utarget e2. (* TODO  I think I use it elsewhere *)
Proof. destruct e1 as [? []], e2 as [? []] => ->; auto. Qed.
(* TODO generalize if utarget = uendpoint b *)
*)

(* Take G an edge-colored graph and v one of its vertices. Let o be a cycle containing v such that
  v is not the pier of a bridge of this cycle, with a minimal number of bridges (with respect to
  all cycles containing v not as a pier).
  The cycle o must contain a bridge, of color d and pier k. There is no alternating path starting
  from an edge of k with a different color than d and ending on a vertex of o different from k, OR
  there is an alternating cycle in G. *)
Lemma colored_bungee_jumping (o o1 o2 : upath) e1 e2 r :
(* Let o be a simple cycle *)
  simple_upath o -> upath_source (usource e1) o = upath_target (usource e1) o ->
(* whose first and last edges are not a bridge, *)
  ~~ bridge (head e1 o).1 (last e1 o).1 ->
(* with o having a minimal number of bridges among such cycles, with the same source. *)
  (forall p, simple_upath p -> upath_source (usource e1) p = upath_source (usource e1) o ->
    upath_source (usource e1) p = upath_target (usource e1) p ->
    ~~ bridge (head e1 p).1 (last e1 p).1 -> nb_bridges p >= nb_bridges o) ->
(* Take e1 e2 a bridge of o *)
  o = o1 ++ [:: e1; e2] ++ o2 -> bridge e1.1 e2.1 ->
(* and r an alternating simple non-cyclic path starting from the pier of this bridge *)
  upath_source (usource e1) r = utarget e1 -> alternating r -> simple_upath r ->
  upath_source (usource e1) r <> upath_target (usource e1) r ->
(* with a different color than the bridge *)
  ~~ bridge (head e1 r).1 e1.1 ->
(* and ending in o. *)
  upath_target (usource e1) r \in [seq usource e | e <- o] ->
(* Then G is not correct. *)
  ~~ correct.
Proof.
  move => Os Oc Onb Omin Oeq B12 Rso Ra Rs Rnc Rc Rta.
(* Up to taking a prefix of r, only the endpoints of r are in both o and r *)
  wlog Rfst : r Rso Ra Rs Rnc Rc Rta / (forall u, u \in [seq utarget e | e <- r] ->
    u \in [seq usource e | e <- o] -> u = upath_target (usource e1) r).
  { clear Oc Os Onb Omin Oeq o1 o2 B12 e2 => Wlog.
    assert (Rta' : (utarget (last e1 r) \in [seq usource e | e <- o]) &&
      (upath_source (usource e1) r != utarget (last e1 r))).
    { replace (utarget (last e1 r)) with (upath_target (usource e1) r).
      2:{ rewrite /= (last_eq _ (utarget e1)) ?(last_map (fun _ => _)) //. by destruct r. }
      rewrite Rta andb_true_l. by apply /eqP. }
    assert (Rtain : last e1 r \in r).
    { apply mem3_last. by destruct r. }
    destruct (@in_elt_sub_fst _ r (fun e => (utarget e \in [seq usource e | e <- o]) &&
      (upath_source (usource e1) r != utarget e)) _ Rta' Rtain) as [[n N] [e [Req [Ein Efst]]]].
    revert Ein Req => /andP[Ein /eqP-Rnc'] /= Req {Rta' Rta Rtain Rnc}.
    assert (Rs' : simple_upath (rcons (take n r) e)).
    { clear - Rs Req.
      rewrite {}Req -cat_rcons in Rs.
      apply simple_upath_subK in Rs. revert Rs => /andP[/orP[/eqP-F | //] _].
      contradict F. apply rcons_nil. }
    apply (Wlog (rcons (take n r) e)); clear Wlog; try by [].
    - revert Rso. by rewrite {1}Req /= map_cat head_cat map_rcons head_rcons.
    - clear -Ra Req. rewrite {}Req -cat_rcons in Ra.
      by destruct (alternating_cat Ra) as [-> _].
    - clear - Rnc' Req.
      revert Rnc'. by rewrite {1}Req /= -cat_rcons map_cat !map_rcons !head_cat !head_rcons last_rcons.
    - rewrite head_rcons head_take. destruct n, r; try by [].
      by rewrite Req in Rc.
    - by rewrite /= map_rcons last_rcons.
    - clear - Efst Req Rs' => u.
      rewrite /= map_rcons mem_rcons in_cons last_rcons => /orP[/eqP--> // | /mapP[a Ain ?]] UinO.
      subst u. contradict UinO. apply /negP.
      revert Efst => /(_ a Ain) /nandP[-> // | /negPn/eqP-Ta].
      exfalso.
      assert (a = e).
      { replace e with (last a (rcons (take n r) e)) by by rewrite last_rcons.
        apply back_source_is_last; try by [].
        - by rewrite -Ta {1}Req /= map_cat head_cat map_rcons head_rcons.
        - by rewrite mem_rcons in_cons Ain orb_true_r. }
      subst a.
      assert (U := uniq_fst_simple_upath Rs').
      contradict U. apply /negP.
      by rewrite map_rcons rcons_uniq map_f. }
(* By symmetry, up to reversing o, upath_target (usource e1) r is in o2 the second half of the cycle,
   and if it is the source of o then its last edge does not make a bridge with the first edge of o. *)
(* This stronger hypothesis replaces the weaker Rta. *)
  wlog {Rta} Rta : o o1 o2 e1 e2 r Os Oc Onb Omin Oeq B12 Rso Ra Rs Rnc Rc Rfst /
    (upath_target (usource e1) r \in [seq usource e | e <- o2]) \/
    (upath_target (usource e1) r = upath_source (usource e1) o /\ ~~ bridge (head e1 o).1 (last e1 r).1).
  { move => Wlog.
(* Some equalities on endpoints of the paths *)
    assert (Ow := @uwalk_of_simple_upath _ _ _ _ Os (usource e1)). rewrite Oeq in Ow.
    assert (O1e1 := uwalk_sub_middle Ow).
    apply uwalk_subK in Ow. destruct Ow as [O1w O2w]. rewrite {}O1e1 in O1w.
    apply uwalk_subK in O2w. destruct O2w as [E1E2 _].
    revert O1w E1E2. rewrite /= !map_cat !head_cat !eq_refl andb_true_r /= => O1w /eqP-E1E2.
    assert (Omem : [seq utarget e | e <- o] =i [seq usource e | e <- o]).
    { apply eq_mem_sym, (@mem_usource_utarget_cycle _ _ _ (upath_source (usource e1) o)).
      rewrite {2}Oc. by apply uwalk_of_simple_upath. }
(* If the target of r is the source of o, and does not make a bridge with it, or
   if the target of r is in o2 and not the source of o, then apply Wlog. *)
    destruct ((upath_target (usource e1) r == upath_source (usource e1) o) &&
      (~~bridge (head e1 o).1 (last e1 r).1) ||
      (last (usource e1) [seq utarget e | e <- r] \in [seq usource e | e <- o2])) eqn:Rta'.
    { apply (Wlog o o1 o2 e1 e2 r); try by [].
      revert Rta' => /orP[/andP[/eqP-? ?] | ?]; [by right | by left]. }
    revert Rta' => /norP[Rta1 Rta2]. rewrite negb_andb negb_involutive in Rta1.
(* The target of r cannot be the source of e2, which is the the source of the non-cyclic r. *)
    destruct (eq_comparable (last (usource e1) [seq utarget e | e <- r]) (usource e2)) as [Rta3 | Rta3].
    { contradict Rnc. by rewrite Rso -E1E2 -Rta3. }
(* Thus, the target of r is in (rcons o1 e1). *)
    revert Rta. rewrite Oeq -cat_rcons !map_cat !mem_cat /= !in_cons.
    revert Rta2 Rta3 => /negPf--> /eqP/negPf-->.
    rewrite !orb_false_r => Rta.
(* In this case, we apply Wlog to the cycle o reversed. *)
    apply (Wlog (upath_rev o) (upath_rev o2) (upath_rev o1) (reversed e2) (reversed e1) r);
      clear Wlog; try by [].
    - by rewrite simple_upath_rev.
    - rewrite /= !negb_involutive map_usource_upath_rev map_utarget_upath_rev head_rev last_rev
        (head_eq _ (usource e1)) ?(last_eq _ (usource e1)) 1?eq_sym ?Oc //; by destruct o.
    - rewrite head_upath_rev last_upath_rev /= negb_involutive (head_eq _ e1) ?(last_eq _ e1) 1?bridge_sym //;
      by destruct o.
    - move => p Ps.
      rewrite upath_endpoint_rev (endpoint_simple_upath _ Os _ (usource e1)) -Oc nb_bridges_upath_rev
        !(endpoint_simple_upath _ Ps (usource (reversed e2)) (usource e1))
        (head_eq _ e1) 1?(last_eq _ e1); try by destruct p.
      by apply Omin.
    - by rewrite Oeq !upath_rev_cat /= -catA -cat1s -catA !cat1s.
    - by rewrite bridge_sym.
    - revert Rso. rewrite /= E1E2 negb_involutive (head_eq _ (usource e1)) //; by destruct r.
    - revert Rnc. rewrite /= negb_involutive (head_eq _ (usource e1)) ?(last_eq _ (usource e1));
        by destruct r.
    - revert Rc. rewrite (head_eq _ e1) /=; last by destruct r.
      by revert B12 => /eqP-->.
    - move => u.
      rewrite map_usource_upath_rev mem_rev Omem (endpoint_simple_upath _ Rs _ (usource e1)).
      apply Rfst.
    - revert Rta.
      rewrite upath_endpoint_rev (endpoint_simple_upath _ Os _ (usource e1)) -Oc
        !map_usource_upath_rev !negb_involutive mem_rev /= map_rcons mem_rcons
        (mem_usource_utarget_uwalk O1w) in_cons (last_eq _ (usource e1)); last by destruct r.
      replace (head (usource e1) [seq usource e | e <- o1]) with
        (head (usource e1) [seq usource e | e <- o]) by by rewrite Oeq map_cat head_cat.
      move => /orP[/eqP-Rta | ->]; [right | by left]. split; try by [].
      rewrite bridge_sym head_upath_rev /= !(last_eq _ e1); [ | by destruct o | by destruct r].
      apply /negP => B.
      contradict Onb. apply /negP/negPn.
      rewrite /= Rta eq_refl /= in Rta1.
      exact (never_two_bridges_without_three Rta1 B). }
(* As r ends in o2, we separate o2 in o21 before the target of r and o22 after,
   and r ends on the source of o (without a bridge) if o22 is empty. *)
  assert (exists o21 o22, o2 = o21 ++ o22 /\
    upath_source (upath_target (utarget e2) o21) o22 = upath_target (usource e1) r /\
    if o22 == [::] then ~~ bridge (head e1 o).1 (last e1 r).1 else true)
    as [o21 [o22 [O2eq [O2so Bnro]]]].
  { destruct Rta as [Rta | [RtOs ->]].
    - revert Rta => /mapP[e Eo2 ->].
      rewrite in_elt_sub in Eo2. revert Eo2 => /existsP[[n N] /= /eqP-Eo2].
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
(* TODO some may be useless... *)
  assert (Ow := @uwalk_of_simple_upath _ _ _ _ Os (usource e1)). rewrite Oeq in Ow.
  assert (O1e1 := uwalk_sub_middle Ow). rewrite /= map_cat head_cat /= in O1e1.
  apply uwalk_subK in Ow. destruct Ow as [_ O2w].
  assert (O2e2 := uwalk_sub_middle O2w). rewrite /= !map_cat head_cat last_cat /= map_cat last_cat in O2e2.
  apply uwalk_subK in O2w. destruct O2w as [E1E2w O2w].
  revert E1E2w. rewrite /= !eq_refl andb_true_r /= => /eqP-E1E2.
  apply uwalk_sub_middle in O2w. rewrite /= !map_cat head_cat !last_cat /= map_cat last_cat in O2w.
  assert (Omem : [seq utarget e | e <- o] =i [seq usource e | e <- o]).
  { apply eq_mem_sym, (@mem_usource_utarget_cycle _ _ _ (upath_source (usource e1) o)).
    rewrite {2}Oc. by apply uwalk_of_simple_upath. }
(* The path o22 is non-cyclic, except if it is empty. *)
  assert (O22nc : o22 <> [::] -> upath_source (usource e1) o22 <> upath_target (usource e1) o22).
  { clear - Oeq Os. move => O22nil F.
    rewrite {}Oeq -cat_rcons in Os.
    apply simple_upath_subK in Os. revert Os => /andP[_ /orP[// | Os]].
    rewrite -cat_cons lastI cat_rcons in Os.
    apply simple_upath_subK in Os. revert Os => /andP[_ /orP[// | Os]].
    revert Os. rewrite simple_upath_cons. move => /orP[/eqP-? // | /andP[/andP[/andP[/andP[_ F'] _] _] _]].
    contradict F'. apply /negP/negPn/eqP.
    revert F. rewrite /= (head_eq _ (usource e1)) ?(last_eq _ (usource e1)) //; by destruct o22. }
(* No edge of r belongs to o. *)
  assert (Dro : [disjoint [seq e.1 | e <- r] & [seq e.1 | e <- o]]). (* TODO lemma? *)
  { clear Oc Onb Omin Ra Rnc Bnro.
    apply /disjointP => e Er Eo.
    destruct (disjoint_or_edge Omem Rs Rfst Er Eo) as [b ?]. subst r.
    apply in_map_fst in Eo. destruct Eo as [b' Eo].
    assert (E22 : utarget (e, b') = utarget e1 \/ usource (e, b') = utarget e1). (* TODO lemma for this, I think I use it elsewhere *)
    { rewrite -Rso. clear. by destruct b, b'; auto. }
    clear Rso. destruct E22 as [E22 | E22].
    - assert (U := uniq_utarget_simple_upath Os).
      contradict U. apply /negP.
      apply (@not_uniq_map _ _ _ _ (e, b') e1); try by [].
      + by rewrite Oeq !mem_cat !in_cons eq_refl !orb_true_r.
      + move => ?. subst e1.
        contradict Rc. by apply /negP/negPn.
    - rewrite -E1E2 in E22.
      assert (U := uniq_usource_simple_upath Os).
      contradict U. apply /negP.
      apply (@not_uniq_map _ _ _ _ (e, b') e2); try by [].
      + by rewrite Oeq !mem_cat !in_cons eq_refl !orb_true_r.
      + move => ?. subst e2.
        contradict Rc. apply /negP/negPn.
        by rewrite /= bridge_sym. }
(* This cycle, p, has the needed properties to use the minimality of o. *)
  set p := o1 ++ e1 :: r ++ o22.
  assert (Ps : simple_upath p).
  { rewrite /p.
    enough (simple_upath (e1 :: r ++ o22)).
    { destruct (eq_comparable o1 [::]) as [? | O1nil]; first by subst o1.
      apply (@simple_upath_cat _ _ _ e1); try by [].
      - rewrite Oeq in Os. clear - Os O1nil.
        apply simple_upath_subK in Os.
        revert Os => /andP[Os _]. by destruct o1.
      - rewrite /= -O1e1.
        apply last_eq. by destruct o1.
      - apply uniq_usource_simple_upath in Os.
        revert Os.
        rewrite Oeq !map_cat !cat_uniq /= !has_cat !negb_orb /= -!disjoint_has !andb_true_r.
        move => /andP[_ /andP[/andP[E1O1 /andP[E2O1 /andP[_ Do22o1]]] _]].
        rewrite disjoint_sym disjoint_cons map_cat disjoint_cat {}E1O1 {}Do22o1 /= andb_true_r.
        apply /disjointP => v Vr Vo1.
        assert (Vr': v \in (upath_target (usource e1) r) :: [seq usource e | e <- r])
          by by rewrite in_cons Vr orb_true_r.
        rewrite (@mem_usource_utarget_uwalk _ _ _ (upath_source (usource e1) r)) in Vr';
          last by apply (@uwalk_of_simple_upath _ _ _ _ Rs (usource e1)).
        revert Vr'. rewrite /= in_cons => /orP[/eqP-? | Vr'].
        + subst v.
          by rewrite E1E2 -Rso Vo1 in E2O1.
        + assert (v = upath_target (usource e1) r).
          { apply Rfst; try by [].
            by rewrite Oeq map_cat mem_cat Vo1. }
          subst v. clear - Vr Rs Rnc.
          contradict Rnc.
          by apply simple_upath_rho.
      - assert (upath_target (usource e1) (e1 :: r ++ o22) = upath_target (usource e1) o) as ->.
        { destruct o22.
          - revert O2so. rewrite cats0 /= Oeq !map_cat !last_cat /= => ->.
            apply last_eq. by destruct r.
          - by rewrite Oeq /= !map_cat !last_cat /= !map_cat !last_cat. }
        rewrite -Oc Oeq /= map_cat head_cat /= -(upath_rev_inv o1) map_usource_upath_rev head_rev
          (map_utarget_upath_rev (upath_rev _)) mem_rev.
        apply /negP => F.
        assert (E : upath_source (usource e1) (upath_rev o1) = upath_target (usource e1) (upath_rev o1)).
        { destruct o1; first by [].
          apply simple_upath_rho; last by [].
          rewrite simple_upath_rev.
          clear - Os Oeq. rewrite {}Oeq in Os.
          apply simple_upath_subK in Os.
          by revert Os => /andP[/orP[// | ->] _]. }
        revert E. rewrite !upath_endpoint_rev.
        clear - Os Oeq O1nil.
        rewrite {}Oeq -cat_rcons in Os. apply simple_upath_subK in Os.
        revert Os => /andP[/orP[/eqP-Os | Os] _].
        { contradict Os. by apply rcons_nil. }
        revert Os. rewrite simple_upath_rcons => /orP[/eqP-? // | /andP[/andP[/andP[/andP[_ /eqP-Os] _] _] _]].
        apply nesym. by destruct o1.
      - rewrite Oeq -cat_rcons /= in Os.
        apply simple_upath_subK in Os. revert Os => /andP[/orP[/eqP-F | Os] _].
        { contradict F. by apply rcons_nil. }
        rewrite simple_upath_rcons in Os. revert Os => /orP[/eqP-? // | /andP[/andP[/andP[_ Os] _] _]].
        move => /= E11. contradict Os. apply /negP/negPn.
        rewrite -E11. by apply map_f, mem3_last. }
    rewrite simple_upath_cons. apply /orP; right. repeat (apply /andP; split).
    - destruct (eq_comparable o22 [::]) as [? | O2nil]; first by (subst o22; rewrite cats0).
      apply (@simple_upath_cat _ _ _ e2); try by [].
      + rewrite Oeq !catA in Os.
        apply simple_upath_subK in Os. by revert Os => /andP[_ /orP[/eqP-? // | ->]].
      + revert O2so. rewrite /= !(head_eq _ (usource e1)) ?(last_eq _ (usource e1)); by destruct o22, r.
      + apply /disjointP => [v Vr Vo22].
        destruct (eq_comparable v (upath_source (usource e1) r)) as [? | Vsr]; [subst v | ].
        * rewrite Rso -E1E2 in Vo22.
          apply uniq_usource_simple_upath in Os.
          contradict Os. apply /negP.
          by rewrite Oeq !map_cat !cat_uniq /= !has_cat (has_sym [:: usource e1; usource e2]
            [seq usource _e | _e <- o22]) /= Vo22 !orb_true_r !andb_false_r.
        * assert (Vint : (v \in [seq usource e | e <- r]) && (v != upath_source v r)).
          { revert Vsr => /eqP. rewrite Vr /= (head_eq _ (usource e1)) //. by destruct r. }
          rewrite (mem_usource_utarget_simple_upath_internal Rs) in Vint.
          revert Vint => /andP[Vrt /eqP-Vrta].
          contradict Vrta.
          rewrite (@endpoint_simple_upath _ _ _ _ _ Rs _ (usource e1)). apply Rfst; first by [].
          by rewrite Oeq !map_cat !mem_cat Vo22 !orb_true_r.
      + replace (upath_target (usource e2) o22) with (upath_target (usource e1) o).
        2:{ rewrite Oeq /= map_cat /= map_cat last_cat /= last_cat.
            apply last_eq. by destruct o22. }
        rewrite -Oc.
        apply /negP => F.
        assert (F' : upath_source (usource e1) o = upath_target (usource e1) r).
        { apply Rfst; first by [].
          rewrite /= mem3_head //; by destruct o. }
        rewrite -O2so Oc in F'.
        assert (F'' : upath_source (usource e1) o22 = upath_target (usource e1) o22).
        { revert F'. rewrite Oeq /= map_cat /= map_cat last_cat /= last_cat. by destruct o22. }
        contradict F''. by apply O22nc. (* TODO only use of O22nc? *)
      + move => F.
        revert Dro => /disjointP/(_ (last e2 r).1)-Dro. apply Dro.
        * apply map_f, mem3_last. by destruct r.
        * rewrite F. apply map_f.
          by rewrite Oeq !mem_cat mem3_head ?orb_true_r.
    - apply /eqP.
      replace (upath_source (utarget e1) (r ++ o22)) with (upath_source (usource e1) r)
        by by destruct r.
      replace (upath_target (utarget e1) (r ++ o22)) with
        (upath_target (upath_target (utarget e1) r) o22) by by  rewrite /= map_cat last_cat.
      destruct o22 as [ | o22 e22 _] using last_ind.
      + simpl in Rnc. rewrite /= (last_eq _ (usource e1)) //; by destruct r.
      + rewrite Rso /= map_rcons last_rcons => F.
        assert (U := uniq_utarget_simple_upath Os).
        contradict U. apply /negP.
        by rewrite Oeq !map_cat !map_rcons !cat_uniq !rcons_uniq !has_cat !has_rcons /=
          !in_cons F eq_refl orb_true_r !andb_false_r.
    - rewrite map_cat mem_cat negb_orb. apply /andP; split.
      + apply /negP => E1r.
        revert Dro => /disjointP/(_ e1.1)-Dro. apply Dro; first by [].
        by rewrite Oeq !map_cat !mem_cat /= in_cons eq_refl orb_true_r.
      + apply /negP => F.
        assert (U := uniq_fst_simple_upath Os). contradict U. apply /negP.
        by rewrite Oeq !map_cat !cat_uniq !has_cat /=
          (has_sym [:: e1.1; e2.1] [seq e.1 | e <- o22]) /= F !orb_true_r !andb_false_r.
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
        revert E1r' => /andP[E1r /eqP-E1rt].
        contradict E1rt.
        apply (Rfst _ E1r).
        by rewrite Oeq !map_cat !mem_cat in_cons eq_refl orb_true_r.
      + apply /negP => F.
        assert (U := uniq_usource_simple_upath Os). contradict U. apply /negP.
        by rewrite Oeq !map_cat !cat_uniq !has_cat (has_sym [:: usource e1; usource e2]
          [seq usource e | e <- o22]) /= F !orb_true_r !andb_false_r. }
  assert (Pso : upath_source (usource e1) p = upath_source (usource e1) o).
  { rewrite /p Oeq. by destruct o1. }
  assert (Pc : upath_source (usource e1) p = upath_target (usource e1) p).
  { revert O2so.
    rewrite Pso Oc /p Oeq /= !map_cat /= !map_cat !last_cat /= !last_cat.
    destruct o22; last by [].
    rewrite /= (last_eq (utarget e1) (usource e1)) //; by destruct r. }
  assert (Pnb : ~~ bridge (head e1 p).1 (last e1 p).1).
  { revert Bnro Onb O2so. rewrite /p Oeq !head_cat !last_cat /= last_cat.
    by destruct o22. }
(* By minimality of o, the last edge of r and the first of o22 makes a bridge,
   o1 is bridge-free and we know some bridge-free points *)
  specialize (Omin _ Ps Pso Pc Pnb).
  rewrite Oeq /c !nb_bridges_cat /= B12 /= nb_bridges_cat {p Pso Pc Ps Pnb} in Omin.
  revert Ra. rewrite /alternating => /eqP-Ra. rewrite Ra in Omin.
  assert (Omin' : 1 + nb_bridges o21 +
    match o21 with | [::] => 0 | ep :: _ =>
      match o22 with | [::] => 0 | eq :: _ => bridge (last ep o21).1 eq.1 end end +
    match o21 ++ o22 with | [::] => 0 | eq :: _ => bridge e2.1 eq.1 end <=
    bridge e1.1 (head e1 r).1 +
    match o22 with | [::] => 0 | eq :: _ => bridge (last e1 r).1 eq.1 end).
  { revert Omin. destruct r; first by []. clear. simpl. lia. }
  clear Omin.
  replace (bridge e1.1 (head e1 r).1) with false in Omin'.
  2:{ clear - Rc. symmetry. rewrite bridge_sym. by apply negb_true_iff. }
  assert (nb_bridges o21 = 0 /\
    match o21 with | [::] => 0 | ep :: _ =>
      match o22 with | [::] => 0 | eq :: _ => bridge (last ep o21).1 eq.1 end end = 0 /\
    match o21 ++ o22 with | [::] => 0 | eq :: _ => bridge e2.1 eq.1 end = 0 /\
    match o22 with | [::] => 0 | eq :: _ => bridge (last e1 r).1 eq.1 end = 1)
    as [O21a [Bno21o22 [Bne2o2122 Be1o22]]].
  { revert Omin'. destruct r; first by []. clear. simpl. destruct o22; lia. }
  clear Omin'.
(* TODO these bridges in bool? *)
(* Thanks to the bridge-freeness hypotheses given by the minimality of o,
   r ++ upath_rev (e2 :: o21) contradicts correctness. *)
  assert (S : simple_upath (r ++ upath_rev (e2 :: o21))).
  { apply (@simple_upath_cat _ _ _ e1); try by [].
    - rewrite simple_upath_rev.
      rewrite Oeq -cat_rcons -cat_cons in Os.
      apply simple_upath_subK in Os. revert Os => /andP[_ /orP[// | Os]].
      apply simple_upath_subK in Os. by revert Os => /andP[/orP[// | ->] _].
    - rewrite -O2so upath_endpoint_rev. by destruct o21, o22.
    - rewrite map_usource_upath_rev disjoint_sym disjoint_rev.
      apply /disjointP => u Uo Ur.
      assert (Uo' : u \in [seq usource e | e <- o])
        by by rewrite -Omem Oeq !cat_cons /= -cat_rcons -cat_cons !map_cat !mem_cat Uo orb_true_r.
      assert (Ur' : u \in upath_target (usource e1) r :: [seq usource _e | _e <- r])
        by by rewrite in_cons Ur orb_true_r.
      rewrite (mem_usource_utarget_uwalk (uwalk_of_simple_upath Rs _)) in_cons in Ur'.
      revert Ur' => /orP[/eqP-? | Ur'].
      + subst u.
        rewrite Rso in Uo.
        rewrite Oeq !cat_cons /= -!cat_cons in Os.
        apply simple_upath_subK in Os. revert Os => /andP[_ /orP[// | Os]].
        apply simple_upath_subK in Os. revert Os => /andP[/orP[// | Os] _].
        revert Os. rewrite simple_upath_cons.
        move => /orP[// | /andP[/andP[/andP[/andP[E2O2s /eqP-E2O2nc] _] /eqP-E1ta] _]].
        contradict E2O2nc.
        rewrite -(upath_rev_inv (e2 :: o21)) upath_endpoint_rev [in RHS]upath_endpoint_rev.
        symmetry. apply simple_upath_rho.
        * by rewrite simple_upath_rev.
        * by rewrite upath_endpoint_rev map_usource_upath_rev mem_rev /= E1E2.
      + specialize (Rfst _ Ur' Uo'). subst u.
        contradict Rnc.
        by apply simple_upath_rho.
    - rewrite upath_endpoint_rev /=.
      apply /negP => F.
      contradict Rnc.
      rewrite -(upath_rev_inv r) upath_endpoint_rev [in RHS]upath_endpoint_rev.
      symmetry. apply simple_upath_rho.
      + by rewrite simple_upath_rev Rs.
      + by rewrite upath_endpoint_rev map_usource_upath_rev mem_rev Rso -E1E2 F.
    - move => F.
        revert Dro => /disjointP/(_ (last e1 r).1)-Dro. apply Dro.
        + apply map_f, mem3_last. by destruct r.
        + by rewrite F Oeq head_rcons head_upath_rev /= negb_involutive -cat_rcons -cat_cons !map_cat
            !mem_cat (@map_f _ _ _ (_ :: o21)) ?orb_true_r // mem_last. }
  rewrite /correct. apply /forallPn.
  exists {| supval := _ ; supvalK := S |}.
  rewrite negb_imply. apply /andP; split.
  - rewrite /alternating nb_bridges_cat nb_bridges_upath_rev nb_bridges_cons Ra O21a.
    replace (match o21 with | [::] => 0 | e :: _ => bridge e2.1 e.1 end) with 0 by by destruct o21.
    assert (Hr : match r with | [::] => 0 | ep :: _ =>
      match upath_rev (e2 :: o21) with
      | [::] => 0 | eq :: _ => bridge (last ep r).1 eq.1 end end =
      bridge (last e1 r).1 (head e2 (upath_rev (e2 :: o21))).1).
    { destruct r, (upath_rev (e2 :: o21)) eqn:F; try by [].
      contradict F. apply rcons_nil. }
    rewrite {}Hr head_upath_rev /=.
    enough (E : ~~ bridge (last e1 r).1 (last e2 o21).1) by (clear - E; lia).
    apply /negP => B.
    destruct o22 as [ | e22 o22]; first by [].
    clear - Bno21o22 Bne2o2122 Be1o22 B.
    assert (BF : bridge (last e2 o21).1 e22.1).
    { rewrite bridge_sym in B. apply (never_two_bridges_without_three B). lia. }
    clear B Be1o22.
    destruct o21 as [ | e21 o21]; simpl in *; lia.
  - apply /forallPn. exists e1. rewrite negb_imply.
    rewrite -Rso in E1E2. revert E1E2.
    rewrite /= !map_cat !map_rcons !head_cat map_utarget_upath_rev !last_cat !last_rcons /= => ->.
    revert B12 => /eqP-<-.
    destruct r; first by [].
    revert Rc => /= ->. by rewrite eq_refl.
Qed.
(* TODO remove all useless by by in all files *)
(* TODO uwalk sans s et t ? *)
(* TODO uwalk_cat; but with empty lists problem? *)
(* TODO lemma simple upath cat avec cas liste(s) vide(s) ? *)
(* TODO mem_usource_utarget_simple_upath_internal to use more *)
(* TODO faire un type simple upath, avec ses target et source sans valeur de base ? *)
(* TODO se faire un type liste non vide? ou toujours écrire e :: p pour les chemins *)
(* TODO prevent simpl of upath_endpoint? *)

(* Given vertices u and v and colors c and d, (u, c) < (v, d) if
   there is a simple alternating non-cyclic path p such that:
   - p starts from u with an edge NOT colored by c
   - p ends in v with an edge colored d
   - any simple alternating non-cyclic path q, starting from v by an edge NOT colored by d,
     contains no vertex of p\{u}. *)
(* We use the finite type of edges instead of the (possibly infinite) type of colors.
   It would be better to use the finite type of colors used by the graph, but this is more complex
   to implement in Coq. *)
Definition pre_ordering (U V : G * edge G) (p : Simple_upath G) : bool :=
  let (u, ec) := U in let (v, ed) := V in
  (alternating p) && (upath_source u p != upath_target u p) &&
  (upath_source u p == u) && (~~ bridge (head (forward ec) (supval p)).1 ec) &&
  (upath_target u p == v) && (bridge (last (forward ec) (supval p)).1 ed) &&
  [forall q : Simple_upath G, (alternating q) ==> (upath_source u q != upath_target u q) ==>
  (upath_source u q == v) ==> (~~ bridge (head (forward ec) (supval q)).1 ed) ==>
  [disjoint [seq utarget e | e <- supval q] & [seq usource e | e <- supval p]]].
(* TODO replace the ec by c : { c e | e : edge G }, sig type? / image c (edge G) ?
or keep it as if to have an edge in context? *)

Definition ordering U V : bool :=
  [exists p, pre_ordering U V p].

Lemma ordering_irrefl : irreflexive ordering.
Proof.
  move => [u ec]. apply /existsPn => P.
  rewrite /pre_ordering. apply /negP => /andP[/andP[/andP[/andP[/andP[/andP[_ /eqP-Pnc] /eqP-PsoU]
    _] /eqP-PtaU] _] _].
  contradict Pnc. by rewrite PsoU PtaU.
Qed.

Lemma simple_disjoints_are_cat_simple (v : G) (p q : upath) :
  simple_upath p -> upath_source v p <> upath_target v p ->
  simple_upath q -> upath_source v q <> upath_target v q ->
  upath_target v p = upath_source v q ->
  [disjoint [seq utarget _e | _e <- q] & [seq usource _e | _e <- p]] ->
  simple_upath (p ++ q).
Proof.
  move => simple_p p_no_cycle simple_q q_no_cycle target_p_eq_source_q
    disjoint_targets_q_sources_p.
  assert (e : edge G * bool) by by destruct p.
  apply (@simple_upath_cat _ _ _ e) => //.
  - by rewrite !(endpoint_simple_upath _ _ _ v).
  - apply /disjointP => u u_in_sources_p u_in_sources_q.
    enough (u_in_targets_q : u \in [seq utarget e | e <- q]).
    { revert disjoint_targets_q_sources_p
        => /disjointP/(_ u)-disjoint_targets_q_sources_p.
      by apply disjoint_targets_q_sources_p. }
    enough (E : (u \in [seq utarget e | e <- q]) && (u != upath_target u q))
      by by revert E => /andP[-> _].
    rewrite -(mem_usource_utarget_simple_upath_internal simple_q)
      u_in_sources_q (endpoint_simple_upath _ _ _ v) //
      -target_p_eq_source_q.
    apply /eqP => ?. subst u.
    contradict p_no_cycle.
    by apply (simple_upath_rho simple_p).
  - enough (E : ~~((upath_target (usource e) q \in [seq utarget e | e <- p]) &&
      (upath_target (usource e) q !=
      upath_target (upath_target (usource e) q) p))).
    { revert E => /nandP[-> // | /negPn/eqP-E].
      contradict q_no_cycle.
      by rewrite [in RHS](endpoint_simple_upath _ _ _ (usource e)) // E
        -target_p_eq_source_q [in RHS](endpoint_simple_upath _ _ _ v). }
    rewrite -mem_usource_utarget_simple_upath_internal //.
    apply /nandP. left. apply /negP => F.
    revert disjoint_targets_q_sources_p =>
      /disjointP/(_ (upath_target (usource e) q))-disjoint_targets_q_sources_p.
    apply disjoint_targets_q_sources_p; last by [].
    apply mem3_last. by destruct q.
  - destruct p as [ | p [ep bp] _] using last_ind; first by [].
    destruct q as [ | [eq bq] q]; first by [].
    rewrite last_rcons /=.
    move => ?. subst eq.
    revert disjoint_targets_q_sources_p => /disjointP/(_ (usource (ep, bp)))-H.
    apply H; clear H.
    + case: (boolP (bp == bq)).
      * move => /eqP-?. subst bq.
        rewrite /= map_rcons last_rcons in target_p_eq_source_q.
        by rewrite -target_p_eq_source_q /= in_cons eq_refl.
      * move => bp_neq_bq.
        assert (bq = ~~ bp) by by clear - bp_neq_bq; destruct bq, bp.
        subst bq. clear bp_neq_bq.
        by rewrite /= in_cons eq_refl.
    + by rewrite map_rcons mem_rcons in_cons eq_refl.
Qed.

Lemma ordering_trans : transitive ordering.
Proof.
  move => [v eb] [u ea] [w ec].
  rewrite /ordering /pre_ordering.
  move => /existsP[[p P] /= /andP[/andP[/andP[/andP[/andP[/andP[Pa Pnc] PsoU]
    Pea] PtaV] Peb] Pdis]].
  move => /existsP[[q Q] /= /andP[/andP[/andP[/andP[/andP[/andP[Qa Qnc] QsoV]
    Qeb] QtaW] Qec] Qdis]].
  assert (Dpq : [disjoint [seq utarget e | e <- q] & [seq usource e | e <- p]]).
  { revert Pdis => /forallP/(_ {| supval := _ ; supvalK := Q |}) /=.
    rewrite !(head_eq u v) ?(last_eq u v) ?(head_eq (forward ea) (forward eb)); try by destruct q.
    by move => /implyP/(_ Qa)/implyP/(_ Qnc)/implyP/(_ QsoV)/implyP/(_ Qeb) ->. }
  assert (PQ : simple_upath (p ++ q)).
  { apply (@simple_disjoints_are_cat_simple u); try by [].
    - by revert Pnc => /= /eqP.
    - revert Qnc => /= /eqP. by destruct q.
    - revert PtaV QsoV => /= /eqP--> /eqP-?. by destruct q. }
  apply /existsP. exists {| supval := _ ; supvalK := PQ |}. simpl. repeat (apply /andP; split).
  - clear - Pa Qa Peb Qeb P Q.
    rewrite /alternating nb_bridges_cat.
    replace (match p with | [::] => 0 | ep :: _ => match q with | [::] => 0 | eq :: _ =>
      bridge (last ep p).1 eq.1 end end) with
      (nat_of_bool (bridge (last (forward ea) p).1 (head (forward eb) q).1))
      by by destruct p, q.
    revert Pa Qa Peb => /eqP--> /eqP--> /eqP-->.
    rewrite bridge_sym. lia.
  - rewrite !map_cat head_cat last_cat.
    apply /eqP => F.
    revert Dpq => /disjointP/(_ (head (head u [seq usource e | e <- q]) [seq usource e | e <- p]))-Dpq. apply Dpq.
    * rewrite F. apply mem3_last. by destruct q.
    * apply mem3_head. by destruct p.
  - rewrite map_cat head_cat (head_eq _ u) //. by destruct p.
  - rewrite head_cat (head_eq _ (forward ea)) //. by destruct p.
  - rewrite map_cat last_cat (last_eq _ v) //. by destruct q.
  - rewrite last_cat (last_eq _ (forward eb)) //. by destruct q.
  - apply /forallP. move => [r R] /=.
    apply/implyP => Ra. apply/implyP => Rnc. apply/implyP => RsoW. apply/implyP => Rec.
    assert (Drq : [disjoint [seq utarget e | e <- r] & [seq usource e | e <- q]]).
    { revert Qdis => /forallP/(_ {| supval := _ ; supvalK := R |}) /=.
      rewrite !(head_eq v u) ?(last_eq v u) ?(head_eq (forward eb) (forward ea)); try by destruct r.
      by move => /implyP/(_ Ra)/implyP/(_ Rnc)/implyP/(_ RsoW)/implyP/(_ Rec) ->. }
    assert (QR : simple_upath (q ++ r)).
    { apply (@simple_disjoints_are_cat_simple v); try by [].
      - by revert Qnc => /= /eqP.
      - revert Rnc => /= /eqP. by destruct r.
      - revert QtaW RsoW => /= /eqP--> /eqP-?. by destruct r. }
    rewrite disjoint_sym map_cat disjoint_cat disjoint_sym
      (disjoint_sym (mem [seq usource e | e <- q])) Drq andb_true_r.
    enough (E : [disjoint [seq utarget e | e <- q ++ r] & [seq usource e | e <- p]]).
    { revert E. by rewrite map_cat disjoint_cat => /andP[_ ->]. }
    revert Pdis => /forallP/(_ {| supval := _ ; supvalK := QR |}) /= Pdis.
    assert (Pdis' : alternating (q ++ r) -> head u [seq usource _e | _e <- q ++ r]
      != last u [seq utarget _e | _e <- q ++ r] ->
      head u [seq usource _e | _e <- q ++ r] == v ->
      c (head (forward ea) (q ++ r)).1 != c eb ->
      [disjoint [seq utarget e | e <- q ++ r] & [seq usource e | e <- p]]).
    { move => H1 H2 H3 H4.
      by revert Pdis => /implyP/(_ H1)/implyP/(_ H2)/implyP/(_ H3)/implyP/(_ H4) ->. }
    apply Pdis'; clear Pdis'.
    + rewrite /alternating nb_bridges_cat.
      revert Qa Ra => /eqP--> /eqP-->.
      destruct q; first by []. destruct r; first by [].
      clear - Qec Rec. simpl in *.
      enough (~~ bridge (last _ _).1 _.1) by lia.
      rewrite bridge_sym.
      apply /negPn => bridge_last_head.
      contradict Rec. apply /negP/negPn.
      exact (never_two_bridges_without_three bridge_last_head Qec).
    + rewrite !map_cat head_cat last_cat.
      apply /eqP => usource_q_eq_utarget_r.
      revert Drq => /disjointP/(_ (head (head u [seq usource e | e <- r])
        [seq usource e | e <- q]))-Drq. apply Drq; clear Drq.
      * rewrite usource_q_eq_utarget_r mem3_last //. by destruct r.
      * rewrite mem3_head //. by destruct q.
    + by destruct q.
    + by destruct q.
Qed.

Open Scope order_scope.

Fact my_le_def : forall x y, (x == y) || (ordering x y) = (x == y) || ordering x y.
Proof. by []. Qed.

Definition perm_porderMixin :=
  LtPOrderMixin my_le_def ordering_irrefl ordering_trans.
Canonical porderType :=
  POrderType tt _ perm_porderMixin.
Canonical finPOrderType := Eval hnf in [finPOrderType of (prod_choiceType G (edge G))].

(* We are looking for a splitting vertex - one for which any simple cycle starting from it
   has its first and last edges making a bridge. *)
Definition splitting (v : G) : bool :=
  [forall p : Simple_upath G, (upath_source v p == v) ==> (upath_target v p == v) ==>
  (match supval p with | [::] => false | e :: _ => bridge (head e (supval p)).1 (last e (supval p)).1 end)].

Lemma test {T : eqType} (s r1 r2 : seq T) (x1 x2 : T) :
  s = r1 ++ [:: x1; x2] ++ r2 -> uniq s ->
  exists n, n.+1 < size s /\ x1 = nth x1 s n /\ x2 = nth x1 s n.+1 /\
  r1 = take n s /\ r2 = drop n.+2 s.
Proof.
  revert r1. induction s as [ | y s IH] => r1; destruct r1 as [ | r r1] => //= S.
  - inversion S. clear S IH => _. subst y s.
    exists 0. by rewrite /= drop0.
  - move => /andP[Z U].
    inversion S as [[Yeq S']]. rewrite -!S'. clear S. subst y.
    specialize (IH _ S' U). destruct IH as [n [N [X1 [X2 [R1 R2]]]]].
    exists n.+1. by rewrite /= -X1 -X2 R1 R2.
Qed.

(* A vertex v which is a maximal element for <G (associated to some color) is splitting.
   Or by contrapose, a non-splitting element cannot be maximal (associated to any color). *)
Lemma no_splitting_is_no_max (v : G) :
  correct -> ~~ splitting v -> forall ec, exists U, ((v, ec) : finPOrderType) < U.
Proof.
(* Take v a non-splitting vertex: it is in a simple cycle o starting from it whose first
   and last edges do not make a bridge. *)
  move => C /forallPn[[o O] /= V] ec.
  rewrite !negb_imply in V.
  revert V => /andP[/eqP-Oso /andP[/eqP-Ota Bv']].
  assert (Bv : ~~ bridge (head (forward ec) o).1 (last (forward ec) o).1)
    by by destruct o. clear Bv'.
(* Without loss of generality, we can take o to have a minimal number of bridges among all
   such cycles. *)
  wlog Omin : o O Oso Ota Bv / forall p, simple_upath p ->
    upath_source v p = upath_source v o ->
    upath_source v p = upath_target v p ->
    ~~ bridge (head (forward ec) p).1 (last (forward ec) p).1 ->
  nb_bridges p >= nb_bridges o.
  { move => Wlog.
    set PropMin := fun (p : Simple_upath G) =>
      (upath_source v p == upath_source v o) && (upath_source v p == upath_target v p) &&
      ~~ bridge (head (forward ec) (supval p)).1 (last (forward ec) (supval p)).1.
    assert (PropMino : PropMin {| supval := _ ; supvalK := O |}).
    { repeat (apply /andP; split); try by []. by rewrite /= Oso Ota. }
    revert PropMino => /(arg_minnP (fun p => nb_bridges (supval p)))-[[o' O']
      /andP[/=/andP[/eqP-O'so /eqP-O'c] O'b] O'min].
    apply (Wlog o'); try by [].
    - by rewrite O'so Oso.
    - by rewrite -O'c O'so Oso.
    - move => p P Pso Pc Pb.
      apply (O'min {| supval := _ ; supvalK := P |}).
      repeat (apply /andP; split); try by [].
      + by rewrite Pso /= O'so.
      + by rewrite -Pc Pso /= O'c. }
(* Still without loss of generality, up to reversing o it does not start with
   an edge colored as ec. This is due to the fact that its first and last
   edges have different colors. *)
  wlog Ostart : o O Oso Ota Bv Omin / ~~ bridge (head (forward ec) o).1 ec.
  { move => Wlog.
    case: (boolP (bridge (head (forward ec) o).1 ec)); last first.
    { move => Ostart. by apply (Wlog o). }
    move => Oend.
    apply (Wlog (upath_rev o)); clear Wlog.
    - by rewrite simple_upath_rev.
    - by rewrite map_usource_upath_rev head_rev.
    - by rewrite map_utarget_upath_rev last_rev.
    - rewrite head_upath_rev last_upath_rev /= eq_sym. by destruct o.
    - rewrite nb_bridges_upath_rev.
      by replace (upath_source v (upath_rev o)) with (upath_source v o)
       by by rewrite upath_endpoint_rev /= Oso Ota.
    - rewrite head_upath_rev /= eq_sym (last_eq _ (forward ec)); last by destruct o.
      apply /negP => bridge_last.
      contradict Bv. apply/negP/negPn.
      exact (never_two_bridges_without_three Oend bridge_last). }
(* By correctness, this cycle o cannot be alternating. *)
  destruct (alternating o) eqn:Oa.
  { contradict C. apply /negP/forallPn.
    exists {| supval := _ ; supvalK := O |}.
    rewrite negb_imply Oa negb_forall /=.
    apply /existsP. exists (forward ec).
    rewrite negb_imply (head_eq _ v) ?(last_eq _ v); [ | by destruct o | by destruct o].
    by rewrite Oso Ota eq_refl. }
  apply negbT in Oa.
(* So, it has a bridge. We take the first one, following o. *)
  destruct (not_alternating_has_bridge Oa) as [o1 [o2 [e1 [e2 [Oeq B12]]]]].
  wlog Bfst : o1 o2 e1 e2 Oeq B12 / alternating (rcons o1 e1).
  { move => Wlog. clear C Oso Ota Bv Omin Oa.
(* Silly thing: if o2 is empty, then it is not simple and we need simple paths
   as just paths are not a finite type. So we use ordinal instead to get e1 and e2. *)
    set PropMin := fun (n : 'I_(size o)) => (n.+1 < size o) && bridge (nth e1 o n).1 (nth e1 o n.+1).1.
    apply uniq_fst_simple_upath in O.
    assert (U := map_uniq O). clear O.
    destruct (test Oeq U) as [n [N [E1 [E2 [O1 O2]]]]].
    assert (Nbis : n < size o) by (clear - N; simpl in *; lia).
    assert (PropMino : PropMin (Ordinal Nbis)) by by rewrite /PropMin -E1 -E2 B12 N.
    revert PropMino => /(arg_minnP (fun n => nat_of_ord n))-[[k K] /andP[/= K' KB] Kmin].
    apply (Wlog (take k o) (drop k.+2 o) (nth e1 o k) (nth e1 o k.+1)); try by [].
    - by rewrite /= -!drop_nth // cat_take_drop.
    - destruct (alternating (rcons (take k o) (nth e1 o k))) eqn:A; first by [].
      revert A => /negP/negP-A.
      destruct (not_alternating_has_bridge A) as [f1 [f2 [fe1 [fe2 [Feq Bf]]]]].
      assert (U' : uniq (rcons (take k o) (nth e1 o k))).
      { revert U. by rewrite -{1}(cat_take_drop k o) (drop_nth e1 K) -cat_rcons cat_uniq => /andP[-> _]. }
      destruct (test Feq U') as [n' [N' [E1' [E2' [O1' O2']]]]].
      rewrite size_rcons size_take K in N'.
      assert (N'bis' : n'.+1 < size o).
      { rewrite -(cat_take_drop k o) (drop_nth e1 K) -cat_rcons size_cat size_rcons size_take K.
        clear - N'. simpl in *. lia. }
      assert (N'bis : n' < size o) by (clear - N'bis'; lia).
      assert (NN : n' < k) by (clear -N'; lia).
      rewrite nth_rcons size_take K in E1'.
      replace ((n' < k)%N) with true in E1' by (clear - NN; lia).
      rewrite nth_take in E1'; last by (clear -N'; lia).
      rewrite nth_rcons size_take K in E2'.
      assert (fe2 = nth fe1 o n'.+1).
      { rewrite E2'.
        destruct (eq_comparable n'.+1 k) as [H | H].
        - rewrite H /=. replace (k < k)%N with false by (clear; lia).
          by rewrite eq_refl (set_nth_default fe1 e1).
        - assert (NNN : (n'.+1 < k)%N) by (clear - NN H; lia).
          by rewrite nth_take NNN. }
      assert (H : PropMin (Ordinal N'bis))
        by by rewrite /PropMin /= N'bis' !(set_nth_default fe1 e1) // -E1' -_H Bf.
      specialize (Kmin _ H). contradict Kmin. apply /negP. rewrite /= -ltnNge. clear - NN. lia. }
(* TODO simplify this wlog above *)
(* By bungee jumping, (v, ec) < (utarget e1, e1.1). *)
  exists (utarget e1, e1.1).
  assert (O1 : simple_upath (rcons o1 e1)).
  { rewrite Oeq -cat_rcons in O.
    apply simple_upath_subK in O. revert O => /andP[/orP[/eqP-F | -> //] _].
    contradict F. apply rcons_nil. }
  apply /existsP. exists {| supval := _ ; supvalK := O1 |}.
  rewrite /=. repeat (apply /andP; split); first by [].
  - rewrite Oeq -!cat_rcons in O.
    apply simple_upath_subK in O. revert O => /andP[/orP[/eqP-F | O] _].
    { contradict F. apply rcons_nil. }
    revert O. rewrite simple_upath_rcons => /orP[/eqP-F | /andP[/andP[/andP[/andP[_ O] _] _] _]].
    { contradict F. apply rcons_nil. }
    revert O. by rewrite /= !map_rcons !head_rcons !last_rcons.
  - by rewrite -Oso Oeq -cat_rcons map_cat head_cat !map_rcons !head_rcons.
  - revert Ostart. rewrite Oeq. by destruct o1.
  - by rewrite map_rcons last_rcons.
  - by rewrite last_rcons.
  - (* This is where we use the bungee jumping lemma. *)
    apply /forallP. move => [r R] /=.
    apply /implyP => Ra. apply /implyP => Rnc. apply /implyP => /eqP-Rso.
    apply /implyP => Rb.
    Check colored_bungee_jumping.
(* remplacer dans bungee "upath_target (usource _e1) _r
         \in [seq usource _e | _e <- _o]"
with "~~ [disjoint
   [seq utarget _e | _e <- p]
 & [seq usource _e | _e <- rcons o1 e1]]"?
ne devrait pas changer grand chose à la preuve,
comme on va se ramener à un prefix pour avoir "upath_target (usource _e1) _r
         \in [seq usource _e | _e <- _o]"
Et ça éviterait ici à se ramener à un préfix de la même façon.
TODO porter cette modification dans le texte du journal. *)
    rewrite (head_eq _ e1) in Rb; last by destruct r.
    apply/negPn/negP => ND.
    contradict C. apply /negP.
    apply (@colored_bungee_jumping o o1 o2 e1 e2 r); try by [].
    + rewrite /= (head_eq _ v) ?(last_eq _ v) ?Oso ?Ota //; by destruct o.
    + by destruct o.
    + move => p P Po Pc Pnb.
      apply Omin; first by [].
      * by rewrite (endpoint_simple_upath _ P _ (usource e1)) (endpoint_simple_upath _ O _ (usource e1)) Po.
      * by rewrite !(endpoint_simple_upath _ P _ (usource e1)) Pc.
      * rewrite (head_eq _ e1) ?(last_eq _ e1) ?Pnb //; by destruct p.
    + rewrite -Rso. by destruct r.
    + apply /eqP. by destruct r.
    + admit.
(* TODO et c'est là qu'il faudrait l'autre hyp de bungee jumping. *)
Admitted.



Lemma well_founded_d :
  well_founded ordering.
Proof.
  apply (Wf_nat.well_founded_lt_compat finPOrderType (fun x => #|[set y | y < x]|)).
  move => x y x_lt_y.
  enough ((#|[set z | (z < x)%O]| < #|[set z | (z < y)%O]|)%N) by lia.
  apply proper_card. apply /properP. split.
  - apply /subsetP => z.
    rewrite !in_set => z_lt_x.
    exact (Order.POrderTheory.lt_trans z_lt_x x_lt_y).
  - exists x.
    + by rewrite in_set.
    + by rewrite in_set Order.POrderTheory.ltxx.
Qed.

Lemma well_founded_gt :
  well_founded (fun x y : finPOrderType => x > y).
Proof.
(* TODO devrait pouvoir être obtenu du précédent en retournant l'ordre,
conserve être un ordre partiel *)
  apply (Wf_nat.well_founded_lt_compat _ (fun x => #|[set y | y > x]|)).
  move => x y y_lt_x.
  enough ((#|[set z | (x < z)%O]| < #|[set z | (y < z)%O]|)%N) by lia.
  apply proper_card. apply /properP. split.
  - apply /subsetP => z.
    rewrite !in_set.
    by apply Order.POrderTheory.lt_trans.
  - exists x.
    + by rewrite in_set.
    + by rewrite in_set Order.POrderTheory.ltxx.
Qed.
(* TODO ces lemmes de façon générale *)

Theorem Yeo (u : G * edge G) : correct -> exists (v : G), splitting v.
(* TODO u : G or #|G| > 0 ? equivalent *)
Proof.
 move => C.
  induction u as [[u ec] IH] using (well_founded_ind well_founded_gt).
  case: (boolP (splitting u)) => U.
  - by exists u.
  - destruct (no_splitting_is_no_max C U ec) as [v u_lt_v].
    by apply (IH v).
Qed.
(* TODO mais il doit bien y avoir un lemme disant qu'il y a un elt max dans un ordre partiel quand même quand même... *)

End Yeo.
(* TODO everywhere - use case: boolP *)