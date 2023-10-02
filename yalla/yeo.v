(* Proof of Yeo's Theorem and bungee jumping lemma *)

From Coq Require Import Bool.
From HB Require Import structures.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
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



Section OrderSimpleUpath.

Context {Lv Le : Type} {G : graph Lv Le} {T : finType}
  (v_of_t : T -> G)
  (Psource : T -> (@upath _ _ G) -> bool)
  (Ptarget : T -> (@upath _ _ G) -> bool)
  (Psource_cat : forall u v p q, Psource u p -> Ptarget v p -> Psource v q -> Psource u (p ++ q))
  (Ptarget_cat : forall u v w p q, Psource u p -> Ptarget v p -> Psource v q -> Ptarget w q -> Ptarget w (p ++ q)).

(* TODO reformulate for new presentation
   Given vertices u and v and colors c and d, (u, c) < (v, d) if
   there is a simple bridge-free non-cyclic path p such that:
   - p starts from u with an edge NOT colored by c
   - p ends in v with an edge colored d
   - any simple bridge-free non-cyclic path q, starting from v by an edge NOT colored by d,
     contains no vertex of p\{u}. *)
(* We use the finite type of edges instead of the (possibly infinite) type of colors.
   It would be better to use the finite type of colors used by the graph, but this is more complex
   to implement in Coq, as here we get a default value for an edge of G. *)
(* Furthermore, we use option (edge G) because when starting, we have no constraint on
   coloration. This will allow us to have a proof holding even when the graph is edge-free. *)
Definition pre_ordering (u v : T) (p : Simple_upath G) : bool :=
  (upath_source (v_of_t u) (val p) != upath_target (v_of_t u) (val p)) &&
  (upath_source (v_of_t u) (val p) == (v_of_t u)) && (Psource u (val p)) &&
  (upath_target (v_of_t u) (val p) == (v_of_t v)) && (Ptarget v (val p)) &&
  [forall q : Simple_upath G, (upath_source (v_of_t u) (val q) != upath_target (v_of_t u) (val q)) ==>
  (upath_source (v_of_t u) (val q) == (v_of_t v)) ==> (Psource v (val q)) ==>
  [disjoint [seq utarget e | e <- val q] & [seq usource e | e <- val p]]].

Definition ordering (u v : T) : bool :=
  [exists p, pre_ordering u v p].

Lemma ordering_irrefl : irreflexive ordering.
Proof.
  move=> u. apply/existsPn => p.
  rewrite /pre_ordering.
  apply/negP => /andP[/andP[/andP[/andP[/andP[/eqP-Pnc PsoU] _] PtaU] _] _].
  contradict Pnc. by rewrite (eqP PsoU) (eqP PtaU).
Qed.

Lemma ordering_trans : transitive ordering.
Proof.
  move=> v u w.
  rewrite /ordering /pre_ordering.
  move=> /existsP[[p P] /= /andP[/andP[/andP[/andP[/andP[/eqP-Pnc PsoU]
    Pea] PtaV] Peb] Pdis]].
  move=> /existsP[[q Q] /= /andP[/andP[/andP[/andP[/andP[/eqP-Qnc QsoV]
    Qeb] QtaW] Qec] Qdis]].
  assert (Dpq : [disjoint [seq utarget e | e <- q] & [seq usource e | e <- p]]).
  { move: Pdis => /forallP/(_ (Sub _ Q)) /=.
    rewrite !(head_eq (v_of_t u) (v_of_t v)) ?(last_eq (v_of_t u) (v_of_t v));
      try by destruct q.
    by move: Qnc => /eqP-Qnc /implyP/(_ Qnc)/implyP/(_ QsoV)/implyP/(_ Qeb) ->. }
  assert (PQ : simple_upath (p ++ q)).
  { apply (@simple_disjoints_are_cat_simple _ _ _ (v_of_t u)); try by [].
    - by destruct q.
    - move: PtaV QsoV => /= /eqP--> /eqP-?. by destruct q. }
  apply/existsP. exists (Sub _ PQ). simpl. repeat (apply/andP; split).
  - rewrite !map_cat head_cat last_cat.
    apply/eqP => F.
    move: Dpq => /disjointP/(_ (head (head (v_of_t u) [seq usource e | e <- q])
      [seq usource e | e <- p]))-Dpq. apply Dpq.
    + rewrite F. apply mem3_last. by destruct q.
    + apply mem3_head. by destruct p.
  - by destruct p.
  - by apply (Psource_cat Pea Peb).
  - rewrite map_cat last_cat. by destruct q.
  - by apply (Ptarget_cat Pea Peb).
  - apply/forallP. move=> [r R] /=.
    apply/implyP => /eqP-Rnc. apply/implyP => RsoW. apply/implyP => Rec.
    assert (Drq : [disjoint [seq utarget e | e <- r] & [seq usource e | e <- q]]).
    { move: Qdis => /forallP/(_ (Sub _ R)) /=.
      rewrite !(head_eq (v_of_t v) (v_of_t u)) ?(last_eq (v_of_t v) (v_of_t u)); try by destruct r.
      by move: Rnc => /eqP-Rnc /implyP/(_ Rnc)/implyP/(_ RsoW)/implyP/(_ Rec) ->. }
    assert (QR : simple_upath (q ++ r)).
    { apply (@simple_disjoints_are_cat_simple _ _ _ (v_of_t v)); try by [].
      - by destruct r.
      - move: QtaW RsoW => /= /eqP--> /eqP-?. by destruct r. }
    rewrite disjoint_sym map_cat disjoint_cat disjoint_sym
      (disjoint_sym (mem [seq usource e | e <- q])) Drq andb_true_r.
    enough (E : [disjoint [seq utarget e | e <- q ++ r] & [seq usource e | e <- p]]).
    { move: E. by rewrite map_cat disjoint_cat => /andP[_ ->]. }
    move: Pdis => /forallP/(_ (Sub _ QR)) /= Pdis.
    assert (Pdis' : head (v_of_t u) [seq usource _e | _e <- q ++ r]
      != last (v_of_t u) [seq utarget _e | _e <- q ++ r] ->
      head (v_of_t u) [seq usource _e | _e <- q ++ r] == (v_of_t v) ->
      Psource v (q ++ r) ->
      [disjoint [seq utarget e | e <- q ++ r] & [seq usource e | e <- p]]).
    { move=> H1 H2 H3. by move: Pdis => /implyP/(_ H1)/implyP/(_ H2)/implyP/(_ H3)-->. }
    apply Pdis'; clear Pdis'.
    + rewrite !map_cat head_cat last_cat.
      apply/eqP => usource_q_eq_utarget_r.
      move: Drq => /disjointP/(_ (head (head (v_of_t u) [seq usource e | e <- r])
        [seq usource e | e <- q]))-Drq. apply Drq; clear Drq.
      * rewrite usource_q_eq_utarget_r mem3_last //. by destruct r.
      * rewrite mem3_head //. by destruct q.
    + by destruct q.
    + by apply (Psource_cat Qeb Qec).
Qed.

(* We consider T as a finite partial ordered type. *)
Definition vertex_finPOrderType : Type := T. (* TODO Define T so that this trick is unneeded *)
HB.instance Definition _ := Finite.on vertex_finPOrderType. (* To prevent delta-expansion *)
HB.instance Definition _ := @Order.Lt_isPOrder.Build
  tt vertex_finPOrderType ordering ordering_irrefl ordering_trans.

End OrderSimpleUpath.

Section BridgeTheory.

(* The local relation bridge(v) between edges incident to v is a symmetric and transitive relation *)
(* TODO use local coloration instead? I thnik no, so as to not take the reflexive closure of bridge in seq *)

Context {Lv Le : Type} {G : graph Lv Le} (bridge : G -> rel (edge G)).

Definition local_symmetric :=
  forall (v : G) (e1 e2 : edge G),
  e1 \in edges_at v -> e2 \in edges_at v ->
  bridge v e1 e2 = bridge v e2 e1.

Definition local_transitive :=
  forall (v : G) (e2 e1 e3 : edge G),
  e1 \in edges_at v -> e2 \in edges_at v -> e3 \in edges_at v ->
  bridge v e1 e2 -> bridge v e2 e3 -> bridge v e1 e3.

Hypothesis (bridge_sym : local_symmetric) (bridge_trans : local_transitive).

Lemma edges_in_edges_at_endpoint (e : edge G) (b : bool) :
  e \in edges_at (endpoint b e).
Proof. rewrite edges_at_eq. by destruct b; rewrite eq_refl // orb_true_r. Qed.

(* Number of bridges in a path, made by couple of successive edges (not
   counting the one made by the last and first edges in the case of a cycle). *)
Fixpoint nb_bridges (p : @upath _ _ G) : nat :=
  match p with
  | [::] => 0
  | e :: p => nb_bridges p + if p is [::] then 0 else bridge (utarget e) e.1 (head e p).1
  end.

Lemma nb_bridges_rcons e (p : upath) :
  nb_bridges (rcons p e) = nb_bridges p +
    if p is [::] then 0 else bridge (utarget (last e p)) (last e p).1 e.1.
Proof.
  induction p as [ | e' p IH]; first by [].
  rewrite rcons_cons /= {}IH.
  destruct (rcons p e) as [ | e0 p0] eqn:F.
  { contradict F. apply rcons_nil. } (* TODO would be great for this to be solved by done...
but I can't manage to do it with just Hint Resolve rcons_nil : core. *)
  destruct p; simpl.
  - by inversion F.
  - rewrite rcons_cons in F. inversion F. clear F. subst. lia.
Qed.

Lemma nb_bridges_upath_rev (p : @upath _ _ G) :
  match p with | [::] => true | e :: _ =>
    uwalk (upath_source (utarget e) p) (upath_target (utarget e) p) p end ->
  (* TODO trickery to write walk ? ? p *)
  nb_bridges (upath_rev p) = nb_bridges p.
Proof.
  induction p as [ | [e1 b1] [ | [e2 b2] p] IH] => // W.
  move: W IH. simpl uwalk. rewrite !eq_refl !andb_true_l. move=> /andP[/eqP-se2_eq_te1 W] /(_ W).
  rewrite /= (nb_bridges_rcons _ (rcons _ _)) => ->. f_equal.
  rewrite last_rcons /= se2_eq_te1.
  destruct (rcons _ _) eqn:F.
  { contradict F. apply rcons_nil. }
  by rewrite bridge_sym // ?edges_in_edges_at_endpoint // -se2_eq_te1 edges_in_edges_at_endpoint.
Qed.

Lemma nb_bridges_cat (p q : upath) :
  nb_bridges (p ++ q) = nb_bridges p + nb_bridges q +
    match p, q with | ep :: _, eq :: _ =>
    bridge (utarget (last ep p)) (last ep p).1 (head eq q).1 | _, _ => 0 end.
Proof.
  move: p. induction q as [ | eq q IHq] => p.
  { rewrite /= cats0. destruct p; lia. }
  rewrite -cat_rcons (IHq _) {IHq} /= nb_bridges_rcons.
  destruct (rcons p eq) eqn:F.
  { contradict F. apply rcons_nil. }
  rewrite -{}F last_rcons.
  destruct p, q; simpl; lia.
Qed.

(* For colors, this corresponds to alternating paths. *)
Notation bridge_free p := (nb_bridges p == 0).

Lemma not_bridge_free_has_first_bridge (p : upath) :
  ~~ bridge_free p -> exists p1 p2 e1 e2,
  p = p1 ++ [:: e1; e2] ++ p2 /\ bridge (utarget e1) e1.1 e2.1 /\ bridge_free (rcons p1 e1).
Proof.
  induction p as [ | e [ | e' p] IH] => // not_bridge_free_e_e'_p.
  case/boolP: (bridge (utarget e) e.1 e'.1) => bridge_e_e'.
  { by exists [::], p, e, e'. }
  case/boolP: (bridge_free (e' :: p)) => not_bridge_free_e'_p.
  { contradict not_bridge_free_e_e'_p. apply/negP/negPn.
    move: not_bridge_free_e'_p. simpl. lia. }
  clear not_bridge_free_e_e'_p.
  destruct (IH not_bridge_free_e'_p) as [p1 [p2 [e1 [e2 [e'_p_eq [B bridge_free_p1_e1]]]]]].
  clear IH not_bridge_free_e'_p. rewrite e'_p_eq.
  exists (e :: p1), p2, e1, e2.
  rewrite {}B. repeat split.
  move: bridge_free_p1_e1. rewrite rcons_cons /= => /eqP-->.
  destruct (rcons p1 e1) eqn:P1eq; first by [].
  rewrite -{}P1eq.
  replace (head e (rcons p1 e1)) with (head e (p1 ++ [:: e1; e2] ++ p2))
    by by rewrite -cat_rcons head_cat !head_rcons.
  by rewrite -{}e'_p_eq /= (negPf bridge_e_e').
Qed.

Lemma bridge_free_cat (p q : upath) :
  bridge_free (p ++ q) ->
  bridge_free p /\ bridge_free q.
Proof. rewrite nb_bridges_cat. lia. Qed.

(** A graph is correct if all its simple bridge-free cycles have their first and last edges
   making a bridge; i.e. it has no non-empty simple bridge-free cycle, if we count as a possible bridge
   also the first and last edges of a cycle. *)
Definition correct : bool :=
  [forall p : Simple_upath G, (bridge_free (val p)) ==>
    match val p with | [::] => true | e ::_ =>
    (upath_source (usource e) (val p) == upath_target (usource e) (val p)) ==>
    bridge (usource (head e (val p))) (head e (val p)).1 (last e (val p)).1 end].
(* TODO def cyclic upath/simple_upath to simplify? *)

(* useless?
Lemma eq_edge_fst (e1 e2 : edge G * bool) :
  e1.1 = e2.1 ->
  utarget e1 = utarget e2 \/ usource e1 = utarget e2. (* TODO  I think I use it elsewhere *)
Proof. destruct e1 as [? []], e2 as [? []] => ->; auto. Qed.
(* TODO generalize if utarget = uendpoint b *)
*)

Lemma cyclic_source_eq_target (o : upath) (v : G) (e1 e2 : edge G * bool) :
  o <> [::] -> upath_source v o = upath_target v o ->
  utarget (last e1 o) = usource (head e2 o).
Proof. destruct o as [ | e o] => //= _ ->. by rewrite -(last_map (fun e => utarget e)). Qed.
(* TODO in upath *)

(* Take G an edge-colored graph and o a simple cycle such that its first and
  last edges are not a bridge, with a minimal number of bridges (with respect
  to all such cycles with the same source), and containing a bridge, of color
  d and pier k.
  If there is an alternating simple non-cyclic path r starting from k with an
  edge not colored d, with r intersecting o (other than in k), then G is not
  correct. *)
(* TODO "upath_target (usource e1) r \in [seq usource e | e <- o]" replaced
  with "~~ [disjoint [seq utarget e | e <- r] & [seq usource e | e <- o]]":
  this leads to less wlog to do, and is coherent with the ordering:
  to adapt in the journal's text *)
Lemma bungee_jumping (o o1 o2 : upath) e1 e2 r :
(* Let o be a simple cycle *)
  simple_upath o -> upath_source (usource e1) o = upath_target (usource e1) o ->
(* whose first and last edges are not a bridge, *)
  ~~ bridge (usource (head e1 o)) (head e1 o).1 (last e1 o).1 ->
(* with o having a minimal number of bridges among such cycles, with the same source. *)
  (forall p, p <> [::] -> simple_upath p -> upath_source (usource e1) p = upath_source (usource e1) o ->
    upath_source (usource e1) p = upath_target (usource e1) p ->
    ~~ bridge (usource (head e1 p)) (head e1 p).1 (last e1 p).1 -> nb_bridges p >= nb_bridges o) ->
(* Take e1 e2 a bridge of o *)
  o = o1 ++ [:: e1; e2] ++ o2 -> bridge (utarget e1) e1.1 e2.1 ->
(* and r an alternating simple non-cyclic path starting from the pier of this bridge *)
  upath_source (usource e1) r = utarget e1 -> bridge_free r -> simple_upath r ->
  upath_source (usource e1) r <> upath_target (usource e1) r ->
(* with a different color than the bridge, and from another edge *)
  ~~ bridge (utarget e1) (head e1 r).1 e1.1 ->
  (head e1 r).1 <> e1.1 -> (head e1 r).1 <> e2.1 ->
(* and not vertex-disjoint with o (other than in the source of r). *)
  ~~ [disjoint [seq utarget e | e <- r] & [seq usource e | e <- o]] ->
(* Then G is not correct. *)
  ~~ correct.
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
      by destruct (bridge_free_cat Ra) as [-> _].
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
   and if it is the source of o then its last edge does not make a bridge with the first edge of o. *)
(* This stronger hypothesis replaces the weaker Rta. *)
  wlog {Rta} Rta : o o1 o2 e1 e2 r Os Oc Onb Omin Oeq B12 Rso Ra Rs Rnc Rc Re1 Re2 Rfst /
    upath_target (usource e1) r \in [seq usource e | e <- o2] \/
    (upath_target (usource e1) r = upath_source (usource e1) o /\
    ~~ bridge (usource (head e1 o)) (head e1 o).1 (last e1 r).1).
  { move=> Wlog.
(* Some equalities on endpoints of the paths *)
    assert (Onil : o <> [::]) by by destruct o, o1.
    assert (Ow := @uwalk_of_simple_upath _ _ _ _ Os (usource e1)). rewrite Oeq in Ow.
    assert (O1e1 := uwalk_sub_middle Ow).
    apply uwalk_subK in Ow as [O1w O2w]. rewrite {}O1e1 in O1w.
    apply uwalk_subK in O2w as [E1E2 _].
    move: O1w E1E2. rewrite /= !map_cat !head_cat !eq_refl andb_true_r /= => O1w /eqP-E1E2.
    assert (Omem : [seq utarget e | e <- o] =i [seq usource e | e <- o]).
    { apply eq_mem_sym, (@mem_usource_utarget_cycle _ _ _ (upath_source (usource e1) o)).
      rewrite {2}Oc. by apply uwalk_of_simple_upath. }
(* If the target of r is the source of o, and does not make a bridge with it, or
   if the target of r is in o2 and not the source of o, then apply Wlog to o. *)
    destruct ((upath_target (usource e1) r == upath_source (usource e1) o) &&
      (~~bridge (usource (head e1 o)) (head e1 o).1 (last e1 r).1) ||
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
    - rewrite /= !negb_involutive map_usource_upath_rev map_utarget_upath_rev head_rev last_rev.
      by destruct o.
    - rewrite head_upath_rev last_upath_rev /= !negb_involutive bridge_sym.
      + rewrite (cyclic_source_eq_target _ e1 Onil Oc). by destruct o.
      + destruct (last (e2.1, e2.2) o).
        by rewrite edges_in_edges_at_endpoint.
      + rewrite (cyclic_source_eq_target _ e1 Onil Oc).
        by destruct o as [ | [? []] ?]; rewrite // edges_in_edges_at_endpoint.
    - move=> p Ps.
      move: Omin => /(_ p Ps).
      rewrite upath_endpoint_rev Oc nb_bridges_upath_rev; last first.
      { destruct o; first by []. by apply uwalk_of_simple_upath. }
      by destruct o, p.
    - by rewrite Oeq !upath_rev_cat /= -catA -cat1s -catA !cat1s.
    - by rewrite bridge_sym ?edges_in_edges_at_endpoint // E1E2 // edges_in_edges_at_endpoint.
    - move: Rso. rewrite /= E1E2 negb_involutive. by destruct r.
    - move: Rnc. rewrite /= negb_involutive. by destruct r.
    - move: Rc. rewrite (head_eq _ e1) /=; last by destruct r.
      move=> Rc. apply/negP => Rc'. contradict Rc. apply/negP/negPn.
      rewrite -E1E2.
      destruct e1, e2.
      refine (bridge_trans _ _ _ Rc' _).
      + destruct r as [ | [? ?] r]; first by [].
        by rewrite E1E2 -Rso edges_in_edges_at_endpoint.
      + by rewrite edges_in_edges_at_endpoint.
      + by rewrite E1E2 edges_in_edges_at_endpoint.
      + by rewrite bridge_sym ?edges_in_edges_at_endpoint // E1E2 // edges_in_edges_at_endpoint.
    - by destruct r.
    - by destruct r.
    - move=> u.
      rewrite map_usource_upath_rev mem_rev Omem.
      replace (upath_target (usource (reversed e2)) r) with
        (upath_target (usource e1) r) by by destruct r.
      apply Rfst.
    - move: Rta.
      rewrite upath_endpoint_rev.
      replace (upath_endpoint (~~ false) (usource (reversed e2)) o)
        with (upath_source (usource e1) o) by by destruct o.
      rewrite !map_usource_upath_rev !negb_involutive mem_rev /= map_rcons mem_rcons
        (mem_usource_utarget_uwalk O1w) in_cons (last_eq _ (usource e1)); last by destruct r.
      replace (head (usource e1) [seq usource e | e <- o1]) with
        (head (usource e1) [seq usource e | e <- o]) by by rewrite Oeq map_cat head_cat.
      move=> /orP[/eqP-Rta | ->]; [right | by left]. split; first by [].
      rewrite head_upath_rev /= !(last_eq _ e1); [ | by destruct r | by destruct o].
      rewrite bridge_sym.
      + apply/negP => B.
        contradict Onb. apply/negP/negPn.
        rewrite /= Rta eq_refl /= in Rta1.
        rewrite negb_involutive (cyclic_source_eq_target _ e1 Onil Oc) in B.
        refine (bridge_trans _ _ _ Rta1 B).
        * by rewrite edges_in_edges_at_endpoint.
        * move: Rta.
          destruct r as [ | r [er br] _] using last_ind; first by [].
          rewrite map_rcons !last_rcons //.
          destruct o; first by [].
          move => /= <-.
          by rewrite edges_in_edges_at_endpoint.
        * by rewrite -(cyclic_source_eq_target e1 e1 Onil Oc) edges_in_edges_at_endpoint.
      + by rewrite edges_in_edges_at_endpoint.
      + move: Rta.
        destruct r as [ | r [er br] _] using last_ind; first by [].
        rewrite map_rcons !last_rcons // negb_involutive (cyclic_source_eq_target e1 e1 Onil Oc).
        destruct o; first by [].
        move => /= <-.
        by rewrite edges_in_edges_at_endpoint. }
(* As r ends in o2, we separate o2 in o21 before the target of r and o22 after,
   and r ends on the source of o (without a bridge) if o22 is empty. *)
  assert (exists o21 o22, o2 = o21 ++ o22 /\
    upath_source (upath_target (utarget e2) o21) o22 = upath_target (usource e1) r /\
    if o22 == [::] then ~~ bridge (usource (head e1 o)) (head e1 o).1 (last e1 r).1 else true)
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
  apply uwalk_subK in Ow. destruct Ow as [_ O2w].
  assert (O2e2 := uwalk_sub_middle O2w). rewrite /= !map_cat head_cat last_cat /= map_cat last_cat in O2e2.
  apply uwalk_subK in O2w. destruct O2w as [E1E2w O2w].
  move: E1E2w. rewrite /= !eq_refl andb_true_r /= => /eqP-E1E2.
  apply uwalk_sub_middle in O2w. rewrite /= !map_cat head_cat !last_cat /= map_cat last_cat in O2w.
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
      + move=> ?. subst e2.
        contradict Rc. apply/negP/negPn.
        by rewrite bridge_sym //= ?edges_in_edges_at_endpoint // -E1E2 edges_in_edges_at_endpoint. }
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
  assert (Pnb : ~~ bridge (usource (head e1 p)) (head e1 p).1 (last e1 p).1).
  { move: Bnro Onb O2so. rewrite /p Oeq !head_cat !last_cat /= last_cat.
    by destruct o22. }
(* By minimality of o, the last edge of r and the first of o22 makes a bridge,
   o1 is bridge-free and we know some bridge-free points *)
  specialize (Omin _ Pnil Ps Pso Pc Pnb).
  rewrite Oeq !nb_bridges_cat /= B12 /= nb_bridges_cat {p Pnil Pso Pc Ps Pnb} in Omin.
  move: Ra => /eqP-Ra. rewrite Ra in Omin. (* TODO Ra in Prop? *)
  assert (Omin' : 1 + nb_bridges o21 +
    match o21 with | [::] => 0 | ep :: _ =>
      match o22 with | [::] => 0 | eq :: _ => bridge (utarget (last ep o21)) (last ep o21).1 (head eq o22).1 end end +
    match o21 ++ o22 with | [::] => 0 | eq :: _ => bridge (utarget e2) e2.1 (head eq (o21 ++ o22)).1 end <=
    bridge (utarget e1) e1.1 (head e1 r).1 +
    match o22 with | [::] => 0 | eq :: _ => bridge (utarget (last e1 r)) (last e1 r).1 (head eq o22).1 end).
  { move: Omin. destruct r; first by []. clear. simpl. lia. }
  clear Omin.
  replace (bridge (utarget e1) e1.1 (head e1 r).1) with false in Omin'; last first.
  { clear - Rso Rc Rnc bridge_sym. symmetry.
    rewrite bridge_sym ?(negPf Rc) // ?edges_in_edges_at_endpoint // -{}Rso.
    destruct r; first by [].
    by rewrite edges_in_edges_at_endpoint. }
  assert (nb_bridges o21 = 0 /\
    match o21 with | [::] => true | _ :: _ =>
      match o22 with | [::] => true | _ :: _ => ~~ bridge (utarget (last e1 o21)) (last e1 o21).1 (head e1 o22).1 end end /\
    match o21 ++ o22 with | [::] => true | _ :: _ => ~~ bridge (utarget e2) e2.1 (head e1 (o21 ++ o22)).1 end /\
    match o22 with | [::] => false | _ :: _ => bridge (utarget (last e1 r)) (last e1 r).1 (head e1 o22).1 end)
    as [O21a [Bno21o22 [Bne2o2122 Be1o22]]].
  { move: Omin'. destruct r; first by []. clear. destruct o22, o21; simpl; lia. }
  clear Omin'.
(* Thanks to the bridge-freeness hypotheses given by the minimality of o,
   r ++ upath_rev (e2 :: o21) contradicts correctness. *)
  assert (S : simple_upath (r ++ upath_rev (e2 :: o21))).
  { apply simple_upath_cat; try by [].
    - rewrite simple_upath_rev.
      rewrite Oeq -cat_rcons -cat_cons in Os.
      by apply simple_upath_suffix, simple_upath_prefix in Os.
    - destruct (upath_rev (e2 :: o21)) eqn:R; first by []; rewrite -{}R.
      rewrite upath_endpoint_rev.
      move: O2so. destruct r; first by []. move=> /= <-.
      apply/eqP. by destruct o21, o22.
    - rewrite map_usource_upath_rev disjoint_sym disjoint_rev.
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
  rewrite /correct. apply/forallPn.
  exists (Sub _ S).
  rewrite negb_imply. apply/andP; split.
  - rewrite nb_bridges_cat nb_bridges_upath_rev; last first.
    { apply simple_upath_suffix in S. rewrite simple_upath_rev in S. by apply uwalk_of_simple_upath. }
    rewrite /= Ra O21a.
    replace (0 + match o21 with | [::] => 0 | _ :: _ => bridge (utarget e2) e2.1 (head e2 o21).1 end)
      with 0 by (clear - Bne2o2122; destruct o21; simpl in *; lia).
    assert (Hr : match r with | [::] => 0 | ep :: _ =>
      match rcons (upath_rev o21) (reversed e2) with
      | [::] => 0 | eq :: _ => bridge (utarget (last ep r)) (last ep r).1 (head eq (rcons (upath_rev o21) (reversed e2))).1 end end =
      bridge(utarget (last e1 r)) (last e1 r).1 (head e2 (rcons (upath_rev o21) (reversed e2))).1).
    { destruct r, (rcons (upath_rev o21) (reversed e2)) eqn:F; try by [].
      contradict F. apply rcons_nil. }
    rewrite {}Hr head_rcons head_upath_rev /= negb_involutive -surjective_pairing /=.
    enough (E : ~~ bridge (utarget (last e1 r)) (last e1 r).1 (last e2 o21).1) by (clear - E; lia).
    apply/negP => B.
    destruct o22 as [ | e22 o22]; first by [].
    assert (lr_eq_lo21 : utarget (last e1 r) = utarget (last e2 o21)).
    { destruct o21 as [ | e21 o21]; simpl in *.
      - rewrite O2e2 O2so -(last_map (fun e => utarget e)).
        apply last_eq. by destruct r.
      - move: O2so O2w. rewrite /= -!(last_map (fun e => utarget e)) => -> ->.
        apply last_eq. by destruct r. }
    assert (H1 : (last e2 o21).1 \in edges_at (utarget (last e1 r)))
      by by rewrite lr_eq_lo21 edges_in_edges_at_endpoint.
    assert (H2 : (last e1 r).1 \in edges_at (utarget (last e1 r)))
      by by rewrite edges_in_edges_at_endpoint.
    rewrite bridge_sym // in B.
    simpl in Be1o22.
    assert (H3 : e22.1 \in edges_at (utarget (last e1 r))).
    { destruct r as [ | er r]; first by [].
      move: O2so. rewrite /= -(last_map (fun e => utarget e)) => <-.
      by rewrite edges_in_edges_at_endpoint. }
    assert (BF := bridge_trans H1 H2 H3 B Be1o22).
    rewrite lr_eq_lo21 in BF.
    clear - Bno21o22 Bne2o2122 BF.
    destruct o21 as [ | e21 o21]; simpl in *.
    + contradict Bne2o2122. apply/negP/negPn. exact: BF.
    + contradict Bno21o22. apply/negP/negPn. exact: BF.
  - rewrite /=. destruct r; first by [].
    rewrite /= negb_imply. simpl in *.
    move: Rso.
    rewrite /= !map_cat !map_rcons map_utarget_upath_rev !last_cat !last_rcons /= E1E2 => Rso.
    rewrite Rso eq_refl /=.
    apply/negP => B. contradict Rc. apply/negP/negPn.
    refine (bridge_trans _ _ _ B _); rewrite 1?bridge_sym 1?B12 //.
    + by rewrite -Rso edges_in_edges_at_endpoint.
    + by rewrite -E1E2 edges_in_edges_at_endpoint.
    + by rewrite edges_in_edges_at_endpoint.
    + by rewrite -E1E2 edges_in_edges_at_endpoint.
    + by rewrite edges_in_edges_at_endpoint.
Qed.

Section OrderSimpleUpathBridge. (* TODO put the previous section on order here, in one go? *)

Context {T : finType} (v_of_t : T -> G) (e_of_t : T -> option (edge G * bool)).

Definition Psource (u : T) (p : @upath _ _ G) : bool :=
  (bridge_free p) &&
  (match e_of_t u with
  | None => true
  | Some e => ~~ bridge (utarget e) e.1 (head e p).1 && ((head e p).1 != e.1)
  end).

Definition Ptarget (u : T) (p : @upath _ _ G) : bool :=
  (p != [::]) &&
  (match (e_of_t u) with | None => false | Some e => last e p == e end).

Lemma Psource_cat u v p q :
  Psource u p -> Ptarget v p -> Psource v q -> Psource u (p ++ q).
Proof.
  rewrite /Psource /Ptarget.
  move=> /andP[alt_p nbr_p] /andP[nil_p br_p] /andP[alt_q nbr_q].
  destruct (e_of_t v) as [e | ] eqn:E_of_t; last by [].
  move: br_p nbr_q => /eqP-br_p /andP[nbr_q1 nbr_q2].
  apply/andP. split.
  - rewrite nb_bridges_cat.
    move: alt_p alt_q => /eqP--> /eqP-->.
    destruct p as [ | ep p]; first by []. simpl in br_p. subst e.
    destruct q as [ | eq q]; first by []. simpl.
    simpl in nbr_q1. by rewrite (negPf nbr_q1).
  - destruct (e_of_t u); last by []. by destruct p.
Qed.

Lemma Ptarget_cat u v w p q :
  Psource u p -> Ptarget v p -> Psource v q -> Ptarget w q ->
  Ptarget w (p ++ q).
Proof.
  rewrite /Ptarget. move=> _ /andP[nil_p _] _ /andP[nil_q br_q].
  rewrite cat_nil negb_andb nil_p /=.
  destruct (e_of_t w); last by [].
  rewrite last_cat. by destruct q.
Qed.

Definition vertex_finPOrderType2 : finPOrderType tt. (* TODO rename those *)
Proof.
  refine (@vertex_finPOrderType T : finPOrderType tt).
  - exact: v_of_t.
  - exact: Psource_cat.
  - exact: Ptarget_cat.
Defined.
(* Definition vertex_finPOrderType2 : finPOrderType _ := 
  yeo_vertex_finPOrderType__canonical__Order_FinPOrder v_of_t Psource_cat Ptarget_cat. *)
(* This is not to name yeo_vertex_finPOrderType__canonical__Order_FinPOrder. *)

(* We are looking for a splitting vertex, one such that any simple cycle starting from it
   has its first and last edges making a bridge. *)
Definition splitting (v : G) : bool :=
  [forall p : Simple_upath G, (upath_source v (val p) == v) ==> (upath_target v (val p) == v) ==>
  (match p with
  | exist [::] _ => true
  | exist (e :: p') _ => bridge (usource e) e.1 (last e p').1 end)].

(* A vertex v which is a maximal element (associated to some color/edge) is splitting.
   Or by contrapose, a non-splitting element cannot be maximal (associated to any color/edge). *)
Lemma no_splitting_is_no_max (v : vertex_finPOrderType2)
(* The following 3 properties are valid for both Yeo and Sequentialization. We
   have to prove them anyway for sequentialization and Yeo,
   and it prevents us from proving twice this lemma. *)
(* Build an element of type T from a bridge between two different edges *)
  (t_of_b : forall (e : edge G * bool) e', bridge (utarget e) e.1 e' -> e.1 <> e' -> T)
  (e_of_t_of_b : forall e e' (H : bridge (utarget e) e.1 e') H', e_of_t (t_of_b e e' H H') = Some e)
  (T_edges_at : forall t, match e_of_t t with | None => true | Some e => utarget e == v_of_t t end) :
(*TODO can we do without it?*)
  correct -> ~~ splitting (v_of_t v) ->
  exists U, (v : vertex_finPOrderType2) < U.
Proof.
(* Take v a non-splitting vertex: it is in a simple cycle o starting from it whose first
   and last edges do not make a bridge. *)
  move=> C /forallPn[[o O] /= V].
  rewrite !negb_imply in V.
  move: V => /andP[/eqP-Oso /andP[/eqP-Ota Bv']].
  assert (Onil : o <> [::]) by by destruct o.
  assert (e_base : edge G * bool) by by destruct o.
  assert (Bv : ~~ bridge (usource (head e_base o)) (head e_base o).1 (last e_base o).1)
    by by destruct o.
  clear Bv'.
(* Without loss of generality, we can take o to have a minimal number of bridges among all
   such cycles. *)
  wlog Omin : o O Oso Ota Onil Bv / forall p, simple_upath p ->
    upath_source (v_of_t v) p = upath_source (v_of_t v) o ->
    upath_source (v_of_t v) p = upath_target (v_of_t v) p ->
    p <> [::] ->
    ~~ bridge (usource (head e_base p)) (head e_base p).1 (last e_base p).1 ->
  nb_bridges p >= nb_bridges o.
  { move=> Wlog.
    set PropMin := fun (p : Simple_upath G) =>
      (upath_source (v_of_t v) (val p) == upath_source (v_of_t v) o) &&
      (upath_source (v_of_t v) (val p) == upath_target (v_of_t v) (val p)) &&
      (val p != [::]) && ~~ bridge (usource (head e_base (val p))) (head e_base (val p)).1 (last e_base (val p)).1.
    assert (PropMino : PropMin (Sub o O)).
    { repeat (apply /andP; split); try by [].
      - by rewrite /= Oso Ota.
      - by apply/eqP. }
    move: PropMino => /(@arg_minnP _ (Sub o O : Simple_upath G) PropMin (fun p => nb_bridges (val p)))-[[o' O']
      /andP[/=/andP[/andP[/eqP-O'so /eqP-O'c] /eqP-O'nil] O'b] O'min].
    apply (Wlog o'); try by [].
    - by rewrite O'so Oso.
    - by rewrite -O'c O'so Oso.
    - move=> p P Pso Pc Pnil Pb.
      apply (O'min (Sub _ P)).
      rewrite /PropMin Pb -Pc Pso /= {1}O'so O'c !eq_refl /= andb_true_r.
      by apply /eqP. }
(* Still without loss of generality, up to reversing o, it does not start with
   an edge colored as ec. This is possible as its first and last
   edges have different colors. *)
  wlog Ostart : o O Oso Ota Onil Bv Omin /
    match e_of_t v with | None => true
    | Some ec => ~~ bridge (usource (head e_base o)) (head e_base o).1 ec.1 && ((head e_base o).1 != ec.1) end.
  { move=> Wlog.
    case/boolP: (match e_of_t v with | None => true |
      Some ec => ~~ bridge (usource (head e_base o)) (head e_base o).1 ec.1 && ((head e_base o).1 != ec.1) end).
    { move=> ?. apply (Wlog o); try by []. by destruct (e_of_t v). }
    destruct (e_of_t v) as [ec | ] eqn:ec_eq; last by [].
    rewrite negb_andb !negb_involutive.
    assert (last_head : utarget (last (reversed e_base) o) = usource (head e_base o))
      by by rewrite (@cyclic_source_eq_target _ (v_of_t v) _ e_base Onil) //= Oso Ota.
    move=> Oend.
    apply (Wlog (upath_rev o)); clear Wlog.
    - by rewrite simple_upath_rev.
    - by rewrite map_usource_upath_rev head_rev.
    - by rewrite map_utarget_upath_rev last_rev.
    - apply/eqP. rewrite upath_rev_nil. by apply/eqP.
    - rewrite head_upath_rev last_upath_rev /= negb_involutive bridge_sym last_head.
      + by destruct o.
      + by rewrite -last_head edges_in_edges_at_endpoint.
      + by destruct o; rewrite //= edges_in_edges_at_endpoint.
    - rewrite nb_bridges_upath_rev; last first.
      { destruct o; first by []. by apply uwalk_of_simple_upath. }
      rewrite upath_endpoint_rev.
      by replace (upath_endpoint (~~ false) (v_of_t v) o) with (upath_source (v_of_t v) o)
       by by rewrite /= Oso Ota.
    - rewrite head_upath_rev /= negb_involutive.
      destruct o as [ | eo o]; first by []. simpl in *.
      rewrite last_head.
      apply/andP. split.
      + rewrite bridge_sym.
        * apply/negP => bridge_last.
          contradict Bv. apply/negP/negPn.
          move: Oend => /orP[Oend | /eqP-Oend].
          *** refine (bridge_trans _ _ _ Oend bridge_last).
            ***** by rewrite edges_in_edges_at_endpoint.
            ***** have := T_edges_at v.
                  rewrite ec_eq -Oso => /eqP-<-.
                  by rewrite edges_in_edges_at_endpoint.
            ***** by rewrite -last_head edges_in_edges_at_endpoint.
          *** destruct eo as [eo beo]. simpl in Oend. by subst eo.
        * by rewrite -last_head edges_in_edges_at_endpoint.
        * have := T_edges_at v.
          rewrite ec_eq -Oso => /eqP-<-.
          by rewrite edges_in_edges_at_endpoint.
      + apply/eqP => F.
        move: Oend => /orP[Oend | /eqP-Oend].
        * contradict Bv. apply/negP/negPn.
          by rewrite F Oend.
        * apply uniq_fst_simple_upath in O.
          contradict O. apply/negP.
          destruct o as [ | o [ol ?] _] using last_ind.
          *** simpl in *.
              move: C => /forallP/(_ (Sub _ (simple_upath_edge eo))) /=.
              by rewrite last_head eq_refl (negPf Bv).
          *** rewrite last_rcons /= in F. subst ol.
              by rewrite /= map_rcons rcons_uniq in_rcons Oend /= eq_refl. }
(* By correctness, this cycle o cannot be bridge_free. *)
  case/boolP: (bridge_free o) => Oa.
  { contradict C. apply/negP/forallPn.
    exists (Sub _ O).
    rewrite /= negb_imply Oa /=.
    destruct o as [ | eo o]; first by [].
    rewrite negb_imply (head_eq _ (v_of_t v)) ?(last_eq _(v_of_t v)) //.
    by rewrite Oso Ota eq_refl. }
(* So, it has a bridge. We take the first one, following o. *)
  destruct (not_bridge_free_has_first_bridge Oa) as [o1 [o2 [e1 [e2 [Oeq [B12 Bfst]]]]]].
(* By bungee jumping, (v, ec) < (utarget e1, Some e1.1). *)
  assert (e1_neq_e2 : e1.1 <> e2.1).
  { clear - O Oeq. rewrite {}Oeq in O.
    apply uniq_fst_simple_upath in O.
    move=> F. contradict O. apply/negP.
    by rewrite /= map_cat cat_uniq /= in_cons F eq_refl !negb_orb !andb_false_r. }
  exists (t_of_b _ _ B12 e1_neq_e2).
  assert (v_of_t_of_e : utarget e1 = v_of_t (t_of_b _ _ B12 e1_neq_e2)).
  { have := T_edges_at (t_of_b e1 e2.1 B12 e1_neq_e2).
    have := e_of_t_of_b _ _ B12 e1_neq_e2.
    destruct (e_of_t (t_of_b e1 e2.1 B12 e1_neq_e2)) as [e' | ]; last by [].
    move=> e'_eq /eqP-<-. inversion e'_eq. clear e'_eq. by subst e'. }
  assert (O1 : simple_upath (rcons o1 e1)).
  { rewrite Oeq -cat_rcons in O.
    by apply simple_upath_prefix in O. }
  apply/existsP. exists (Sub _ O1).
  rewrite /pre_ordering /Psource /Ptarget Bfst /=.
  repeat (apply /andP; split).
  - rewrite Oeq -!cat_rcons in O.
    apply simple_upath_prefix in O.
    move: O. rewrite simple_upath_rcons => /andP[_ /orP[/eqP-F | O]].
    { contradict F. apply rcons_nil. }
    move: O. by rewrite /= !map_rcons !head_rcons !last_rcons.
  - by rewrite -Oso Oeq -cat_rcons map_cat head_cat !map_rcons !head_rcons.
  - have := T_edges_at v.
    destruct (e_of_t v) as [ev | ] => // /eqP-EV.
    apply/andP. split.
    + move: Oso Ostart.
      rewrite EV Oeq. destruct o1 => //= V /andP[? _]; rewrite -V bridge_sym //.
      * by rewrite V -EV edges_in_edges_at_endpoint.
      * by rewrite edges_in_edges_at_endpoint.
      * by rewrite V -EV edges_in_edges_at_endpoint.
      * by rewrite edges_in_edges_at_endpoint.
    + move: Ostart => /andP[_ ].
      by rewrite Oeq head_cat head_rcons.
  - by rewrite map_rcons last_rcons v_of_t_of_e.
  - apply/eqP. apply rcons_nil.
  - by rewrite e_of_t_of_b last_rcons.
  - (* This is where we use the bungee jumping lemma. *)
    apply/forallP. move=> [r R] /=.
    apply/implyP => /eqP-Rnc. apply/implyP => /eqP-Rso.
    apply/implyP => /andP[Ra Rb]. apply/negPn/negP => ND.
    contradict C. apply/negP.
    rewrite e_of_t_of_b /= in Rb.
    apply (@bungee_jumping o o1 o2 e1 e2 r); try by [].
    + rewrite /= (head_eq _ (v_of_t v)) ?(last_eq _ (v_of_t v)) ?Oso ?Ota //; by destruct o.
    + by destruct o.
    + move=> [// | ? ?] _ P Po Pc Pnb.
      apply Omin; try by []. by destruct o.
    + rewrite v_of_t_of_e -Rso. by destruct r.
    + by destruct r.
    + move: Rb => /andP[? _].
      rewrite bridge_sym // ?edges_in_edges_at_endpoint //.
      move: Rso. rewrite v_of_t_of_e. destruct r; first by [].
      move=> /= <-. by rewrite edges_in_edges_at_endpoint.
    + by move: Rb => /andP[_ /eqP-?].
    + move: Rb => /andP[Rb _] F.
      contradict Rb. apply/negP/negPn.
      by rewrite F B12.
    + by rewrite Oeq disjoint_sym -cat_rcons map_cat disjoint_cat disjoint_sym negb_andb ND.
Qed.

End OrderSimpleUpathBridge.

End BridgeTheory.

Section Yeo.

(** We consider an edge-colored multigraph G.
    There is no label on vertices (more accurately, they are all labeled by
    tt : unit) and the labels of edges belong to the type Colors,
    which has decidable equality (for we need to compare colors). *)
(* TODO make a theorem local yeo? *)
Variables (Colors : eqType) (G : graph unit Colors).

(** We instanciate previous notions. *)
(* Bridges - pairs of edges of the same color *)
Definition bridge (_ : G) : rel (edge G) :=
  fun e1 e2 => (elabel e1) == (elabel e2).

Notation T := ((G + (edge G * bool))%type : finType).

Definition v_of_t (t : T) : G :=
  match t with
  | inl v => v
  | inr e => utarget e
  end.

Definition e_of_t (t : T) : option (edge G * bool) :=
  match t with
  | inl _ => None
  | inr e => Some e
  end.

Definition vertex_finPOrderType3 : finPOrderType tt :=
  @vertex_finPOrderType2 _ _ _ bridge _ v_of_t e_of_t.

Theorem Yeo : correct bridge -> G -> exists (v : G), splitting bridge v.
Proof.
  move=> C u'.
(* Thanks to using not only edges but also vertices in our ordering type T,
   we start from no color, thus this proof holds even in a graph without colors/edges. *)
  set u : vertex_finPOrderType3 := inl u'. clearbody u. clear u'.
  induction u as [u IH] using (well_founded_ind gt_wf).
  case/boolP: (splitting bridge (v_of_t u)) => U; [by exists (v_of_t u) | ].
  enough (exists v, u < v) as [v ?] by by apply (IH v).
  refine (@no_splitting_is_no_max _ _ _ bridge _ _ _ _ _ _ (fun e _ _ _ => (inr e)) _ _ _ _);
    try by rewrite /bridge.
  - by rewrite /bridge => ? ? ? ? _ _ _ /eqP-->.
  - by move=> [? | ?] /=.
Qed.

End Yeo.

(* TODO everywhere - use case/boolP: b *)
(* TODO remove all useless by by in all files *)
(* TODO uwalk without s and t should simplify *)
(* TODO uwalk_cat; but with empty lists problem? *)
(* TODO mem_usource_utarget_simple_upath_internal to use more *)
(* TODO prevent simpl of upath_endpoint? *)
(* TODO general lemma for uwalk last? *)
