(* Proof of Yeo's Theorem *)

From Coq Require Import Bool Wf_nat.
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

Section FinPOrderTheoryWf. (* TODO in mll_prelim.v *)

Context {disp : unit} {T : finPOrderType disp}.

Lemma lt_wf :
  well_founded (fun (x y : T) => x < y).
Proof.
  apply (well_founded_lt_compat T (fun (x : T) => #|[set y | y < x]|)).
  move => x y x_lt_y.
  enough ((#|[set z | (z < x)%O]| < #|[set z | (z < y)%O]|)%N) by lia.
  apply proper_card. apply /properP. split.
  - apply /subsetP => z.
    rewrite !in_set => z_lt_x.
    exact (lt_trans z_lt_x x_lt_y).
  - exists x.
    + by rewrite in_set.
    + by rewrite in_set ltxx.
Qed.

Lemma gt_wf :
  well_founded (fun (x y : T) => x > y).
Proof.
(* TODO devrait pouvoir être obtenu du précédent en retournant l'ordre,
conserve être un ordre partiel; /!\ [finPOrderType of T^d] est une copie de T,
pas T avec l'ordre à l'envers... *)
  apply (well_founded_lt_compat _ (fun x => #|[set y | y > x]|)).
  move => x y y_lt_x.
  enough ((#|[set z | (x < z)%O]| < #|[set z | (y < z)%O]|)%N) by lia.
  apply proper_card. apply /properP. split.
  - apply /subsetP => z.
    rewrite !in_set.
    by apply lt_trans.
  - exists x.
    + by rewrite in_set.
    + by rewrite in_set ltxx.
Qed.

(* TODO surprising it is not in the library, as well as that there is a
   maximal element in a finPOrderType... *)

End FinPOrderTheoryWf.

Section OrderSimpleUpath.

Context {Lv Le : Type} {G : graph Lv Le} {T : finType}
  (v_of_t : T -> G)
  (Psource : T -> (@upath _ _ G) -> bool)
  (Ptarget : T -> (@upath _ _ G) -> bool)
  (Psource_cat : forall u v p q, Psource u p -> Ptarget v p -> Psource v q -> Psource u (p ++ q))
  (Ptarget_cat : forall u v w p q, Psource u p -> Ptarget v p -> Psource v q -> Ptarget w q -> Ptarget w (p ++ q)).

(*TODO Given vertices u and v and colors c and d, (u, c) < (v, d) if
   there is a simple alternating non-cyclic path p such that:
   - p starts from u with an edge NOT colored by c
   - p ends in v with an edge colored d
   - any simple alternating non-cyclic path q, starting from v by an edge NOT colored by d,
     contains no vertex of p\{u}. *)
(* We use the finite type of edges instead of the (possibly infinite) type of colors.
   It would be better to use the finite type of colors used by the graph, but this is more complex
   to implement in Coq, as here we get a default value for an edge of G. *)
(* Furthermore, we use option (edge G) because when starting, we have no constraint on
   coloration. This will allow us to have a proof holding even when the graph is edge-free. *)
Definition pre_ordering (u v : T) (p : Simple_upath G) : bool :=
  (upath_source (v_of_t u) p != upath_target (v_of_t u) p) &&
  (upath_source (v_of_t u) p == (v_of_t u)) && (Psource u p) &&
  (upath_target (v_of_t u) p == (v_of_t v)) && (Ptarget v p) &&
  [forall q : Simple_upath G, (upath_source (v_of_t u) q != upath_target (v_of_t u) q) ==>
  (upath_source (v_of_t u) q == (v_of_t v)) ==> (Psource v q) ==>
  [disjoint [seq utarget e | e <- supval q] & [seq usource e | e <- supval p]]].

Definition ordering (u v : T) : bool :=
  [exists p, pre_ordering u v p].

Lemma ordering_irrefl : irreflexive ordering.
Proof.
  move => u. apply /existsPn => p.
  rewrite /pre_ordering. apply /negP
    => /andP[/andP[/andP[/andP[/andP[/eqP-Pnc /eqP-PsoU] _] /eqP-PtaU] _] _].
  contradict Pnc. by rewrite PsoU PtaU.
Qed.

Lemma ordering_trans : transitive ordering.
Proof.
  move => v u w.
  rewrite /ordering /pre_ordering.
  move => /existsP[[p P] /= /andP[/andP[/andP[/andP[/andP[/eqP-Pnc PsoU]
    Pea] PtaV] Peb] Pdis]].
  move => /existsP[[q Q] /= /andP[/andP[/andP[/andP[/andP[/eqP-Qnc QsoV]
    Qeb] QtaW] Qec] Qdis]].
  assert (Dpq : [disjoint [seq utarget e | e <- q] & [seq usource e | e <- p]]).
  { revert Pdis => /forallP/(_ {| supval := _ ; supvalK := Q |}) /=.
    rewrite !(head_eq (v_of_t u) (v_of_t v)) ?(last_eq (v_of_t u) (v_of_t v));
      try by destruct q.
    by revert Qnc => /eqP-Qnc /implyP/(_ Qnc)/implyP/(_ QsoV)/implyP/(_ Qeb) ->. }
  assert (PQ : simple_upath (p ++ q)).
  { apply (@simple_disjoints_are_cat_simple _ _ _ (v_of_t u)); try by [].
    - by destruct q.
    - revert PtaV QsoV => /= /eqP--> /eqP-?. by destruct q. }
  apply /existsP. exists {| supval := _ ; supvalK := PQ |}. simpl. repeat (apply /andP; split).
  - rewrite !map_cat head_cat last_cat.
    apply /eqP => F.
    revert Dpq => /disjointP/(_ (head (head (v_of_t u) [seq usource e | e <- q]) [seq usource e | e <- p]))-Dpq. apply Dpq.
    + rewrite F. apply mem3_last. by destruct q.
    + apply mem3_head. by destruct p.
  - by destruct p.
  - by apply (Psource_cat Pea Peb).
  - rewrite map_cat last_cat. by destruct q.
  - by apply (Ptarget_cat Pea Peb).
  - apply /forallP. move => [r R] /=.
    apply/implyP => /eqP-Rnc. apply/implyP => RsoW. apply/implyP => Rec.
    assert (Drq : [disjoint [seq utarget e | e <- r] & [seq usource e | e <- q]]).
    { revert Qdis => /forallP/(_ {| supval := _ ; supvalK := R |}) /=.
      rewrite !(head_eq (v_of_t v) (v_of_t u)) ?(last_eq (v_of_t v) (v_of_t u)); try by destruct r.
      by revert Rnc => /eqP-Rnc /implyP/(_ Rnc)/implyP/(_ RsoW)/implyP/(_ Rec) ->. }
    assert (QR : simple_upath (q ++ r)).
    { apply (@simple_disjoints_are_cat_simple _ _ _ (v_of_t v)); try by [].
      - by destruct r.
      - revert QtaW RsoW => /= /eqP--> /eqP-?. by destruct r. }
    rewrite disjoint_sym map_cat disjoint_cat disjoint_sym
      (disjoint_sym (mem [seq usource e | e <- q])) Drq andb_true_r.
    enough (E : [disjoint [seq utarget e | e <- q ++ r] & [seq usource e | e <- p]]).
    { revert E. by rewrite map_cat disjoint_cat => /andP[_ ->]. }
    revert Pdis => /forallP/(_ {| supval := _ ; supvalK := QR |}) /= Pdis.
    assert (Pdis' : head (v_of_t u) [seq usource _e | _e <- q ++ r]
      != last (v_of_t u) [seq utarget _e | _e <- q ++ r] ->
      head (v_of_t u) [seq usource _e | _e <- q ++ r] == (v_of_t v) ->
      Psource v (q ++ r) ->
      [disjoint [seq utarget e | e <- q ++ r] & [seq usource e | e <- p]]).
    { move => H1 H2 H3. by revert Pdis => /implyP/(_ H1)/implyP/(_ H2)/implyP/(_ H3) ->. }
    apply Pdis'; clear Pdis'.
    + rewrite !map_cat head_cat last_cat.
      apply /eqP => usource_q_eq_utarget_r.
      revert Drq => /disjointP/(_ (head (head (v_of_t u) [seq usource e | e <- r])
        [seq usource e | e <- q]))-Drq. apply Drq; clear Drq.
      * rewrite usource_q_eq_utarget_r mem3_last //. by destruct r.
      * rewrite mem3_head //. by destruct q.
    + by destruct q.
    + by apply (Psource_cat Qeb Qec).
Qed.

(* We consider G * (option (edge G)) as a finite partial ordered type. *)
Fact ordering_le :
  forall x y, (x == y) || (ordering x y) = (x == y) || ordering x y.
Proof. by []. Qed.

Definition vertexCol_porderMixin :=
  LtPOrderMixin ordering_le ordering_irrefl ordering_trans.
Canonical vertexCol_porderType :=
  POrderType tt _ vertexCol_porderMixin.
Canonical vertexCol_finPOrderType :=
  Eval hnf in [finPOrderType of [choiceType of T]].

End OrderSimpleUpath.

Section BridgeTheory.

(* The relation bridge between edges of G is an equivalence relation *)
(* /!\ equivalence_rel from ssrbool has no symmetry... *)

Context {Lv Le : Type} {G : graph Lv Le} (bridge : rel (edge G))
  (bridge_refl : reflexive bridge) (bridge_sym : symmetric bridge)
  (bridge_trans : transitive bridge).
(* TODO do we really need reflexivity? maybe not, by adding some
emptiness of path where it is used... *)

(* Number of bridges in a path, made by couple of successive edges (not
   counting the one made by the last and first edges in the case of a cycle). *)
Fixpoint nb_bridges (p : @upath _ _ G) : nat :=
  match p with
  | [::] => 0
  | e :: p => nb_bridges p + if p is [::] then 0 else bridge e.1 (head e p).1
  end.

Lemma nb_bridges_rcons e (p : upath) :
  nb_bridges (rcons p e) = nb_bridges p +
    if p is [::] then 0 else bridge (last e p).1 e.1.
Proof.
  induction p as [ | e' p IH]; first by [].
  rewrite rcons_cons /= {}IH.
  destruct (rcons p e) as [ | e0 p0] eqn:F.
  { contradict F. apply rcons_nil. } (* TODO would be great for this to be solved by done...
but I can't manage to do it with just Hint Resolve rcons_nil : core. *)
  destruct p; simpl.
  - inversion F. subst. lia.
  - rewrite rcons_cons in F. inversion F. subst. lia.
Qed.

Lemma nb_bridges_upath_rev (p : @upath _ _ G) :
  nb_bridges (upath_rev p) = nb_bridges p.
Proof.
  induction p as [ | ? p IH]; first by [].
  rewrite /= nb_bridges_rcons {}IH last_upath_rev /= negb_involutive bridge_sym.
  destruct p; first by []. simpl.
  destruct (rcons _ _) eqn:F; last by [].
  contradict F. apply rcons_nil.
Qed.

Lemma nb_bridges_cat (p q : upath) :
  nb_bridges (p ++ q) = nb_bridges p + nb_bridges q +
    match p, q with | ep :: _, eq :: _ =>
    bridge (last ep p).1 (head eq q).1 | _, _ => 0 end.
Proof.
  revert p. induction q as [ | eq q IHq] => p.
  { rewrite /= cats0. destruct p; lia. }
  rewrite -cat_rcons (IHq _) {IHq} /= nb_bridges_rcons.
  destruct (rcons p eq) eqn:F.
  { contradict F. apply rcons_nil. }
  rewrite -{}F last_rcons.
  destruct p, q; simpl; lia.
Qed.

(* TODO rename bridge_free? *) (* TODO notation instead? *)
Definition alternating (p : upath) : bool :=
  nb_bridges p == 0.

Lemma not_alternating_has_first_bridge (p : upath) :
  ~~ alternating p -> exists p1 p2 e1 e2,
  p = p1 ++ [:: e1; e2] ++ p2 /\ bridge e1.1 e2.1 /\ alternating (rcons p1 e1).
Proof.
  induction p as [ | e [ | e' p] IH] => // not_alternating_e_e'_p.
  case/boolP: (bridge e.1 e'.1) => bridge_e_e'.
  { by exists [::], p, e, e'. }
  case/boolP: (alternating (e' :: p)) => not_alternating_e'_p.
  { contradict not_alternating_e_e'_p. apply /negP/negPn.
    revert not_alternating_e'_p. rewrite {IH} /alternating /=. lia. }
  clear not_alternating_e_e'_p.
  destruct (IH not_alternating_e'_p) as [p1 [p2 [e1 [e2 [e'_p_eq [B alternating_p1_e1]]]]]].
  clear IH not_alternating_e'_p. rewrite e'_p_eq.
  exists (e :: p1), p2, e1, e2.
  rewrite {}B. repeat split.
  revert alternating_p1_e1.
  rewrite /alternating rcons_cons /= => /eqP-->.
  destruct (rcons p1 e1) eqn:P1eq; first by [].
  rewrite -{}P1eq.
  replace (head e (rcons p1 e1)) with (head e (p1 ++ [:: e1; e2] ++ p2))
    by by rewrite -cat_rcons head_cat !head_rcons.
  rewrite -{}e'_p_eq /=. lia.
Qed.

Lemma alternating_cat (p q : upath) :
  alternating (p ++ q) ->
  alternating p /\ alternating q.
Proof. rewrite /alternating nb_bridges_cat. lia. Qed.

(** A graph is correct if all its simple alternating cycles have their first and last edges
   making a bridge; i.e. it has no simple bridge-free cycle, if we count as a possible bridge
   also the first and last edges of a cycle. *)
Definition correct : bool :=
  [forall p : Simple_upath G, (alternating p) ==>
  [forall e, (upath_source (usource e) p == upath_target (usource e) p) ==>
  bridge (head e (supval p)).1 (last e (supval p)).1]].
(* TODO def cyclic upath/simple_upath to simplify? *)

(* useless?
Lemma eq_edge_fst (e1 e2 : edge G * bool) :
  e1.1 = e2.1 ->
  utarget e1 = utarget e2 \/ usource e1 = utarget e2. (* TODO  I think I use it elsewhere *)
Proof. destruct e1 as [? []], e2 as [? []] => ->; auto. Qed.
(* TODO generalize if utarget = uendpoint b *)
*)

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
(* and not vertex-disjoint with o (other than in the source of r). *)
  ~~ [disjoint [seq utarget e | e <- r] & [seq usource e | e <- o]] ->
(* Then G is not correct. *)
  ~~ correct.
Proof.
  move => Os Oc Onb Omin Oeq B12 Rso Ra Rs Rnc Rc Rta.
(* Up to taking a prefix of r, exactly the endpoints of r are in both o and r *)
  wlog {Rta} [Rfst Rta] : r Rso Ra Rs Rnc Rc / (forall u, u \in [seq utarget e | e <- r] ->
    u \in [seq usource e | e <- o] -> u = upath_target (usource e1) r) /\
    upath_target (usource e1) r \in [seq usource e | e <- o].
  { move {Oc Os Onb Omin Oeq o1 o2 B12 e2} => Wlog.
    revert Rta => /disjointP-Rta.
    assert (Rta' : ~~[forall x, (x \in [seq utarget _e | _e <- r]) ==>
       (x \in [seq usource _e | _e <- o]) ==> false]).
    { clear - Rta.
      apply /negP => Rta'.
      contradict Rta => x Xr Xo.
      by revert Rta' => /forallP/(_ x)/implyP/(_ Xr)/implyP/(_ Xo). }
    revert Rta' => {Rta} /forallPn/sigW[u U].
    revert U. rewrite !negb_imply andb_true_r
      => /andP[/mapP-[a a_in_r ?] target_a_in_sources_o]. subst u.
    assert (Rta' : (utarget a \in [seq usource e | e <- o]) &&
      (upath_source (usource e1) r != utarget a)).
    { rewrite target_a_in_sources_o /=.
      apply /eqP => F.
      contradict Rnc.
      apply (simple_upath_source_in_targets Rs).
      by rewrite /= F (map_f (fun _ => _)). }
    destruct (@in_elt_sub_fst _ r (fun e => (utarget e \in [seq usource e | e <- o]) &&
      (upath_source (usource e1) r != utarget e)) a Rta' a_in_r) as [[n N] [e [Req [Ein Efst]]]].
    revert Ein Req => /andP[Ein /eqP-Rnc'] /= Req {Rta' a a_in_r target_a_in_sources_o Rnc}.
    assert (Rs' : simple_upath (rcons (take n r) e)).
    { clear - Rs Req.
      rewrite {}Req -cat_rcons in Rs.
      by apply simple_upath_prefix in Rs. }
    apply (Wlog (rcons (take n r) e)); clear Wlog; try by [].
    - revert Rso. by rewrite {1}Req /= map_cat head_cat map_rcons head_rcons.
    - clear - Ra Req. rewrite {}Req -cat_rcons in Ra.
      by destruct (alternating_cat Ra) as [-> _].
    - clear - Rnc' Req.
      revert Rnc'. by rewrite {1}Req /= -cat_rcons map_cat !map_rcons !head_cat !head_rcons last_rcons.
    - rewrite head_rcons head_take. destruct n, r; try by [].
      by rewrite Req in Rc.
    - rewrite /= map_rcons last_rcons Ein. split; last by [].
      clear - Efst Req Rs' => u.
      rewrite /= mem_rcons in_cons => /orP[/eqP--> // | /mapP[a Ain ?]] UinO.
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
    upath_target (usource e1) r \in [seq usource e | e <- o2] \/
    (upath_target (usource e1) r = upath_source (usource e1) o /\
    ~~ bridge (head e1 o).1 (last e1 r).1).
  { move => Wlog.
(* Some equalities on endpoints of the paths *)
    assert (o <> [::]) by by destruct o, o1.
    assert (Ow := @uwalk_of_simple_upath _ _ _ _ Os (usource e1)). rewrite Oeq in Ow.
    assert (O1e1 := uwalk_sub_middle Ow).
    apply uwalk_subK in Ow as [O1w O2w]. rewrite {}O1e1 in O1w.
    apply uwalk_subK in O2w as [E1E2 _].
    revert O1w E1E2. rewrite /= !map_cat !head_cat !eq_refl andb_true_r /= => O1w /eqP-E1E2.
    assert (Omem : [seq utarget e | e <- o] =i [seq usource e | e <- o]).
    { apply eq_mem_sym, (@mem_usource_utarget_cycle _ _ _ (upath_source (usource e1) o)).
      rewrite {2}Oc. by apply uwalk_of_simple_upath. }
(* If the target of r is the source of o, and does not make a bridge with it, or
   if the target of r is in o2 and not the source of o, then apply Wlog to o. *)
    destruct ((upath_target (usource e1) r == upath_source (usource e1) o) &&
      (~~bridge (head e1 o).1 (last e1 r).1) ||
      (last (usource e1) [seq utarget e | e <- r] \in [seq usource e | e <- o2])) eqn:Rta'.
    { apply (Wlog o o1 o2 e1 e2 r); try by [].
      revert Rta' => /orP[/andP[/eqP-? ?] | ?]; [by right | by left]. }
    revert Rta' => /norP[Rta1 Rta2]. rewrite negb_andb negb_involutive in Rta1.
(* The target of r cannot be the source of e2, which is the the source of the non-cyclic r. *)
    case/boolP: (last (usource e1) [seq utarget e | e <- r] == usource e2) => /eqP-Rta3.
    { contradict Rnc. by rewrite Rso -E1E2 -Rta3. }
(* Thus, the target of r is in (rcons o1 e1). *)
    revert Rta. rewrite Oeq -cat_rcons !map_cat !mem_cat /= !in_cons.
    revert Rta2 Rta3 => /negPf--> /eqP/negPf-->.
    rewrite !orb_false_r => Rta.
(* In this case, we apply Wlog to the cycle o reversed. *)
    apply (Wlog (upath_rev o) (upath_rev o2) (upath_rev o1) (reversed e2) (reversed e1) r);
      clear Wlog; try by [].
    - by rewrite simple_upath_rev.
    - rewrite /= !negb_involutive map_usource_upath_rev map_utarget_upath_rev head_rev last_rev.
      by destruct o.
    - rewrite head_upath_rev last_upath_rev /= negb_involutive bridge_sym.
      by destruct o.
    - move => p Ps.
      revert Omin => /(_ p Ps).
      rewrite upath_endpoint_rev Oc nb_bridges_upath_rev /= negb_involutive.
      by destruct o, p; rewrite // !bridge_refl.
    - by rewrite Oeq !upath_rev_cat /= -catA -cat1s -catA !cat1s.
    - by rewrite bridge_sym.
    - revert Rso. rewrite /= E1E2 negb_involutive. by destruct r.
    - revert Rnc. rewrite /= negb_involutive. by destruct r.
    - revert Rc. rewrite (head_eq _ e1) /=; last by destruct r.
      move => Rc. apply /negP => Rc'. contradict Rc. apply /negP/negPn.
      apply (bridge_trans Rc'). by rewrite bridge_sym B12.
    - move => u.
      rewrite map_usource_upath_rev mem_rev Omem.
      replace (upath_target (usource (reversed e2)) r) with
        (upath_target (usource e1) r) by by destruct r.
      apply Rfst.
    - revert Rta.
      rewrite upath_endpoint_rev.
      replace (upath_endpoint (~~ false) (usource (reversed e2)) o)
        with (upath_source (usource e1) o) by by destruct o.
      rewrite !map_usource_upath_rev !negb_involutive mem_rev /= map_rcons mem_rcons
        (mem_usource_utarget_uwalk O1w) in_cons (last_eq _ (usource e1)); last by destruct r.
      replace (head (usource e1) [seq usource e | e <- o1]) with
        (head (usource e1) [seq usource e | e <- o]) by by rewrite Oeq map_cat head_cat.
      move => /orP[/eqP-Rta | ->]; [right | by left]. split; first by [].
      rewrite bridge_sym head_upath_rev /= !(last_eq _ e1); [ | by destruct o | by destruct r].
      apply /negP => B.
      contradict Onb. apply /negP/negPn.
      rewrite /= Rta eq_refl /= in Rta1.
      exact (bridge_trans Rta1 B). }
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
  assert (o <> [::]) by by destruct o, o1.
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
(* No edge of r belongs to o. *)
  assert (Dro : [disjoint [seq e.1 | e <- r] & [seq e.1 | e <- o]]). (* TODO lemma? *)
  { clear Oc Onb Omin Ra Rnc Bnro.
    apply /disjointP => e Er Eo.
    assert (Rfst' : forall u, u \in [seq utarget e | e <- r] ->
      u \in [seq usource e | e <- o] -> u = upath_target u r).
    { move => u Ur Uo. rewrite (Rfst u Ur Uo). by destruct r. }
    destruct (disjoint_or_edge Omem Rs Rfst' Er Eo) as [b ?]. clear Rfst'. subst r.
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
        by rewrite bridge_sym. }
(* The following cycle, p, has the needed properties to use the minimality of o. *)
  set p := o1 ++ e1 :: r ++ o22.
  assert (Ps : simple_upath p).
  { rewrite /p.
    enough (simple_upath (e1 :: r ++ o22)).
    { case/boolP: (o1 == [::]) => /eqP-?; first by subst o1.
      apply (@simple_upath_cat _ _ _ e1); try by [].
      - rewrite Oeq in Os. by apply simple_upath_prefix in Os.
      - rewrite -O1e1. by destruct o1.
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
          by apply simple_upath_target_in_sources.
      - assert (upath_target (usource e1) (e1 :: r ++ o22) = upath_target (usource e1) o) as ->.
        { destruct o22.
          - revert O2so. rewrite cats0 /= Oeq !map_cat !last_cat /= => ->.
            by destruct r.
          - by rewrite Oeq /= !map_cat !last_cat /= !map_cat !last_cat. }
        rewrite -Oc Oeq.
        apply /negP => F.
        assert (E : upath_source (usource e1) o1 = upath_target (usource e1) o1).
        { destruct o1; first by [].
          apply simple_upath_source_in_targets; last by [].
          rewrite Oeq in Os. by apply simple_upath_prefix in Os. }
        revert E.
        clear - F Os Oeq.
        rewrite {}Oeq -cat_rcons in Os. apply simple_upath_prefix in Os.
        revert Os. rewrite simple_upath_rcons => /andP[_ /orP[/eqP-? | /eqP-?]].
        + by subst o1.
        + by destruct o1.
      - rewrite Oeq -cat_rcons /= in Os.
        apply simple_upath_prefix in Os.
        rewrite simple_upath_rcons in Os.
        revert Os => /andP[/andP[/andP[/andP[_ Os] _] _] _].
        destruct o1; first by [].
        apply /eqP. by rewrite eq_sym. }
    rewrite simple_upath_cons. apply /andP; split; [apply /andP; split | ];
      [apply /andP; split | | ]; [apply /andP; split | | | ].
    - case/boolP: (o22 == [::]) => /eqP-O22nil; first by (subst o22; rewrite cats0).
      apply (@simple_upath_cat _ _ _ e2); try by [].
      + rewrite Oeq !catA in Os. by apply simple_upath_suffix in Os.
      + by destruct o22, r.
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
          revert Vint => /andP[Vrt /eqP-Vrta].
          contradict Vrta.
          replace (upath_target v r) with (upath_target (usource e1) r) by by destruct r.
          apply Rfst; first by [].
          by rewrite Oeq !map_cat !mem_cat Vo22 !orb_true_r.
      + replace (upath_target (usource e2) o22) with (upath_target (usource e1) o).
        2:{ rewrite Oeq /= map_cat /= map_cat last_cat /= last_cat. by destruct o22. }
        rewrite -Oc.
        apply /negP => F.
        assert (F' : upath_source (usource e1) o = upath_target (usource e1) r).
        { apply Rfst; first by []. rewrite mem3_head //; by destruct o. }
        rewrite -O2so Oc in F'.
        assert (F'' : upath_source (usource e1) o22 = upath_target (usource e1) o22).
        { revert F'. rewrite Oeq /= map_cat /= map_cat last_cat /= last_cat. by destruct o22. }
        contradict F''.
        (* TODO lemma for the 5 following lines? The path o22 is non-cyclic, except if it is empty. *)
(* of the kind simple_upath (o1 ++ o2) -> o1 <> [::] -> o2 <> [::] ->
(forall v, upath_source v o1 <> upath_target v o1) /\
(forall v, upath_source v o2 <> upath_target v o2) .. mais je ne m'en sers que là... *)
        clear - Oeq Os O22nil. move => F.
        rewrite {}Oeq -cat_rcons -cat_cons lastI (cat_rcons (last _ _)) in Os.
        apply simple_upath_suffix, simple_upath_suffix in Os.
        revert Os. rewrite simple_upath_cons => /andP[_ /orP[/eqP-? // | /eqP-F']].
        by destruct o22.
      + move => F.
        revert Dro => /disjointP/(_ (last e2 r).1)-Dro. apply Dro.
        * apply map_f, mem3_last. by destruct r.
        * rewrite F. apply map_f.
          by rewrite Oeq !mem_cat mem3_head ?orb_true_r.
    - destruct r => //=.
      apply /eqP => E1r.
      revert Dro => /disjointP/(_ e1.1)-Dro. apply Dro.
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
        revert E1r' => /andP[E1r /eqP-E1rt].
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
  { revert O2so.
    rewrite Pso Oc /p Oeq /= !map_cat /= !map_cat !last_cat /= !last_cat.
    by destruct o22, r. }
  assert (Pnb : ~~ bridge (head e1 p).1 (last e1 p).1).
  { revert Bnro Onb O2so. rewrite /p Oeq !head_cat !last_cat /= last_cat.
    by destruct o22. }
(* By minimality of o, the last edge of r and the first of o22 makes a bridge,
   o1 is bridge-free and we know some bridge-free points *)
  specialize (Omin _ Ps Pso Pc Pnb).
  rewrite Oeq !nb_bridges_cat /= B12 /= nb_bridges_cat {p Pso Pc Ps Pnb} in Omin.
  revert Ra. rewrite /alternating => /eqP-Ra. rewrite Ra in Omin.
  assert (Omin' : 1 + nb_bridges o21 +
    match o21 with | [::] => 0 | ep :: _ =>
      match o22 with | [::] => 0 | eq :: _ => bridge (last ep o21).1 (head eq o22).1 end end +
    match o21 ++ o22 with | [::] => 0 | eq :: _ => bridge e2.1 (head eq (o21 ++ o22)).1 end <=
    bridge e1.1 (head e1 r).1 +
    match o22 with | [::] => 0 | eq :: _ => bridge (last e1 r).1 (head eq o22).1 end).
  { revert Omin. destruct r; first by []. clear. simpl. lia. }
  clear Omin.
  replace (bridge e1.1 (head e1 r).1) with false in Omin'.
  2:{ clear - Rc bridge_sym. symmetry. rewrite bridge_sym. by apply negb_true_iff. }
  assert (nb_bridges o21 = 0 /\
    match o21 with | [::] => true | _ :: _ =>
      match o22 with | [::] => true | _ :: _ => ~~ bridge (last e1 o21).1 (head e1 o22).1 end end /\
    match o21 ++ o22 with | [::] => true | _ :: _ => ~~ bridge e2.1 (head e1 (o21 ++ o22)).1 end /\
    match o22 with | [::] => false | _ :: _ => bridge (last e1 r).1 (head e1 o22).1 end)
    as [O21a [Bno21o22 [Bne2o2122 Be1o22]]].
  { revert Omin'. destruct r; first by []. clear. destruct o22, o21; simpl; lia. }
  clear Omin'.
(* Thanks to the bridge-freeness hypotheses given by the minimality of o,
   r ++ upath_rev (e2 :: o21) contradicts correctness. *)
  assert (S : simple_upath (r ++ upath_rev (e2 :: o21))).
  { apply (@simple_upath_cat _ _ _ e1); try by [].
    - rewrite simple_upath_rev.
      rewrite Oeq -cat_rcons -cat_cons in Os.
      by apply simple_upath_suffix, simple_upath_prefix in Os.
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
        apply simple_upath_suffix, simple_upath_prefix in Os.
        revert Os. rewrite simple_upath_cons
          => /andP[/andP[/andP[/andP[E2O21s _] /eqP-E1ta] _] /orP[// | /eqP-E2O2nc]].
        contradict E2O2nc.
        apply (simple_upath_source_in_targets E2O21s).
        by rewrite /= E1E2.
      + specialize (Rfst _ Ur' Uo'). subst u.
        contradict Rnc.
        by apply simple_upath_target_in_sources.
    - rewrite upath_endpoint_rev /=.
      apply /negP => F.
      contradict Rnc.
      apply (simple_upath_source_in_targets Rs).
      by rewrite Rso -E1E2 F.
    - move => F.
        revert Dro => /disjointP/(_ (last e1 r).1)-Dro. apply Dro.
        + apply map_f, mem3_last. by destruct r.
        + by rewrite F Oeq head_rcons head_upath_rev /= negb_involutive -cat_rcons -cat_cons !map_cat
            !mem_cat (@map_f _ _ _ (_ :: o21)) ?orb_true_r // mem_last. }
  rewrite /correct. apply /forallPn.
  exists {| supval := _ ; supvalK := S |}.
  rewrite negb_imply. apply /andP; split.
  - rewrite /alternating nb_bridges_cat nb_bridges_upath_rev /= Ra O21a.
    replace (0 + match o21 with | [::] => 0 | _ :: _ => bridge e2.1 (head e2 o21).1 end)
      with 0 by (clear - Bne2o2122; destruct o21; simpl in *; lia).
    assert (Hr : match r with | [::] => 0 | ep :: _ =>
      match rcons (upath_rev o21) (reversed e2) with
      | [::] => 0 | eq :: _ => bridge (last ep r).1 (head eq (rcons (upath_rev o21) (reversed e2))).1 end end =
      bridge (last e1 r).1 (head e2 (rcons (upath_rev o21) (reversed e2))).1).
    { destruct r, (rcons (upath_rev o21) (reversed e2)) eqn:F; try by [].
      contradict F. apply rcons_nil. }
    rewrite {}Hr head_rcons head_upath_rev /= negb_involutive -surjective_pairing /=.
    enough (E : ~~ bridge (last e1 r).1 (last e2 o21).1) by (clear - E; lia).
    apply /negP => B.
    destruct o22; first by [].
    rewrite bridge_sym in B.
    assert (BF := bridge_trans B Be1o22).
    clear - Bno21o22 Bne2o2122 BF.
    destruct o21 as [ | e21 o21]; simpl in *; lia.
  - apply /forallPn. exists e1. rewrite negb_imply.
    rewrite -Rso in E1E2. revert E1E2.
    rewrite /= !map_cat !map_rcons !head_cat map_utarget_upath_rev !last_cat !last_rcons /= => ->.
    destruct r; first by [].
    rewrite eq_refl /=.
    apply /negP => B. contradict Rc. apply /negP/negPn.
    apply (bridge_trans B). by rewrite bridge_sym B12.
Qed.

Section OrderSimpleUpathBridge.

Context {T : finType} (v_of_t : T -> G) (e_of_t : T -> option (edge G))
  (Psource : T -> (@upath _ _ G) -> bool) (Ptarget : T -> (@upath _ _ G) -> bool)
  (Psource_cat : forall u v p q, Psource u p -> Ptarget v p -> Psource v q -> Psource u (p ++ q))
  (Ptarget_cat : forall u v w p q, Psource u p -> Ptarget v p -> Psource v q -> Ptarget w q -> Ptarget w (p ++ q)).

Definition Psource_bis (u : T) (p :@upath _ _ G) : bool :=
  (Psource u p) && (alternating p) &&
  (match (e_of_t u) with | None => true | Some e => ~~ bridge (head (forward e) p).1 e end).

Definition Ptarget_bis (u : T) (p :@upath _ _ G) : bool :=
  (Ptarget u p) &&
  (match (e_of_t u) with | None => false | Some e => bridge (last (forward e) p).1 e end).

Lemma Psource_bis_cat u v p q :
  Psource_bis u p -> Ptarget_bis v p -> Psource_bis v q -> Psource_bis u (p ++ q).
Proof.
  rewrite /Psource_bis /Ptarget_bis.
  move => /andP[/andP[Ps_u_p alt_p] nbr_p] /andP[Pta_v_p br_p]
    /andP[/andP[Qs_v_p alt_q] nbr_q].
  repeat (apply /andP; split).
  - by apply (Psource_cat Ps_u_p Pta_v_p).
  - rewrite /alternating nb_bridges_cat.
    revert alt_p alt_q => /eqP--> /eqP-->.
    destruct p; first by []. destruct q; first by [].
    destruct (e_of_t v); last by [].
    enough (~~ bridge (last _ _).1 (head _ _).1) by lia.
    apply /negP => B. contradict nbr_q. apply /negP/negPn.
    rewrite bridge_sym in B.
    exact (bridge_trans B br_p).
  - destruct (e_of_t u); last by [].
    destruct p; last by [].
    contradict nbr_p. apply /negP/negPn.
    by rewrite bridge_refl.
Qed.

Lemma Ptarget_bis_cat u v w p q :
  Psource_bis u p -> Ptarget_bis v p -> Psource_bis v q -> Ptarget_bis w q ->
  Ptarget_bis w (p ++ q).
Proof.
  rewrite /Psource_bis /Ptarget_bis.
  move => /andP[/andP[Ps_u_p alt_p] nbr_p] /andP[Pta_v_p br_p]
    /andP[/andP[Qs_v_p alt_q] nbr_q] /andP[Pta_w_q br_q].
  repeat (apply /andP; split).
  - by apply (Ptarget_cat Ps_u_p Pta_v_p).
  - destruct (e_of_t w); last by [].
    rewrite last_cat.
    destruct q; last by [].
    destruct (e_of_t v); last by [].
    contradict nbr_q. apply /negP/negPn.
    by rewrite bridge_refl.
Qed.

Definition vertexCol2_finPOrderType :=
  vertexCol_finPOrderType v_of_t Psource_bis_cat Ptarget_bis_cat.
(* TODO rename those *)

(* We are looking for a splitting vertex, one such that any simple cycle starting from it
   has its first and last edges making a bridge. *)
Definition splitting (v : G) : bool :=
  [forall p : Simple_upath G, (upath_source v p == v) ==> (upath_target v p == v) ==>
  (match supval p with | [::] => true | e :: _ => bridge (head e (supval p)).1 (last e (supval p)).1 end)].

Context (t_of_v_e : forall (e : edge G * bool) e', bridge e.1 e' -> e.1 <> e' -> T)
  (e_of_t_of_v_e : forall e e' (H : bridge e.1 e') H', e_of_t (t_of_v_e e e' H H') = Some e.1).
(* Build an element of type T from v, e and a well-chosen property *)
Context (H : forall v p, match e_of_t v with
         | Some e => ~~ bridge (head (forward e) p).1 e
         | None => true
         end -> Psource v p)
(H2 : forall e e' p (H : bridge e.1 e') H', Ptarget (t_of_v_e H H') (rcons p e))
(H3 : forall (o o1 o2 : upath) e1 e2 (H : bridge e1.1 e2.1) H',
  o = o1 ++ [:: e1; e2] ++ o2 ->
  simple_upath o -> ~~ bridge (head e1 o).1 (last e1 o).1 ->
  utarget e1 = v_of_t (t_of_v_e H H')).
(* TODO name + put in no_max *)
(* Ugly thing to have a property enough to prove no_splitting_is_no_max,
and working for both Yeo and Sequentialization.
Still, it is something we would have to prove anyway for sequentialization
(this is trivial for Yeo), and it prevent us from doing twice the long
following lemma. *)

(* A vertex v which is a maximal element (associated to some color/edge) is splitting.
   Or by contrapose, a non-splitting element cannot be maximal (associated to any color/edge). *)
Lemma no_splitting_is_no_max (v : vertexCol2_finPOrderType) :
  correct -> ~~ splitting (v_of_t v) ->
  exists U, (v : vertexCol2_finPOrderType) < U.
Proof.
(* Take v a non-splitting vertex: it is in a simple cycle o starting from it whose first
   and last edges do not make a bridge. *)
  move => C /forallPn[[o O] /= V].
  rewrite !negb_imply in V.
  revert V => /andP[/eqP-Oso /andP[/eqP-Ota Bv']].
  assert (Onil : o <> [::]) by by destruct o.
  assert (e_base : edge G * bool) by by destruct o.
  assert (Bv : ~~ bridge (head e_base o).1 (last e_base o).1)
    by by destruct o.
  clear Bv'.
(* Without loss of generality, we can take o to have a minimal number of bridges among all
   such cycles. *)
  wlog Omin : o O Oso Ota Onil Bv / forall p, simple_upath p ->
    upath_source (v_of_t v) p = upath_source (v_of_t v) o ->
    upath_source (v_of_t v) p = upath_target (v_of_t v) p ->
    p <> [::] ->
    ~~ bridge (head e_base p).1 (last e_base p).1 ->
  nb_bridges p >= nb_bridges o.
  { move => Wlog.
    set PropMin := fun (p : Simple_upath G) =>
      (upath_source (v_of_t v) p == upath_source (v_of_t v) o) &&
      (upath_source (v_of_t v) p == upath_target (v_of_t v) p) &&
      (supval p != [::]) && ~~ bridge (head e_base (supval p)).1 (last e_base (supval p)).1.
    assert (PropMino : PropMin {| supval := _ ; supvalK := O |}).
    { repeat (apply /andP; split); try by [].
      - by rewrite /= Oso Ota.
      - by apply /eqP. }
    revert PropMino => /(arg_minnP (fun p => nb_bridges (supval p)))-[[o' O']
      /andP[/=/andP[/andP[/eqP-O'so /eqP-O'c] /eqP-O'nil] O'b] O'min].
    apply (Wlog o'); try by [].
    - by rewrite O'so Oso.
    - by rewrite -O'c O'so Oso.
    - move => p P Pso Pc Pnil Pb.
      apply (O'min {| supval := _ ; supvalK := P |}).
      repeat (apply /andP; split); try by [].
      + by rewrite Pso /= O'so.
      + by rewrite -Pc Pso /= O'c.
      + by apply /eqP. }
(* Still without loss of generality, up to reversing o, it does not start with
   an edge colored as ec. This is possible as its first and last
   edges have different colors. *)
  wlog Ostart : o O Oso Ota Onil Bv Omin /
    match e_of_t v with | None => true | Some ec => ~~ bridge (head e_base o).1 ec end.
  { move => Wlog.
    case/boolP: (match e_of_t v with | None => true | Some ec => ~~ bridge (head e_base o).1 ec end).
    { move => ?. apply (Wlog o); try by []. by destruct (e_of_t v). }
    destruct (e_of_t v) as [ec | ]; last by [].
    move => /negPn-Oend.
    apply (Wlog (upath_rev o)); clear Wlog.
    - by rewrite simple_upath_rev.
    - by rewrite map_usource_upath_rev head_rev.
    - by rewrite map_utarget_upath_rev last_rev.
    - apply /eqP. rewrite upath_rev_nil. by apply /eqP.
    - rewrite head_upath_rev last_upath_rev /= bridge_sym. by destruct o.
    - rewrite nb_bridges_upath_rev upath_endpoint_rev.
      by replace (upath_endpoint (~~ false) (v_of_t v) o) with (upath_source (v_of_t v) o)
       by by rewrite /= Oso Ota.
    - rewrite head_upath_rev /= bridge_sym (last_eq _ e_base); last by destruct o.
      apply /negP => bridge_last.
      contradict Bv. apply/negP/negPn.
      exact (bridge_trans Oend bridge_last). }
(* By correctness, this cycle o cannot be alternating. *)
  case/boolP: (alternating o) => Oa.
  { contradict C. apply /negP/forallPn.
    exists {| supval := _ ; supvalK := O |}.
    rewrite negb_imply Oa negb_forall /=.
    apply /existsP. exists e_base.
    rewrite negb_imply (head_eq _ (v_of_t v)) ?(last_eq _(v_of_t v)); [ | by destruct o | by destruct o].
    by rewrite Oso Ota eq_refl. }
(* So, it has a bridge. We take the first one, following o. *)
  destruct (not_alternating_has_first_bridge Oa) as [o1 [o2 [e1 [e2 [Oeq [B12 Bfst]]]]]].
(* By bungee jumping, (v, ec) < (utarget e1, Some e1.1). *)
  assert (e1_neq_e2 : e1.1 <> e2.1).
  { clear - O Oeq. rewrite {}Oeq in O.
    apply uniq_fst_simple_upath in O.
    move => F. contradict O. apply /negP.
    by rewrite /= map_cat cat_uniq /= in_cons F eq_refl !negb_orb !andb_false_r. }
  exists (t_of_v_e B12 e1_neq_e2).
  assert (v_of_t_of_v_e : utarget e1 = v_of_t (t_of_v_e B12 e1_neq_e2)).
  { apply (H3 B12 e1_neq_e2 Oeq); try by []. by destruct o. }
  assert (O1 : simple_upath (rcons o1 e1)).
  { rewrite Oeq -cat_rcons in O.
    by apply simple_upath_prefix in O. }
  apply /existsP. exists {| supval := _ ; supvalK := O1 |}.
  rewrite /pre_ordering /=.
  repeat (apply /andP; split) => //. (* uses H2 *)
  - rewrite Oeq -!cat_rcons in O.
    apply simple_upath_prefix in O.
    revert O. rewrite simple_upath_rcons => /andP[_ /orP[/eqP-F | O]].
    { contradict F. apply rcons_nil. }
    revert O. by rewrite /= !map_rcons !head_rcons !last_rcons.
  - by rewrite -Oso Oeq -cat_rcons map_cat head_cat !map_rcons !head_rcons.
  - apply H.
    destruct (e_of_t v); last by [].
    revert Ostart. by rewrite Oeq head_cat head_rcons.
  - destruct (e_of_t v); last by [].
    revert Ostart. by rewrite Oeq head_cat head_rcons.
  - by rewrite map_rcons last_rcons v_of_t_of_v_e.
  - by rewrite e_of_t_of_v_e last_rcons bridge_refl.
  - (* This is where we use the bungee jumping lemma. *)
    apply /forallP. move => [r R] /=.
    apply /implyP => /eqP-Rnc. apply /implyP => /eqP-Rso.
    apply /implyP => /andP[/andP[_ Ra] Rb]. apply/negPn/negP => ND.
    contradict C. apply /negP.
    rewrite e_of_t_of_v_e (head_eq _ e1) in Rb; last by destruct r.
    apply (@colored_bungee_jumping o o1 o2 e1 e2 r); try by [].
    + rewrite /= (head_eq _ (v_of_t v)) ?(last_eq _ (v_of_t v)) ?Oso ?Ota //; by destruct o.
    + by destruct o.
    + move => [ | ? ?] P Po Pc Pnb.
      { by rewrite bridge_refl in Pnb. }
      apply Omin; try by [].
      by destruct o.
    + rewrite v_of_t_of_v_e -Rso. by destruct r.
    + by destruct r.
    + by rewrite Oeq disjoint_sym -cat_rcons map_cat disjoint_cat disjoint_sym negb_andb ND.
Qed.

End OrderSimpleUpathBridge.

End BridgeTheory.

Section Yeo.

(** We consider an edge-colored multigraph G.
    There is no label on vertices (more accurately, they are all labeled by
    tt : unit) and the labels of edges belong to the type Colors,
    which has decidable equality (for we need to compare colors). *)
Variables (Colors : eqType) (G : graph unit Colors).

(** We instanciate previous notions. *)
(* Bridges - pairs of edges of the same color *)
Definition bridge : rel (edge G) :=
  fun e1 e2 => ((elabel e1) == (elabel e2)).

Lemma bridge_refl : reflexive bridge.
Proof. by rewrite /bridge. Qed.

Lemma bridge_sym : symmetric bridge.
Proof. by rewrite /bridge. Qed.

Lemma bridge_trans : transitive bridge.
Proof. by rewrite /bridge => ? ? ? /eqP-->. Qed.

Notation T :=
  [finType of (prod_choiceType G (option_choiceType (edge G)))].

Definition v_of_t (u : T) : G :=
  u.1.

Definition e_of_t (u : T) : option (edge G) :=
  u.2.

Definition Psource (u : T) (p: (@upath _ _ G)) : bool :=
  true.

Definition Ptarget (u : T) (p: (@upath _ _ G)) : bool :=
  true.

Lemma Psource_cat u v p q :
  Psource u p -> Ptarget v p -> Psource v q -> Psource u (p ++ q).
Proof. by []. Qed.

Lemma Ptarget_cat u v w p q :
  Psource u p -> Ptarget v p -> Psource v q -> Ptarget w q -> Ptarget w (p ++ q).
Proof. by []. Qed.

Definition vertexCol3_finPOrderType :=
  vertexCol2_finPOrderType bridge_refl bridge_sym bridge_trans v_of_t e_of_t Psource_cat Ptarget_cat.


Theorem Yeo : G -> correct bridge -> exists (v : G), splitting bridge v.
Proof.
  move => u' C.
(* Thanks to using an option type in our ordering, we start from no color,
   thus having a proof holding even in a graph without colors/edges. *)
  assert (u : vertexCol3_finPOrderType) by exact (u', None). clear u'.
  induction u as [[u ec] IH] using (well_founded_ind gt_wf).
  case/boolP: (splitting bridge u) => U.
  { by exists u. }
  enough (exists v, ((u, ec) : vertexCol3_finPOrderType) < v) as [v ?]
    by by apply (IH v).
  by apply (no_splitting_is_no_max (t_of_v_e := fun e _ _ _ => (utarget e, Some e.1))).
Qed.

End Yeo.

(* TODO everywhere - use case/boolP: b *)
(* TODO remove all useless by by in all files *)
(* TODO uwalk without s and t should simplify *)
(* TODO uwalk_cat; but with empty lists problem? *)
(* TODO mem_usource_utarget_simple_upath_internal to use more *)
(* TODO prevent simpl of upath_endpoint? *)
(* TODO general lemma for uwalk last? *)
