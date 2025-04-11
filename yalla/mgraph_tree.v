(* Extension for [mgraph] of the library GraphTheory
   In an acyclic mgraph, there is at most one simple path between two vertices.
 *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From GraphTheory Require Import preliminaries mgraph.
From Yalla Require Import mll_prelim graph_more upath supath.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(* In an acyclic graph (where we removed only edges), there is at most one path between two vertices *)
Lemma uacyclic_unique_path {Lv Le : Type} {G : graph Lv Le} {I : finType} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f -> forall (s t : G) (p q : Supath f),
  upath_source s (val p) = s -> upath_source s (val q) = s ->
  upath_target s (val p) = t -> upath_target s (val q) = t ->
  p = q.
(* Proof:
  By induction, we can assume p and q differ on their first edges, respectively ep and eq.
  We denote by p' and q' the rest of p and q respectively.
  With p' and q', we get a path pq from the target of ep to the target of eq (this is the part where we need
  the injectivity of f).
  Remark that q' does not contain ep. Otherwise, (eq ++ q') would go back to s, by following q' until
  reaching ep (ep being in q' or not according to signs). This would yield a non-trivial cycle,
  contradicting acyclicity.
  Similarly, p' does not contain eq.
  Thus, the path pq does not contain ep nor eq, as it is contained in the walk p' ++ q'.
  But then, ep ++ pq ++ eq give us a non-trivial cycle, a contradiction.
*)
(* TODO better names + simplify this proof *)
Proof.
  move=> F A s t [p P] [q Q] /= source_p source_q target_p target_q.
  apply val_inj. rewrite /=.
  destruct (eq_comparable p q) as [ | Neq]; first by trivial. exfalso.
  move: s P source_p target_p q Q source_q target_q Neq.
  induction p as [ | [ep bp] p IHp] => s P source_p target_p q Q source_q target_q Neq;
  destruct q as [ | [eq bq] q]; first by [].
  - subst t.
    move: A => /(_ s (Sub _ Q)) /=.
    by move: source_q target_q => /= -> -> /(_ erefl).
  - subst t.
    move: A => /(_ s (Sub _ P)) /=.
    by move: source_p target_q => /= -> -> /(_ erefl).
  - assert (Pe : supath f ((ep, bp) :: p)) by assumption.
    assert (Qe : supath f ((eq, bq) :: q)) by assumption.
    move: P. rewrite /supath /= in_cons => /andP[/andP[/andP[/eqP-SP WP] /andP[uP UP]] /norP[/eqP-nP NP]].
    move: Q. rewrite /supath /= in_cons => /andP[/andP[/andP[/eqP-SQ WQ] /andP[uQ UQ]] /norP[/eqP-nQ NQ]].
    destruct (eq_comparable ep eq) as [ | Hneq]; [subst eq | ].
    + destruct (eq_or_eq_negb bp bq); subst bq.
      * move: Neq => /eqP. cbn. move=> /nandP[/nandP[/eqP // | /eqP //] | /eqP-Neq].
        eapply (IHp (endpoint bp ep) _ _ _ q _ _ _ Neq). Unshelve. all: by [] || (by symmetry) || splitb.
      * move: source_p source_q => /= <- loop_ep.
        contradict loop_ep.
        destruct bp; [apply nesym | ]; by apply (uacyclic_loop A), nesym.
    + clear Neq IHp.
      set pq : upath := p ++ upath_rev q.
      assert (WPQ : uwalk pq).
      { rewrite uwalk_cat uwalk_rev WP WQ /=.
        destruct p; first by [].
        destruct q; first by rewrite orb_true_r.
        simpl. apply/orP. right. apply/forallP => ?.
        move: target_p target_q.
        by rewrite map_rcons head_rcons map_usource_upath_rev head_rev /= negb_involutive => -> ->. }
      assert (NPQ : None \notin [seq f e.1 | e <- pq]).
      { rewrite /pq map_cat mem_cat. splitb.
        by rewrite map_comp upath_rev_fst map_rev in_rev -map_comp. }
      destruct (uconnected_simpl s F WPQ NPQ) as [PQ' [source_pq [target_pq HPQ']]].
      assert (Eq : supath f [:: (eq, ~~bq)]).
      { rewrite supath_cons /= eq_refl /=. by apply/eqP. }
      set EQ : Supath _ := Sub _ Eq.
      assert (Ep : supath f [:: (ep, bp)]).
      { rewrite supath_cons /= eq_refl /=. by apply/eqP. }
      set EP : Supath _ := Sub _ Ep.
      assert (Qep : ep \notin [seq e.1 | e <- q]).
      { case/boolP : (ep \in [seq e.1 | e <- q]) => //= In.
        apply in_map_fst in In as [b In].
        rewrite in_elt_sub in In.
        move: In => /existsP/sigW[[n /= _] /eqP-Qeq].
        rewrite Qeq in Qe.
        destruct (eq_or_eq_negb bp b); subst b.
        - assert (Hr : (eq, bq) :: take n q ++ (ep, bp) :: drop n.+1 q =
            ((eq, bq) :: take n q) ++ [:: (ep, bp)] ++ drop n.+1 q).
          { by rewrite -(cat1s (ep, bp) (drop n.+1 q))
                       -(cat1s (eq, bq) ((take n q) ++ ([:: (ep, bp)] ++ (drop n.+1 q))))
                       -(cat1s (eq, bq) (take n q)) -!catA. }
          rewrite {}Hr in Qe.
          destruct (supath_subKK Qe) as [L _].
          assert (Hr : (upath_target s ((eq, bq) :: (take n q))) = s).
          { transitivity (upath_source t ([:: (ep, bp)] ++ (drop n.+1 q))); last by rewrite -source_p /=.
            simpl in *.
            move: Qe => /andP[/andP[Qe _] _].
            move: Qe. rewrite /= uwalk_cat /= map_cat head_cat /=.
            move=> /andP[_ /andP[_ /orP[/orP[/eqP-H | //] | ]]].
            - destruct n; last by destruct q.
              move: SQ. by rewrite Qeq take0 /=.
            - by move=> /forallP/(_ (endpoint bq eq))/eqP-->. }
          move: A => /(_ s (Sub _ L)).
          by rewrite {}Hr /= -source_q /= => /(_ erefl).
        - assert (Hr : (eq, bq) :: take n q ++ (ep, ~~ bp) :: drop n.+1 q =
            (((eq, bq) :: take n q) ++ [:: (ep, ~~ bp)]) ++ drop n.+1 q).
          { by rewrite -(cat1s (ep, ~~ bp) (drop n.+1 q))
                       -(cat1s (eq, bq) ((take n q) ++ ([:: (ep, ~~ bp)] ++ (drop n.+1 q))))
                       -(cat1s (eq, bq) (take n q)) -!catA. }
          rewrite {}Hr in Qe.
          destruct (supath_subKK Qe) as [L _].
          move: A => /(_ s (Sub _ L)).
          rewrite /= map_cat /= last_cat /=.
          by move: source_p source_q => /= -> -> /(_ erefl). }
      assert (Peq : eq \notin [seq e.1 | e <- p]).
      (* TODO same as Qep above: possible to do the 2 in 1 with a wlog/forall? *)
      { case/boolP : (eq \in [seq e.1 | e <- p]) => //= In.
        apply in_map_fst in In as [b In].
        rewrite in_elt_sub in In.
        revert In => /existsP/sigW[[n /= _] /eqP-Peq].
        rewrite Peq in Pe.
        destruct (eq_or_eq_negb bq b); subst b.
        - assert (Hr : (ep, bp) :: take n p ++ (eq, bq) :: drop n.+1 p =
            ((ep, bp) :: take n p) ++ [:: (eq, bq)] ++ drop n.+1 p).
          { by rewrite -(cat1s (eq, bq) (drop n.+1 p))
                       -(cat1s (ep, bp) ((take n p) ++ ([:: (eq, bq)] ++ (drop n.+1 p))))
                       -(cat1s (ep, bp) (take n p)) -!catA. }
          rewrite {}Hr in Pe.
          destruct (supath_subKK Pe) as [L _].
          assert (Hr : (upath_target s ((ep, bp) :: (take n p))) = s).
          { transitivity (upath_source t ([:: (eq, bq)] ++ (drop n.+1 p))); last by rewrite -source_q /=.
            simpl in *.
            move: Pe => /andP[/andP[Pe _] _].
            move: Pe. rewrite /= uwalk_cat /= map_cat head_cat /=.
            move=> /andP[_ /andP[_ /orP[/orP[/eqP-H | //] | ]]].
            - destruct n; last by destruct p.
              move: SP. by rewrite Peq take0 /=.
            - by move=> /forallP/(_ (endpoint bp ep))/eqP-->. }
          move: A => /(_ s (Sub _ L)).
          by rewrite {}Hr /= -source_p /= => /(_ erefl).
        - assert (Hr : (ep, bp) :: take n p ++ (eq, ~~ bq) :: drop n.+1 p =
            (((ep, bp) :: take n p) ++ [:: (eq, ~~ bq)]) ++ drop n.+1 p).
          { by rewrite -(cat1s (eq, ~~ bq) (drop n.+1 p))
                       -(cat1s (ep, bp) ((take n p) ++ ([:: (eq, ~~ bq)] ++ (drop n.+1 p))))
                       -(cat1s (ep, bp) (take n p)) -!catA. }
          rewrite {}Hr in Pe.
          destruct (supath_subKK Pe) as [L _].
          move: A => /(_ s (Sub _ L)).
          rewrite /= map_cat /= last_cat /=.
          by move: source_p source_q => /= -> -> /(_ erefl). }
      (* TODO use supath_cons instead. *)
      assert (DQ : upath_disjoint f (val PQ') (val EQ)).
      { rewrite /upath_disjoint disjoint_sym disjoint_has /= orb_false_r.
        apply/mapP. move=> [[k b] K /= KEQ].
        specialize (HPQ' _ K). clear K.
        assert (eq = k).
        { apply F; trivial.
          - rewrite !in_set. apply /eqP. by apply nesym.
          - rewrite !in_set. apply /eqP => FK.
            contradict NPQ. apply /negP/negPn.
            rewrite -FK.
            replace k with ((k, b).1) by trivial.
            by apply (map_f (fun e => f e.1)). }
        subst k. clear KEQ.
        move: HPQ'. rewrite /pq mem_cat upath_rev_in => /orP[In | In].
        - contradict Peq. apply/negP/negPn.
          replace eq with ((eq, b).1) by trivial.
          by apply map_f.
        - contradict uQ. apply/negP/negPn.
          replace eq with ((eq, ~~b).1) by trivial.
          by apply (map_f (fun e => f e.1)). }
      assert (PQ'EQ : supath f (\val PQ' ++ \val EQ)).
      { case/boolP: (p ++ q == [::]).
        - rewrite cat_nil => /andP[/eqP-? /eqP-?]. subst p q pq.
          simpl in *.
          destruct PQ' as [pq' PQ'].
          assert (pq' = [::]).
          { destruct pq' as [ | e' ?]; first by [].
            move: HPQ' => /= /(_ e'). by rewrite in_cons eq_refl /= => /(_ is_true_true). }
          by subst pq'.
        - move=> ?.
          apply (@supath_catK _ _ _ _ _ (upath_source s pq)); last by assumption.
          rewrite target_pq /pq /= negb_involutive map_cat last_cat map_utarget_upath_rev last_rev SQ.
          destruct q; last by [].
          simpl in *. rewrite target_q -target_p.
          by destruct p. }
      set PQ'Q : Supath f := Sub _ PQ'EQ.
      assert (DP : upath_disjoint f (val EP) (val PQ'Q)).
      { rewrite /upath_disjoint disjoint_has /= map_cat mem_cat /= in_cons in_nil !orb_false_r.
        assert ((f ep) == (f eq) = false) as ->.
        { apply /eqP => FPQ.
          contradict Hneq.
          apply F; trivial.
          all: by rewrite !in_set; apply /eqP; apply nesym. }
        rewrite orb_false_r.
        apply/mapP. move => [[k b] K /= KEQ].
        specialize (HPQ' _ K). clear K.
        assert (ep = k).
        { apply F; trivial.
          - rewrite !in_set. apply /eqP. by apply nesym.
          - rewrite !in_set. apply /eqP => FK.
            contradict NPQ. apply /negP/negPn.
            rewrite -FK.
            replace k with ((k, b).1) by trivial.
            by apply (map_f (fun e => f e.1)). }
        subst k. clear KEQ.
        revert HPQ'. rewrite /pq mem_cat upath_rev_in => /orP[In | In].
        - contradict uP. apply /negP/negPn.
          replace ep with ((ep, b).1) by trivial.
          by apply (map_f (fun e => f e.1)).
        - contradict Qep. apply /negP/negPn.
          replace ep with ((ep, ~~b).1) by trivial.
          by apply map_f. }
      assert (bp_ep_neq_bq_eq : endpoint bp ep <> endpoint bq eq).
      { move=> ?.
        assert (C : supath f [:: (ep, bp) ; (eq, ~~bq)]).
        { rewrite !supath_cons supath_nilK /= in_cons in_nil negb_orb negb_involutive eq_refl /=.
          splitb; apply/eqP; trivial.
          move=> f_ep_eq_f_eq.
          contradict Hneq.
          apply F; trivial.
          - rewrite in_set -mem_preim eq_sym. by apply/eqP.
          - rewrite in_set -mem_preim eq_sym. by apply/eqP. }
        move: A => /(_ (endpoint (~~ bp) ep) (Sub _ C)).
        by move: source_p source_q => /= -> -> /(_ Logic.eq_refl). }
      assert (val PQ' <> [::]).
      { destruct PQ' as [[ | ? ?] ?]; last by [].
        contradict bp_ep_neq_bq_eq.
        move: target_pq SP SQ. rewrite /pq upath_source_cat upath_target_cat !upath_endpoint_rev /=.
        destruct p, q; simpl in *.
        - by rewrite target_p -target_q.
        - by rewrite target_q -target_p => <-.
        - by rewrite target_p -target_q => ->.
        - by move=> -> -> ->. }
      assert (cyclic : upath_target (endpoint bp ep) (\val EP) = upath_source (endpoint bp ep) (\val PQ'Q)).
      { move: source_pq.
        rewrite /PQ'Q !SubK /pq !upath_source_cat /= SP negb_involutive map_usource_upath_rev head_rev.
        destruct PQ' as [[ | ? ?] ?] => //= H1. rewrite H1.
        destruct p => //=.
        move : target_p target_q => /= H2 H3. rewrite H2 -H3.
        destruct q => //=.
        contradict bp_ep_neq_bq_eq.
        by rewrite H2 -H3. }
      assert (Nnil : supath_cat cyclic DP <> supath_nil f) by by [].
      contradict Nnil.
      apply (A (endpoint bp ep)).
      rewrite /= map_cat last_cat /=.
      by move: source_p source_q => /= -> ->.
Qed.
