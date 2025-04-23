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
  {in ~: f @^-1 None &, injective f} -> uacyclic f -> forall (s t : G) (p q : Supath f s t), p = q.
Proof.
  intros F A s t [p P] [q Q]. cbnb.
  destruct (eq_comparable p q) as [ | Neq]; trivial.
  exfalso.
  move: s P q Q Neq. induction p as [ | [ep bp] p IHp] => s P q Q Neq; destruct q as [ | [eq bq] q]; try by [].
  - revert P. rewrite /supath /= !andb_true_r => /eqP-?. subst t.
    by specialize (A _ (Sub _ Q)).
  - revert Q. rewrite /supath /= !andb_true_r => /eqP-?. subst t.
    by specialize (A _ (Sub _ P)).
  - assert (Pe : supath f s t ((ep, bp) :: p)) by assumption.
    assert (Qe : supath f s t ((eq, bq) :: q)) by assumption.
    revert P. rewrite /supath /= in_cons => /andP[/andP[/andP[/eqP-SP WP] /andP[uP UP]] /norP[/eqP-nP NP]].
    revert Q. rewrite /supath /= in_cons => /andP[/andP[/andP[/eqP-SQ WQ] /andP[uQ UQ]] /norP[/eqP-nQ NQ]].
    destruct (eq_comparable ep eq) as [ | Hneq]; [subst eq | ].
    + assert (bp = bq).
      { destruct (eq_comparable bp bq) as [ | Hneq]; trivial.
        contradict SQ. rewrite -SP.
        destruct bp, bq; try by [].
        - by apply nesym, (uacyclic_loop A), nesym.
        - by apply (uacyclic_loop A), nesym. }
      subst bq.
      revert Neq => /eqP. cbn. move => /nandP[/nandP[/eqP // | /eqP //] | /eqP-Neq].
      eapply (IHp (endpoint bp ep) _ q _ Neq). Unshelve. splitb. splitb.
    + clear Neq IHp.
      set pq : upath := p ++ upath_rev q.
      assert (WPQ : uwalk (endpoint bp ep) (endpoint bq eq) pq).
      { destruct (uwalk_endpoint WP) as [_ t_eq].
        by rewrite uwalk_cat uwalk_rev t_eq WP WQ. }
      assert (NPQ : None \notin [seq f e.1 | e <- pq]).
      { rewrite /pq map_cat mem_cat. splitb.
        by rewrite map_comp upath_rev_fst map_rev in_rev -map_comp. }
      destruct (uconnected_simpl F WPQ NPQ) as [PQ' HPQ'].
      assert (Eq : supath f (endpoint bq eq) (endpoint (~~bq) eq) [:: (eq, ~~bq)]).
      { rewrite /supath !in_cons /= orb_false_r /uendpoint negb_involutive. splitb. by apply /eqP. }
      set EQ : Supath _ _ _ := Sub _ Eq.
      assert (Ep : supath f (endpoint (~~bp) ep) (endpoint bp ep) [:: (ep, bp)]).
      { rewrite /supath !in_cons /= orb_false_r. splitb. by apply /eqP. }
      set EP : Supath _ _ _ := Sub _ Ep.
      assert (Qep : ep \notin [seq e.1 | e <- q]).
      { remember (ep \in [seq e.1 | e <- q]) as b eqn:In. symmetry in In.
        destruct b; trivial.
        apply in_map_fst in In. destruct In as [b In].
        rewrite in_elt_sub in In.
        revert In => /existsP/sigW[[n /= _] /eqP-Qeq].
        rewrite Qeq in Qe.
        destruct (eq_comparable b bp).
        - subst b.
          assert (Hr : (eq, bq) :: take n q ++ (ep, bp) :: drop n.+1 q =
            ((eq, bq) :: take n q) ++ [:: (ep, bp)] ++ drop n.+1 q).
          { by rewrite -(cat1s (ep, bp) (drop n.+1 q))
                       -(cat1s (eq, bq) ((take n q) ++ ([:: (ep, bp)] ++ (drop n.+1 q))))
                       -(cat1s (eq, bq) (take n q)) -!catA. }
          rewrite Hr {Hr} in Qe.
          destruct (supath_subKK Qe) as [L _].
          assert (Hr : (upath_target s ((eq, bq) :: (take n q))) = s).
          { transitivity (upath_source t ([:: (ep, bp)] ++ (drop n.+1 q))); last by rewrite /= SP.
            apply uwalk_sub_middle.
            by revert Qe => /andP[/andP[-> _] _]. }
          rewrite Hr {Hr} in L.
          specialize (A s (Sub _ L)).
          contradict A. cbnb.
        - assert (b = ~~bp) by by destruct b, bp.
          subst b.
          assert (Hr : (eq, bq) :: take n q ++ (ep, ~~ bp) :: drop n.+1 q =
            (((eq, bq) :: take n q) ++ [:: (ep, ~~ bp)]) ++ drop n.+1 q).
          { by rewrite -(cat1s (ep, ~~ bp) (drop n.+1 q))
                       -(cat1s (eq, bq) ((take n q) ++ ([:: (ep, ~~ bp)] ++ (drop n.+1 q))))
                       -(cat1s (eq, bq) (take n q)) -!catA. }
          rewrite Hr {Hr} in Qe.
          destruct (supath_subKK Qe) as [L _].
          rewrite /uendpoint /= in SP.
          rewrite /= map_cat /= last_cat /uendpoint /= SP in L.
          specialize (A s (Sub _ L)).
          contradict A. cbnb. }
      assert (Peq : eq \notin [seq e.1 | e <- p]).
      (* TODO same as Qep above: possible to do the 2 in 1 with a wlog/forall? *)
      { remember (eq \in [seq e.1 | e <- p]) as b eqn:In. symmetry in In.
        destruct b; trivial.
        apply in_map_fst in In. destruct In as [b In].
        rewrite in_elt_sub in In.
        revert In => /existsP/sigW[[n /= _] /eqP-Peq].
        rewrite Peq in Pe.
        destruct (eq_comparable b bq).
        - subst b.
          assert (Hr : (ep, bp) :: take n p ++ (eq, bq) :: drop n.+1 p =
            ((ep, bp) :: take n p) ++ [:: (eq, bq)] ++ drop n.+1 p).
          { by rewrite -(cat1s (eq, bq) (drop n.+1 p))
                       -(cat1s (ep, bp) ((take n p) ++ ([:: (eq, bq)] ++ (drop n.+1 p))))
                       -(cat1s (ep, bp) (take n p)) -!catA. }
          rewrite Hr {Hr} in Pe.
          destruct (supath_subKK Pe) as [L _].
          assert (Hr : (upath_target s ((ep, bp) :: (take n p))) = s).
          { transitivity (upath_source t ([:: (eq, bq)] ++ (drop n.+1 p))); last by rewrite /= SQ.
            apply uwalk_sub_middle.
            by revert Pe => /andP[/andP[-> _] _]. }
          rewrite Hr {Hr} in L.
          specialize (A s (Sub _ L)).
          contradict A. cbnb.
        - assert (b = ~~bq) by by destruct b, bq.
          subst b.
          assert (Hr : (ep, bp) :: take n p ++ (eq, ~~ bq) :: drop n.+1 p =
            (((ep, bp) :: take n p) ++ [:: (eq, ~~ bq)]) ++ drop n.+1 p).
          { by rewrite -(cat1s (eq, ~~ bq) (drop n.+1 p))
                       -(cat1s (ep, bp) ((take n p) ++ ([:: (eq, ~~ bq)] ++ (drop n.+1 p))))
                       -(cat1s (ep, bp) (take n p)) -!catA. }
          rewrite Hr {Hr} in Pe.
          destruct (supath_subKK Pe) as [L _].
          rewrite /uendpoint /= in SQ.
          rewrite /= map_cat /= last_cat /uendpoint /= SQ in L.
          specialize (A s (Sub _ L)).
          contradict A. cbnb. }
      assert (DQ : upath_disjoint f (val PQ') (val EQ)).
      { rewrite /upath_disjoint disjoint_sym disjoint_has /= orb_false_r.
        apply /mapP. move => [[k b] K /= KEQ].
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
        revert HPQ'. rewrite /pq mem_cat upath_rev_in => /orP[In | In].
        - contradict Peq. apply /negP/negPn.
          replace eq with ((eq, b).1) by trivial.
          by apply map_f.
        - contradict uQ. apply /negP/negPn.
          replace eq with ((eq, ~~b).1) by trivial.
          by apply (map_f (fun e => f e.1)). }
      set PQ'Q := supath_cat DQ.
      assert (DP : upath_disjoint f (val EP) (val PQ'Q)).
      { rewrite /upath_disjoint disjoint_has /= map_cat mem_cat /= in_cons in_nil !orb_false_r.
        assert ((f ep) == (f eq) = false) as ->.
        { apply /eqP => FPQ.
          contradict Hneq.
          apply F; trivial.
          all: by rewrite !in_set; apply /eqP; apply nesym. }
        rewrite orb_false_r.
        apply /mapP. move => [[k b] K /= KEQ].
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
      set PPQ'Q := supath_cat DP.
      assert (Nnil : val PPQ'Q <> [::]) by by [].
      rewrite /uendpoint in SP SQ.
      clearbody PPQ'Q. move: PPQ'Q Nnil. rewrite SP SQ => PPQ'Q Nnil.
      contradict Nnil.
      by rewrite (A _ PPQ'Q).
Qed.
(* Proof:
  By induction, we can assume P and Q differ on their first edges, respectively ep and eq.
  We denote by p and q the rest of P and Q respectively.
  With p and q, we get a path pq from the target of ep to the target of eq (this is the part where we need
  the infectivity of f).
  Remark that q does not contain ep. Otherwise, (eq ++ q) would go back to s, by following q until
  reaching ep (ep being in q or not according to signs). This would yield a non-trivial cycle,
  contradicting acyclicity.
  Similarly, p does not contain eq.
  Thus, the path pq does not contain ep nor eq, as it is contain in the walk p ++ q.
  But then, ep ++ pq ++ eq give us a non-trivial cycle, a contradiction
*)
