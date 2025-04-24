(* Extension for [mgraph] of the library GraphTheory
   In an acyclic mgraph, there is at most one trail between two vertices.
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

(* In an acyclic graph (where we removed only edges), there is at most one trail between two vertices. *)
(* Proof:
  By induction, we can assume ep :: p and eq :: q differ on their first edges.
  Then from p ++ rev q one gets a trail r from the target of ep to the target of eq (this is the
  part where we need the injectivity of the coloring).
  Remark that q does not contain ep (helper lemma). Otherwise, (eq ++ q) would go back to s, by
  following q until reaching ep (ep being in this prefix of q or not according to signs). This
  would yield a non-trivial cycle, contradicting acyclicity. Similarly, p does not contain eq.
  Thus, r does not contain ep nor eq, as it is contained in the walk p ++ rev q.
  But then, ep ++ r ++ eq is a non-empty cycle, a contradiction.
*)

Lemma uacyclic_unique_path_helper {Lv Le : Type} {G : graph Lv Le} {C : finType} (c : edge G -> option C) :
  uacyclic c ->
  forall (s t : G) (ep : edge G) bp eq q,
  well_colored_utrail c s t (eq :: q) -> endpoint (~~ bp) ep = s ->
  ep \notin [seq _e.1 | _e <- q].
Proof.
  move=> A s t ep bp eq q Q SP.
  apply/negPn => /in_map_fst[b In].
  move: In. rewrite in_elt_sub => /existsP/sigW[[n /= _] /eqP-Qeq].
  rewrite {}Qeq in Q.
  destruct (eq_or_eq_negb bp b); subst b.
  - change (eq :: take n q ++ (ep, bp) :: drop n.+1 q) with
      ((eq :: take n q) ++ [:: (ep, bp)] ++ drop n.+1 q) in Q.
    destruct (well_colored_utrail_sub Q) as [L _].
    replace (upath_target s (eq :: (take n q))) with s in L; last first.
    { transitivity (upath_source t ([:: (ep, bp)] ++ (drop n.+1 q)));
        first by rewrite /= /uendpoint SP.
      symmetry. apply uwalk_sub_middle, (well_colored_utrail_is_uwalk Q). }
    by specialize (A s (Sub _ L)).
  - replace (eq :: take n q ++ (ep, ~~ bp) :: drop n.+1 q) with
      (((eq :: take n q) ++ [:: (ep, ~~ bp)]) ++ drop n.+1 q) in Q
      by by rewrite cats1 cat_rcons.
    destruct (well_colored_utrail_sub Q) as [L _].
    rewrite /= map_cat /= last_cat /uendpoint /= SP in L.
    by specialize (A s (Sub _ L)).
Qed.

Lemma uacyclic_unique_path {Lv Le : Type} {G : graph Lv Le} {C : finType} (c : edge G -> option C) :
  {in ~: c @^-1 None &, injective c} -> uacyclic c ->
  forall (s t : G) p q,
  well_colored_utrail c s t p -> well_colored_utrail c s t q -> p = q.
Proof.
  move=> F A s t p q P Q.
  destruct (eq_comparable p q) as [ | Neq]; first by []. exfalso.
  move: s P q Q Neq. induction p as [ | [ep bp] p IHp] => s P q Q Neq;
    destruct q as [ | [eq bq] q]; first by [].
  - move: P. rewrite well_colored_utrail_of_nil => /eqP-?. subst t.
    by specialize (A _ (Sub _ Q)).
  - move: Q. rewrite well_colored_utrail_of_nil => /eqP-?. subst t.
    by specialize (A _ (Sub _ P)).
  - have : well_colored_utrail c s t ((ep, bp) :: p) by assumption.
    have : well_colored_utrail c s t ((eq, bq) :: q) by assumption.
    rewrite 2!well_colored_utrail_cons /uendpoint /=.
    move=> /andP[/andP[/andP[Q' /eqP-SQ] uQ] /eqP-nQ] /andP[/andP[/andP[P' /eqP-SP] uP] /eqP-nP].
    destruct (eq_comparable ep eq) as [ | Hneq]; [subst eq | ].
    + assert (bp = bq).
      { destruct (eq_comparable bp bq) as [ | Hneq]; trivial.
        contradict SQ. rewrite -SP.
        destruct bp, bq; try by [].
        - rewrite /uendpoint /=. by apply nesym, (uacyclic_loop A), nesym.
        - rewrite /uendpoint /=. by apply (uacyclic_loop A), nesym. }
      subst bq.
      move: Neq => /eqP. cbn => /nandP[/nandP[/eqP // | /eqP //] | /eqP-Neq].
      apply (IHp (endpoint bp ep) P' q Q' Neq).
    + clear Neq IHp.
      (* We extract a trail r from p ++ rev q. *)
      assert (WPQ : uwalk (endpoint bp ep) (endpoint bq eq) (p ++ upath_rev q))
        by by rewrite uwalk_cat uwalk_rev (uwalk_endpoint _ (well_colored_utrail_is_uwalk P'))
          (well_colored_utrail_is_uwalk P') (well_colored_utrail_is_uwalk Q').
      assert (NPQ : None \notin [seq c e.1 | e <- p ++ upath_rev q]).
      { rewrite map_cat mem_cat negb_orb (map_comp _ _ (upath_rev _)) upath_rev_fst
          map_rev in_rev -map_comp.
        by move: P' Q' => /andP[_ ->] /andP[_ ->]. }
      destruct (uconnected_simpl F WPQ NPQ) as [[r utrail_r] r_sub_pq].
      clear WPQ NPQ P' Q'. rewrite /= in r_sub_pq.
      (* Here ep ++ r ++ eq yields the contradictory cycle. *)
      enough (H : well_colored_utrail c (endpoint (~~ bq) eq) (endpoint (~~ bq) eq)
        ([:: (ep, bp)] ++ r ++ [:: (eq, ~~ bq)])) by by specialize (A _ (Sub _ H)).
      apply (@well_colored_utrail_concat _ _ _ _ _ _ (endpoint bp ep)).
      * rewrite SQ -SP /well_colored_utrail !in_cons /= orb_false_r /uendpoint /= !eq_refl /=. by apply/eqP.
      * apply (well_colored_utrail_concat utrail_r).
        { rewrite /well_colored_utrail !in_cons /= orb_false_r /uendpoint negb_involutive /= !eq_refl /=.
          by apply/eqP. }
        rewrite /upath_color_disjoint disjoint_sym disjoint_has /= orb_false_r.
        apply/mapP. move=> [[k b] K /= KEQ].
        assert (eq = k).
        { apply F; trivial.
          - rewrite !in_set. apply/eqP. by apply nesym.
          - rewrite !in_set. apply/eqP => FK.
            contradict nQ. by rewrite KEQ FK. }
        subst k. clear KEQ.
        move: r_sub_pq => /(_ _ K) {K}. rewrite mem_cat upath_rev_in => /orP[In | /= In].
        -- assert (Peq : eq \notin [seq e.1 | e <- p]) by apply (uacyclic_unique_path_helper A P SQ).
           contradict Peq. apply/negP/negPn. exact (map_f fst In).
        -- contradict uQ. apply/negP/negPn. exact (map_f _ In).
      * rewrite /upath_color_disjoint disjoint_has /= map_cat mem_cat /= in_cons in_nil !orb_false_r negb_orb.
        assert ((c ep) != (c eq)) as ->.
        { apply/eqP => FPQ.
          contradict Hneq.
          apply F; trivial; by rewrite !in_set; apply/eqP; apply nesym. }
        rewrite andb_true_r.
        apply/mapP. move=> [[k b] K /= KEQ].
        assert (ep = k).
        { apply F; trivial.
          - rewrite !in_set. apply/eqP. by apply nesym.
          - rewrite !in_set. apply/eqP => FK.
            contradict nP. by rewrite KEQ FK. }
        subst k. clear KEQ.
        move: r_sub_pq => /(_ _ K) {K}. rewrite mem_cat upath_rev_in => /orP[In | /= In].
        -- contradict uP. apply/negP/negPn. exact (map_f _ In).
        -- assert (Qep : ep \notin [seq e.1 | e <- q]) by apply (uacyclic_unique_path_helper A Q SP).
           contradict Qep. apply/negP/negPn. exact (map_f _ In).
Qed.
