(* Simple undirected path in a directed multigraph *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From HB Require Import structures.
From GraphTheory Require Import preliminaries mgraph.
From Yalla Require Import mll_prelim graph_more upath.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section SimpleUpath.

Variables (Lv Le : Type) (G : graph Lv Le).

(** Simple path - no repetition of vertex nor edge, except target may be source *)
Definition simple_upath (p : @upath _ _ G) : bool :=
  (uwalk p) &&
  match p with | [::] => true | e :: _ =>
  ((upath_target (utarget e) p \notin [seq usource e | e <- p]) ||
  (upath_target (utarget e) p == upath_source (utarget e) p))
  end &&
  uniq [seq e.1 | e <- p] && uniq [seq usource e | e <- p].

Lemma uwalk_of_simple_upath (p : upath) :
  simple_upath p -> uwalk p.
Proof. by move=> /andP[/andP[/andP[-> _] _] _]. Qed.

Lemma uniq_fst_simple_upath (p : upath) :
  simple_upath p -> uniq [seq e.1 | e <- p].
Proof. by move=> /andP[/andP[_ ->] _]. Qed.

Lemma uniq_usource_simple_upath (p : upath) :
  simple_upath p -> uniq [seq usource e | e <- p].
Proof. by move=> /andP[_ ->]. Qed.
(* TODO some lemmas like those and then Opaque simple_upath? *)

(** The type of simple upaths in a graph is a finite type. *)
Lemma simple_upath_size (p : upath) :
  simple_upath p -> size p < S #|edge G|.
Proof.
  move=> P.
  apply uniq_fst_simple_upath in P.
  move: P => /card_uniqP.
  rewrite size_map => <-.
  exact: max_card.
Qed.

Definition Simple_upath := {p : upath | simple_upath p}.

Definition Simple_upath_tuple (p : Simple_upath) : {n : 'I_(S #|edge G|) & n.-tuple (edge G * bool)} :=
  let (p, Up) := p in existT _ (Ordinal (simple_upath_size Up)) (in_tuple p).

Definition tuple_Simple_upath (m : {n : 'I_(S #|edge G|) & n.-tuple (edge G * bool)}) : option Simple_upath :=
  let (_, p) := m in match boolP (simple_upath p) with
  | AltTrue P => Some (Sub (val p) P)
  | AltFalse _ => None
  end.

Lemma Simple_upath_tupleK :
  pcancel Simple_upath_tuple tuple_Simple_upath.
Proof.
  move=> [p P] /=.
  case: {-}_ / boolP; last by rewrite P.
  move=> P'. by rewrite (bool_irrelevance P' P).
Qed.

Set Warnings "-redundant-canonical-projection". (* to ignore warnings of already canonical *)
HB.instance Definition _ := Countable.on Simple_upath. (* To prevent delta-expansion *)
HB.instance Definition _ : isFinite Simple_upath := PCanIsFinite Simple_upath_tupleK.
Set Warnings "redundant-canonical-projection".


(** Many results on simple upath *)

Lemma simple_upath_nil :
  simple_upath [::].
Proof. by []. Qed.

Lemma simple_upath_edge e :
  simple_upath [:: e].
Proof. by rewrite /simple_upath /= !eq_refl in_cons in_nil orb_false_r orNb. Qed.

(* e :: p is a simple path if and only if p is a simple path starting from the
   target of e, not containing the source of e except possibly as its target,
   and p is non-cyclic or empty. *)
Lemma simple_upath_cons e (p : upath) :
  simple_upath (e :: p) =
  (simple_upath p) &&
  (if p is a :: _ then e.1 != a.1 else true) &&
  (utarget e == upath_source (utarget e) p) && (usource e \notin [seq usource a | a <- p]) &&
  ((p == [::]) || (upath_source (utarget e) p != upath_target (utarget e) p)).
Proof.
  destruct p as [ | a p].
  { by rewrite simple_upath_edge eq_refl. }
  rewrite /simple_upath /= !in_cons !negb_orb !(eq_sym (usource a)) /=.
  case/boolP: (utarget e == usource a) => /eqP-TESA; rewrite ?andb_false_r //=.
  case/boolP: (usource e == usource a) => SESA; rewrite ?andb_false_r //=.
  case/boolP: (usource e \in [seq usource f | f <- p]) => Es; rewrite ?andb_false_r //=.
  case/boolP: (usource a \in [seq usource f | f <- p]) => As; rewrite ?andb_false_r //=.
  assert (e.1 \notin [seq e.1 | e <- p]) as ->.
  { apply/mapP. move=> [[? b] /= b_in_p ?]. subst.
    destruct (eq_or_eq_negb e.2 b); subst b.
    - rewrite -surjective_pairing in b_in_p.
      contradict Es. apply/negP/negPn.
      by apply (map_f (fun e => usource e)).
    - contradict As. apply/negP/negPn.
      rewrite -TESA -usource_reversed.
      by apply (map_f (fun e => usource e)). }
  case/boolP: (last (utarget a) [seq utarget f | f <- p] == usource e) => [/eqP--> | _] /=.
  - rewrite Es SESA. lia.
  - lia.
Qed.

Lemma simple_upath_rcons e (p : upath) :
  simple_upath (rcons p e) =
  (simple_upath p) &&
  (if p is a :: _ then e.1 != (last a p).1 else true) &&
  (usource e == upath_target (usource e) p) && (utarget e \notin [seq utarget a | a <- p]) &&
  ((p == [::]) || (upath_source (utarget e) p != upath_target (utarget e) p)).
Proof.
  induction p as [ | a p IHp].
  { by rewrite simple_upath_edge eq_refl. }
  rewrite rcons_cons !simple_upath_cons {}IHp /= !map_rcons !mem_rcons !in_cons
    head_rcons last_rcons !negb_orb (eq_sym (head _ _) (utarget e)).
  replace (rcons p e == [::]) with false by (symmetry; apply /eqP; apply rcons_nil).
  destruct p as [ | b p] => /=.
  - rewrite !eq_refl /= eq_sym !andb_true_r !(eq_sym (usource e)).
    case/boolP: (utarget a == usource e); rewrite ?andb_false_r //= => /eqP-->.
    lia.
  - case/boolP: (usource e == last (utarget b) [seq utarget f | f <- p]);
      rewrite ?andb_false_r //= => /eqP-->.
    case/boolP: (utarget a == usource b); rewrite ?andb_false_r //= => /eqP-->.
    lia.
Qed.

Lemma simple_upath_rev (p : upath) :
  simple_upath (upath_rev p) = simple_upath p.
Proof.
  induction p as [ | e p IH]; first by [].
  rewrite simple_upath_cons /= simple_upath_rcons upath_rev_nil {}IH /=
    negb_involutive map_usource_upath_rev map_utarget_upath_rev
    !mem_rev head_rev !last_rev (eq_sym (last _ _)).
  destruct p as [ | b p] => //=.
  enough (match rcons (upath_rev p) (reversed b) with
    | [::] => true | a :: _ => e.1 != (last a (rcons (upath_rev p) (reversed b))).1
    end = (e.1 != b.1)) as -> by reflexivity.
  destruct (rcons (upath_rev p) (reversed b)) eqn:Hr.
  - contradict Hr. apply rcons_nil.
  - by rewrite -Hr last_rcons.
Qed.

Lemma uniq_utarget_simple_upath (p : upath) :
  simple_upath p ->
  uniq [seq utarget e | e <- p].
Proof.
  rewrite -(upath_rev_inv p) simple_upath_rev map_utarget_upath_rev rev_uniq.
  apply uniq_usource_simple_upath.
Qed.

Lemma simple_upath_suffix (p q : upath) :
  simple_upath (p ++ q) -> simple_upath q.
Proof.
  move: q. induction p as [ | e p IH] => q //.
  rewrite cat_cons simple_upath_cons cat_nil => /andP[/andP[/andP[/andP[? _] _] _] _].
  by apply IH.
Qed.

Lemma simple_upath_prefix (p q : upath) :
  simple_upath (p ++ q) -> simple_upath p.
Proof.
  rewrite -(upath_rev_inv (p ++ q)) simple_upath_rev upath_rev_cat => S.
  apply simple_upath_suffix in S.
  by rewrite simple_upath_rev in S.
Qed.

Lemma simple_upath_target_in_sources (v : G) (p : upath) :
  simple_upath p -> upath_target v p \in [seq usource e | e <- p] ->
  upath_source v p = upath_target v p.
Proof.
  move: v. case/lastP: p => [// | p e] v.
  rewrite simple_upath_rcons /= !map_rcons last_rcons head_rcons mem_rcons in_cons.
  move=> /andP[/andP[/andP[/andP[S _] /eqP-Eso] Etnin] /orP[/eqP-? | /eqP-Pcyc]].
  { subst p. by rewrite /= in_nil orb_false_r => /eqP-->. }
  move=> /orP[/eqP-F | Etin].
  { contradict Etnin. apply/negP/negPn.
    rewrite {}F {}Eso.
    apply mem3_last. by destruct p. }
  have: utarget e \in rcons [seq usource e | e <- p] (upath_target v p)
    by by rewrite in_rcons Etin orb_true_r.
  rewrite (mem_usource_utarget_uwalk _ (@uwalk_of_simple_upath _ S)) in_cons /=.
  move=> /orP[/eqP--> | Etin'].
  - by destruct p.
  - by rewrite Etin' in Etnin.
Qed.

Lemma simple_upath_source_in_targets (v : G) (p : upath) :
  simple_upath p -> upath_source v p \in [seq utarget e | e <- p] ->
  upath_source v p = upath_target v p.
Proof.
  move => simple_p source_p_in_targets_p.
  rewrite -(upath_rev_inv p) upath_endpoint_rev [in RHS]upath_endpoint_rev.
  symmetry. apply simple_upath_target_in_sources.
  - by rewrite simple_upath_rev.
  - by rewrite upath_endpoint_rev map_usource_upath_rev mem_rev.
Qed.

Lemma mem_usource_utarget_simple_upath_internal (p: upath) :
  simple_upath p -> forall (v : G),
  (v \in [seq usource e | e <- p]) && (v != upath_source v p) =
  (v \in [seq utarget e | e <- p]) && (v != upath_target v p).
Proof.
  induction p as [ | e p IH]; first by [].
  rewrite simple_upath_cons.
  case/boolP: (p == [::]) => /eqP-Pnil /=.
  { subst p => _ ?. by rewrite /= !in_cons !in_nil !orb_false_r !andbN. }
  move=> /andP[/andP[/andP[/andP[Ps E1] /eqP-Et] Es] Pnc] v.
  specialize (IH Ps v).
  rewrite /= !in_cons !andb_orb_distrib_l andbN /= (last_eq (utarget e) v); last by destruct p.
  rewrite -{}IH.
  case/boolP: (v == utarget e) => /eqP-Vte /=.
  - subst v. rewrite Et.
    replace (last (head _ _) _) with (last (utarget e) [seq utarget e | e <- p])
      by by destruct p.
    rewrite Pnc mem3_head /=; last by destruct p.
    apply/eqP => F. contradict Es. apply/negP/negPn.
    rewrite -F mem3_head //. by destruct p.
  - case/boolP: (v \in [seq usource e | e <- p]) => V //=.
    transitivity true; [ | symmetry].
    + apply/eqP => ?. subst v. by rewrite V in Es.
    + rewrite (head_eq _ (utarget e)); last by destruct p.
      rewrite -Et. by apply/eqP.
Qed.

Lemma simple_upath_cat (p q : upath) :
  simple_upath p -> simple_upath q ->
  (if q is eq :: _ then upath_target (usource eq) p == upath_source (usource eq) q
    else true) ->
  [disjoint [seq usource e | e <- p] & [seq usource e | e <- q]] ->
  (if q is eq :: _ then upath_target (usource eq) q \notin [seq utarget e | e <- p]
    else true) ->
  (if q is eq :: _ then if p is ep :: _ then (last ep p).1 != eq.1
    else true else true) ->
  simple_upath (p ++ q).
Proof.
  move: p. induction q as [ | eq q IH] => p.
  { by rewrite cats0. }
  rewrite simple_upath_cons -cat_rcons disjoint_sym /= disjoint_cons.
  move=> Ps /andP[/andP[/andP[/andP[Qs Eq1nin] /eqP-Eqta] Eqsonin]
    /orP[/eqP-? | /eqP-Qcyc]].
  - subst q. rewrite {IH} cats0 simple_upath_rcons Ps disjoint_nil andb_true_r /=.
    move=> {Eqsonin Eqta Eq1nin Qs} Eqso Eqsonin Eqtanin Eq1neq.
    rewrite Eqtanin -(eqP Eqso) andb_true_r.
    repeat (apply /andP; split); trivial.
    + destruct p; first by []. by rewrite eq_sym.
    + by destruct p.
    + destruct p => //=.
      apply/eqP => HL.
      contradict Eqsonin. apply/negP/negPn.
      by rewrite -(eqP Eqso) /= -HL in_cons eq_refl.
  - move=> Eqso /andP[Eqsonin' D] Lnin Eq1neq.
    apply IH; clear IH; trivial.
    + rewrite simple_upath_rcons Ps /=.
      repeat (apply /andP; split); trivial.
      * destruct p; by rewrite // eq_sym.
      * rewrite -(eqP Eqso). by destruct p.
      * rewrite Eqta.
        enough (E : head (utarget eq) [seq usource e | e <- q]
          \notin upath_source (usource eq) p :: [seq utarget e | e <- p]).
        { revert E. by rewrite in_cons negb_orb => /andP[_ ->]. }
        rewrite -(mem_usource_utarget_uwalk _ (uwalk_of_simple_upath Ps))
          in_rcons negb_orb /= (eqP Eqso).
        destruct q; first by [].
        move: Eqsonin D. by rewrite /= in_cons negb_orb eq_sym disjoint_cons => /andP[-> _] /andP[-> _].
      * destruct p; first by []. simpl in *.
        rewrite (eqP Eqso).
        move: Eqsonin'. by rewrite /= in_cons negb_orb eq_sym => /andP[-> _].
    + destruct q; first by [].
      by rewrite /= map_rcons last_rcons Eqta.
    + by rewrite map_rcons disjoint_rcons Eqsonin disjoint_sym D.
    + destruct q; first by [].
      rewrite /= map_rcons mem_rcons in_cons negb_orb Eqta Lnin andb_true_r eq_sym.
      by apply /eqP.
    + destruct p, q; by rewrite //= last_rcons.
Qed.

Lemma disjoint_or_edge (o r : upath) :
  [seq utarget e | e <- o] =i [seq usource e | e <- o] ->
  simple_upath r ->
  (forall u, u \in [seq utarget e | e <- r] ->
    u \in [seq usource e | e <- o] -> u = upath_target u r) ->
  forall e, e \in [seq a.1 | a <- r] -> e \in [seq a.1 | a <- o] ->
  exists (b : bool), r = [:: (e, b)].
Proof.
  move=> Omem Rs Rfst e Er Eo.
  apply in_map_fst in Er as [br Er].
  exists br.
  assert (Et : utarget (e, br) = upath_target (utarget (e, br)) r).
  { apply Rfst.
    - by apply (map_f (fun e => utarget e)).
    - by apply endpoint_of_edge_in_cycle. }
  destruct r as [ | r er _] using last_ind; first by [].
  rewrite /= map_rcons last_rcons in Et.
  assert (er = (e, br)).
  { revert Er. rewrite mem_rcons in_cons => /orP[/eqP--> // | Er].
    revert Rs. rewrite simple_upath_rcons => /andP[/andP[_ Rs] _].
    contradict Rs. apply /negP/negPn.
    by rewrite -Et (map_f (fun e => utarget e) Er). }
  subst er. clear Et Er.
  destruct r as [ | r a _] using last_ind; first by [].
  exfalso.
  rewrite -!cats1 -catA cat1s in Rs.
  apply simple_upath_suffix in Rs.
  revert Rs. rewrite /simple_upath /= !eq_refl !in_cons !in_nil /= !andb_true_r !orb_false_r !negb_orb.
    move => /andP[/andP[/andP[/eqP-At As'] _] As].
  contradict As. apply /negP/negPn.
  assert (At' : utarget a = upath_target (utarget a) (rcons (rcons r a) (e, br))).
  { apply Rfst.
    - by rewrite !map_rcons mem_rcons in_cons mem_rcons in_cons eq_refl /= orb_true_r.
    - rewrite At. by apply endpoint_of_edge_in_cycle. }
  rewrite /= map_rcons last_rcons /= in At'.
  by rewrite -At' At eq_refl andb_false_r /= eq_sym in As'.
Qed.

Lemma back_source_is_last (p : upath) e :
  simple_upath p ->
  utarget e = upath_source (utarget e) p -> e \in p ->
  e = last e p.
Proof.
  case/lastP: p => [// | p a].
  rewrite in_rcons last_rcons simple_upath_rcons.
  move=> /andP[/andP[/andP[/andP[simple_p _] _] _] p_not_cycle]
    target_e_is /orP[/eqP--> // | e_in_p] //.
  exfalso.
  assert (E : (utarget e \in [seq utarget _e | _e <- p]) &&
    (utarget e != upath_target (utarget e) p)).
  { apply/andP. split.
    - by apply (map_f (fun e => utarget e)).
    - rewrite {1}target_e_is. by destruct p. }
  rewrite -(mem_usource_utarget_simple_upath_internal simple_p (utarget e)) in E.
  move: E => /andP[_ /eqP-?].
  by destruct p.
Qed.

(* Lemma to show a concatenation is a simple upath, only if p ++ q is non-cyclic. *)
Lemma simple_disjoints_are_cat_simple (v : G) (p q : upath) :
  simple_upath p -> upath_source v p <> upath_target v p ->
  simple_upath q -> upath_source v q <> upath_target v q ->
  upath_target v p = upath_source v q ->
  [disjoint [seq utarget _e | _e <- q] & [seq usource _e | _e <- p]] ->
  simple_upath (p ++ q).
Proof.
  move=> simple_p p_no_cycle simple_q q_no_cycle tp_eq_sq disjoint_tq_sp.
  apply simple_upath_cat; trivial.
  - by destruct p, q; apply/eqP.
  - apply /disjointP => u u_in_sources_p u_in_sources_q.
    enough (u_in_targets_q : u \in [seq utarget e | e <- q]).
    { revert disjoint_tq_sp => /disjointP/(_ u)-disjoint_tq_sp.
      by apply disjoint_tq_sp. }
    enough (E : (u \in [seq utarget e | e <- q]) && (u != upath_target u q))
      by by revert E => /andP[-> _].
    rewrite -(mem_usource_utarget_simple_upath_internal simple_q)
      u_in_sources_q.
    replace (upath_source u q) with (upath_target v p)
      by (rewrite tp_eq_sq; by destruct q).
    apply /eqP => ?. subst u.
    contradict p_no_cycle.
    by apply simple_upath_target_in_sources.
  - destruct q as [ | eq q]; first by [].
    enough (E : ~~((upath_target (usource eq) (eq :: q) \in [seq utarget e | e <- p]) &&
      (upath_target (usource eq) (eq :: q) !=
      upath_target (upath_target (usource eq) (eq :: q)) p))).
    { revert E => /nandP[-> // | /negPn/eqP-E].
      contradict q_no_cycle.
      destruct p; first by [].
      by revert E tp_eq_sq => /= -> <-. }
    rewrite -mem_usource_utarget_simple_upath_internal //.
    apply /nandP. left. apply /negP => F.
    revert disjoint_tq_sp => /disjointP/(_ (upath_target (usource eq) (eq :: q)))-disjoint_tq_sp.
    apply disjoint_tq_sp; last by [].
    by apply mem3_last.
  - destruct q as [ | [eq bq] q]; first by [].
    destruct p as [ | p [ep bp] _] using last_ind; first by [].
    enough (ep != eq).
    { destruct (rcons p (ep, bp)) eqn:F ; first by [].
      by rewrite -F last_rcons. }
    apply/eqP => ?. subst eq.
    revert disjoint_tq_sp => /disjointP/(_ (usource (ep, bp)))-H. apply H; clear H.
    + destruct (eq_or_eq_negb bp bq); subst bq.
      * rewrite /= map_rcons last_rcons in tp_eq_sq.
        by rewrite -tp_eq_sq /= in_cons eq_refl.
      * by rewrite /= in_cons eq_refl.
    + by rewrite map_rcons mem_rcons in_cons eq_refl.
Qed.

Lemma simple_cat_not_cyclic (o1 o2 : upath) :
  simple_upath (o1 ++ o2) -> o1 <> [::] -> o2 <> [::] ->
  forall (v : G), upath_source v o2 <> upath_target v o2.
Proof.
  move => Os ? ? v F.
  destruct o1; first by []. destruct o2; first by [].
  rewrite lastI (cat_rcons (last _ _)) in Os.
  apply simple_upath_suffix in Os.
  move: Os. by rewrite simple_upath_cons => /andP[_ /orP[/eqP-? | /eqP-?]].
Qed.

(* Two edges in a simple path, sharing the same target, are
   consecutive modulo this path. *)
Lemma same_target_are_consecutive (p : upath) (e : edge G * bool) (i j : nat) :
  simple_upath p -> i < size p -> j < size p -> i < j ->
  target (nth e p i).1 = target (nth e p j).1 ->
  ((j == i+1) && (nth e p i).2 && ~~ (nth e p j).2) ||
  ((i == 0) && (j == (size p).-1) && ~~ (nth e p i).2 && (nth e p j).2).
Proof.
  move=> P i_lt j_lt i_lt_j.
  destruct (nth e p i) as [ei []] eqn:I, (nth e p j) as [ej []] eqn:J
    => /= t_eq.
  - rewrite !andb_false_r /=.
    apply uniq_utarget_simple_upath in P.
    contradict P. apply /negP/(uniqP (utarget e)).
    rewrite size_map.
    move => /(_ i j i_lt j_lt).
    rewrite !(nth_map e) // I J /= => /(_ t_eq). lia.
  - rewrite !andb_true_r !andb_false_r orb_false_r.
    apply/negPn/negP => j_neq_i1.
    assert (i1_lt : i.+1 < size p) by lia.
    assert (I1 : usource (nth e p i.+1) = utarget (nth e p i))
      by by apply (uwalk_nth (uwalk_of_simple_upath P)).
    apply uniq_usource_simple_upath in P.
    contradict P. apply/negP/(uniqP (usource e)).
    rewrite size_map.
    move => /(_ i.+1 j i1_lt j_lt).
    rewrite !(nth_map e) // I1 I J /= => /(_ t_eq). lia.
  - rewrite !andb_false_r !andb_true_r /=.
    apply/negPn/negP => /nandP[/eqP-ij2 | /eqP-ij2].
    + assert (i1_lt : i.-1 < size p) by lia.
      assert (I1 : usource (nth e p i) = utarget (nth e p i.-1)).
      { replace i with (i.-1.+1) by lia.
        by apply (uwalk_nth (uwalk_of_simple_upath P)); lia. }
      apply uniq_utarget_simple_upath in P.
      contradict P. apply/negP/(uniqP (utarget e)).
      rewrite size_map.
      move => /(_ i.-1 j i1_lt j_lt).
      rewrite !(nth_map e) // -I1 I J /= => /(_ t_eq). lia.
    + assert (j1_lt : j.+1 < size p) by lia.
      assert (J1 : usource (nth e p j.+1) = utarget (nth e p j))
        by by apply (uwalk_nth (uwalk_of_simple_upath P)).
      apply uniq_usource_simple_upath in P.
      contradict P. apply/negP/(uniqP (usource e)).
      rewrite size_map.
      move => /(_ i j.+1 i_lt j1_lt).
      rewrite !(nth_map e) // I J1 J /= => /(_ t_eq). lia.
  - rewrite !andb_false_r /=.
    apply uniq_usource_simple_upath in P.
    contradict P. apply/negP/(uniqP (usource e)).
    rewrite size_map.
    move => /(_ i j i_lt j_lt).
    rewrite !(nth_map e) // I J /= => /(_ t_eq). lia.
Qed.
(* TODO try to factorize all of this *)

End SimpleUpath.

Lemma simple_upath_in_subgraph {Lv Le : Type} {G : graph Lv Le} {V : {set G}} {E : {set edge G}}
  (con : consistent V E) (p : @upath _ _ (subgraph_for con)) :
  simple_upath p = simple_upath [seq (val e.1, e.2) | e <- p].
Proof.
  rewrite /simple_upath.
  destruct p as [ | e p]; first by [].
  rewrite /= uwalk_in_subgraph /= !in_cons sub_val_eq /=.
  repeat f_equal.
  - move: e. by induction p => /=.
  - move: e. by induction p => /=.
  - move: e. induction p as [ | a p IH] => e //=.
    by rewrite !in_cons {}IH sub_val_eq -last_map -!map_comp.
  - move: e. by induction p => /=.
  - induction p as [ | a p IH] => //=.
    by rewrite !in_cons {}IH.
  - induction p as [ | a p IH] => //=.
    by rewrite {}IH in_seq_sig -!map_comp.
  - induction p as [ | a p IH] => //=.
    by rewrite !in_cons {}IH.
  - induction p as [ | a p IH] => //=.
    by rewrite {}IH in_seq_sig -!map_comp.
Qed.

Lemma uwalk_to_simple_upath {Lv Le : Type} {G : graph Lv Le}  (p : upath) :
  uwalk p -> {q : Simple_upath G |
    (if p is e :: _ then upath_source (usource e) (val q) = upath_source (usource e) p /\
      upath_target (usource e) (val q) = upath_target (usource e) p else true) /\ {subset val q <= p}}.
Proof.
  induction p as [ | e p IH].
  { move=> _. by exists (Sub [::] (simple_upath_nil G)). }
  move=> /= /andP[/eqP-source_p uwalk_p].
  move: IH => /(_ uwalk_p) {uwalk_p} [[q simple_q] /= [endpoints_q sub_q]].
  destruct p as [ | f p].
  { exists (Sub _ (simple_upath_edge e)). rewrite SubK /=. repeat split => // ?. }
  destruct endpoints_q as [source_q target_q].
  (* Two cases: e :: q is simple or not *)
  case/boolP: ((e.1 != (head e q).1) && (utarget e == upath_source (utarget e) q) && (usource e \notin [seq usource a | a <- q]) &&
    (upath_source (utarget e) q != upath_target (utarget e) (f :: p))).
  (* If e :: q is simple, take this path *)
  - move=> H.
    enough (K : simple_upath (e :: q)).
    { exists (Sub _ K). rewrite SubK. repeat split; trivial.
      - destruct q; last by [].
        move: H. by rewrite eq_refl /=.
      - move=> a. rewrite !in_cons => /orP[-> // | ?].
        apply/orP. right. by apply sub_q. }
    rewrite simple_upath_cons simple_q /=.
    destruct q as [ | eq q]; first by rewrite /= eq_refl.
    simpl in *.
    by rewrite target_q H.
  (* Otherwise, a simplification can be done *)
  - rewrite !negb_andb !negb_involutive.
    have [/eqP-e_eq_headq | e_neq_headq] := boolP (e.1 == (head e q).1).
    { move=> _.
      destruct q as [ | [g b] q]; simpl in *.
      - clear simple_q source_q sub_q e_eq_headq.
        rewrite -target_q -source_p.
        exists (Sub _ (simple_upath_edge e)). rewrite SubK /=. repeat split; trivial.
        move=> ?. by rewrite !in_cons in_nil orb_false_r => ->.
      - subst g.
        have H : (b == e.2) || (b == ~~ e.2) by by destruct b, e as [? []].
        elim: (orb_sum H) => /eqP-?; subst b; clear H.
        + exists (Sub _ simple_q). rewrite SubK /= target_q. repeat split; trivial.
          move=> a a_in. move: sub_q => /(_ a a_in).
          rewrite !in_cons => /orP[-> | ->]; by rewrite !orb_true_r.
        + move: simple_q. rewrite simple_upath_cons => /andP[/andP[/andP[/andP[simple_q /= _] /eqP-usource_e] _] _].
          exists (Sub _ simple_q). rewrite SubK /= -target_q -usource_e. repeat split; trivial.
          move=> a a_in. move: sub_q => /(_ a).
          rewrite !in_cons a_in orb_true_r => /(_ is_true_true) /orP[-> | ->]; by rewrite !orb_true_r. }
    have [/eqP-target_e_eq_source_q | target_e_neq_source_q] := boolP (utarget e == upath_source (utarget e) q); first last.
    { exfalso.
      move: source_q source_p target_e_neq_source_q => /= <- ->.
      by destruct q; rewrite /= eq_refl. }
    have [source_e_in_sources_q | source_e_nin_sources_q] := boolP (usource e \in [seq usource a | a <- q]).
    { (* We take the suffix of q starting at usource e *)
        move=> _. move: source_e_in_sources_q. rewrite in_elt_sub => /existsP/sigW[[n N] /= /eqP-sources_q].
        rewrite -{1}(cat_take_drop n [seq usource a | a <- q]) in sources_q.
        apply cat_eq_l in sources_q.
        assert (simple_drop : simple_upath (drop n q)).
        { move: simple_q. rewrite -{1}(cat_take_drop n q). by apply simple_upath_suffix. }
        exists (Sub _ (simple_drop)).
        rewrite /= !map_drop sources_q /=. repeat split; trivial; last first.
        { move=> a a_in. by rewrite in_cons sub_q ?orb_true_r // (mem_drop a_in). }
        clear sub_q.
        move: target_q => /= <-.
        generalize (usource f). clear - n N. move: n N.
        induction q as [ | eq q IH] => //= n N v.
        destruct n as [ | n]; first by rewrite drop0.
        apply IH. move: N. clear. simpl. lia. }
    move=> /= /eqP- source_q_eq_target_p.
    destruct q as [ | g q]; first by rewrite eq_refl in e_neq_headq.
    simpl in *.
    rewrite -source_q_eq_target_p.
    exists (Sub _ (simple_upath_edge e)). rewrite SubK /= target_e_eq_source_q. repeat split; trivial.
    move=> ?. by rewrite !in_cons in_nil orb_false_r => ->.
Qed.

Lemma simple_upath_if_uwalk {Lv Le : Type} {G : graph Lv Le} (s t : G) :
  reflect (exists p, uwalk p && (upath_source s p == s) && (upath_target s p == t))
  [exists p : Simple_upath G, (upath_source s (val p) == s) && (upath_target s (val p) == t)].
Proof.
  apply iff_reflect. split.
  - move=> [p /andP[/andP[walk_p source_p] target_p]].
    apply uwalk_to_simple_upath in walk_p as [q [endpoints_q sub_q]].
    apply/existsP. exists q.
    destruct p as [ | e p].
    + destruct q as [[ | f ?] ?].
      * by rewrite source_p target_p.
      * move: sub_q => /= /(_ f). by rewrite !in_cons eq_refl in_nil /= => /(_ is_true_true).
    + rewrite -(eqP source_p) -(eqP target_p) /=.
      elim: endpoints_q => /= -> ->. by rewrite !eq_refl.
  - move=> /existsP/sigW[[q simple_q] /= /andP[/eqP-source_q /eqP-target_q]].
    apply uwalk_of_simple_upath in simple_q.
    exists q. by rewrite simple_q source_q target_q !eq_refl.
Qed.

Lemma simple_upath_to_no_cyclic {Lv Le : Type} {G : graph Lv Le} (s t : G) (p : upath) :
  simple_upath p -> upath_source s p = s -> upath_target s p = t ->
  {q : Simple_upath G | upath_source s (val q) = s /\ upath_target s (val q) = t /\
    (val q = [::] \/ s <> t)}.
Proof.
  move => simple_p source_p target_p.
  destruct (eq_comparable s t) as [s_eq_t | s_neq_t].
  - exists (Sub [::] (@simple_upath_nil _ _ _)). auto.
  - exists (Sub p simple_p). auto.
Qed.

(* Lemma uwalk_to_no_cyclic {Lv Le : Type} {G : graph Lv Le} (v : G) (p : upath) :
  uwalk p ->
  {q : Simple_upath G | upath_source v (val q) = upath_source v p /\ upath_target v (val q) = upath_target v p /\
    (val q = [::] \/ upath_source v p <> upath_target v p)}.
Proof.
  move=> uwalk_p.
  apply uwalk_to_simple_upath in uwalk_p as [[q simple_q] [endpoints_q sub_q]].
  destruct p.
  - exists (Sub _ (simple_upath_nil _)). auto.
  - destruct endpoints_q as [source_q target_q].
(*     exists (Sub q simple_q). *)
  destruct (simple_upath_to_no_cyclic simple_q source_q target_q) as [[[ | e' q'] simple_q'] hyp_q'].
  + exists (Sub _ (simple_upath_nil _)). simpl in *. auto.
  rewrite /=.
  exact (simple_upath_to_no_cyclic Q S T).
Qed. *)

(* TODO try to simplify all of this file *)
