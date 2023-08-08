(* Simple undirected path in a directed multigraph *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph.
From Yalla Require Import mll_prelim graph_more.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section SimpleUpath.

Variables (Lv Le : Type) (G : graph Lv Le).

(** Simple path - no repetition of vertex nor edge, except target may be source, not empty *)
Definition simple_upath (p : @upath _ _ G) : bool :=
  match p with | [::] => false | e :: _ => 
  (uwalk (upath_source (utarget e) p) (upath_target (utarget e) p) p) &&
  uniq [seq e.1 | e <- p] && uniq [seq usource e | e <- p] &&
  ((upath_target (utarget e) p \notin [seq usource e | e <- p]) ||
  (upath_target (utarget e) p == upath_source (utarget e) p))
  end.
(* TODO sortir du match ce qui n'utilise pas e ? *)

Lemma uniq_fst_simple_upath (p : upath) :
  simple_upath p ->
  uniq [seq e.1 | e <- p].
Proof. rewrite /simple_upath. destruct p; first by []. introb. Qed.

Lemma uniq_usource_simple_upath (p : upath) :
  simple_upath p ->
  uniq [seq usource e | e <- p].
Proof. rewrite /simple_upath. destruct p; first by []. introb. Qed.
(* TODO que des lemmes comme ça, puis opaque de simple_upath? *)


(** The type of simple upaths in a graph is a finite type. *)
Record Simple_upath : predArgType :=
  {supval :> upath; supvalK : simple_upath supval}.
Canonical Simple_upath_subType :=
  [subType for @supval].
Definition Simple_upath_eqMixin :=
  Eval hnf in [eqMixin of Simple_upath by <:].
Canonical Simple_upath_eqType :=
  Eval hnf in EqType Simple_upath Simple_upath_eqMixin.
Definition Simple_upath_choiceMixin :=
  Eval hnf in [choiceMixin of Simple_upath by <:].
Canonical Simple_upath_choiceType :=
  Eval hnf in ChoiceType Simple_upath Simple_upath_choiceMixin.
Definition Simple_upath_countMixin :=
  Eval hnf in [countMixin of Simple_upath by <:].
Canonical Supath_countType :=
  Eval hnf in CountType Simple_upath Simple_upath_countMixin.

Lemma simple_upath_size (p : upath) :
  simple_upath p -> size p < S #|edge G|.
Proof.
  move => P.
  assert (U := uniq_fst_simple_upath P).
  revert U => /card_uniqP-U.
  rewrite size_map in U.
  rewrite -U.
  exact: max_card.
Qed.

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
  move => [p P] /=.
  case: {-}_ / boolP; last by rewrite P.
  move => P'. by rewrite (bool_irrelevance P' P).
Qed.

Definition Simple_upath_finMixin :=
  Eval hnf in PcanFinMixin Simple_upath_tupleK.
Canonical Simple_upath_finType :=
  Eval hnf in FinType Simple_upath Simple_upath_finMixin.


(** Many results on simple upath *)

Lemma endpoint_simple_upath (b : bool) (p : upath) :
  simple_upath p -> forall (x y : G), upath_endpoint b x p = upath_endpoint b y p.
Proof. by destruct p. Qed.

Lemma uwalk_of_simple_upath (p : upath) :
  simple_upath p -> forall v, uwalk (upath_source v p) (upath_target v p) p.
Proof. destruct p => // /andP[/andP[/andP[W _] _] _] v. revert W. by rewrite /= !eq_refl. Qed.

Lemma simple_upath_edge e :
  simple_upath [:: e].
Proof. by rewrite /simple_upath /= !eq_refl in_cons in_nil orb_false_r orNb. Qed.

(* e :: p is a simple path if and only if p is empty or
   p is a simple path starting from the target of e, p is not a cycle,
   p does not contains e nor the source of e except possibly as its target *)
Lemma simple_upath_cons e (p : upath) :
  simple_upath (e :: p) =
  (p == [::]) ||
  (simple_upath p) && (upath_source (utarget e) p != upath_target (utarget e) p) &&
  (e.1 \notin [seq a.1 | a <- p]) &&
  (utarget e == upath_source (utarget e) p) && (usource e \notin [seq usource a | a <- p]).
Proof.
  destruct p as [ | a p]; first by rewrite simple_upath_edge.
  rewrite /simple_upath /= !in_cons !negb_orb !eq_refl /= !(eq_sym (usource a)).
  destruct (utarget e == usource a)                          ; rewrite      ?andb_true_r ?andb_false_r //=.
  destruct (uwalk (utarget a) _ p)                           ; rewrite      ?andb_true_r ?andb_false_r //=.
  destruct (e.1 == a.1)                                      ; rewrite      ?andb_true_r ?andb_false_r //=.
  destruct (e.1 \notin [seq f.1 | f <- p]) eqn:E1            ; rewrite {}E1 ?andb_true_r ?andb_false_r //=.
  destruct (a.1 \notin [seq f.1 | f <- p]) eqn:A1            ; rewrite {}A1 ?andb_true_r ?andb_false_r //=.
  destruct (uniq [seq f.1 | f <- p])                         ; rewrite      ?andb_true_r ?andb_false_r //=.
  destruct (usource e == usource a) eqn:SESA                 ; rewrite      ?andb_true_r ?andb_false_r //=.
  destruct (usource e \notin [seq usource f | f <- p]) eqn:Es; rewrite Es   ?andb_true_r ?andb_false_r //=.
  destruct (usource a \notin [seq usource f | f <- p]) eqn:As; rewrite {}As ?andb_true_r ?andb_false_r //=.
  destruct (uniq [seq usource f | f <- p])                   ; rewrite      ?andb_true_r ?andb_false_r //=.
  destruct (last (utarget a) [seq utarget f | f <- p] == usource e) eqn:Lp; simpl.
  { revert Lp => /eqP-->. by rewrite Es SESA. }
  by destruct (last (utarget a) [seq utarget f | f <- p] == usource a) eqn:Lp'; rewrite //= orb_false_r andb_true_r.
Qed.

Lemma simple_upath_rcons e (p : upath) :
  simple_upath (rcons p e) =
  (p == [::]) ||
  (simple_upath p) && (upath_source (utarget e) p != upath_target (utarget e) p) &&
  (e.1 \notin [seq a.1 | a <- p]) &&
  (usource e == upath_target (usource e) p) && (utarget e \notin [seq utarget a | a <- p]).
Proof.
  destruct p as [ | a p]; first by rewrite simple_upath_edge.
  rewrite /simple_upath /= uwalk_rcons !map_rcons !last_rcons !rcons_uniq in_cons !mem_rcons
    !in_cons !negb_orb !eq_refl /= !(eq_sym (usource a)) !(eq_sym a.1).
  destruct (e.1 == a.1) ; rewrite ?andb_true_r ?andb_false_r //=.
  destruct (e.1 \notin [seq f.1 | f <- p]) eqn:E1; rewrite {}E1 ?andb_true_r ?andb_false_r //=.
  destruct (a.1 \notin [seq f.1 | f <- p]) eqn:A1; rewrite {}A1 ?andb_true_r ?andb_false_r //=.
  destruct (uniq [seq f.1 | f <- p]); rewrite ?andb_true_r ?andb_false_r //=.
  destruct (usource a \notin [seq usource f | f <- p]) eqn:As; rewrite As ?andb_true_r ?andb_false_r //=.
  destruct (uniq [seq usource f | f <- p]); rewrite ?andb_true_r ?andb_false_r //=.
  destruct (usource e == last (utarget a) [seq utarget f | f <- p]) eqn:Lp; rewrite ?andb_true_r ?andb_false_r /=; last first.
  { enough (uwalk (utarget a) (usource e) p = false) as -> by by [].
    apply /negP => W. destruct (uwalk_endpoint W) as [_ T]. by rewrite -T /= eq_refl in Lp. }
  revert Lp => /eqP-->.
  destruct (uwalk (utarget a) _ p) eqn:W; rewrite ?andb_true_r ?andb_false_r //=.
  destruct (last (utarget a) [seq utarget f | f <- p] == usource a) eqn:SESA; rewrite ?andb_true_r ?andb_false_r //=.
  destruct (last (utarget a) [seq utarget f | f <- p] \notin [seq usource f | f <- p]) eqn:Es; rewrite {}Es ?andb_true_r ?andb_false_r //=.
  destruct (uwalk_endpoint W) as [Ta _]. simpl in Ta.
  destruct (utarget e == usource a) eqn:TESA; rewrite ?andb_true_r ?andb_false_r /=.
  - revert TESA => /eqP-->. symmetry.
    rewrite -{}Ta. clear e.
    apply /andP; split.
    + apply /eqP => F.
      contradict As. apply /negP/negPn.
      rewrite F mem3_head //.
      destruct p; last by []. simpl in *. by rewrite F eq_refl in SESA.
    + induction p as [ | p e' IH] using last_ind; first by [].
      revert As SESA. rewrite !map_rcons /= !mem_rcons !in_cons !negb_orb last_rcons => /andP[SASE As] SESA.
      rewrite eq_sym SESA /=.
      revert W. rewrite uwalk_rcons => /andP[W SE].
      destruct (uwalk_endpoint W) as [_ T]. simpl in T.
      revert IH. by rewrite T W eq_sym (negPf SASE) => ->.
  - clear As SESA TESA.
    rewrite -Ta in W.
    rewrite orb_false_r -{}Ta.
    revert a W. induction p as [ | f p IH] => //= a /andP[_ W].
    rewrite !in_cons !negb_orb.
    destruct (utarget e == usource f); rewrite ?andb_true_r ?andb_false_r //=.
    destruct p as [ | f2 p] => //=.
    destruct (uwalk_endpoint W) as [S _]. simpl in S.
    specialize (IH f2).
    change (head (utarget f2) [seq usource x | x <- f2 :: p]) with (usource f2) in IH.
    rewrite S in IH.
    by rewrite (IH W).
Qed. (* TODO to simplify *)

Lemma simple_upath_rev (p : upath) :
  simple_upath (upath_rev p) = simple_upath p.
Proof.
  induction p as [ | (e, b) p IH]; first by done.
  rewrite simple_upath_cons /= simple_upath_rcons.
  rewrite upath_rev_nil {}IH /= negb_involutive upath_rev_fst map_usource_upath_rev
    map_utarget_upath_rev !mem_rev head_rev !last_rev.
  by destruct p; rewrite /= ?eq_refl 1?eq_sym.
Qed.

Lemma uniq_utarget_simple_upath (p : upath) :
  simple_upath p ->
  uniq [seq utarget e | e <- p].
Proof.
  rewrite -(upath_rev_inv p) simple_upath_rev map_utarget_upath_rev rev_uniq.
  apply uniq_usource_simple_upath.
Qed.

Lemma simple_upath_subK (p q : upath) :
  simple_upath (p ++ q) ->
  ((p == [::]) || (simple_upath p)) &&
  ((q == [::]) || (simple_upath q)).
Proof.
  revert p. induction q as [ | eq q IHq] => p.
  { rewrite cats0 /= => ->. by rewrite orb_true_r. }
  induction p as [ | ep p IHp]; first by [].
  rewrite cat_cons simple_upath_cons cat_nil => /orP[/andP[//] | S].
  revert S => /andP[/andP[/andP[/andP[Spq Cycpq] E1] Et] Es].
  revert IHp => /(_ Spq) /andP[P Q].
  rewrite Q simple_upath_cons /=.
  revert E1 Es. rewrite !map_cat !mem_cat !negb_orb => /andP[-> _] /andP[-> _].
  rewrite !andb_true_r.
  simpl in Et.
  revert P => /orP[/eqP--> // | S].
  rewrite S /=. apply /orP; right.
  apply /andP; split.
  - rewrite -cat_rcons in Spq.
    specialize (IHq _ Spq). clear Spq.
    revert IHq => /andP[/orP[/eqP-F | Speq] _].
    { contradict F. apply rcons_nil. (* TODO rcons_nil in bool? *) }
    assert (Pnil : p == [::] = false) by (apply /eqP => ?; by subst p).
    rewrite simple_upath_rcons Pnil S /= in Speq.
    revert Speq => /andP[/andP[/andP[? _] _] _].
    rewrite (head_eq _ (utarget eq)) ?(last_eq _ (utarget eq)) //; by destruct p.
  - revert Et. rewrite map_cat head_cat (head_eq _ (utarget ep)) //; by destruct p.
Qed. (* TODO can be simplified *)
(* 
Lemma test' e p eq :
  simple_upath p -> upath_source (usource e) p <> upath_target (usource e) p ->
  upath_target (usource e) p = usource eq ->
  (last e p).1 <> eq.1 ->
  eq.1 \notin [seq a.1 | a <- p].
Proof.
  move => Ps Pcyc Eqso Eq1neq.
  apply /negP => Eqin. apply in_map_fst in Eqin. destruct Eqin as [b Eqin].
  destruct eq as [eq beq]. simpl in *.
      destruct (eq_comparable beq b) as [B | B].
      * subst b.
        contradict Eqsonin. apply /negP/negPn/mapP. by exists (eq, beq).
      * assert (bx = ~~beq) by by destruct beq, bx. subst bx. clear B.
        induction p as [ | ep p IH]; first by [].
        revert Ps Eqso Eqsonin Eq1neq Xin.
        rewrite simple_upath_cons /= !in_cons !negb_orb.
        move => /orP[/eqP-? |
          /andP[/andP[/andP[/andP[Ps /eqP-Pcyc] Ep1] /eqP-Epta] Epsonin]].
        { subst p => {IH} _ _.
          rewrite !in_nil !orb_false_r.
          destruct ep. cbn. move => ? /andP[/eqP-? _]. by subst. }
        move => Pl /andP[Eptain Eqtanin Eq1neq] /orP[/eqP-? | Eqin].
        { subst ep. simpl in *. contradict Pcyc. by rewrite Pl -Epta. }
        rewrite (last_eq _ (usource e)) in Pl; last by destruct p.
        rewrite (last_eq _ e) in Eq1neq; last by destruct p.
        by apply IH.
Qed.
 *)
Lemma simple_disjoint_next_edge e p a :
  simple_upath p ->
  last (usource e) [seq utarget e | e <- p] = usource a ->
  usource a \notin [seq usource e | e <- p] -> (* TODO equivalent to p not cyclic *)
  (last e p).1 <> a.1 ->
  a.1 \notin [seq a.1 | a <- p].
(* TODO e is useless here *)
Proof.
  destruct a as [a b].
  move => /= Ps Aso Asonin Aneq.
  apply /mapP. move => [[a' b'] /= Ain ?]. subst a'.
  destruct (eq_comparable b b') as [B | B].
  { subst b'. contradict Asonin. apply /negP/negPn/mapP. by exists (a, b). }
  assert (b' = ~~b) by by destruct b, b'. subst b'. clear B.
  induction p as [ | ep p IH]; first by [].
  revert Ps Aso Asonin Aneq Ain.
  rewrite simple_upath_cons /= !in_cons !negb_orb => /orP[/eqP-? |
    /andP[/andP[/andP[/andP[Ps /eqP-Pcyc] Ep1] /eqP-Epta] Epsonin]].
  { subst p => {IH} _ _. rewrite !in_nil !orb_false_r /= => ? /eqP-?. by subst. }
  move => Pl /andP[Eptain Eqtanin Eq1neq] /orP[/eqP-? | Eqin].
  { subst ep. contradict Pcyc. by rewrite Pl -Epta. }
  rewrite (last_eq _ (usource e)) in Pl; last by destruct p.
  rewrite (last_eq _ e) in Eq1neq; last by destruct p.
  by apply IH.
Qed.

Lemma simple_upath_target_in_sources v (p : upath) :
  simple_upath p -> upath_target v p \in [seq usource e | e <- p] ->
  upath_source v p = upath_target v p.
(* TODO v is useless here *)
Proof.
  revert v. case/lastP: p => [// | p e] v.
  rewrite simple_upath_rcons /= !map_rcons last_rcons head_rcons mem_rcons in_cons.
  move => /orP[/eqP-? | /andP[/andP[/andP[/andP[S _] _] /eqP-Eso] Etnin]].
  { subst p. by rewrite /= in_nil orb_false_r => /eqP-->. }
  move => /orP[/eqP-F | Etin].
  { contradict Etnin. apply /negP/negPn.
    rewrite {}F {}Eso.
    apply mem3_last. by destruct p. }
  assert (Etin' : utarget e \in upath_target v p :: [seq usource e | e <- p]).
  { by rewrite in_cons Etin orb_true_r. }
  rewrite (mem_usource_utarget_uwalk (@uwalk_of_simple_upath _ S v)) in_cons /= in Etin'.
  revert Etin' => /orP[/eqP--> | Etin'].
  { apply head_eq. by destruct p. }
  by rewrite Etin' in Etnin.
Qed.

Lemma simple_upath_source_in_targets (v : G) (p : upath) :
  simple_upath p -> upath_source v p \in [seq utarget e | e <- p] ->
  upath_source v p = upath_target v p.
(* TODO v is useless here *)
Proof.
  move => simple_p source_p_in_targets_p.
  rewrite -(upath_rev_inv p).
  rewrite upath_endpoint_rev [in RHS]upath_endpoint_rev.
  symmetry.
  apply simple_upath_target_in_sources.
  - by rewrite simple_upath_rev.
  - by rewrite upath_endpoint_rev map_usource_upath_rev mem_rev.
Qed.
(* TODO in simple_uapth.v + to use instead of reversing then rho *)

Lemma simple_upath_cat e (p q : upath) :
  simple_upath p -> simple_upath q ->
  upath_target (usource e) p = upath_source (usource e) q ->
  [disjoint [seq usource e | e <- p] & [seq usource e | e <- q]] ->
  upath_target (usource e) q \notin [seq utarget e | e <- p] ->
  (last e p).1 <> (head e q).1 ->
  simple_upath (p ++ q).
(* TODO e is useless here *)
Proof.
  revert e p. induction q as [ | eq q IH] => e p //.
  rewrite simple_upath_cons -cat_rcons disjoint_sym /= disjoint_cons.
  move => Ps /orP[/eqP-? | /andP[/andP[/andP[/andP[Qs Qcyc] Eq1nin] /eqP-Eqta] Eqsonin]].
  - subst q. rewrite {IH} cats0 simple_upath_rcons Ps disjoint_nil andb_true_r /=.
    move => Eqso Eqsonin Eqtanin Eq1neq.
    apply /orP; right.
    rewrite Eqtanin -Eqso (last_eq (last _ _) (usource e)) ?eq_refl ?andb_true_r; last by destruct p.
    apply /andP; split.
    + apply /eqP => HL.
      contradict Eqsonin. apply /negP/negPn.
      rewrite -Eqso (last_eq _ (utarget eq)) -?HL; destruct p; try by [].
      by rewrite /= in_cons eq_refl.
    + clear Eqtanin. by apply (@simple_disjoint_next_edge e).
  - move => Eqso /andP[Eqsonin' D] Lnin Eq1neq.
    apply (IH e); clear IH; try by [].
    + rewrite simple_upath_rcons Ps /=.
      apply /orP; right. repeat (apply /andP; split).
      * rewrite (last_eq _ (usource e)); last by destruct p.
        rewrite Eqso. destruct p; first by [].
        revert Eqsonin'. clear.
        by rewrite /= in_cons negb_orb eq_sym => /andP[-> _].
      * by apply (@simple_disjoint_next_edge e).
      * apply /eqP. rewrite -Eqso.
        apply last_eq. by destruct p.
      * rewrite Eqta.
        enough (E : head (utarget eq) [seq usource e | e <- q]
          \notin upath_source (usource e) p :: [seq utarget e | e <- p]).
        { revert E. by rewrite in_cons negb_orb => /andP[_ ->]. }
        rewrite -(@mem_usource_utarget_uwalk _ _ _ _ (upath_target (usource e) p));
        last by apply uwalk_of_simple_upath.
        rewrite in_cons negb_orb /= Eqso.
        clear - Qs Eqsonin D. destruct q; first by []. clear Qs.
        revert Eqsonin D. by rewrite /= in_cons negb_orb eq_sym disjoint_cons => /andP[-> _] /andP[-> _].
    + rewrite /= map_rcons last_rcons Eqta.
      apply head_eq. by destruct q.
    + by rewrite map_rcons disjoint_rcons Eqsonin disjoint_sym D.
    + rewrite /= map_rcons mem_rcons in_cons negb_orb Eqta (last_eq _ (utarget eq)); last by destruct q.
      by rewrite eq_sym Qcyc Lnin.
    + rewrite last_rcons. clear - Qs Eq1nin. destruct q; first by []. clear Qs.
      revert Eq1nin. by rewrite /= in_cons negb_orb => /andP[/eqP-? _].
Qed.

Lemma mem_usource_utarget_simple_upath_internal (p: @upath _ _ G) :
  simple_upath p -> forall v,
  (v \in [seq usource e | e <- p]) && (v != upath_source v p) =
  (v \in [seq utarget e | e <- p]) && (v != upath_target v p).
Proof.
  induction p as [ | e p IH]; first by [].
  rewrite simple_upath_cons.
  destruct (eq_comparable p [::]) as [? | Pnil]; [subst p | ].
  { move => _ v. by rewrite /= !in_cons !in_nil !orb_false_r !andbN. }
  move => /orP[/eqP-? // | /andP[/andP[/andP[/andP[Ps /eqP-Pnc] E1] /eqP-Et] Es]] v.
  specialize (IH Ps v).
  rewrite /= !in_cons !andb_orb_distrib_l andbN /= (last_eq (utarget e) v); last by destruct p.
  rewrite -IH (endpoint_simple_upath _ Ps v (utarget e)) -Et.
  destruct (eq_comparable v (utarget e)) as [? | Vte]; [subst v | ].
  - rewrite eq_refl /= andb_false_r orb_false_r.
    transitivity true; [ | symmetry].
    + assert (E : utarget e \in [seq usource e | e <- p]).
      { rewrite Et /= mem3_head //. by destruct p. }
      rewrite E /=.
      apply /eqP => F. contradict E. apply /negP.
      by rewrite F Es.
    + rewrite Et. apply /eqP. clear - Pnc Pnil. simpl in *.
      rewrite (last_eq _ (utarget e)) //. by destruct p.
  - replace (v == utarget e) with false by by symmetry; apply /eqP.
    destruct (v \in [seq usource e | e <- p]) eqn:V; rewrite V //=.
    apply /eqP => ?. subst v.
    by rewrite V in Es.
Qed.

Lemma endpoint_of_edge_in_cycle (o : @upath _ _ G) :
  [seq utarget a | a <- o] =i [seq usource a | a <- o] ->
  forall e, e \in [seq a.1 | a <- o] ->
  forall b, endpoint b e \in [seq usource a | a <- o].
Proof.
  move => Omem e E b'.
  apply in_map_fst in E. destruct E as [b E].
  destruct (eq_comparable b b') as [? | B]; [subst b' | ].
  - rewrite -Omem. change (endpoint b e) with (utarget (e, b)).
    by apply (map_f (fun e => utarget e)).
  - assert (b' = ~~ b) by (clear - B; by destruct b, b'). subst b'. clear B.
    change (endpoint (~~ b) e) with (usource (e, b)).
    by apply (map_f (fun e => usource e)).
Qed. (* TODO plutôt dans uwalk *)

Lemma disjoint_or_edge v (o r : upath) :
  [seq utarget e | e <- o] =i [seq usource e | e <- o] ->
  simple_upath r ->
  (forall (u : G), u \in [seq utarget e | e <- r] ->
    u \in [seq usource e | e <- o] -> u = upath_target v r) ->
  forall e : edge G, e \in [seq a.1 | a <- r] ->
  e \in [seq a.1 | a <- o] ->
  exists (b : bool), r = [:: (e, b)].
(* TODO v is useless here *)
Proof.
  move => Omem Rs Rfst e Er Eo.
  apply in_map_fst in Er. destruct Er as [br Er].
  exists br.
  assert (Et : utarget (e, br) = upath_target v r).
  { apply Rfst.
    - by apply (map_f (fun e => utarget e)).
    - by apply endpoint_of_edge_in_cycle. }
  destruct r as [ | r er _] using last_ind; first by [].
  rewrite /= map_rcons last_rcons in Et.
  assert (er = (e, br)).
  { revert Er. rewrite mem_rcons in_cons => /orP[/eqP--> // | Er].
    revert Rs. rewrite simple_upath_rcons => /orP[/eqP-? | /andP[_ Rs]]; first by subst r.
    contradict Rs. apply /negP/negPn.
    rewrite -Et. change (endpoint br e) with (utarget (e, br)).
    by apply (map_f (fun e => utarget e)). }
  subst er. clear Et Er.
  destruct r as [ | r a _] using last_ind; first by [].
  rewrite -!cats1 -catA in Rs.
  apply simple_upath_subK in Rs.
  revert Rs. rewrite /= !eq_refl !in_cons !in_nil /= !andb_true_r !orb_false_r !negb_orb
    => /andP[_ /andP[/andP[/andP[/eqP-At _] Asn] As]].
  assert (At' : utarget a = upath_target v (rcons (rcons r a) (e, br))).
  { apply Rfst.
    - by rewrite !map_rcons mem_rcons in_cons mem_rcons in_cons eq_refl /= orb_true_r.
    - rewrite -At. by apply endpoint_of_edge_in_cycle. }
  rewrite /= map_rcons last_rcons /= in At'.
  rewrite At -At' eq_refl andb_false_r /= eq_sym in As.
  by rewrite At As in Asn.
Qed.

Lemma back_source_is_last (p : upath) e :
  simple_upath p ->
  utarget e = upath_source (utarget e) p -> e \in p ->
  e = last e p.
Proof.
  move => Ps Et.
  rewrite in_elt_sub => /existsP[[n /= N] /eqP-Peq].
  destruct (eq_comparable n (size p - 1)) as [? | Nneq]; [subst n | ].
  { revert Peq.
    replace ((size p - 1).+1) with (size p) by lia.
    rewrite drop_size => ->.
    by rewrite cats1 last_rcons. }
  exfalso.
  destruct (drop n.+1 p) as [ | ed d] eqn:D.
  { assert (F : size (drop n.+1 p) = 0) by by rewrite D.
    contradict F.
    rewrite size_drop. lia. }
  assert (Et' : utarget e = usource ed).
  { assert (W := uwalk_of_simple_upath Ps (utarget e)).
    rewrite Peq in W. destruct (uwalk_subK W) as [_ W'].
    by revert W' => /= /andP[_ /andP[/eqP--> _]]. }
  assert (U := uniq_usource_simple_upath Ps).
  contradict U. apply /negP.
  rewrite Peq -cat_rcons map_cat cat_uniq /= !negb_orb !negb_andb !negb_involutive.
  enough (usource ed \in [seq usource _e | _e <- rcons (take n p) e]) as ->
    by by rewrite !orb_true_r.
  rewrite -Et' Et {1}Peq -cat_rcons /= map_cat head_cat.
  apply mem3_head.
  rewrite map_rcons. apply rcons_nil.
Qed.

End SimpleUpath.
