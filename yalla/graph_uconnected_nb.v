(* Extension for [mgraph] of the library GraphTheory *)
(** Proof of the lemma uacyclic_uconnected_nb:
  for f, supposed to be injective (except on None), defined on a uacyclic graph G,
  the number of connected components of G + its number of (non-None) edges is equal
  to its number of vertices*)

From Coq Require Import Bool.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From GraphTheory Require Import preliminaries mgraph structures bij setoid_bigop.
From Yalla Require Import mll_prelim graph_more upath supath.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Section Uacyclic_uconnected_nb.
(** Intermediate lemmas for the proof of the lemma uacyclic_uconnected_nb
  We will proceed by induction on the number of vertices of G,
  and look at what happens if we remove a given vertex v *)

Variables (Lv Le : Type) (I : finType) (G : graph Lv Le) (f : edge G -> option I) (v : G).

(* Notations for the graph without v, and the function induced by f on it *)
Local Notation G' := (remove_vertex v).
Local Notation f' := (@remove_vertex_f _ _ _ _ f v).

Lemma remove_vertex_None_nb :
  #|~: f' @^-1 None| = #|~: f @^-1 None :\: edges_at v|.
Proof.
  rewrite -!card_set_subset.
  assert (Hg : forall (e : {E | E \notin f' @^-1 None}),
    (val (val e) \notin edges_at v) && (val (val e) \in ~: f @^-1 None)).
  { move => [[? In] E] /=. splitb.
    - clear - In. by rewrite in_set in In.
    - revert E. by rewrite !in_set. }
  set g : {e | e \notin f' @^-1 None} ->
    {e : edge G | (e \notin edges_at v) && (e \in ~: f @^-1 None)} :=
    fun e => Sub (val (val e)) (Hg e).
  assert (Hh : forall (e : {e : edge G | (e \notin edges_at v) && (e \in ~: f @^-1 None)}),
    val e \in ~: edges_at v).
  { move => [? /andP[? _]] /=. by rewrite in_set. }
  assert (Hh' : forall (e : {e : edge G | (e \notin edges_at v) && (e \in ~: f @^-1 None)}),
    (Sub (val e) (Hh e) \notin f' @^-1 None)).
  { move => [e E] /=.
    rewrite in_set /remove_vertex_f /=.
    revert E => /andP[_]. by rewrite !in_set. }
  set h : {e : edge G | (e \notin edges_at v) && (e \in ~: f @^-1 None)} ->
    {e | e \notin f' @^-1 None} :=
    fun e => Sub (Sub (val e) (Hh e)) (Hh' e).
  apply (@bij_card_eq _ _ g), (@Bijective _ _ _ h); move => *; cbnb.
Qed.

Lemma remove_vertex_uconnected_to u w :
  is_uconnected f' u w -> is_uconnected f (val u) (val w).
Proof.
  revert u w; move => [u U] [w W] /existsP[[q /andP[/andP[Wq Uq]] Nq] _] /=. apply /existsP.
  enough (Q' : well_colored_utrail f u w [seq (val e.1, e.2) | e <- q])
    by by exists (Sub _ Q').
  revert u U Wq Uq Nq; induction q as [ | [[e E] b] q IHq] => u U.
  { move => *. splitb. }
  cbnb; rewrite /remove_vertex_f /= !in_cons => /andP[? Wq] /andP[? Uq] /norP[? Nq].
  revert IHq => /(_ _ _ Wq Uq Nq) /andP[/andP[? ?] ?].
  rewrite /well_colored_utrail /= in_cons -map_comp. splitb.
Qed.

Lemma remove_vertex_uconnected_to_NS :
  {in ~: f @^-1 None &, injective f} -> forall u w, ~~ is_uconnected f v (val u) ->
  is_uconnected f' u w = is_uconnected f (val u) (val w).
Proof.
  move => F [u U] [w W] /= /existsPn /= Hu.
  destruct (is_uconnected f u w) eqn:UW.
  2:{ destruct (is_uconnected f' (Sub u U) (Sub w W)) eqn:UW'; trivial.
    by rewrite (remove_vertex_uconnected_to UW') in UW. }
  revert UW => /existsP[[p P] _].
  revert u U Hu P; induction p as [ | e p IHp] => u U Hu P.
  { revert P => /andP[/andP[/eqP-? _] _]; subst w.
    rewrite (eq_irrelevance U W).
    apply is_uconnected_id. }
  revert P => /andP[/andP[/= /andP[/eqP-? Wp] /andP[up Up]]];
  rewrite in_cons => /norP[/eqP-np Np]; subst u.
  assert (P' : well_colored_utrail f (utarget e) w p) by splitb.
  assert (U' : utarget e \in [set~ v]).
  { rewrite !in_set in_set1.
    apply /eqP => Hc.
    enough (Pc : well_colored_utrail f v (usource e) [:: (e.1, ~~e.2)]) by by specialize (Hu (Sub _ Pc)).
    rewrite well_colored_utrail_cons well_colored_utrail_of_nil !uendpoint_reversed Hc !eq_refl /=. by apply /eqP. }
  assert (Hu' : Well_colored_utrail f v (utarget e) -> false).
  { move=> [q /andP[/andP[Wq _ ] Nq]].
    enough (Well_colored_utrail f v (usource e)) by by apply Hu.
    apply (@uconnected_simpl _ _ _ _ _ F _ _ (rcons q (e.1, ~~e.2))); trivial.
    - by rewrite uwalk_rcons 2!uendpoint_reversed Wq eq_refl.
    - rewrite map_rcons in_rcons negb_orb Nq andb_true_r. by apply /eqP. }
  move: IHp => /(_ _ U' Hu' P') /existsP[[q /andP[/andP[Wq _ ] Nq]] _] {Hu' P'}.
  enough (P : Well_colored_utrail f' (Sub (usource e) U) (Sub w W)).
  { apply/existsP. by exists P. }
  assert (E : e.1 \in ~: edges_at v).
  { clear - U U'. revert U U'; rewrite !in_set !in_set1 => ? ?.
    apply /existsPn; move => []; by destruct e as [e []]. }
  apply (@uconnected_simpl _ _ _ _ _ (remove_vertex_f_sinj F) _ _ ((Sub e.1 E, e.2) :: q)).
  - assert (Hr : (Sub (endpoint e.2 (sval (Sub e.1 E))) (consistent_del1 _ (valP _))) =
      (Sub (utarget e) U' : G')) by cbnb.
    cbn. rewrite {}Hr. splitb.
  - splitb. by apply/eqP.
Qed.

Lemma remove_vertex_uconnected_NS_staying (u : G') :
  ~~ is_uconnected f v (val u) ->
  [set val w | w : G' & is_uconnected f (val u) (val w)] = [set w | is_uconnected f (val u) w].
Proof.
  intro Hu.
  apply /setP => w.
  rewrite in_set.
  destruct (is_uconnected f (val u) w) eqn:UW; apply /imsetP.
  - assert (W : w \in [set~ v]).
    { rewrite in_set in_set1. apply /eqP => ?; subst w.
      contradict Hu; apply /negP/negPn.
      by apply is_uconnected_sym. }
    exists (Sub w W); rewrite ?in_set; cbnb.
  - move => [[w' ?]]. rewrite in_set /= => Hc ?; subst w'.
    by rewrite Hc in UW.
Qed.

Lemma remove_vertex_uconnected_NS_Hg (E : sig (pred_of_set
    [set [set w : G' | is_uconnected f (val u) (val w)] | u : G' & ~~ is_uconnected f v (val u)])) :
  [set val u | u in val E] \in [set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u].
Proof.
  destruct E as [E HE].
  assert (HE' := HE). revert HE' => /imsetP/sig2_eqW[u Hu ?]; subst E.
  rewrite in_set in Hu.
  rewrite SubK (remove_vertex_uconnected_NS_staying Hu).
  apply /imsetP. exists (val u); by rewrite // in_set.
Qed.

Lemma remove_vertex_uconnected_NS :
  {in ~: f @^-1 None &, injective f} ->
  #|[set [set w : G' | is_uconnected f (val u) (val w)] | u : G' & ~~ is_uconnected f v (val u)]| =
  #|[set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u]|.
Proof.
  move => F.
  rewrite -card_sig -[in RHS]card_sig.
  set g : sig (pred_of_set
    [set [set w | is_uconnected f (val u) (val w)] | u : G' & ~~ is_uconnected f v (val u)]) ->
    sig (pred_of_set [set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u]) :=
    fun E => Sub [set val u | u in val E] (remove_vertex_uconnected_NS_Hg E).
  assert (Hh : forall u : G, ~~ is_uconnected f v u -> [set w | is_uconnected f u (val w)] \in
    [set [set w : G' | is_uconnected f (val u) (val w)] | u : G' & ~~ is_uconnected f v (val u)]).
  { move => u Hu.
    apply /imsetP.
    assert (U : u \in [set~ v]).
    { rewrite in_set in_set1. apply /eqP => ?; subst u.
      contradict Hu; apply /negP/negPn.
      apply is_uconnected_id. }
    exists (Sub u U); by rewrite // in_set. }
  assert (Hh' : forall E : sig (pred_of_set [set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u]),
    {u : G | ~~ is_uconnected f v u & val E = [set w | is_uconnected f u w]}).
  { move=> [E /= /imsetP/sig2_eqW[u Hu ?]].
    rewrite in_set in Hu.
    by exists u. }
  set h : sig (pred_of_set [set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u])
    -> sig (pred_of_set [set [set w | is_uconnected f (val u) (val w)] |
    u : G' & ~~ is_uconnected f v (val u)]) :=
    fun E => let (u, Hu, _) := Hh' E in Sub [set w | is_uconnected f u (val w)] (Hh u Hu).
  apply (bij_card_eq (f := g)), (Bijective (g := h)).
  - move => E.
    unfold h. destruct (Hh' (g E)) as [u U Hu].
    destruct E as [E HE].
    apply/eqP. rewrite eq_sym sub_val_eq /=. apply/eqP.
    revert Hu. rewrite /g /=.
    revert HE => /imsetP[[w W] Hw ?]. subst E; simpl.
    move => /setP/(_ u).
    rewrite !in_set is_uconnected_id.
    move => /imsetP[[x X]]. rewrite !in_set /= => WU ?. subst x.
    apply /setP; move => {X} [x X].
    rewrite !in_set /=.
    by apply (is_uconnected_eq F).
  - move => E.
    unfold h, g. destruct (Hh' E) as [u U Hu].
    destruct E as [E HE].
    apply/eqP. rewrite sub_val_eq /=. apply/eqP.
    simpl in Hu; subst E.
    apply /setP => w.
    rewrite in_set.
    destruct (is_uconnected f u w) eqn:UW.
    + apply /imsetP.
      assert (W : w \in [set~ v]).
      { rewrite in_set in_set1. apply /eqP => ?; subst w.
        contradict U; apply /negP/negPn.
        by apply is_uconnected_sym. }
      exists (Sub w W); [ | cbnb].
      by rewrite in_set.
    + apply /imsetP. move => [[x X]]. rewrite in_set /= => UX ?; subst x.
      by rewrite UX in UW.
Qed.

Lemma uconnected_cc :
  {in ~: f @^-1 None &, injective f} ->
  [set [set w | is_uconnected f u w] | u : G & is_uconnected f v u] =
  [set [set w | is_uconnected f v w]].
Proof.
  move => F.
  apply /setP => E.
  rewrite in_set1.
  destruct (E == [set w | is_uconnected f v w]) eqn:B; revert B => /eqP-B.
  - subst E.
    apply /imsetP.
    exists v; trivial.
    rewrite !in_set.
    apply is_uconnected_id.
  - apply /imsetP. move => [u]; rewrite !in_set => VU ?; subst E.
    contradict B.
    apply /setP => w.
    rewrite !in_set.
    by apply is_uconnected_eq, is_uconnected_sym.
Qed.

Lemma remove_vertex_uconnected_S_Hg :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  forall (E : sig (pred_of_set [set [set w | is_uconnected f' u w]
    | u : G' & is_uconnected f v (val u)])),
  { u : G' | val u \in neighbours f v &
    val E = [set w : G' | is_uconnected f' u w]}.
Proof.
  move => F A [E HE] /=.
  revert HE => /imsetP/sig2_eqW[[u U] VU ?]; subst E.
  rewrite !in_set /= in VU. apply is_uconnected_sym in VU.
  revert VU => /existsP/sigW[[p P] _].
  revert P; case/lastP: p => [ | p e].
  { move => /andP[/andP[/eqP ? _] _]; subst u.
    contradict U; apply /negP.
    by rewrite in_set in_set1 negb_involutive. }
  rewrite /well_colored_utrail uwalk_rcons map_rcons rcons_uniq in_rcons
    => /andP[/andP[/andP[Wp /eqP Et] /andP[Ep Up]]] /norP[/eqP En Np].
  wlog : e p Wp Up Np Et Ep En / forall a, a \in p -> utarget a <> v.
  { move => Hw.
    destruct [forall a, (a \in p) ==> (utarget a != v)] eqn:HHw.
    { apply (Hw _ _ Wp); trivial.
      move => a Ain. by revert HHw => /forallP /(_ a) /implyP /(_ Ain) /eqP-?. }
    revert HHw => /forallPn/sigW[x].
    rewrite negb_imply negb_involutive => /andP[Xin Xv].
    assert (Xin0 := @in_elt_sub_fst _ _ (fun f => utarget f == v) _ Xv Xin).
    revert Xv => {Xin} /eqP-Xv.
    assert (Xin' : exists n, [exists a, (p == take n p ++ a :: drop n.+1 p) &&
      (utarget a == utarget x) && [forall f, (f \in take n p) ==> (utarget f != utarget x)]]).
    { destruct Xin0 as [m [a [Hp [Ha Xin]]]].
      exists m; apply /existsP; exists a.
      rewrite Xv {1}Hp Ha. splitb.
      apply /forallP => ?; apply /implyP => ?.
      by apply Xin. }
    revert Xin' => {Xin0} /sigW[nx /existsP/sigW[t /andP[/andP[/eqP Hp /eqP Tt] /forallP Inpx]]].
    rewrite Xv in Inpx. rewrite Xv {x Xv} in Tt.
    assert (P' : well_colored_utrail f u (usource t) (take nx p)).
    { assert (P : well_colored_utrail f u (usource e) p) by splitb.
      rewrite Hp in P. rewrite Hp in Wp.
      destruct (well_colored_utrail_sub P) as [P' _].
      by rewrite (uwalk_sub_middle Wp) in P'. }
    revert P' => /andP[/andP[Wp' Up'] Np'].
    apply (Hw _ _ Wp' Up' Np'); trivial.
    - revert Up. rewrite {1}Hp map_cat cat_uniq /=. introb.
    - revert Np. rewrite {1}Hp map_cat mem_cat /= in_cons. introb.
    - move => a Ain ?. by revert Inpx => /(_ a) /implyP /(_ Ain) /eqP-?. }
  move => Hpv.
  set w := usource e.
  assert (P : well_colored_utrail f u w p) by splitb.
  clear Wp Up Np.
  assert (W : w \in [set~ v]).
  { rewrite /w in_set in_set1. apply /eqP => Hc.
    assert (Pe : well_colored_utrail f v v [:: e]).
    { rewrite /well_colored_utrail /= Et -Hc in_cons orb_false_r. splitb. by apply /eqP. }
    specialize (A _ (Sub _ Pe)).
    contradict A. cbnb. }
  exists (Sub w W).
  { rewrite /= /neighbours.
    apply /imsetP. exists (e.1, ~~e.2); trivial.
    rewrite in_set uendpoint_reversed Et eq_refl andb_true_r. by apply /eqP; apply nesym. }
  apply /setP => x.
  rewrite !in_set.
  apply (is_uconnected_eq (remove_vertex_f_sinj F)). clear x.
  apply /existsP.
  revert u U P; induction p as [ | a p IHp] => u U P.
  { revert P => /andP[/andP[/eqP ? _] _]; subst u.
    rewrite (eq_irrelevance U W).
    by exists (well_colored_utrail_nil _ _). }
  revert P => /andP[/andP[/= /andP[/eqP Ha Wp] /andP[up Up]]];
  rewrite in_cons => /norP[/eqP np Np]; subst w.
  assert (P' : well_colored_utrail f (utarget a) (usource e) p) by splitb.
  revert Ep; rewrite /= in_cons => /norP[/eqP ? Ep].
  assert (U' : utarget a \in [set~ v]).
  { rewrite in_set in_set1. apply /eqP.
    apply Hpv. rewrite in_cons. caseb. }
  assert (Hpv' : forall a, a \in p -> utarget a <> v).
  { move => *. apply Hpv. rewrite in_cons. caseb. }
  specialize (IHp Ep Hpv' _ U' P'). destruct IHp as [[pf Pf] _].
  enough (P : Well_colored_utrail f' (Sub u U) (Sub (usource e) W))
    by by exists P.
  assert (U'' : usource a != v) by by revert U; rewrite in_set in_set1 Ha.
  assert (Ain : a.1 \in ~: edges_at v).
  { clear - U U' U''. revert U U'; rewrite !in_set !in_set1 /incident => ? ?.
    by apply /existsPn; move => []; destruct a as [a []]. }
  revert Pf => /andP[/andP[Wpf _ ] Npf].
  apply (@uconnected_simpl _ _ _ _ _ (remove_vertex_f_sinj F) _ _ ((Sub a.1 Ain, a.2) :: pf)); simpl.
  - assert ((Sub (utarget a) _) = Sub (utarget a) U') as -> by cbnb.
    splitb. by cbn; apply /eqP.
  - rewrite /= in_cons. splitb. by apply /eqP.
Qed.

Definition remove_vertex_uconnected_S_g
  (F : {in ~: f @^-1 None &, injective f}) (A : uacyclic f) :
  sig (pred_of_set [set [set w | is_uconnected f' u w]
    | u : G' & is_uconnected f v (val u)]) ->
  sig (pred_of_set (neighbours f v)) := fun E =>
    let (u, U, _) := remove_vertex_uconnected_S_Hg F A E in Sub (val u) U.

Lemma remove_vertex_uconnected_S_Hh :
  uacyclic f ->
  forall u : sig (pred_of_set (neighbours f v)), val u \in [set~ v].
Proof.
  move=> A [u U].
  rewrite /= in_set in_set1. apply/eqP => ?. subst u.
  enough (exists (e : edge G), source e = target e /\ None <> f e) as [e [Ce Ne]].
  { assert (Pe : well_colored_utrail f (source e) (target e) [:: forward e]).
    { rewrite /well_colored_utrail /= in_cons orb_false_r. splitb. by apply /eqP. }
    rewrite Ce in Pe.
    specialize (A _ (Sub _ Pe)).
    contradict A; cbnb. }
  assert (Hu : v \in neighbours f v) by by []. clear U.
  revert Hu => /imsetP[[e b]]; rewrite in_set => /andP[/eqP-Ne /eqP-E] E'; apply nesym in Ne.
  exists e. split; trivial.
  rewrite -E in E'.
  by destruct b.
Qed.

Lemma remove_vertex_uconnected_S_Hh'
  (A : uacyclic f) (u : sig (pred_of_set (neighbours f v))) :
  [set w | is_uconnected f'
    (Sub (val u) (remove_vertex_uconnected_S_Hh A u)) w]
  \in [set [set w | is_uconnected f' u0 w]
    | u0 : G' & is_uconnected f v (val u0)].
Proof.
  apply /imsetP.
  exists (Sub (val u) (remove_vertex_uconnected_S_Hh A u)); trivial.
  destruct u as [u U].
  rewrite !in_set /=.
  assert (Hu : u \in neighbours f v) by by []. clear U.
  apply /existsP.
  revert Hu => /imsetP[e]; rewrite in_set => /andP[/eqP Ne /eqP E] E'; apply nesym in Ne.
  assert (Pe : well_colored_utrail f v u [:: e]).
  { rewrite /well_colored_utrail /= in_cons orb_false_r E E'. splitb. by apply /eqP. }
  by exists (Sub _ Pe).
Qed.

Definition remove_vertex_uconnected_S_h (A : uacyclic f) :
  sig (pred_of_set (neighbours f v)) ->
  sig (pred_of_set [set [set w | is_uconnected f' u w]
    | u : G' & is_uconnected f v (val u)]) :=
  fun u => Sub [set w | is_uconnected f'
    (Sub (val u) (remove_vertex_uconnected_S_Hh A u)) w] (remove_vertex_uconnected_S_Hh' A u).

Lemma remove_vertex_uconnected_S_gh (F : {in ~: f @^-1 None &, injective f}) (A : uacyclic f) :
  cancel (remove_vertex_uconnected_S_g F A) (remove_vertex_uconnected_S_h A).
Proof.
  move => E.
  unfold remove_vertex_uconnected_S_g.
  destruct (remove_vertex_uconnected_S_Hg F A E) as [[u Uin] U Hu]. simpl.
  unfold remove_vertex_uconnected_S_h.
  destruct E as [E HE]; cbnb; f_equal.
  simpl in Hu. subst E.
  by assert (Sub u (remove_vertex_uconnected_S_Hh A (Sub u U)) = Sub u Uin) as -> by cbnb.
Qed.

Lemma remove_vertex_uconnected_S_hg (F : {in ~: f @^-1 None &, injective f}) (A : uacyclic f) :
  cancel (remove_vertex_uconnected_S_h A) (remove_vertex_uconnected_S_g F A).
Proof.
  move => u.
  unfold remove_vertex_uconnected_S_g.
  destruct (remove_vertex_uconnected_S_Hg F A (remove_vertex_uconnected_S_h A u)) as [[w Win] W Hw],
    u as [u U].
  cbnb. simpl in W. rewrite /remove_vertex_uconnected_S_h /= in Hw.
  revert Hw => /setP /(_ (Sub w Win)). rewrite !in_set is_uconnected_id => /existsP[[p P] _].
  assert (exists ew, usource ew = w /\ utarget ew = v /\ None <> f ew.1) as [ew [Sew [Tew New]]].
  { revert W => /imsetP[e]; rewrite in_set => /andP[/eqP Ne /eqP E] E'; apply nesym in Ne; symmetry in E'.
    exists (e.1, ~~e.2). splitb. by rewrite uendpoint_reversed. }
  assert (exists eu, usource eu = v /\ utarget eu = u /\ None <> f eu.1) as [eu [Seu [Teu Neu]]].
  { assert (U' : u \in neighbours f v) by by [].
    revert U' => /imsetP[e]; rewrite in_set => /andP[/eqP Ne /eqP E] E'; apply nesym in Ne; symmetry in E'.
    exists e. splitb. }
  destruct (eq_comparable w u) as [ | Hneq]; trivial.
  assert (Heuw : eu.1 <> ew.1).
  { intro Hc. contradict Hneq.
    rewrite /uendpoint in Seu Tew.
    destruct eu as [eu []], ew as [ew []]; by rewrite -Sew -Teu /uendpoint Hc // -[in LHS]Hc /= Seu Tew. }
  enough (Pc : well_colored_utrail f v v (eu :: rcons [seq (val a.1, a.2) | a <- p] ew)).
  { clear P. specialize (A _ (Sub _ Pc)).
    contradict A; cbnb. }
  assert (Pm : well_colored_utrail f u w [seq (val a.1, a.2) | a <- p]).
  { revert P => /andP[/andP[Wp Up] Np].
    assert (Hr : [seq f e.1 | e <- [seq (val a.1, a.2) | a <- p]] = [seq f' e.1 | e <- p]).
    { rewrite -map_comp. by apply eq_map. }
    rewrite -Hr in Up; rewrite -Hr in Np.
    splitb.
    enough (He : forall (p : @upath _ _ G') u U w W, uwalk (Sub u U : G') (Sub w W) p ->
      uwalk u w [seq (val a.1, a.2) | a <- p]) by apply (He _ _ _ _ _ Wp).
    clear => p; induction p as [ | ? ? IHp] => // ? ? ? ?; cbnb => /andP[? W].
    splitb. apply (IHp _ _ _ _ W). }
  revert Pm => /andP[/andP[? ?] ?].
  rewrite /well_colored_utrail /= !map_rcons !mem_rcons !in_cons !mem_rcons !rcons_uniq.
  splitb; try by apply /eqP.
  - rewrite uwalk_rcons Tew Teu Sew. splitb.
  - apply /eqP => Hc.
    contradict Heuw.
    apply F; rewrite // !in_set; apply /eqP; by apply nesym.
  - apply /mapP. move => [[e b] Ein Eeq].
    assert (e = eu.1).
    { apply F; rewrite // !in_set; apply /eqP; [ | by apply nesym].
      move => Ne. contradict Eeq.
      rewrite Ne. by apply nesym. }
    subst e.
    revert Ein => /mapP[[[a Av] c] _ /eqP]; cbn => /andP[/eqP-? /eqP-?]. subst a c.
    contradict Av; apply /negP.
    rewrite !in_set negb_involutive /incident -Seu. apply /existsP.
    destruct eu as [? []]; by [exists false | exists true].
  - apply /mapP. move => [[e b] Ein Eeq].
    assert (e = ew.1).
    { apply F; rewrite // !in_set; apply /eqP; [ | by apply nesym].
      move => Ne. contradict Eeq.
      rewrite Ne. by apply nesym. }
    subst e.
    revert Ein => /mapP[[[a Av] c] _ /eqP]; cbn => /andP[/eqP-? /eqP-?]. subst a c.
    contradict Av; apply /negP.
    rewrite !in_set negb_involutive /incident -Tew. apply /existsP.
    destruct ew as [? []]; by [exists true | exists false].
Qed.

Lemma remove_vertex_uconnected_S_g_bij (F : {in ~: f @^-1 None &, injective f}) (A : uacyclic f) :
  bijective (remove_vertex_uconnected_S_g F A).
Proof. eapply Bijective; [apply remove_vertex_uconnected_S_gh | apply remove_vertex_uconnected_S_hg]. Qed.

Lemma remove_vertex_uconnected_S :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  #|[set [set w | is_uconnected f' u w] | u : _ & is_uconnected f v (val u)]| =
  #|neighbours f v|.
Proof.
  move => F A.
  rewrite -card_sig -[in RHS]card_sig.
  eapply bij_card_eq, (remove_vertex_uconnected_S_g_bij F A).
Qed.

Lemma remove_vertex_uconnected_nb :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  uconnected_nb f' + 1 = uconnected_nb f + #|~: f @^-1 None :&: edges_at v|.
Proof.
  move => F A.
  assert (equivalence_partition (is_uconnected f) setT =
    [set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u] :|:
    [set [set w | is_uconnected f u w] | u : G & is_uconnected f v u] /\
    equivalence_partition (is_uconnected f') setT =
    [set [set w | is_uconnected f' u w] | u : G' & ~~ is_uconnected f v (val u)] :|:
    [set [set w | is_uconnected f' u w] | u : G' & is_uconnected f v (val u)]) as [Hr Hr'].
  { split; rewrite /equivalence_partition imsetUCr; apply eq_imset => ?; by rewrite setT_in_pred. }
  rewrite /uconnected_nb Hr Hr' {Hr Hr'}.
  assert (Hr : [set [set w | is_uconnected f' u w] | u : G' & ~~ is_uconnected f v (val u)] =
    [set [set w | is_uconnected f (val u) (val w)] | u : G' & ~~ is_uconnected f v (val u)]).
  { apply eq_in_imset => u. rewrite in_set => Hu. apply eq_finset => w.
    by apply remove_vertex_uconnected_to_NS. }
  rewrite Hr {Hr} !cardsU.
  assert (Hr : [set [set w | is_uconnected f (val u) (val w)] | u : G' & ~~ is_uconnected f v (val u)]
    :&: [set [set w | is_uconnected f' u w] | u : G' & is_uconnected f v (val u)] = set0).
  { apply disjoint_setI0. apply /disjointP => ? /imsetP [u U] ? /imsetP [w W]; subst.
    revert U W; rewrite !in_set => U W.
    move => /setP /(_ u). rewrite !in_set is_uconnected_id => Hc. symmetry in Hc.
    apply is_uconnected_sym in Hc.
    rewrite remove_vertex_uconnected_to_NS // in Hc.
    apply is_uconnected_sym in Hc.
    contradict U; apply /negP/negPn.
    apply (is_uconnected_comp F W Hc). }
  rewrite Hr {Hr} cards0.
  assert (Hr : [set [set w | is_uconnected f u w] | u : G & ~~ is_uconnected f v u]
    :&: [set [set w | is_uconnected f u w] | u : G & is_uconnected f v u] = set0).
  { apply disjoint_setI0. apply /disjointP => ? /imsetP [u U] ? /imsetP [w W]; subst.
    revert U W; rewrite !in_set => U W.
    move => /setP /(_ u). rewrite !in_set is_uconnected_id => Hc. symmetry in Hc.
    contradict U; apply /negP/negPn.
    apply (is_uconnected_comp F W Hc). }
  rewrite {}Hr cards0 remove_vertex_uconnected_NS // uconnected_cc // -/S cards1 remove_vertex_uconnected_S //
    neighbours_nb //=. lia.
Qed.

End Uacyclic_uconnected_nb.

Lemma uacyclic_uconnected_nb {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  uconnected_nb f + #|~: f @^-1 None| = #|G|.
Proof.
  remember #|G| as n eqn:N; symmetry in N.
  revert G N f; induction n as [ | n IH] => G N f F A.
  { rewrite -cardsT in N. apply cards0_eq in N.
    rewrite /uconnected_nb N /equivalence_partition imset0 cards0.
    enough (#|~: f @^-1 None| <= 0) by lia.
    enough (#|edge G| = 0) as <- by apply max_card.
    apply eq_card0 => e.
    assert (H : source e \in set0) by by rewrite -N.
    by rewrite in_set in H. }
  destruct (set_0Vmem [set: G]) as [Hc | [v _]].
  { contradict N. by rewrite -cardsT Hc cards0. }
  set f' := remove_vertex_f f (v := v).
  assert (N' : #|remove_vertex v| = n) by (rewrite -(remove_vertex_card v) in N; lia).
  assert (F' : {in ~: f' @^-1 None &, injective f'}) by by apply remove_vertex_f_sinj.
  specialize (IH _ N' _ F' (remove_vertex_uacyclic A)).
  assert (#|~: f' @^-1 None| = #|~: f @^-1 None :\: edges_at v|) by by apply remove_vertex_None_nb.
  assert (uconnected_nb f' + 1 = uconnected_nb f + #|~: f @^-1 None :&: edges_at v|)
    by by apply remove_vertex_uconnected_nb.
  assert (#|~: f @^-1 None| = #|~: f @^-1 None :\: edges_at v| + #|~: f @^-1 None :&: edges_at v|) as ->.
  { rewrite cardsD.
    enough (#|~: f @^-1 None| >= #|~: f @^-1 None :&: edges_at v|) by lia.
    rewrite -(cardsID (edges_at v) (~: f @^-1 None)).
    lia. }
  simpl in *. lia.
Qed.
(* TODO simplify this proof with all its parts *)