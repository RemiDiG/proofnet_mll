(* Extension for [mgraph] of the library GraphTheory *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From HB Require Import structures.
From GraphTheory Require Import preliminaries mgraph structures bij setoid_bigop.
From Yalla Require Import mll_prelim graph_more upath simple_upath.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Section Supath.
Context {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I).

(** ** Simple undirected paths : paths whose edges have different non-forbidden id *)
(** The function f : edge G -> option I is used to identify some edges. *)
(** Taking f := fun e => Some e gives the standard simple paths, which do not use the same edge twice *)
Definition supath (p : upath) : bool :=
  (uwalk p) && uniq [seq f e.1 | e <- p] && (None \notin [seq f e.1 | e <- p]).

Lemma upath_size p :
  supath p -> size p < S #|edge G|.
Proof.
  move => /andP[/andP[_ U] _].
  rewrite map_comp in U.
  apply map_uniq in U.
  revert U => /card_uniqP-U.
  rewrite size_map in U.
  rewrite -U.
  exact: max_card.
Qed.

Definition Supath := {p : upath | supath p}.
(* TODO
This is better than
Record Supath : predArgType := {upval :> upath; upvalK : supath upval}.
for it directly inherits a countType structure.
However, we lose the coercion Supath >-> upath.
*)

Definition Supath_tuple (p : Supath) : {n : 'I_(S #|edge G|) & n.-tuple (edge G * bool)} :=
  let (p, Up) := p in existT _ (Ordinal (upath_size Up)) (in_tuple p).

Definition tuple_Supath
  (m : {n : 'I_(S #|edge G|) & n.-tuple (edge G * bool)}) : option Supath :=
  let (_, p) := m in match boolP (supath p) with
  | AltTrue P => Some (Sub (val p) P)
  | AltFalse _ => None
  end.

Lemma Supath_tupleK :
  pcancel Supath_tuple tuple_Supath.
Proof.
  move=> [/= p P].
  case: {-}_ / boolP; last by rewrite P.
  move=> P'. by rewrite (bool_irrelevance P' P).
Qed.

Set Warnings "-redundant-canonical-projection". (* to ignore warnings of already canonical *)
HB.instance Definition _ := Countable.on Supath. (* To prevent delta-expansion *)
HB.instance Definition _ : isFinite Supath := PCanIsFinite Supath_tupleK.
Set Warnings "redundant-canonical-projection".

End Supath.


(* Lemma supath_endpoint {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I)
  (s t : G) (p : Supath f s t) :
  upath_source s (val p) = s /\ upath_target s (val p) = t.
Proof. destruct p as [p P]. revert P => /= /andP[/andP[W _] _]. by apply uwalk_endpoint. Qed. *)

Lemma supath_nin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I)
  (p q : upath) e b :
  supath f (p ++ e :: q) -> (e.1, b) \notin p ++ q.
Proof.
  rewrite /supath !map_cat !cat_uniq /=.
  move => /andP[/andP[_ /andP[_ /andP[/norP[P _] /andP[Q _]]]] _].
  rewrite mem_cat; apply /negP => /orP[? | ?];
  [contradict P | contradict Q]; apply /negP/negPn/mapP; by exists (e.1, b).
Qed.

Lemma supath_catK {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G)
  (p : Supath f) (q : Supath f) :
  upath_target v (val p) = upath_source v (val q) ->
  upath_disjoint f (val p) (val q) -> supath f (val p ++ val q).
Proof.
  move: p q => [p /andP[/andP[Wp Up] Np]] [q /andP[/andP[Wq Uq] Nq]] /= target_p_eq_source_q disjoint_p_q.
  splitb.
  - rewrite uwalk_cat Wp Wq !andb_true_r /=.
    destruct p; first by [].
    destruct q; first by rewrite orb_true_r.
    apply/orP. right. apply/forallP => ? /=.
    by move: target_p_eq_source_q => /= ->.
  - rewrite map_cat cat_uniq. splitb.
    by rewrite /upath_disjoint disjoint_sym disjoint_has in disjoint_p_q.
  - rewrite map_cat mem_cat. splitb.
Qed.

Definition supath_cat {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G)
  (p : Supath f) (q : Supath f) (endpoints : upath_target v (val p) = upath_source v (val q))
  (D : upath_disjoint f (val p) (val q)) : Supath f :=
  Sub (val p ++ val q) (supath_catK endpoints D).

Lemma supath_subKK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I)
  (p q : upath) :
  supath f (p ++ q) -> supath f p /\ supath f q.
Proof.
  move=> /andP[/andP[W ] ].
  rewrite !map_cat cat_uniq mem_cat =>/andP[Up /andP[_ ?]] /norP[? ?].
  splitb; apply (uwalk_subK W).
Qed.

Lemma supath_subK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I)
  (p q r : upath) :
  supath f (p ++ q ++ r) -> supath f q.
Proof.
  move=> H.
  destruct (supath_subKK H) as [_ H'].
  by destruct (supath_subKK H') as [-> _].
Qed.

Definition supath_sub {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I)
  (p q r : upath) (H : supath f (p ++ q ++ r)) : Supath _ :=
  Sub q (supath_subK H).

Lemma supath_revK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (p : upath) :
  supath f p -> supath f (upath_rev p).
Proof.
  move=> /andP[/andP[W U] N]. splitb.
  - by rewrite uwalk_rev.
  - by rewrite map_comp upath_rev_fst map_rev rev_uniq -map_comp.
  - by rewrite map_comp upath_rev_fst map_rev in_rev -map_comp.
Qed.

Definition supath_rev {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I)
  (p : Supath f) : Supath f :=
  Sub _ (supath_revK (valP p)).

Lemma supath_turnK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (v : G)
  (p : upath) :
  upath_source v p = upath_target v p ->
  supath f p -> supath f (upath_turn p).
Proof.
  move=> cyclic_p /andP[/andP[uwalk_p uniq_p] none_p]. splitb.
  - exact: uwalk_turn cyclic_p uwalk_p.
  - destruct p; first by [].
    rewrite map_rcons rcons_uniq.
    by move: uniq_p => /= /andP[-> ->].
  - destruct p; first by [].
    rewrite map_rcons in_rcons.
    by move: none_p; rewrite /= in_cons.
Qed.
(*
Definition supath_turn {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G)
  (e : edge G * bool) (???(e :: p) : Supath f s s) := {| upval := _ ; upvalK := supath_turnK (upvalK ???) |}. *)

Lemma supath_turnsK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (v : G)
  (p q : upath) :
  upath_source v (p ++ q) = upath_target v (p ++ q) ->
  supath f (p ++ q) -> supath f (q ++ p).
Proof.
  move => cyclic_pq /andP[/andP[W U] N]. splitb.
  - exact: uwalk_turns cyclic_pq W.
  - by rewrite map_cat uniq_catC -map_cat.
  - by rewrite map_cat mem_cat orbC -mem_cat -map_cat.
Qed.
(* 
Definition supath_turns {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G)
  (p ++ q : Supath f s s) := ???. *)

Lemma supath_nilK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :
  supath f [::].
Proof. by []. Qed.

Definition supath_nil {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) : Supath f :=
  Sub [::] (supath_nilK f).


(* TODO would be good to have it in bool! *)
(*
Definition uacyclic {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) : bool :=
  [forall x : G, [forall p : Supath f x x, p == supath_nil f x]].
Lemma uacyclic_T {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :
  uacyclic f -> forall (x : G) (p : Supath f x x), p = supath_nil f x.
Proof. move => C x p. by revert C => /forallP/(_ x)/forallP/(_ p)/eqP. Qed.
*)
Definition uacyclic {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :=
  forall (v : G) (p : Supath f), upath_source v (val p) = upath_target v (val p) -> p = supath_nil f.

(* We define connectivity by "forall (x y : G), exists (_ : Supath f x y), true" and not
   "forall (x y : G), Supath f x y" to be in Prop instead of Type, which allows case analysis
   as well as to define properties such as tree <-> uacyclic /\ uconnected *)
(* TODO would be good to have it in bool! try it, and acyc too *)
(*
Definition uconnected {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) : bool :=
  [forall x : G, [forall y : G, [exists p : Supath f x y, true]]].
Lemma uconnected_T {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :
  uconnected f -> forall (x y : G), Supath f x y.
Proof. move => C x y. by revert C => /forallP/(_ x)/forallP/(_ y)/existsP/sigW[? _]. Qed.
*)
Definition uconnected {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :=
  forall (x y : G), exists (p : Supath f), upath_source x (val p) = x /\ upath_target x (val p) = y.


(** ** Connectivity for functions injective except on None *)
Definition is_uconnected {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (x y : G) :=
  [exists p : (Supath f : finType), (upath_source x (val p) == x) && (upath_target x (val p) == y)].

Definition is_uconnected_id {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (x : G) :
  is_uconnected f x x.
Proof. apply/existsP. exists (supath_nil _). by rewrite /= eq_refl. Defined.

Definition is_uconnected_sym {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (x y : G) :
  is_uconnected f x y -> is_uconnected f y x.
Proof.
  move=> /existsP[P H].
  apply/existsP. exists (supath_rev P).
  move: H. rewrite !upath_endpoint_rev.
  destruct P as [[ | ? ?] simple_p].
  - by rewrite !eq_refl eq_sym.
  - by rewrite andbC.
Defined.

Lemma simple_upath_is_supath {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) p :
  {in ~: f @^-1 None &, injective f} ->
  simple_upath p -> None \notin [seq f e.1 | e <- p] ->
  supath f p.
Proof.
  rewrite /simple_upath /supath.
  move=> F /andP[/andP[/andP[-> _] uniq_p] _] none_p.
  rewrite none_p andb_true_r /=.
  rewrite map_comp map_inj_in_uniq //.
  hnf => e1 e2 e1_in _ f_e1_e2.
  assert (f e1 != None).
  { apply/eqP => f_e1. contradict none_p. apply/negP/negPn.
    rewrite -f_e1 map_comp.
    by apply map_f. }
  apply (F e1 e2); trivial.
  - by rewrite in_set -mem_preim.
  - by rewrite in_set -mem_preim -f_e1_e2.
Qed.

Lemma uconnected_simpl {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G) p :
  {in ~: f @^-1 None &, injective f} -> uwalk p -> None \notin [seq f e.1 | e <- p] ->
  {P : Supath f | upath_source (upath_source v p) (val P) = upath_source v p /\
    upath_target (upath_source v p) (val P) = upath_target v p /\
    {subset val P <= p}}.
Proof.
  move=> F uwalk_p none_p.
  destruct (uwalk_to_simple_upath uwalk_p) as [[q simple_q] [endpoints_q sub_q_p]].
  assert (supath_q : supath f q).
  { apply (simple_upath_is_supath F simple_q).
    apply/negP => /mapP[e e_in_q none_e].
    contradict none_p. apply/negP/negPn/mapP.
    exists e; trivial.
    by apply sub_q_p. }
  destruct p.
  - by exists (supath_nil _).
  - exists (Sub q supath_q).
    destruct endpoints_q as [source_q target_q].
    move: source_q target_q sub_q_p => /= -> -> ?.
    by repeat split.
Qed.

Definition is_uconnected_comp {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} ->
  forall (x y z : G), is_uconnected f x y -> is_uconnected f y z -> is_uconnected f x z.
Proof.
  move=> F x y z /existsP[[pxy /= /andP[/andP[Wxy _] Nxy]] /andP[/eqP-source_x /eqP-target_y]]
    /existsP[[pyz /= /andP[/andP[Wyz _] Nyz]] /andP[/eqP-source_y /eqP-target_z]].
  edestruct (@uconnected_simpl _ _ _ _ f x (pxy ++ pyz)) as [pxz [source_pxz [target_pxz _]]]; trivial.
  - rewrite uwalk_cat Wxy Wyz.
    destruct pxy; first by [].
    destruct pyz; first by [].
    apply/forallP => v /=.
    by move: target_y source_y => /= -> ->.
  - by rewrite map_cat mem_cat negb_orb Nxy Nyz.
  - apply/existsP. exists pxz.
    move: source_pxz target_pxz source_x target_y source_y target_z.
    destruct pxz as [[ | ? ?] ?], pxy, pyz.
    + move=> /= _ _ _ -> _ ->. by rewrite !eq_refl.
    + move=> /= _ -> _ -> -> ->. by rewrite !eq_refl.
    + rewrite cats0 => /= _ -> -> -> _ ->. by rewrite !eq_refl.
    + rewrite /= map_cat last_cat => /= _ -> -> _ _ ->. by rewrite !eq_refl.
    + move=> /= -> -> _ -> _ ->. by rewrite !eq_refl.
    + move=> /= -> -> _ -> -> ->. by rewrite !eq_refl.
    + rewrite cats0 => /= -> -> -> -> _ ->. by rewrite !eq_refl.
    + rewrite /= map_cat last_cat => /= -> -> -> _ _ ->. by rewrite !eq_refl.
Defined.

Global Instance is_uconnected_Equivalence {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) : CEquivalence (is_uconnected f).
Proof. constructor. exact (is_uconnected_id _). exact (is_uconnected_sym (f := _)). exact (is_uconnected_comp F). Defined.

Lemma is_uconnected_eq {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} ->
  forall u v w, is_uconnected f u v ->
  is_uconnected f u w = is_uconnected f v w.
Proof.
  move=> F u v w UV.
  destruct (is_uconnected f v w) eqn:VW.
  - apply (is_uconnected_comp F UV VW).
  - destruct (is_uconnected f u w) eqn:UW; trivial.
    contradict VW; apply not_false_iff_true.
    apply (is_uconnected_comp F (is_uconnected_sym UV) UW).
Qed.

Lemma is_uconnected_equivalence {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} ->
  equivalence_rel (is_uconnected f).
Proof.
  move=> F x y z. split.
  - by apply is_uconnected_id.
  - by apply is_uconnected_eq.
Qed.

(** Equivalence classes of uconnected, so to speak about connected components *)
Definition uconnected_nb {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :=
  #|equivalence_partition (is_uconnected f) [set: G]|.

Lemma uconnected_to_nb1 {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  #|G| <> 0 -> uconnected f -> uconnected_nb f = 1.
Proof.
  move=> N C.
  destruct (set_0Vmem [set: G]) as [Hc | [v _]]; trivial.
  { contradict N. by rewrite -cardsT Hc cards0. }
  unfold uconnected_nb, equivalence_partition.
  apply/eqP/cards1P.
  exists [set u in [set: G] | is_uconnected f v u].
  apply/eqP/eq_set1P. split.
  { apply/imsetP. by exists v. }
  move=> ? /imsetP [u _ ?]; subst.
  apply eq_finset => w.
  rewrite in_set /=.
  transitivity true; [ | symmetry]; apply/existsP.
  - destruct (C u w) as [p [source_p target_p]].
    exists p. by rewrite source_p target_p !eq_refl.
  - destruct (C v w) as [p [source_p target_p]].
    exists p. by rewrite source_p target_p !eq_refl.
Qed.

Lemma uconnected_from_nb1 {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  uconnected_nb f = 1 -> uconnected f.
Proof.
  move=> /eqP/cards1P[S /eqP/eq_set1P[Sin Seq]] u v.
  assert (Suin : [set w in [set: G] | is_uconnected f u w] \in
    equivalence_partition (is_uconnected f) [set: G]).
  { apply/imsetP. by exists u. }
  assert (UW := Seq _ Suin). cbn in UW. subst S.
  assert (Svin : [set w in [set: G] | is_uconnected f v w] \in
    equivalence_partition (is_uconnected f) [set: G]).
  { apply/imsetP. by exists v. }
  assert (Heq := Seq _ Svin). cbn in Heq.
  assert (V : v \in [set w in [set: G] | is_uconnected f v w]).
  { rewrite in_set. splitb. apply is_uconnected_id. }
  rewrite Heq !in_set /= in V.
  move: V => /existsP[p /andP[/eqP-source_p /eqP-target_p]]. by exists p.
Qed.

Lemma nb1_not_empty {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  uconnected_nb f = 1 -> #|G| <> 0.
Proof.
  move=> /eqP/cards1P[? /eqP/eq_set1P[Sin _]] N.
  rewrite -cardsT in N. apply cards0_eq in N.
  contradict Sin. apply/negP.
  rewrite N /equivalence_partition. apply/imsetP. move=> [? In].
  contradict In. apply/negP.
  by rewrite !in_set.
Qed.

Definition neighbours {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G) :=
  [set utarget e | e : edge G * bool & (f e.1 != None) && (usource e == v)].

Lemma uacyclic_loop {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  uacyclic f -> forall e, f e <> None -> source e <> target e.
Proof.
  move=> A e En E.
  enough (P : supath f [:: forward e]).
  { specialize (A (source e) (Sub _ P) E).
    contradict A. cbnb. }
  rewrite /supath in_cons orb_false_r. splitb.
  apply/eqP. by apply nesym.
Qed.

Lemma uacyclip_2loop {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  {in [set e | f e.1 != None & usource e == v] &, injective (fun e : edge G * bool => utarget e)}.
Proof.
  move=> F A [e eb] [j jb]; rewrite !in_set /= =>
    /andP[/eqP-En /eqP-Es] /andP[/eqP-Jn /eqP-Js] T.
  apply /eqP/negPn/negP => /eqP-Hejb.
  assert (Hej : e <> j).
  { move => ?; subst j.
    destruct (eq_comparable eb jb) as [ | Hb]; [by subst jb | ].
    assert (Hf := uacyclic_loop A En). contradict Hf.
    by destruct eb, jb. }
  enough (P : supath f [:: (e, eb); (j, ~~ jb)]).
  { move: A => /(_ v (Sub _ P)). rewrite /= Es Js => /(_ Logic.eq_refl). cbnb. }
  rewrite /supath /= !in_cons !orb_false_r !andb_true_r.
  splitb; apply /eqP; rewrite ?negb_involutive //; try by apply nesym.
  intro Fej. contradict Hej.
  apply F; rewrite // !in_set; by apply/eqP.
Qed.

Lemma neighbours_nb {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  #|neighbours f v| = #|~: f @^-1 None :&: edges_at v|.
Proof.
  move=> F A.
  rewrite /neighbours card_in_imset -?card_set_subset; last by by apply uacyclip_2loop.
  assert (Hg : forall (e : {a | (f a.1 != None) && (usource a == v)}),
    ((val e).1 \in ~: f @^-1 None) && ((val e).1 \in edges_at v)).
  { move => [[e b] /= /andP[? ?]].
    rewrite !in_set. splitb.
    apply /existsP. by exists (~~b). }
  set g : {a | (f a.1 != None) && (usource a == v)} ->
    {e | (e \in ~: f @^-1 None) && (e \in edges_at v)} :=
    fun e => Sub (val e).1 (Hg e).
  assert (Hh : forall e : {e | (e \in ~: f @^-1 None) && (e \in edges_at v)},
    exists b, (f (val e, b).1 != None) && (usource (val e, b) == v)).
  { move => [e] /=.
    rewrite !in_set => /andP[? /existsP[b ?]].
    exists (~~b). splitb. by rewrite negb_involutive. }
  set h : {e | (e \in ~: f @^-1 None) && (e \in edges_at v)} ->
    {a | (f a.1 != None) && (usource a == v)} :=
    fun e => let (b, H) := sigW (Hh e) in Sub (val e, b) H.
  apply (@bij_card_eq _ _ g), (@Bijective _ _ _ h).
  - move => [e E].
    rewrite /h /g /=.
    destruct (sigW _) as [b H].
    apply /eqP. cbn. rewrite /= eq_refl /=. apply /eqP.
    destruct (eq_comparable b e.2) as [-> | Hbe]; trivial.
    revert E H => /andP[/eqP-En /eqP-V] /andP[_ /eqP-V'].
    assert (Hf := uacyclic_loop A En). contradict Hf.
    destruct b, e as [? []]; by rewrite // V V'.
  - move => ?. rewrite /h /g /=. destruct (sigW _). cbnb.
Qed.

Definition remove_vertex_f {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) : edge (remove_vertex v) -> option I :=
  fun e => f (val e).

Lemma remove_vertex_f_sinj {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) :
  {in ~: f @^-1 None &, injective f} ->
  {in ~: (@remove_vertex_f _ _ _ _ f v) @^-1 None &, injective (@remove_vertex_f _ _ _ _ f v)}.
Proof.
  move => F u w.
  rewrite !in_set /remove_vertex_f /= => /eqP-Fu /eqP-Fw Eq. cbnb.
  by apply F; rewrite // !in_set; apply /eqP.
Qed.

Lemma supath_induced {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (S : {set G})
  (p : Supath (fun (e : edge (induced S)) => f (val e))) :
  {q : Supath f & val q = [seq (val a.1, a.2) | a <- val p]}.
Proof.
  destruct p as [p P].
  move: P. induction p as [ | ([a A], b) p IH]; rewrite /supath /=.
  { move=> _. by exists (supath_nil _). }
  rewrite in_cons => /andP[/andP[/andP[/= /eqP-source_p W] /andP[u U]] /norP[n N]].
  assert (P : supath (fun (e : edge (induced S)) => f (val e)) p) by splitb.
  specialize (IH P). destruct IH as [[q Q] HQ].
  revert HQ; cbnb => ?; subst q.
  enough (QS : supath f ((a, b) :: _)) by by exists (Sub _ QS).
  move: Q. rewrite /supath /= in_cons -!map_comp. introb. splitb.
  move: source_p. clear => /eqP.
  rewrite eq_sym sub_val_eq /= => /eqP-<-. by destruct p.
Qed.

(*
Lemma supath_to_induced {Lv Le : Type} {G : graph Lv Le} (S : {set G})
  {I J : finType} (f : edge G -> option I) (f' : edge (induced S) -> option J)
  (p : Supath f s t) :
  (forall e (E : e \in edge_set S), None <> f e -> None <> f' (Sub e E)) ->
  (forall e a (E : e \in edge_set S) (A : a \in edge_set S),
    f' (Sub e E) = f' (Sub a A) -> f e = f a) ->
  (forall (e : (edge G) * bool), e \in val p -> e.1 \in edge_set S) ->
  forall (Sin : s \in S) (Tin : t \in S),
  {q : Supath f' (Sub s Sin) (Sub t Tin) & val p = [seq (val a.1, a.2) | a <- val q]}.
Proof. (* in fact can even deduce Sin and Tin, provided p not empty *)
  intros F0 F1 Hp Sin Tin.
  destruct p as [p P].
  simpl in Hp.
  revert s Sin P. induction p as [ | e p IHp] => s Sin.
  { rewrite /supath /=. introb.
    assert (Sin = Tin) by apply eq_irrelevance. subst.
    by exists (supath_nil _ _). }
  rewrite /supath /= in_cons => /andP[/andP[/andP[/eqP-? PW] /andP[Pu PU]] /norP[/eqP-Pn PN]].
  subst s.
  assert (P : supath f (utarget e) t p) by splitb.
  assert (E : e.1 \in edge_set S).
  { apply Hp. rewrite in_cons. caseb. }
  assert (Hp' : forall e, e \in p -> e.1 \in edge_set S).
  { intros. apply Hp. rewrite in_cons. caseb. }
  assert (T : utarget e \in S).
  { revert E. rewrite in_set. destruct e as [? []]; introb. }
  revert IHp => /= /(_ Hp' _ T P) {Hp Hp' P} [[q Q] ?]. subst p.
  enough (Q' : supath (f' : edge (induced _) -> _) (Sub (usource e) Sin) (Sub t Tin)
    ((Sub e.1 E : edge (induced S), e.2) :: q)).
  { exists (Sub _ Q'). by destruct e. }
  assert (E' : supath f' (Sub (usource e) Sin) (Sub (utarget e) T) [:: (Sub e.1 E, e.2)]). (* TODO lemma for edge supath? *)
  { rewrite /supath /= in_cons in_nil orb_false_r. splitb; try by cbnb.
    apply /eqP. clear - F0 Pn. by apply F0. }
  rewrite -cat1s.
  apply (@supath_catK _ _ _ _ _ _ _ _ (Sub _ E' : Supath f' _ _) (Sub _ Q)).
  rewrite /upath_disjoint disjoint_has /= orb_false_r.
  clear - F1 Pu.
  apply /mapP. move => [[[z Z] zb] Zin Zeq].
  contradict Pu. apply /negP/negPn/mapP.
  exists (z, zb); last by apply (F1 _ _ _ _ Zeq).
  simpl. revert Zin. generalize q. clear. intro l.
  induction l as [ | [? ?] ? H]; trivial.
  rewrite !in_cons. cbn.
  move => /orP[-> // | ?].
  apply /orP. right. by apply H.
Qed. (* TODO strictly more general than supath_induced? *)
*)

Lemma induced_upath_inside {Lv Le : Type} {G : graph Lv Le} (S : {set G}) (q : @upath _ _ (induced S)) e :
  e \in [seq (val a.1, a.2) | a <- q] -> e.1 \in edge_set S.
Proof. move => /mapP[[[e' Ein] ?] ? ?]. by subst e. Qed.

Lemma remove_vertex_uacyclic {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) :
  uacyclic f -> uacyclic (@remove_vertex_f _ _ _ _ f v).
Proof.
  move=> A [x X] [p' P'] /= cyclic_p'.
  apply val_inj. simpl.
  enough (P : supath f [seq (val e.1, e.2) | e <- p']).
  { move: A => /(_ x (Sub _ P)).
    move: cyclic_p'. clear. destruct p' as [ | e p']; first by [].
    destruct p' as [ | p' e' _] using last_ind.
    - move=> /= /eqP. by rewrite sub_val_eq /= => /eqP-H /(_ H) {H}.
    - rewrite /= -map_comp !map_rcons !last_rcons => /eqP. by rewrite sub_val_eq /= => /eqP-H /(_ H) {H}. }
  move: P' => /andP[/andP[W ?] ?].
  splitb; rewrite -?map_comp //.
  enough (H : uwalk p' -> uwalk [seq (val e.1, e.2) | e <- p']) by by apply (H W).
  clear. induction p' as [ | [[? ?] ?] p' IH]; cbn => //= /andP[/eqP--> W].
  rewrite (IH W) andb_true_r. by destruct p'.
Qed.

Lemma supath_cons {Lv Le : Type} {G : graph Lv Le}
  {I : finType} (f : edge G -> option I) e (p : upath) :
  supath f (e :: p) =
  (supath f p && (utarget e == upath_source (utarget e) p) &&
  (f e.1 \notin [seq f a.1 | a <- p]) && (None != f e.1)).
Proof.
  rewrite /supath /= in_cons negb_orb.
  destruct (uwalk p); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (uniq [seq f a.1 | a <- p]); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (None \notin [seq f a.1 | a <- p]) eqn:Hr; rewrite !Hr ?andb_false_r ?andb_true_r //=.
Qed. (* TODO use it everywhere *)

Lemma supath_rcons {Lv Le : Type} {G : graph Lv Le}
  {I : finType} (f : edge G -> option I) e (p : upath) :
  supath f (rcons p e) =
  (supath f p && (usource e == upath_target (usource e) p) &&
  (f e.1 \notin [seq f a.1 | a <- p]) && (None != f e.1)).
Proof.
  rewrite /supath /= map_rcons in_rcons rcons_uniq negb_orb uwalk_rcons.
  destruct (uwalk p); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (uniq [seq f a.1 | a <- p]); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (None \notin [seq f a.1 | a <- p]) eqn:Hr; rewrite !Hr ?andb_false_r ?andb_true_r //=.
Qed. (* TODO use it everywhere *)

Lemma supath_of_nil {Lv Le : Type} {G : graph Lv Le} {I : finType} (f : edge G -> option I) :
  supath f [::].
Proof. by []. Qed. (* TODO use it everywhere *)

Lemma supath_from_induced {Lv Le : Type} {G : graph Lv Le} (S : {set G})
  {I J : finType} (f : edge G -> option I) (f' : edge (induced S) -> option J)
  (q : Supath f') :
  (forall e (E : e \in edge_set S), None <> f' (Sub e E) -> None <> f e) ->
  (forall e a (E : e \in edge_set S) (A : a \in edge_set S),
    f e = f a -> f' (Sub e E) = f' (Sub a A)) ->
  supath f [seq (val a.1, a.2) | a <- val q].
Proof.
  move=> F0 F1.
  destruct q as [q simple_q].
  move: simple_q. induction q as [ | ([a A], b) q IH] => //=.
  rewrite !supath_cons => /andP[/andP[/andP[simple_q /eqP-source_q] uniq_q] /eqP-none_ab].
  move: IH => /(_ simple_q)--> /=. splitb.
  - move: source_q. destruct q => //= /eqP. by rewrite sub_val_eq /=.
  - clear - F1 uniq_q.
    apply/mapP. move => [c' /mapP[c Cin ?] Fc]. subst c'. simpl in Fc.
    contradict uniq_q. apply/negP/negPn/mapP.
    exists c; trivial.
    destruct c as [[? ?] ?]. by apply F1.
  - clear - F0 none_ab.
    apply/eqP. apply (F0 _ _ none_ab).
Qed.

(* TODO Supath pour turn et turns ? *)
