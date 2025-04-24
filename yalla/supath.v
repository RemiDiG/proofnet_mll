(* Extension for [mgraph] of the library GraphTheory *)
(* TODO file to reorganize and rename well_colored_utrail *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From HB Require Import structures.
From GraphTheory Require Import preliminaries mgraph structures bij setoid_bigop.
From Yalla Require Import mll_prelim graph_more upath.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Section WellColoredUtrailDef.
Context {Lv Le : Type} {G : graph Lv Le} {C : eqType} (c : edge G -> option C) (s t : G).

(** ** Well Colored Undirected Trails : undirected walks whose edges have different non-forbidden colors *)
(** The coloring c : edge G -> option I gives a coloring, with None the forbidden color. *)
(** Choosing c := fun e => Some e gives the standard undirected trails. *)
Definition well_colored_utrail (p : upath) : bool :=
  (uwalk s t p) && uniq [seq c e.1 | e <- p] && (None \notin [seq c e.1 | e <- p]).

Definition Well_colored_utrail := {p : upath | well_colored_utrail p}.
(* Coercion upath_of_Well_colored_utrail := val : Well_colored_utrail -> upath. *) (* TODO? *)
(*
This is better than
Record Well_colored_utrail : predArgType := {wcutval :> upath; _ : well_colored_utrail wcutval}.
Set Warnings "-redundant-canonical-projection". (* to ignore warnings of already canonical *)
HB.instance Definition _ := [isSub for wcutval].
(* TODO warnings *)
  HB.instance Definition _ := [Countable of Well_colored_utrail by <:].

for it directly inherits a countType structure.
*)

(* Well colored undirected trails are a finite type. *)
Lemma well_colored_utrail_size p :
  well_colored_utrail p -> size p < S #|edge G|.
Proof.
  move=> /andP[/andP[_ uniq_p] _].
  move: uniq_p. rewrite map_comp => /map_uniq/card_uniqP.
  rewrite size_map => <-.
  exact: max_card.
Qed.

Definition well_colored_utrail_tuple (p : Well_colored_utrail) : {n : 'I_(S #|edge G|) & n.-tuple (edge G * bool)} :=
  let (p, Up) := p in existT _ (Ordinal (well_colored_utrail_size Up)) (in_tuple p).

Definition tuple_well_colored_utrail
  (m : {n : 'I_(S #|edge G|) & n.-tuple (edge G * bool)}) : option Well_colored_utrail :=
  let (_, p) := m in match boolP (well_colored_utrail p) with
  | AltTrue  P => Some (Sub (val p) P)
  | AltFalse _ => None
  end.

Lemma well_colored_utrail_tupleK :
  pcancel well_colored_utrail_tuple tuple_well_colored_utrail.
Proof.
  move=> [p P] /=.
  case: {-}_ / boolP; last by rewrite P.
  move=> P'. by rewrite (bool_irrelevance P' P).
Qed.

Set Warnings "-redundant-canonical-projection". (* to ignore warnings of already canonical *)
HB.instance Definition _ := Countable.on Well_colored_utrail. (* To prevent delta-expansion *)
HB.instance Definition _ : isFinite Well_colored_utrail := PCanIsFinite well_colored_utrail_tupleK.
Set Warnings "redundant-canonical-projection".

End WellColoredUtrailDef.


(* Basic results on these trails. *)
Section WellColoredUtrailResults.
Context {Lv Le : Type} {G : graph Lv Le} {C : eqType} (c : edge G -> option C).

Lemma well_colored_utrail_is_uwalk (s t : G) p :
  well_colored_utrail c s t p -> uwalk s t p.
Proof. by move=> /andP[/andP[-> _] _]. Qed.

Lemma well_colored_utrail_of_nil (s t : G) :
  well_colored_utrail c s t [::] = (s == t).
Proof. by rewrite /well_colored_utrail /= 2!andb_true_r. Qed.
(* TODO use it everywhere *)

(* The empty path is a well-colored undirected trail. *)
Lemma well_colored_utrail_nilK (s : G) : well_colored_utrail c s s [::].
Proof. by rewrite well_colored_utrail_of_nil. Qed.

Definition well_colored_utrail_nil (s : G) : Well_colored_utrail c s s :=
  Sub [::] (well_colored_utrail_nilK s).

Lemma well_colored_utrail_cons (s t : G) e (p : upath) :
  well_colored_utrail c s t (e :: p) =
  (well_colored_utrail c (utarget e) t p && (usource e == s) &&
  (c e.1 \notin [seq c a.1 | a <- p]) && (None != c e.1)).
Proof. rewrite /well_colored_utrail /= in_cons negb_orb /=. lia. Qed.
(* TODO use it everywhere *)

Lemma well_colored_utrail_rcons (s t : G) e (p : upath) :
  well_colored_utrail c s t (rcons p e) =
  (well_colored_utrail c s (usource e) p && (utarget e == t) &&
  (c e.1 \notin [seq c a.1 | a <- p]) && (None != c e.1)).
Proof. rewrite /well_colored_utrail /= map_rcons in_rcons rcons_uniq negb_orb uwalk_rcons /=. lia. Qed.
(* TODO use it everywhere *)

Lemma well_colored_utrail_of_edge e :
  well_colored_utrail c (usource e) (utarget e) [:: e] = (c e.1 != None).
Proof. by rewrite well_colored_utrail_cons well_colored_utrail_of_nil !eq_refl /= eq_sym. Qed.
(* Use directly instead of re-proving it every time *)

Lemma well_colored_utrail_endpoint (b : bool) (s t : G) (p : Well_colored_utrail c s t) :
  upath_endpoint b s (val p) = (if b then t else s).
Proof. case: p => /= ? /andP[/andP[uwalk_p _] _]. by apply uwalk_endpoint. Qed.
Notation well_colored_utrail_source := (well_colored_utrail_endpoint false).
Notation well_colored_utrail_target := (well_colored_utrail_endpoint true).
(* TODO replace by -> uwalk *)

Lemma well_colored_utrail_nin (s t : G) (p q : upath) e b :
  well_colored_utrail c s t (p ++ e :: q) -> (e.1, b) \notin p ++ q.
Proof.
  rewrite /well_colored_utrail !map_cat !cat_uniq /=.
  move=> /andP[/andP[_ /andP[_ /andP[/norP[P _] /andP[Q _]]]] _].
  rewrite mem_cat. apply/negP => /orP[? | ?];
  [contradict P | contradict Q]; apply/negP/negPn/mapP; by exists (e.1, b).
Qed.

(* TODO a cat lemma instead ! *)
Lemma well_colored_utrail_cat (s t : G) (p q : upath) :
  well_colored_utrail c s t (p ++ q) =
  well_colored_utrail c s (upath_target s p) p && well_colored_utrail c (upath_source t q) t q
    && [forall e, [forall f, (e \in p) ==> (f \in q) ==> c e.1 != c f.1]].
Proof. Abort.
Lemma well_colored_utrail_sub (s t : G) (p q : upath) :
  well_colored_utrail c s t (p ++ q) ->
  well_colored_utrail c s (upath_target s p) p /\ well_colored_utrail c (upath_target s p) t q.
Proof.
  rewrite /well_colored_utrail uwalk_cat !map_cat cat_uniq mem_cat.
  by move=> /andP[/andP[/andP[-> ->] /andP[-> /andP[_ ->]]] /norP[-> ->]].
Qed.

(* Lemma well_colored_utrail_subK (s t : G) (p q r : upath) :
  well_colored_utrail f s t (p ++ q ++ r) -> well_colored_utrail f (upath_target s p) (upath_source t r) q.
Proof.
  move=> H.
  assert (W : uwalk s t (p ++ q ++ r)) by by move: H => /andP[/andP[-> _] _].
  assert (H' : well_colored_utrail f (upath_target s p) t (q ++ r)).
  { rewrite (uwalk_sub_middle W).
    by destruct (well_colored_utrail_subKK H) as [_ ->]. }
  assert (W' : uwalk (upath_target s p) t (q ++ r)) by by move: H' => /andP[/andP[-> _] _].
  rewrite -(uwalk_sub_middle W').
  by destruct (well_colored_utrail_subKK H') as [-> _].
Qed. *)

Lemma well_colored_utrail_rev (s t : G) (p : upath) :
  well_colored_utrail c s t (upath_rev p) = well_colored_utrail c t s p.
Proof.
  by rewrite /well_colored_utrail uwalk_rev 2!(map_comp _ fst) upath_rev_fst map_rev rev_uniq in_rev.
Qed.

Lemma well_colored_utrail_turn (s : G) (e : edge G * bool) (p : upath) :
  well_colored_utrail c s s (e :: p) -> well_colored_utrail c (utarget e) (utarget e) (upath_turn (e :: p)).
Proof.
  move=> /andP[/andP[W /= /andP[U1 U2]] N]. splitb.
  - exact (uwalk_turn W).
  - by rewrite map_rcons rcons_uniq U1 U2.
  - rewrite map_rcons in_rcons.
    by move: N; rewrite /= in_cons.
Qed.

Lemma well_colored_utrail_turns (s : G) (p q : upath) :
  well_colored_utrail c s s (p ++ q) ->
  well_colored_utrail c (upath_source s q) (upath_source s q) (q ++ p).
Proof.
  move=> /andP[/andP[W ?] ?]. splitb.
  - apply (uwalk_turns W).
  - by rewrite map_cat uniq_catC -map_cat.
  - by rewrite map_cat mem_cat orbC -mem_cat -map_cat.
Qed.

Definition neighbours (v : G) :=
  [set utarget e | e : edge G * bool & (c e.1 != None) && (usource e == v)].
(* TODO rename as still with coloring f *)

End WellColoredUtrailResults.


(* Basic results on these trails when the type of colors is finite. *)
Section WellColoredUtrailResultsFinite.
Context {Lv Le : Type} {G : graph Lv Le} {C : finType} (c : edge G -> option C).

Definition upath_color_disjoint (p q : upath) :=
  [disjoint [seq c x.1 | x <- p] & [seq c x.1 | x <- q]].

Lemma well_colored_utrail_concat (s i t : G) p q :
  well_colored_utrail c s i p -> well_colored_utrail c i t q ->
  upath_color_disjoint p q ->
  well_colored_utrail c s t (p ++ q).
Proof.
  rewrite /upath_color_disjoint disjoint_sym disjoint_has.
  move => /andP[/andP[Wp Up] Np] /andP[/andP[Wq Uq] Nq] D.
  by rewrite /well_colored_utrail uwalk_cat !map_cat cat_uniq mem_cat negb_orb D Up Uq Np Nq (uwalk_target Wp) Wp Wq.
Qed.
(* TODO we should not need finiteness her! *)

(* Definition Well_colored_utrail_cat (s i t : G) (p : Well_colored_utrail f s i) (q : Well_colored_utrail f i t)
  (D : upath_disjoint f (val p) (val q)) : Well_colored_utrail f s t :=
  Sub (val p ++ val q) (Well_colored_utrail_catK D). *)

End WellColoredUtrailResultsFinite.


(* Results on acyclicity *)
Section AcyclicityConnectivity.
Context {Lv Le : Type} {G : graph Lv Le} {C : eqType} (c : edge G -> option C).
(* TODO would be good to have it in bool! *)
(*
Definition uacyclic {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) : bool :=
  [forall x : G, [forall p : Well_colored_utrail f x x, p == well_colored_utrail_nil f x]].
Lemma uacyclic_T {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :
  uacyclic f -> forall (x : G) (p : Well_colored_utrail f x x), p = well_colored_utrail_nil f x.
Proof. move => C x p. by revert C => /forallP/(_ x)/forallP/(_ p)/eqP. Qed.
*)
Definition uacyclic :=
  forall (x : G) (p : Well_colored_utrail c x x), p = well_colored_utrail_nil c x.

Lemma uacyclic_loop :
  uacyclic -> forall e, c e <> None -> source e <> target e.
Proof.
  move=> A e /eqP-En E.
  enough (P : well_colored_utrail c (source e) (source e) [:: forward e])
    by by specialize (A _ (Sub _ P)).
  by rewrite well_colored_utrail_cons well_colored_utrail_of_nil /uendpoint /= E !eq_refl /= eq_sym.
Qed.


(* We define connectivity by "forall (x y : G), exists (_ : Well_colored_utrail f x y), true" and not
   "forall (x y : G), Well_colored_utrail f x y" to be in Prop instead of Type, which allows case analysis
   as well as to define properties such as tree <-> uacyclic /\ uconnected *)
(* TODO would be good to have it in bool! try it, and acyc too *)
(*
Definition uconnected {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) : bool :=
  [forall x : G, [forall y : G, [exists p : Well_colored_utrail f x y, true]]].
Lemma uconnected_T {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :
  uconnected f -> forall (x y : G), Well_colored_utrail f x y.
Proof. move => C x y. by revert C => /forallP/(_ x)/forallP/(_ y)/existsP/sigW[? _]. Qed.
*)
Definition uconnected :=
  forall (x y : G), exists (_ : Well_colored_utrail c x y), true.


(** ** Connectivity *)
Definition is_uconnected (x y : G) :=
  [exists p : (Well_colored_utrail c x y), true].

Definition is_uconnected_id (x : G) :
  is_uconnected x x.
Proof. apply/existsP. by exists (well_colored_utrail_nil _ _). Defined.

Definition is_uconnected_sym (x y : G) :
  is_uconnected x y -> is_uconnected y x.
Proof.
  move=> /existsP[[p P] _].
  rewrite -well_colored_utrail_rev in P.
  apply/existsP. by exists (Sub _ P).
Defined.

End AcyclicityConnectivity.


(*  For a finite coloring f injective except on None, ie a removal of edges *)
Section AcyclicityConnectivityInjectiveFinite.
Context {Lv Le : Type} {G : graph Lv Le} {C : finType} (c : edge G -> option C)
  (c_some_injective : {in ~: c @^-1 None &, injective c}).

Lemma uconnected_simpl (s t : G) p :
  uwalk s t p -> None \notin [seq c e.1 | e <- p] ->
  {P : Well_colored_utrail c s t | {subset val P <= p}}.
Proof.
  move: s. induction p as [ | e p IH] => s.
  { move => /eqP-<- _. by exists (well_colored_utrail_nil _ _). }
  rewrite /well_colored_utrail /= in_cons => /andP[/eqP-<- W] {s} /norP[n N].
  move: IH => /(_ _ W N) {W N} [[q Q] Qin].
  rewrite eq_sym in n.
  have E : well_colored_utrail c (usource e) (utarget e) [:: e]
    by by rewrite well_colored_utrail_of_edge.
  destruct (upath_color_disjoint c [:: e] q) eqn:D.
  { exists (Sub _ (well_colored_utrail_concat E Q D)).
    move=> a. rewrite /= !in_cons => /orP[-> // | ?].
    apply/orP. right. by apply Qin. }
  move: D. rewrite /upath_color_disjoint disjoint_sym disjoint_has has_sym /= orb_false_r => /negPn/mapP-Ein.
  have {Ein} /sig2W[[a b] In /eqP-Hea] : exists2 a, a \in q & c e.1 == c a.1.
  { destruct Ein as [a ? ?]. exists a; trivial. by apply/eqP. }
  assert (a = e.1).
  { enough (a \in ~: c @^-1 None /\ e.1 \in ~: c @^-1 None) as [A Ein] by by apply (c_some_injective A Ein).
    by rewrite !in_set -Hea n. }
  subst a. clear Hea.
  rewrite in_elt_sub in In.
  move: In => /existsP/sigW[[m /= _] /eqP-Qeq].
  assert (Q' : well_colored_utrail c (utarget e) t q) by assumption.
  rewrite Qeq in Q'.
  destruct (well_colored_utrail_sub Q') as [_ R], e as [e be].
  replace (upath_target (utarget (e, be)) (take m q)) with (usource (e, b)) in R
    by by move: Q' => /andP[/andP[/uwalk_sub_middle--> _] _].
  clear Q'.
  destruct (eq_comparable b be); [subst b | ].
  - exists (Sub _ R : Well_colored_utrail _ _ _).
    move=> a. rewrite /= !in_cons => /orP[-> // | In].
    apply/orP. right. apply Qin, (mem_drop In).
  - assert (b = ~~be) by by destruct b, be. subst b.
    move: R. rewrite /well_colored_utrail map_cons in_cons /=
      => /andP[/andP[/andP[_ W] /andP[_ U]] /norP[_ N]].
    assert (M : well_colored_utrail c (endpoint (~~ be) e) t (drop m.+1 q)) by splitb.
    exists (Sub _ M : Well_colored_utrail _ _ _).
    move=> a. rewrite /= !in_cons => In.
    apply/orP. right. apply Qin, (mem_drop In).
Qed.

Definition is_uconnected_comp (x y z : G) :
  is_uconnected c x y -> is_uconnected c y z -> is_uconnected c x z.
Proof.
  move=> /existsP[[pxy /andP[/andP[Wxy _] Nxy]] _] /existsP[[pyz /andP[/andP[Wyz _] Nyz]] _].
  enough (P : Well_colored_utrail c x z).
  { apply/existsP. by exists P. }
  apply (@uconnected_simpl _ _ (pxy ++ pyz)); trivial.
  - by rewrite uwalk_cat (uwalk_endpoint _ Wxy) Wxy Wyz.
  - by rewrite map_cat mem_cat negb_orb Nxy Nyz.
Defined.

Global Instance is_uconnected_Equivalence : CEquivalence (is_uconnected c).
Proof. constructor. exact (is_uconnected_id _). exact (is_uconnected_sym (c := _)). exact is_uconnected_comp. Defined.


Lemma is_uconnected_eq (u v w : G) :
  is_uconnected c u v ->
  is_uconnected c u w = is_uconnected c v w.
Proof.
  move=> UV.
  case/boolP: (is_uconnected _ v w) => VW.
  - apply (is_uconnected_comp UV VW).
  - case/boolP: (is_uconnected _ u w) => UW //.
    contradict VW. apply/negP/negPn.
    exact (is_uconnected_comp (is_uconnected_sym UV) UW).
Qed.

Lemma is_uconnected_equivalence : equivalence_rel (is_uconnected c).
Proof.
  move=> ? ? ?. split.
  - apply is_uconnected_id.
  - by apply is_uconnected_eq.
Qed.

End AcyclicityConnectivityInjectiveFinite.



Section ConnectedComponents.
Context {Lv Le : Type} {G : graph Lv Le} {C : eqType} (c : edge G -> option C).

(** Equivalence classes of uconnected, so to speak about connected components *)
Definition uconnected_nb :=
  #|equivalence_partition (is_uconnected c) [set: G]|.

Lemma uconnected_to_nb1 :
  #|G| <> 0 -> uconnected c -> uconnected_nb = 1.
Proof.
  move=> not_empty_G uconnected_G.
  destruct (set_0Vmem [set: G]) as [Hc | [v _]].
  { contradict not_empty_G. by rewrite -cardsT Hc cards0. }
  unfold uconnected_nb, equivalence_partition.
  apply/eqP/cards1P.
  exists [set u in [set: G] | is_uconnected c v u].
  apply/eqP/eq_set1P. split.
  { apply/imsetP. by exists v. }
  move=> ? /imsetP [? _ ?]. subst.
  apply eq_finset => ?.
  rewrite in_set /=.
  transitivity true; [ | symmetry]; apply/existsP; apply uconnected_G.
Qed.

Lemma uconnected_from_nb1 :
  uconnected_nb = 1 -> uconnected c.
Proof.
  move=> /eqP/cards1P[S /eqP/eq_set1P[Sin Seq]] u v.
  assert (Suin : [set w in [set: G] | is_uconnected c u w] \in
    equivalence_partition (is_uconnected c) [set: G]).
  { apply/imsetP. by exists u. }
  assert (UW := Seq _ Suin). cbn in UW. subst S.
  assert (Svin : [set w in [set: G] | is_uconnected c v w] \in
    equivalence_partition (is_uconnected c) [set: G]).
  { apply/imsetP. by exists v. }
  assert (Heq := Seq _ Svin). cbn in Heq.
  assert (V : v \in [set w in [set: G] | is_uconnected c v w]).
  { rewrite in_set. splitb. apply is_uconnected_id. }
  rewrite Heq !in_set /= in V.
  by revert V => /existsP.
Qed.

Lemma nb1_not_empty :
  uconnected_nb = 1 -> #|G| <> 0.
Proof.
  move => /eqP/cards1P[? /eqP/eq_set1P[Sin _]] N.
  rewrite -cardsT in N. apply cards0_eq in N.
  contradict Sin; apply /negP.
  rewrite N /equivalence_partition. apply /imsetP. move => [? In].
  contradict In; apply /negP.
  by rewrite !in_set.
Qed.

(* Lemma uconnected_nb_eq_1 :
  (uconnected_nb == 1) = (uconnected c) && (#|G| != 0).
Proof. Abort. *)
(* TODO? *)

End ConnectedComponents.

Lemma uacyclip_2loop {Lv Le : Type} {C : eqType} {G : graph Lv Le} (c : edge G -> option C) (v : G) :
  {in ~: c @^-1 None &, injective c} -> uacyclic c ->
  {in [set e | c e.1 != None & usource e == v] &, injective (fun e : edge G * bool => utarget e)}.
Proof.
  move=> F A [e eb] [j jb].
  rewrite !in_set /= =>
    /andP[/eqP-En /eqP-Es] /andP[/eqP-Jn /eqP-Js] T.
  apply /eqP/negPn/negP => /eqP-Hejb.
  assert (Hej : e <> j).
  { move=> ?; subst j.
    destruct (eq_comparable eb jb) as [ | Hb]; [by subst jb | ].
    assert (Hf := uacyclic_loop A En). contradict Hf.
    by destruct eb, jb. }
  enough (P : well_colored_utrail c v v [:: (e, eb); (j, ~~ jb)]).
  { specialize (A _ (Sub _ P)). contradict A. cbnb. }
  rewrite /well_colored_utrail /= !in_cons !orb_false_r.
  splitb; apply /eqP; rewrite /uendpoint ?negb_involutive //; try by apply nesym.
  intro Fej. contradict Hej.
  apply F; rewrite // !in_set; by apply/eqP.
Qed.

Lemma neighbours_nb {Lv Le : Type} {C : eqType} {G : graph Lv Le} (c : edge G -> option C) (v : G) :
  {in ~: c @^-1 None &, injective c} -> uacyclic c ->
  #|neighbours c v| = #|~: c @^-1 None :&: edges_at v|.
Proof.
  move=> F A.
  rewrite /neighbours card_in_imset -?card_set_subset; last by by apply uacyclip_2loop.
  assert (Hg : forall (e : {a | (c a.1 != None) && (usource a == v)}),
    ((val e).1 \in ~: c @^-1 None) && ((val e).1 \in edges_at v)).
  { move => [[e b] /= /andP[? ?]].
    rewrite !in_set. splitb.
    apply /existsP. by exists (~~b). }
  set g : {a | (c a.1 != None) && (usource a == v)} ->
    {e | (e \in ~: c @^-1 None) && (e \in edges_at v)} :=
    fun e => Sub (val e).1 (Hg e).
  assert (Hh : forall e : {e | (e \in ~: c @^-1 None) && (e \in edges_at v)},
    exists b, (c (val e, b).1 != None) && (usource (val e, b) == v)).
  { move => [e] /=.
    rewrite !in_set => /andP[? /existsP[b ?]].
    exists (~~b). splitb. by rewrite /uendpoint negb_involutive. }
  set h : {e | (e \in ~: c @^-1 None) && (e \in edges_at v)} ->
    {a | (c a.1 != None) && (usource a == v)} :=
    fun e => let (b, H) := sigW (Hh e) in Sub (val e, b) H.
  apply (@bij_card_eq _ _ g), (@Bijective _ _ _ h).
  - move => [e E].
    rewrite /h /g /=.
    destruct (sigW _) as [b H].
    apply /eqP. cbn. rewrite /= eq_refl /=. apply /eqP.
    destruct (eq_comparable b e.2) as [-> | Hbe]; trivial.
    move: E H => /andP[/eqP-En /eqP-V] /andP[_ /eqP-V'].
    assert (Hf := uacyclic_loop A En). contradict Hf.
    rewrite /uendpoint in V, V'.
    destruct b, e as [? []]; by rewrite // V V'.
  - move=> ?. rewrite /h /g /=. destruct (sigW _). cbnb.
Qed.

(* TODO rename those *)
Definition remove_vertex_f {Lv Le : Type} {C : eqType} {G : graph Lv Le}
  (c : edge G -> option C) (v : G) : edge (remove_vertex v) -> option C :=
  fun e => c (val e).

Lemma remove_vertex_f_sinj {Lv Le : Type} {C : eqType} {G : graph Lv Le}
  (c : edge G -> option C) (v : G) :
  {in ~: c @^-1 None &, injective c} ->
  {in ~: (@remove_vertex_f _ _ _ _ c v) @^-1 None &, injective (@remove_vertex_f _ _ _ _ c v)}.
Proof.
  move=> F u w.
  rewrite !in_set /remove_vertex_f /= => /eqP-Fu /eqP-Fw Eq. cbnb.
  by apply F; rewrite // !in_set; apply/eqP.
Qed.

Lemma well_colored_utrail_induced {Lv Le : Type} {C : eqType} {G : graph Lv Le} (c : edge G -> option C) (S : {set G})
  s t (p : Well_colored_utrail (fun (e : edge (induced S)) => c (val e)) s t) :
  {q : Well_colored_utrail c (val s) (val t) & val q = [seq (val a.1, a.2) | a <- val p]}.
Proof.
  destruct p as [p P].
  move: s t P. induction p as [ | ([a A], b) p IH] => /= s t; rewrite /well_colored_utrail /=.
  { introb. by exists (well_colored_utrail_nil _ _). }
  rewrite in_cons => /andP[/andP[/andP[/eqP-? W] /andP[u U]] /norP[n N]]. subst s. simpl.
  assert (P : well_colored_utrail (fun (e : edge (induced S)) => c (val e)) (Sub (endpoint b a) (induced_proof b (valP (exist _ a A))) : induced S)
    t p) by splitb.
  specialize (IH _ _ P). destruct IH as [[q Q] HQ].
  revert HQ; cbnb => ?; subst q. simpl in Q.
  enough (QS : well_colored_utrail c (endpoint (~~ b) a) (val t) ((a, b) :: _))
    by by exists (Sub _ QS).
  rewrite well_colored_utrail_cons /uendpoint /= Q eq_refl n /= andb_true_r.
  move: u. clear. induction p as [ | ? ? IH]; first by [].
  by rewrite /= !in_cons !negb_orb => /andP[-> /IH-->].
Qed.

Lemma well_colored_utrail_to_induced {Lv Le : Type} {G : graph Lv Le} (S : {set G})
  {I J : finType} (f : edge G -> option I) (f' : edge (induced S) -> option J)
  s t (p : Well_colored_utrail f s t) :
  (forall e (E : e \in edge_set S), None <> f e -> None <> f' (Sub e E)) ->
  (forall e a (E : e \in edge_set S) (A : a \in edge_set S),
    f' (Sub e E) = f' (Sub a A) -> f e = f a) ->
  (forall (e : (edge G) * bool), e \in val p -> e.1 \in edge_set S) ->
  forall (Sin : s \in S) (Tin : t \in S),
  {q : Well_colored_utrail f' (Sub s Sin) (Sub t Tin) & val p = [seq (val a.1, a.2) | a <- val q]}.
Proof. (* in fact can even deduce Sin and Tin, provided p not empty *)
  intros F0 F1 Hp Sin Tin.
  destruct p as [p P].
  simpl in Hp.
  revert s Sin P. induction p as [ | e p IHp] => s Sin.
  { rewrite /well_colored_utrail /=. introb.
    assert (Sin = Tin) by apply eq_irrelevance. subst.
    by exists (well_colored_utrail_nil _ _). }
  rewrite /well_colored_utrail /= in_cons => /andP[/andP[/andP[/eqP-? PW] /andP[Pu PU]] /norP[/eqP-Pn PN]].
  subst s.
  assert (P : well_colored_utrail f (utarget e) t p) by splitb.
  assert (E : e.1 \in edge_set S).
  { apply Hp. rewrite in_cons. caseb. }
  assert (Hp' : forall e, e \in p -> e.1 \in edge_set S).
  { intros. apply Hp. rewrite in_cons. caseb. }
  assert (T : utarget e \in S).
  { revert E. rewrite in_set. destruct e as [? []]; introb. }
  revert IHp => /= /(_ Hp' _ T P) {Hp Hp' P} [[q Q] ?]. subst p.
  enough (Q' : well_colored_utrail (f' : edge (induced _) -> _) (Sub (usource e) Sin) (Sub t Tin)
    ((Sub e.1 E : edge (induced S), e.2) :: q)).
  { exists (Sub _ Q'). by destruct e. }
  assert (E' : well_colored_utrail f' (Sub (usource e) Sin) (Sub (utarget e) T) [:: (Sub e.1 E, e.2)]). (* TODO lemma for edge well_colored_utrail? *)
  { rewrite /well_colored_utrail /= in_cons in_nil orb_false_r. splitb; try by cbnb.
    apply /eqP. clear - F0 Pn. by apply F0. }
  rewrite -cat1s.
  apply (well_colored_utrail_concat E' Q).
  rewrite /upath_color_disjoint disjoint_has /= orb_false_r.
  clear - F1 Pu.
  apply /mapP. move => [[[z Z] zb] Zin Zeq].
  contradict Pu. apply /negP/negPn/mapP.
  exists (z, zb); last by apply (F1 _ _ _ _ Zeq).
  simpl. revert Zin. generalize q. clear. intro l.
  induction l as [ | [? ?] ? H]; trivial.
  rewrite !in_cons. cbn.
  move => /orP[-> // | ?].
  apply /orP. right. by apply H.
Qed. (* TODO strictly more general than well_colored_utrail_induced? *)

Lemma induced_upath_inside {Lv Le : Type} {G : graph Lv Le} (S : {set G}) (q : @upath _ _ (induced S)) e :
  e \in [seq (val a.1, a.2) | a <- q] -> e.1 \in edge_set S.
Proof. move=> /mapP[[[? ?] ?] ? ?]. by subst e. Qed.
(* TODO somewhere else *)

Lemma remove_vertex_uacyclic {Lv Le : Type} {I : eqType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) :
  uacyclic f -> uacyclic (@remove_vertex_f _ _ _ _ f v).
Proof.
  move => A [x X] [p' P'].
  apply val_inj. simpl.
  enough (P : well_colored_utrail f x x [seq (val e.1, e.2) | e <- p']).
  { specialize (A _ (Sub _ P)).
    by destruct p'. }
  revert P' => /andP[/andP[W ?] ?].
  splitb; rewrite -?map_comp //.
  enough (H : forall x X y Y, uwalk (Sub x X : remove_vertex v) (Sub y Y) p' ->
    uwalk x y [seq (val e.1, e.2) | e <- p']) by by apply (H _ _ _ _ W).
  clear; induction p' as [ | [[? ?] ?] ? IH] => // ? ? ? ?; cbnb => /andP[? W].
  splitb. apply (IH _ _ _ _ W).
Qed.

Lemma well_colored_utrail_from_induced {Lv Le : Type} {G : graph Lv Le} (S : {set G})
  {I J : eqType} (f : edge G -> option I) (f' : edge (induced S) -> option J)
  s t (q : Well_colored_utrail f' s t) :
  (forall e (E : e \in edge_set S), None <> f' (Sub e E) -> None <> f e) ->
  (forall e a (E : e \in edge_set S) (A : a \in edge_set S),
    f e = f a -> f' (Sub e E) = f' (Sub a A)) ->
  well_colored_utrail f (val s) (val t) [seq (val a.1, a.2) | a <- val q].
Proof.
  intros F0 F1.
  destruct q as [q Q]. revert s t Q.
  induction q as [ | ([a A], b) q IH] => /= s t Q.
  { move: Q. by rewrite 2!well_colored_utrail_of_nil => /eqP-->. }
  rewrite well_colored_utrail_cons /= in Q. revert Q => /andP[/andP[/andP[Q /eqP-?] U] /eqP-N]. subst s. simpl.
  revert IH => /(_ _ _ Q)-IH. rewrite well_colored_utrail_cons IH. splitb.
  - clear - F1 U.
    apply/mapP. move => [c' /mapP[c Cin ?] Fc]. subst c'. simpl in Fc.
    contradict U. apply /negP/negPn/mapP.
    exists c; trivial. simpl.
    destruct c as [[? ?] ?]. by apply F1.
  - clear - F0 N.
    apply /eqP. apply (F0 _ _ N).
Qed.

Section Utrail.
Context {Lv Le : Type} {G : graph Lv Le}.
(** ** Undirected Trails : undirected walks without repetition of edges *)
Definition utrail (s t : G) (p : upath) : bool :=
  (uwalk s t p) && uniq [seq e.1 | e <- p].

Lemma well_colored_utrail_is_utrail {I : eqType} (f : edge G -> option I) (s t : G) (p : upath) :
  well_colored_utrail f s t p -> utrail s t p.
Proof. by rewrite /well_colored_utrail /utrail map_comp => /andP[/andP[-> /map_uniq-->] _]. Qed.

(* We deduce results from the previous, more general trails. *)
Lemma utrail_is_id_well_colored_utrail (s t : G) (p : upath) :
  utrail s t p = well_colored_utrail Some s t p.
Proof.
  rewrite /well_colored_utrail /utrail (map_comp Some) (map_inj_uniq Some_inj).
  case: (uwalk s t p && uniq [seq e.1 | e <- p]) => //=.
  by induction p.
Qed.

End Utrail.
