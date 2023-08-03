(* Extension for [mgraph] of the library GraphTheory *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph structures bij setoid_bigop.
From Yalla Require Import mll_prelim.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



(** * Notations from the library *)
Open Scope graph_scope.
(* G0 ⊎ G1 = disjoint union
   G ∔ v = add a vertex labelled v
   G ∔ [ x , u , y ] = add an arrow from x to y labelled u *)

(** ** Dual of a graph, with all edges flipped **)
Definition dual {Lv Le : Type} (G : graph Lv Le) : graph Lv Le :=
  {| vertex := G;
     edge := edge G;
     endpoint b := @endpoint _ _ G (~~ b);
     vlabel := @vlabel _ _ G;
     elabel := @elabel _ _ G;
  |}.


(** ** Out & In edges of a vertex *)
Definition edges_at_outin (b : bool) {Lv Le : Type} {G : graph Lv Le} (v : G) : {set edge G} :=
  [set e | endpoint b e == v].
Notation edges_at_out := (edges_at_outin false).
Notation edges_at_in := (edges_at_outin true).

Lemma endpoint_in_edges_at_outin (b : bool) {Lv Le : Type} {G : graph Lv Le} (e : edge G) :
  e \in edges_at_outin b (endpoint b e).
Proof. by rewrite in_set. Qed.
Notation source_in_edges_at_out := (endpoint_in_edges_at_outin false).
Notation target_in_edges_at_in := (endpoint_in_edges_at_outin true).


(** ** Rewriting of edges_at *)
Lemma edges_at_eq {Lv Le : Type} (G : graph Lv Le) (v : G) (e : edge G) :
  (e \in edges_at v) = (source e == v) || (target e == v).
Proof.
  rewrite !in_set /incident. symmetry.
  destruct [exists b, endpoint b e == v] eqn:E.
  - revert E => /existsP[[] ->]; caseb.
  - revert E => /existsPn-?. splitb.
Qed.

Lemma edges_at_at_outin (Lv Le : Type) (G : graph Lv Le) (v : G) :
  edges_at v = (edges_at_in v) :|: (edges_at_out v).
Proof. apply /setP => e. by rewrite edges_at_eq !in_set orbC. Qed.


(** ** The set of edge of the whole set of vertices, is the whole set of edges *)
Lemma edge_set_setT {Lv Le : Type} (G : graph Lv Le) :
  edge_set [set: G] = setT.
Proof. apply /setP => ?. by rewrite !in_set. Qed. 


(** ** Isomorphisms preserve cardinality *)
Lemma card_iso {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) :
  F ≃ G -> #|F| = #|G|.
Proof. intros [? _ _ _]. by apply card_bij. Qed.

(** ** Some specific isomorphisms *)
(* Definition edge_graph_iso {Lv: comMonoid} {Le : elabelType} (u v : Lv) (e e' : Le) :
  e = e' -> edge_graph u e v = edge_graph u e' v.
Proof.
  intros. by subst e'.
Defined. *) (* TODO see where it is used! *)

(** ** Some specific isomorphisms *)
Definition edge_graph_iso {Lv: comMonoid} {Le : elabelType} (u v : Lv) (e e' : Le) :
  e = e' -> edge_graph u e v ≃ edge_graph u e' v.
Proof.
  intros.
  apply (@add_edge_iso'' _ _ _ _ iso_id); trivial.
  by replace e with e'.
Defined. (* TODO see where it is used! *)

Definition induced_func_v {Lv Le : Type} (F G : graph Lv Le) (f : bij F G) (S : {set F}) (R : {set G}) :
  R = [set f v | v in S]  -> induced S -> induced R.
Proof.
  intros E [v V].
  exists (f v).
  by rewrite E bij_imset_f.
Defined.

Lemma edge_set_iso {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (f : F ≃ G) (S : {set F}) :
  edge_set [set f v | v in S] = [set f.e e | e in edge_set S].
Proof.
  apply /setP => e.
  rewrite !in_set -(bijK' f (source e)) -(bijK' f (target e)) -[in RHS](bijK' f.e e)
    !bij_imset_f !in_set !endpoint_iso'.
  destruct (f.d _); trivial.
  apply andbC.
Qed.

Definition induced_func_e {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (f : F ≃ G)
  (S : {set F}) (R : {set G}) : R = [set f v | v in S]  -> edge (induced S) -> edge (induced R).
Proof.
  intros E [a A].
  exists (f.e a).
  by rewrite E edge_set_iso bij_imset_f.
Defined.

Definition induced_iso {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (h : F ≃ G)
  (S : {set F}) (R : {set G}) : R = [set h v | v in S] -> induced S ≃ induced R.
Proof.
  intro E.
  assert (E' : S = [set h^-1 v | v in R]) by by apply bij_imset_invert.
  set f := induced_func_v E.
  set f' := @induced_func_v _ _ _ _ (iso_sym _) _ _ E'.
  assert (fK : cancel f f').
  { intros [? ?]. cbnb. apply bijK. }
  assert (fK' : cancel f' f).
  { intros [? ?]. cbnb. apply bijK'. }
  set iso_v := {| bij_fwd := _ ; bij_bwd := _ ; bijK := fK ; bijK' := fK' |}.
  set g := induced_func_e E.
  set g' := @induced_func_e _ _ _ _ (iso_sym _) _ _ E'.
  assert (gK : cancel g g').
  { intros [? ?]. cbnb. apply bijK. }
  assert (gK' : cancel g' g).
  { intros [? ?]. cbnb. apply bijK'. }
  set iso_e := {| bij_fwd := _ ; bij_bwd := _ ; bijK := gK ; bijK' := gK' |}.
  exists iso_v iso_e (fun v => h.d (val v)). splitb.
  - intros [? ?] ?. cbnb. apply endpoint_iso.
  - intros [? ?]. cbnb. apply vlabel_iso.
  - intros [? ?]. cbnb. apply elabel_iso.
Defined.

(** * The induced subgraph with all vertices is (isomorphic to) the whole graph *)
Lemma induced_all {Lv: comMonoid} {Le : elabelType} (G : graph Lv Le) :
  induced [set : G] ≃ G.
Proof.
  set f : induced [set : G] -> G := fun v => val v.
  set f' : G -> induced [set : G] := fun v => Sub v (in_setT v).
  assert (fK : cancel f f') by (intros [? ?]; cbnb).
  assert (fK' : cancel f' f) by cbnb.
  set iso_v := {| bij_fwd := _ ; bij_bwd := _ ; bijK := fK ; bijK' := fK' |}.
  set g : edge (induced [set : G]) -> edge G := fun e => val e.
  assert (Hg : forall e, e \in edge_set [set: G]).
  { intros. by rewrite !in_set. }
  set g' : edge G -> edge (induced [set : G]) := fun e => Sub e (Hg e).
  assert (gK : cancel g g') by (intros [? ?]; cbnb).
  assert (gK' : cancel g' g) by cbnb.
  set iso_e := {| bij_fwd := _ ; bij_bwd := _ ; bijK := gK ; bijK' := gK' |}.
  exists iso_v iso_e pred0.
  splitb.
Defined.

Definition induced_all_iso {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (h : F ≃ G) :
  induced [set: F] ≃ induced [set: G].
Proof.
  etransitivity. apply induced_all.
  etransitivity. apply h.
  symmetry. apply induced_all.
Defined.

(** * Basic results about cardinality *)
Lemma card_edge_add_vertex (Lv Le : Type) (G : graph Lv Le) (v : Lv) :
  #|edge (G ∔ v)| = #|edge G|.
Proof. rewrite card_sum card_void. lia. Qed.

Lemma card_edge_add_edge (Lv Le : Type) (G : graph Lv Le) (u v : G) (e : Le) :
  #|edge (G ∔ [u, e, v])| = #|edge G| + 1.
Proof. rewrite card_option. lia. Qed.

Lemma card_add_vertex (Lv Le : Type) (G : graph Lv Le) (v : Lv) :
  #|G ∔ v| = #|G| + 1.
Proof. by rewrite card_sum card_unit. Qed.

Lemma card_induced_all {Lv: comMonoid} {Le : elabelType} (G : graph Lv Le) :
 #|induced [set : G]| = #|G|.
Proof. apply card_iso, induced_all. Qed.

Lemma card_inducedD1 (Lv Le : Type) (G : graph Lv Le) (S : {set G}) (v : G) :
  #|induced S| = (v \in S) + #|induced (S :\ v)|.
Proof. rewrite /= !card_set_subset 2!cardsE. apply cardsD1. Qed.

Lemma cards_subgraph_pred (Lv Le : Type) (G : graph Lv Le) V E (C : consistent V E) (P : pred G) :
  #|[set x : subgraph_for C | P (val x)]| = #|[set x | P x] :&: V|.
Proof.
  rewrite -!card_set_subset.
  assert (Hf : forall (u : {u : subgraph_for C | P (val u)}),
    (val (val u) \in [set x | P x]) && (val (val u) \in V)).
  { move => [[u In]/= U]. by rewrite in_set U In. }
  set f : {u : subgraph_for C | P (val u)} ->
    {u : G | (u \in [set x | P x]) && (u \in V)} :=
    fun u => Sub (val (val u)) (Hf u).
  assert (Hg0 : forall (u : {u : G | (u \in [set x | P x]) && (u \in V)}),
    val u \in V) by by move => [? /= /andP[_ ?]].
  assert (Hg1 : forall (u : {u : G | (u \in [set x | P x]) && (u \in V)}),
    P (val (Sub (val u) (Hg0 u) : subgraph_for C))).
  { move => [? /= /andP[U _]]. revert U. by rewrite in_set. }
  set g : {u : G | (u \in [set x | P x]) && (u \in V)} ->
    {u : subgraph_for C | P (val u)} :=
    fun u => Sub _ (Hg1 u).
  apply (@bij_card_eq _ _ f), (@Bijective _ _ _ g) => ?; cbnb.
Qed.


(** ** Undirected paths in an oriented multigraph *)
Notation forward e := (e, true).
Notation backward e := (e, false).
Notation reversed e := (e.1, ~~e.2).
Notation usource e := (endpoint (~~e.2) e.1).
Notation utarget e := (endpoint e.2 e.1).
(* TODO with
Definition uendpoint {Lv Le : Type} {G : graph Lv Le} b (e : (edge G) * bool) :=
  endpoint (if b then ~~e.2 else e.2) e.1.
Notation usource := (uendpoint false).
Notation utarget := (uendpoint true).
???
 *)

Definition upath {Lv Le : Type} {G : graph Lv Le} := seq ((edge G) * bool).

Definition upath_endpoint {Lv Le : Type} {G : graph Lv Le} (b : bool) (s : G) (p : upath) :=
  match b with
  | false => head s [seq usource e | e <- p]
  | true => last s [seq utarget e | e <- p]
  end.
Notation upath_source := (upath_endpoint false).
Notation upath_target := (upath_endpoint true).

Lemma upath_target_cat {Lv Le : Type} {G : graph Lv Le} (s : G) (p q : upath) :
  upath_target s (p ++ q) = upath_target (upath_target s p) q.
Proof.
  revert p; induction q as [ | e q IH] => p.
  { by rewrite cats0. }
  replace (p ++ e :: q) with ((rcons p e) ++ q) by by rewrite -cats1 -catA.
  rewrite IH.
  destruct q; trivial.
  by rewrite /= map_rcons last_rcons.
Qed.

Definition upath_disjoint {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I)
  (p q : upath) := [disjoint [seq f x.1 | x <- p] & [seq f x.1 | x <- q]].

Fixpoint upath_rev {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) : @upath _ _ G :=
  match p with
  | [::] => [::]
  | (* (e, b) :: q => rcons (upath_rev q) (e, ~~b) *) e :: q => rcons (upath_rev q) (e.1, ~~e.2)
  end.
(* TODO with this new definition, do not longer need some destruct e when using upath_rev *)

Lemma upath_rev_fst {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) :
  [seq e.1 | e <- upath_rev p] = rev [seq e.1 | e <- p].
Proof.
  rewrite -map_rev.
  induction p as [ | [e b] p IH]; first by [].
  by rewrite /= rev_cons !map_rcons IH.
Qed.

Lemma upath_rev_size {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) :
  size (upath_rev p) = size p.
Proof. induction p as [ | (e, b) p H]; by rewrite // size_rcons H. Qed.

Lemma upath_rev_rcons {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) e :
  upath_rev (rcons p e) = reversed e :: upath_rev p.
Proof.
  revert e; induction p as [ | (?, ?) ? H] => e //=.
   by rewrite H rcons_cons.
Qed.

Lemma upath_rev_cat {Lv Le : Type} {G : graph Lv Le} (p q : @upath _ _ G) :
  upath_rev (p ++ q) = upath_rev q ++ upath_rev p.
Proof.
  revert q; induction p as [ | (?, ?) ? H] => q /=.
  - by rewrite cats0.
  - by rewrite H rcons_cat.
Qed.

Lemma upath_rev_nil {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) :
  (upath_rev p == [::]) = (p == [::]).
Proof.
  destruct p as [ | [? ?] ?] => //=.
  cbn. apply /eqP. apply rcons_nil.
Qed.

Lemma upath_rev_inv {Lv Le : Type} {G : graph Lv Le} : involutive (@upath_rev _ _ G).
Proof.
  intro p. induction p as [ | (?, ?) ? H]; trivial; cbn.
  by rewrite -cats1 upath_rev_cat H /= negb_involutive.
Qed.

Lemma upath_rev_in {Lv Le : Type} {G : graph Lv Le} (p : upath) (e : edge G * bool) :
  (e \in upath_rev p) = (reversed e \in p).
Proof.
  revert e. induction p as [ | (?, b) ? H] => e //=.
  rewrite in_rcons in_cons H.
  by destruct b, e as [? []].
Qed.

Definition upath_turn {Lv Le : Type} {G : graph Lv Le} : @upath _ _ G -> @upath _ _ G :=
  fun p => match p with
  | [::] => [::]
  | e :: p => rcons p e
  end.


(** ** Undirected walk in an oriented multigraph *)
Fixpoint uwalk {Lv Le : Type} {G : graph Lv Le} (x y : G) (p : upath) :=
  if p is e :: p' then (usource e == x) && uwalk (utarget e) y p' else x == y.
(* TODO or without the endpoints, seems better to me
Fixpoint uwalk' {Lv Le : Type} {G : graph Lv Le} (p : @upath _ _ G) :=
  if p is e :: p' then (utarget e == upath_source (utarget e) p') && uwalk' p' else true.
*)

Lemma uwalk_endpoint {Lv Le : Type} {G : graph Lv Le} (p : upath) (x y : G) :
  uwalk x y p -> upath_source x p = x /\ upath_target x p = y.
Proof.
  revert x y. induction p as [ | (e, b) p IH] => x y /=.
  { by move => /eqP ->. }
  move => /andP[/eqP -> W]. split; trivial.
  by destruct (IH _ _ W) as [_ <-].
Qed.

Lemma uwalk_eq {Lv Le : Type} {G : graph Lv Le} (p : upath) (x y s t : G) :
  p <> nil -> uwalk x y p -> uwalk s t p -> x = s /\ y = t.
Proof.
  revert x y s t. induction p as [ | (e, b) p IH]; try by [].
  move => x y s t _ /= /andP[/eqP ? W] /andP[/eqP ? W']. subst x s. split; trivial.
  destruct p as [ | f p].
  - by revert W W' => /eqP-<- /eqP-<-.
  - assert (H : f :: p <> nil) by by [].
    apply (IH _ _ _ _ H W W').
Qed.

Lemma uwalk_rcons {Lv Le : Type} {G : graph Lv Le} (s t : G) (p : upath) (e : edge G * bool) :
  uwalk s t (rcons p e) = (uwalk s (usource e) p) && (utarget e == t).
Proof.
  revert s t e; induction p as [ | ep p IH] => s t e /=.
  all: apply /eqP; cbn; apply /eqP; case: ifP => /eqP ?; subst.
  - by rewrite eq_refl.
  - symmetry; apply andb_false_intro1. apply /eqP. by apply nesym.
  - rewrite eq_refl. apply IH.
  - symmetry; apply andb_false_intro1, andb_false_intro1. by apply /eqP.
Qed.

Lemma uwalk_cat {Lv Le : Type} {G : graph Lv Le} (s i t : G) (p q : upath) :
  uwalk s i p -> uwalk i t q -> uwalk s t (p ++ q).
Proof.
  revert s i t q; induction p as [ | e p Hp] => s i t q Wp Wq; revert Wp; cbn.
  - by move => /eqP-->.
  - move => /andP[/eqP-<- ?]. apply /andP; split; trivial. by apply (Hp _ i).
Qed.

Lemma uwalk_sub_middle {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q : upath) :
  uwalk s t (p ++ q) -> upath_target s p = upath_source t q.
Proof.
  revert s t q; induction p as [ | e p Hp] => s t q; cbn in *.
  - destruct q; cbn; [by move => /eqP--> | by move => /andP[/eqP--> _]].
  - move =>/andP[_ W]. apply (Hp _ _ _ W).
Qed.

Lemma uwalk_subK {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q : upath) :
  uwalk s t (p ++ q) -> uwalk s (upath_target s p) p /\ uwalk (upath_source t q) t q.
Proof.
  revert s t q; induction p as [ | e p Hp] => s t q W.
  - cbn. split; trivial.
    assert (H := uwalk_sub_middle W). cbn in H. by rewrite -H.
  - cbn in *. revert W => /andP[/eqP--> W].
    splitb; apply (Hp _ _ _ W).
Qed.

Lemma uwalk_sub {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q r : upath) :
  uwalk s t (p ++ q ++ r) -> uwalk (upath_target s p) (upath_source t r) q.
Proof.
  intro W.
  assert (W' : uwalk (upath_target s p) t (q ++ r)).
  { rewrite (uwalk_sub_middle W). by destruct (uwalk_subK W) as [_ ->]. }
  rewrite -(uwalk_sub_middle W'). by destruct (uwalk_subK W') as [-> _].
Qed.

Lemma uwalk_rev {Lv Le : Type} {G : graph Lv Le} (s t : G) (p : upath) :
  uwalk t s (upath_rev p) = uwalk s t p.
Proof.
  revert s t; induction p as [ | (e, b) p H] => s t /=.
  { apply eq_sym. }
  rewrite uwalk_rcons negb_involutive H.
  apply andbC.
Qed.

Lemma uwalk_turn {Lv Le : Type} {G : graph Lv Le} (s : G) (e : edge G * bool) (p : upath) :
  uwalk s s (e :: p) -> uwalk (utarget e) (utarget e) (upath_turn (e :: p)).
Proof. by rewrite uwalk_rcons eq_refl andb_true_r => /= /andP[/eqP-<- W]. Qed.

Lemma uwalk_turns {Lv Le : Type} {G : graph Lv Le} (s : G) (p q : upath) :
  uwalk s s (p ++ q) -> uwalk (upath_source s q) (upath_source s q) (q ++ p).
Proof.
  revert p; induction q as [ | e q IH] => p /=.
  { by rewrite cats0. }
  replace (p ++ e :: q) with ((p ++ [:: e]) ++ q) by by rewrite -catA.
  intro W. splitb.
  specialize (IH _ W).
  rewrite catA cats1 uwalk_rcons in IH.
  by revert IH => /andP[? /eqP-->].
Qed.


(** ** Simple undirected paths : paths whose edges have different non-forbidden id *)
(** The function f : edge G -> option I is used to identify some edges. *)
(** Taking f := fun e => Some e gives the standard simple paths, which do not use the same edge twice *)
Definition supath {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : upath) :=
  (uwalk s t p) && uniq [seq f e.1 | e <- p] && (None \notin [seq f e.1 | e <- p]).

Record Supath {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :
  predArgType := {upval :> upath; upvalK : supath f s t upval}.
Canonical Ssupath_subType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  [subType for (@upval _ _ _ _ f s t)].
Definition Supath_eqMixin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in [eqMixin of Supath f s t by <:].
Canonical Supath_eqType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in EqType (Supath f s t) (Supath_eqMixin f s t).
Definition Supath_choiceMixin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in [choiceMixin of (Supath f s t) by <:].
Canonical Supath_choiceType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in ChoiceType (Supath f s t) (Supath_choiceMixin f s t).
Definition Supath_countMixin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in [countMixin of (Supath f s t) by <:].
Canonical Supath_countType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in CountType (Supath f s t) (Supath_countMixin f s t).

Lemma upath_size {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) p :
  supath f s t p -> size p < S #|edge G|.
Proof.
  move => /andP[/andP[_ U] _].
  rewrite map_comp in U.
  apply map_uniq in U.
  revert U => /card_uniqP U.
  rewrite size_map in U.
  rewrite -U.
  exact: max_card.
Qed.

Definition Supath_tuple {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : Supath f s t) : {n : 'I_(S #|edge G|) & n.-tuple (edge G * bool)} :=
  let (p, Up) := p in existT _ (Ordinal (upath_size Up)) (in_tuple p).

Definition tuple_Supath {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (m : {n : 'I_(S #|edge G|) & n.-tuple (edge G * bool)}) : option (Supath f s t) :=
  let (_, p) := m in match boolP (supath f s t p) with
  | AltTrue P => Some (Sub (val p) P)
  | AltFalse _ => None
  end.

Lemma Supath_tupleK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :
  pcancel (@Supath_tuple _ _ _ _ f s t) (tuple_Supath f s t).
Proof.
  move => [/= p P].
  case: {-}_ / boolP; last by rewrite P.
  by move => P'; rewrite (bool_irrelevance P' P).
Qed.

Definition Supath_finMixin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in PcanFinMixin (@Supath_tupleK _ _ _ _ f s t).
Canonical Supath_finType {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) :=
  Eval hnf in FinType (Supath f s t) (Supath_finMixin f s t).


Lemma supath_endpoint {Lv Le : Type} {I : finType} {G' : graph Lv Le} (f : edge G' -> option I)
  (s t : G') (p : Supath f s t) :
  upath_source s p = s /\ upath_target s p = t.
Proof. destruct p as [p P]. revert P => /= /andP[/andP[W _] _]. by apply uwalk_endpoint. Qed.

Lemma supath_nin {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p q : upath) e b :
  supath f s t (p ++ e :: q) -> (e.1, b) \notin p ++ q.
Proof.
  rewrite /supath !map_cat !cat_uniq /=.
  move => /andP[/andP[_ /andP[_ /andP[/norP[P _] /andP[Q _]]]] _].
  rewrite mem_cat; apply /negP => /orP[? | ?];
  [contradict P | contradict Q]; apply /negP/negPn/mapP; by exists (e.1, b).
Qed.

Lemma supath_catK {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s i t : G)
  (p : Supath f s i) (q : Supath f i t) :
  upath_disjoint f p q -> supath f s t (val p ++ val q).
Proof.
  revert p q; move => [p /andP[/andP[Wp Up] Np]] [q /andP[/andP[Wq Uq] Nq]] /= D.
  splitb.
  - apply (uwalk_cat Wp Wq).
  - rewrite map_cat cat_uniq. splitb.
    by rewrite /upath_disjoint disjoint_sym disjoint_has in D.
  - rewrite map_cat mem_cat. splitb.
Qed.

Definition supath_cat {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s i t : G)
  (p : Supath f s i) (q : Supath f i t) (D : upath_disjoint f p q) :=
  {| upval := val p ++ val q ; upvalK := supath_catK D |}.

Lemma supath_subKK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p q : upath) :
  supath f s t (p ++ q) -> supath f s (upath_target s p) p /\ supath f (upath_source t q) t q.
Proof.
  move => /andP[/andP[W U] N].
  revert U N. rewrite !map_cat cat_uniq mem_cat =>/andP[Up /andP[_ ?]] /norP[? ?].
  splitb; apply (uwalk_subK W).
Qed.

Lemma supath_subK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p q r : upath) :
  supath f s t (p ++ q ++ r) -> supath f (upath_target s p) (upath_source t r) q.
Proof.
  intro H.
  assert (W : uwalk s t (p ++ q ++ r)) by by revert H => /andP[/andP[-> _] _].
  assert (H' : supath f (upath_target s p) t (q ++ r)).
  { rewrite (uwalk_sub_middle W).
    by destruct (supath_subKK H) as [_ ->]. }
  assert (W' : uwalk (upath_target s p) t (q ++ r)) by by revert H' => /andP[/andP[-> _] _].
  rewrite -(uwalk_sub_middle W').
  by destruct (supath_subKK H') as [-> _].
Qed.

Definition supath_sub {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p q r : upath) (H : supath f s t (p ++ q ++ r)) :=
  {| upval := q ; upvalK := supath_subK H |}.

Lemma supath_revK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : upath) :
  supath f s t p -> supath f t s (upath_rev p).
Proof.
  move =>/andP[/andP[W U] N]. splitb.
  - by rewrite uwalk_rev.
  - by rewrite map_comp upath_rev_fst map_rev rev_uniq -map_comp.
  - by rewrite map_comp upath_rev_fst map_rev in_rev -map_comp.
Qed.

Definition supath_rev {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s t : G)
  (p : Supath f s t) :=
  {| upval := _ ; upvalK := supath_revK (upvalK p) |}.

Lemma supath_turnK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G)
  (e : edge G * bool) (p : upath) :
  supath f s s (e :: p) -> supath f (utarget e) (utarget e) (upath_turn (e :: p)).
Proof.
  move =>/andP[/andP[W U] N]. splitb.
  - apply (uwalk_turn W).
  - rewrite map_rcons rcons_uniq.
    by revert U => /= /andP[-> ->].
  - rewrite map_rcons in_rcons.
    by revert N; rewrite /= in_cons.
Qed.
(*
Definition supath_turn {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G)
  (e : edge G * bool) (???(e :: p) : Supath f s s) := {| upval := _ ; upvalK := supath_turnK (upvalK ???) |}. *)

Lemma supath_turnsK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G)
  (p q : upath) :
  supath f s s (p ++ q) -> supath f (upath_source s q) (upath_source s q) (q ++ p).
Proof.
  move =>/andP[/andP[W U] N]. splitb.
  - apply (uwalk_turns W).
  - by rewrite map_cat uniq_catC -map_cat.
  - by rewrite map_cat mem_cat orbC -mem_cat -map_cat.
Qed.
(* 
Definition supath_turns {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G)
  (p ++ q : Supath f s s) := ???. *)

Lemma supath_nilK {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G) :
  supath f s s [::].
Proof. unfold supath; cbn. splitb. Qed.

Definition supath_nil {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (s : G) :=
  {| upval := [::] ; upvalK := supath_nilK f s |}.


(* TODO would be good to have it in bool! *)
(*
Definition uacyclic {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) : bool :=
  [forall x : G, [forall p : Supath f x x, p == supath_nil f x]].
Lemma uacyclic_T {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :
  uacyclic f -> forall (x : G) (p : Supath f x x), p = supath_nil f x.
Proof. move => C x p. by revert C => /forallP/(_ x)/forallP/(_ p)/eqP. Qed.
*)
Definition uacyclic {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) :=
  forall (x : G) (p : Supath f x x), p = supath_nil f x.

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
  forall (x y : G), exists (_ : Supath f x y), true.


(** ** Connectivity for functions injective except on None *)
Definition is_uconnected {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (x y : G) :=
  [exists p : Supath f x y, true].

Definition is_uconnected_id {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (x : G) :
  is_uconnected f x x.
Proof. apply /existsP. by exists (supath_nil _ _). Defined.

Definition is_uconnected_sym {Lv Le : Type} {I : eqType} {G : graph Lv Le} (f : edge G -> option I) (x y : G) :
  is_uconnected f x y -> is_uconnected f y x.
Proof. move => /existsP[P _]. apply /existsP. by exists (supath_rev P). Defined.

Lemma uconnected_simpl {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (s t : G) p :
  {in ~: f @^-1 None &, injective f} -> uwalk s t p -> None \notin [seq f e.1 | e <- p] ->
  {P : Supath f s t | {subset upval P <= p}}.
Proof.
  move => F. revert s t. induction p as [ | e p IH] => s t.
  { move => /eqP-<- _. by exists (supath_nil f s). }
  rewrite /supath /= in_cons => /andP[/eqP-<- W] {s} /norP[n N].
  revert IH => /(_ _ _ W N) {W N} [q Qin].
  assert (K : supath f (usource e) (utarget e) [:: e]).
  { rewrite /supath !in_cons /= orb_false_r. splitb. }
  set k := {| upval := _ ; upvalK := K |}.
  destruct (upath_disjoint f k q) eqn:D.
  { exists (supath_cat D).
    intros a. rewrite /= !in_cons => /orP[-> | ?] //.
    apply /orP; right. by apply Qin. }
  destruct q as [q Q].
  revert D; rewrite /upath_disjoint disjoint_sym disjoint_has /k has_sym /= orb_false_r => /negPn/mapP-E.
  assert (E' : exists2 a, a \in q & f e.1 == f a.1).
  { destruct E as [a]. exists a; trivial. by apply /eqP. }
  revert E' => {E} /sig2W[[a b] In /eqP-Hea].
  assert (a = e.1).
  { enough (a \in ~: f @^-1 None /\ e.1 \in ~: f @^-1 None) as [A E] by by apply (F _ _ A E).
    rewrite !in_set -Hea.
    by revert n; rewrite eq_sym => ->. }
  subst a; clear Hea.
  rewrite in_elt_sub in In.
  revert In => /existsP/sigW[[m /= _] /eqP-Qeq].
  assert (Q' : supath f (utarget e) t q) by assumption.
  rewrite Qeq in Q'.
  destruct (supath_subKK Q') as [_ R], e as [e c]; cbn in *.
  destruct (eq_comparable b c); [subst b | ].
  - exists {| upval := _ ; upvalK := R |}.
    intros a. rewrite /= !in_cons => /orP[-> | In] //.
    apply /orP; right. apply Qin, (mem_drop In).
  - assert (b = ~~c) by by destruct b, c. subst b.
    revert R. rewrite /supath map_cons in_cons /=
      => /andP[/andP[/andP[_ W] /andP[_ U]] /norP[_ N]].
    assert (M : supath f (endpoint (~~ c) e) t (drop m.+1 q)) by splitb.
    exists {| upval := (drop m.+1 q) ; upvalK := M |}.
    intros a. rewrite /= !in_cons => In.
    apply /orP; right. apply Qin, (mem_drop In).
Qed.

Definition is_uconnected_comp {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} ->
  forall (x y z : G), is_uconnected f x y -> is_uconnected f y z -> is_uconnected f x z.
Proof.
  move => F x y z /existsP[[pxy /andP[/andP[Wxy _] Nxy]] _] /existsP[[pyz /andP[/andP[Wyz _] Nyz]] _].
  enough (P : Supath f x z).
  { apply /existsP. by exists P. }
  apply (@uconnected_simpl _ _ _ _ _ _ _ (pxy ++ pyz)); trivial.
  - by apply (uwalk_cat Wxy).
  - rewrite map_cat mem_cat. splitb.
Defined.

Global Instance is_uconnected_Equivalence {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) : CEquivalence (is_uconnected f).
Proof. constructor. exact (is_uconnected_id _). exact (is_uconnected_sym (f := _)). exact (is_uconnected_comp F). Defined.

Lemma is_uconnected_eq {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> forall u v w, is_uconnected f u v ->
  is_uconnected f u w = is_uconnected f v w.
Proof.
  move => F u v w UV.
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
  intros F x y z. split.
  - apply is_uconnected_id.
  - by apply is_uconnected_eq.
Qed.

(** Equivalence classes of uconnected, so to speak about connected components *)
Definition uconnected_nb {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :=
  #|equivalence_partition (is_uconnected f) [set: G]|.

Lemma uconnected_to_nb1 {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  #|G| <> 0 -> uconnected f -> uconnected_nb f = 1.
Proof.
  move => N C.
  destruct (set_0Vmem [set: G]) as [Hc | [v _]]; trivial.
  { contradict N. by rewrite -cardsT Hc cards0. }
  unfold uconnected_nb, equivalence_partition.
  apply /eqP/cards1P.
  exists [set u in [set: G] | is_uconnected f v u].
  apply /eqP/eq_set1P. split.
  { apply /imsetP. by exists v. }
  move => ? /imsetP [u _ ?]; subst.
  apply eq_finset => w.
  rewrite in_set /=.
  transitivity true; [ | symmetry]; apply /existsP; apply C.
Qed.

Lemma uconnected_from_nb1 {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  uconnected_nb f = 1 -> uconnected f.
Proof.
  move => /eqP/cards1P[S /eqP/eq_set1P[Sin Seq]] u v.
  assert (Suin : [set w in [set: G] | is_uconnected f u w] \in
    equivalence_partition (is_uconnected f) [set: G]).
  { apply /imsetP. by exists u. }
  assert (UW := Seq _ Suin). cbn in UW. subst S.
  assert (Svin : [set w in [set: G] | is_uconnected f v w] \in
    equivalence_partition (is_uconnected f) [set: G]).
  { apply /imsetP. by exists v. }
  assert (Heq := Seq _ Svin). cbn in Heq.
  assert (V : v \in [set w in [set: G] | is_uconnected f v w]).
  { rewrite in_set. splitb. apply is_uconnected_id. }
  rewrite Heq !in_set /= in V.
  by revert V => /existsP.
Qed.

Lemma nb1_not_empty {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  uconnected_nb f = 1 -> #|G| <> 0.
Proof.
  move => /eqP/cards1P[? /eqP/eq_set1P[Sin _]] N.
  rewrite -cardsT in N. apply cards0_eq in N.
  contradict Sin; apply /negP.
  rewrite N /equivalence_partition. apply /imsetP. move => [? In].
  contradict In; apply /negP.
  by rewrite !in_set.
Qed.

Definition neighbours {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G) :=
  [set utarget e | e : edge G * bool & (f e.1 != None) && (usource e == v)].

Lemma uacyclic_loop {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) :
  uacyclic f -> forall e, f e <> None -> source e <> target e.
Proof.
  move => A e En E.
  enough (P : supath f (source e) (source e) [:: forward e]).
  { specialize (A _ {| upval := _ ; upvalK := P |}).
    contradict A; cbnb. }
  rewrite /supath in_cons orb_false_r. splitb; apply /eqP.
  - by rewrite E.
  - by apply nesym.
Qed.

Lemma uacyclip_2loop {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  {in [set e | f e.1 != None & usource e == v] &, injective (fun e : edge G * bool => utarget e)}.
Proof.
  move => F A [e eb] [j jb]; rewrite !in_set /= =>
    /andP[/eqP-En /eqP-Es] /andP[/eqP-Jn /eqP-Js] T.
  apply /eqP/negPn/negP => /eqP-Hejb.
  assert (Hej : e <> j).
  { move => ?; subst j.
    destruct (eq_comparable eb jb) as [ | Hb]; [by subst jb | ].
    assert (Hf := uacyclic_loop A En). contradict Hf.
    by destruct eb, jb. }
  enough (P : supath f v v [:: (e, eb); (j, ~~ jb)]).
  { specialize (A _ {| upval := _ ; upvalK := P |}).
    contradict A. cbnb. }
  rewrite /supath /= !in_cons !orb_false_r.
  splitb; apply /eqP; rewrite ?negb_involutive //; try by apply nesym.
  intro Fej. contradict Hej.
  apply F; rewrite // !in_set; by apply /eqP.
Qed.

Lemma neighbours_nb {Lv Le : Type} {I : finType} {G : graph Lv Le} (f : edge G -> option I) (v : G) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f ->
  #|neighbours f v| = #|~: f @^-1 None :&: edges_at v|.
Proof.
  move => F A.
  rewrite /neighbours card_in_imset -?card_set_subset; last by by apply uacyclip_2loop.
  assert (Hg : forall (e : [finType of {a | (f a.1 != None) && (usource a == v)}]),
    ((val e).1 \in ~: f @^-1 None) && ((val e).1 \in edges_at v)).
  { move => [[e b] /= /andP[? ?]].
    rewrite !in_set. splitb.
    apply /existsP. by exists (~~b). }
  set g : [finType of {a | (f a.1 != None) && (usource a == v)}] ->
    [finType of {e | (e \in ~: f @^-1 None) && (e \in edges_at v)}] :=
    fun e => Sub (val e).1 (Hg e).
  assert (Hh : forall e : [finType of {e | (e \in ~: f @^-1 None) && (e \in edges_at v)}],
    exists b, (f (val e, b).1 != None) && (usource (val e, b) == v)).
  { move => [e] /=.
    rewrite !in_set => /andP[? /existsP[b ?]].
    exists (~~b). splitb. by rewrite negb_involutive. }
  set h : [finType of {e | (e \in ~: f @^-1 None) && (e \in edges_at v)}] ->
    [finType of {a | (f a.1 != None) && (usource a == v)}] :=
    fun e => let (b, H) := sigW (Hh e) in Sub (val e, b) H.
  apply (@bij_card_eq _ _ g), (@Bijective _ _ _ h).
  - move => [e E].
    rewrite /h /g /=.
    destruct (sigW _) as [b H].
    apply /eqP; cbn; simpl; splitb; apply /eqP.
    destruct (eq_comparable b e.2) as [-> | Hbe]; trivial.
    revert E H => /andP[/eqP-En /eqP-V] /andP[_ /eqP-V'].
    assert (Hf := uacyclic_loop A En). contradict Hf.
    destruct b, e as [? []]; by rewrite // V V'.
  - move => ?. rewrite /h /g /=. destruct (sigW _). cbnb.
Qed.

Lemma remove_vertex_card {Lv Le : Type} {G : graph Lv Le} (v : G) :
  #|remove_vertex v| + 1 = #|G|.
Proof.
  rewrite card_set_subset cardsE cardsC1.
  enough (#|G| <> 0) by lia.
  intro N. apply card0_eq in N. by specialize (N v).
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
  s t (p : Supath (fun (e : edge (induced S)) => f (val e)) s t) :
  {q : Supath f (val s) (val t) & upval q = [seq (val a.1, a.2) | a <- upval p]}.
Proof.
  destruct p as [p P]. revert s t P.
  induction p as [ | ([a A], b) p IH]; simpl => s t; rewrite /supath /=.
  { introb. by exists (supath_nil _ _). }
  rewrite in_cons => /andP[/andP[/andP[/eqP-? W] /andP[u U]] /norP[n N]]. subst s. simpl.
  assert (P : supath (fun (e : edge (induced S)) => f (val e)) (Sub (endpoint b a) (induced_proof b (valP (exist _ a A))) : induced S)
    t p) by splitb.
  specialize (IH _ _ P). destruct IH as [[q Q] HQ].
  revert HQ; cbnb => ?; subst q. simpl in Q.
  enough (QS : supath f (endpoint (~~ b) a) (val t) ((a, b) :: _))
    by by exists {| upval := _ ; upvalK := QS|}.
  revert Q. rewrite /supath /= in_cons. introb. splitb.
  revert u. clear. induction p as [ | c p IH]; trivial.
  rewrite /= !in_cons. move => /norP[l L]. splitb.
  by apply IH.
Qed.

Lemma supath_to_induced {Lv Le : Type} {G : graph Lv Le} (S : {set G})
  {I J : finType} (f : edge G -> option I) (f' : edge (induced S) -> option J)
  s t (p : Supath f s t) :
  (forall e (E : e \in edge_set S), None <> f e -> None <> f' (Sub e E)) ->
  (forall e a (E : e \in edge_set S) (A : a \in edge_set S),
    f' (Sub e E) = f' (Sub a A) -> f e = f a) ->
  (forall e, e \in upval p -> e.1 \in edge_set S) ->
  forall (Sin : s \in S) (Tin : t \in S),
  {q : Supath f' (Sub s Sin) (Sub t Tin) & upval p = [seq (val a.1, a.2) | a <- upval q]}.
Proof. (* in fact can even deduce Sin and Tin, provided p not empty *)
  intros F0 F1 Hp Sin Tin.
  destruct p as [p P].
  simpl in *.
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
  revert IHp => /(_ Hp' _ T P) {Hp Hp' P} [[q Q] ?]. subst p.
  enough (Q' : supath (f' : edge (induced _) -> _) (Sub (usource e) Sin) (Sub t Tin)
    ((Sub e.1 E : edge (induced S), e.2) :: q)).
  { exists {| upvalK := Q' |}. by destruct e. }
  assert (E' : supath (f' : edge (induced _) -> _) (Sub (usource e) Sin) (Sub (utarget e) T) [:: (Sub e.1 E, e.2)]). (* TODO lemma for edge supath? *)
  { rewrite /supath /= in_cons in_nil orb_false_r. splitb; try by cbnb.
    apply /eqP. clear - F0 Pn. by apply F0. }
  rewrite -cat1s.
  apply (@supath_catK _ _ _ _ _ _ _ _ {| upvalK := E' |} {| upvalK := Q |}).
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

Lemma induced_upath_inside {Lv Le : Type} {G : graph Lv Le} (S : {set G}) (q : @upath _ _ (induced S)) e :
  e \in [seq (val a.1, a.2) | a <- q] -> e.1 \in edge_set S.
Proof. move => /mapP[[[e' Ein] ?] ? ?]. by subst e. Qed.

Lemma remove_vertex_uacyclic {Lv Le : Type} {I : finType} {G : graph Lv Le}
  (f : edge G -> option I) (v : G) :
  uacyclic f -> uacyclic (@remove_vertex_f _ _ _ _ f v).
Proof.
  move => A [x X] [p' P']. cbnb.
  enough (P : supath f x x [seq (val e.1, e.2) | e <- p']).
  { specialize (A _ {| upval := _ ; upvalK := P |}).
    by destruct p'. }
  revert P' => /andP[/andP[W ?] ?].
  splitb; rewrite -?map_comp //.
  enough (H : forall x X y Y, uwalk (Sub x X : remove_vertex v) (Sub y Y) p' ->
    uwalk x y [seq (val e.1, e.2) | e <- p']) by by apply (H _ _ _ _ W).
  clear; induction p' as [ | [[? ?] ?] ? IH] => // ? ? ? ?; cbnb => /andP[? W].
  splitb. apply (IH _ _ _ _ W).
Qed.

(** ** Some lemmae when considering standard isomorphisms (those which do not flip edges) *)
(** Isomorphisms preserve out/in-edges *)
Lemma edges_at_outin_iso {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (h : F ≃ G) :
  h.d =1 xpred0 ->
  forall b v, edges_at_outin b (h v) = [set h.e e | e in edges_at_outin b v].
Proof.
  move => H b v. apply /setP => e.
  by rewrite -[e](bijK' h.e) bij_imset_f !inE endpoint_iso H bij_eqLR bijK.
Qed.

Definition iso_path {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (h : F ≃ G) :
  upath -> upath :=
  fun p => [seq (h.e e.1, e.2) | e <- p].

Lemma iso_walk {Lv: comMonoid} {Le : elabelType} (F G : graph Lv Le) (h : F ≃ G) :
  h.d =1 xpred0 ->
  forall p s t, uwalk s t p -> uwalk (h s) (h t) (iso_path h p).
Proof.
  intros H p; induction p as [ | u p HP]; intros s t; cbn.
  + by move => /eqP ->.
  + move => /andP[/eqP w W].
    rewrite !endpoint_iso !H w.
    splitb. by apply HP.
Qed.

Lemma supath_cons {Lv Le : Type} {G : graph Lv Le}
  {I : finType} (f : edge G -> option I) (s t : G) e (p : upath) :
  supath f s t (e :: p) =
  (supath f (utarget e) t p && (usource e == s) &&
  (f e.1 \notin [seq f a.1 | a <- p]) && (None != f e.1)).
Proof.
  rewrite /supath /= in_cons negb_orb.
  destruct (usource e == s); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (uwalk (utarget e) t p); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (uniq [seq f a.1 | a <- p]); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (None \notin [seq f a.1 | a <- p]) eqn:Hr; rewrite !Hr ?andb_false_r ?andb_true_r //=.
Qed. (* TODO use it everywhere *)

Lemma supath_rcons {Lv Le : Type} {G : graph Lv Le}
  {I : finType} (f : edge G -> option I) (s t : G) e (p : upath) :
  supath f s t (rcons p e) =
  (supath f s (usource e) p && (utarget e == t) &&
  (f e.1 \notin [seq f a.1 | a <- p]) && (None != f e.1)).
Proof.
  rewrite /supath /= map_rcons in_rcons rcons_uniq negb_orb uwalk_rcons.
  destruct (utarget e == t); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (uwalk s (usource e) p); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (uniq [seq f a.1 | a <- p]); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (None \notin [seq f a.1 | a <- p]) eqn:Hr; rewrite !Hr ?andb_false_r ?andb_true_r //=.
Qed. (* TODO use it everywhere *)

Lemma supath_of_nil {Lv Le : Type} {G : graph Lv Le} {I : finType} (f : edge G -> option I)
  (s t : G) :
  supath f s t [::] = (s == t).
Proof. by rewrite /supath /= 2!andb_true_r. Qed. (* TODO use it everywhere *)

Lemma supath_of_nilP {Lv Le : Type} {G : graph Lv Le} {I : finType} (f : edge G -> option I)
  (s t : G) :
  reflect (s = t) (supath f s t [::]).
Proof. rewrite supath_of_nil. apply /eqP. Qed.

Lemma supath_from_induced {Lv Le : Type} {G : graph Lv Le} (S : {set G})
  {I J : finType} (f : edge G -> option I) (f' : edge (induced S) -> option J)
  s t (q : Supath f' s t) :
  (forall e (E : e \in edge_set S), None <> f' (Sub e E) -> None <> f e) ->
  (forall e a (E : e \in edge_set S) (A : a \in edge_set S),
    f e = f a -> f' (Sub e E) = f' (Sub a A)) ->
  supath f (val s) (val t) [seq (val a.1, a.2) | a <- upval q].
Proof.
  intros F0 F1.
  destruct q as [q Q]. revert s t Q.
  induction q as [ | ([a A], b) q IH] => /= s t Q.
  { revert Q => /supath_of_nilP-?. subst. apply supath_nilK. }
  rewrite supath_cons /= in Q. revert Q => /andP[/andP[/andP[Q /eqP-?] U] /eqP-N]. subst s. simpl.
  revert IH => /(_ _ _ Q)-IH. rewrite supath_cons IH. splitb.
  - clear - F1 U.
    apply /mapP. move => [c' /mapP[c Cin ?] Fc]. subst c'. simpl in Fc.
    contradict U. apply /negP/negPn/mapP.
    exists c; trivial. simpl.
    destruct c as [[? ?] ?]. by apply F1.
  - clear - F0 N.
    apply /eqP. apply (F0 _ _ N).
Qed.

(* TODO Supath pour turn et turns ? *) (* TODO mettre un fichier upath *)

(* TODO c'est le vrai disjoint, l'autre est plutôt un f-disjoint *)
(* TODO Utiliser plutôt disjoint avec f = id ? pour en déduire des lemmes *)
(* TODO renommer ; et mettre ailleurs ? *)
Definition upath_disjoint2 {Lv Le : Type} {G : graph Lv Le}
  (p q : @upath _ _ G) := [disjoint [seq x.1 | x <- p] & [seq x.1 | x <- q]].

Lemma upath_disjoint2_sym {Lv Le : Type} {G : graph Lv Le} (p q : @upath _ _ G) :
  upath_disjoint2 p q = upath_disjoint2 q p.
Proof. by rewrite /upath_disjoint2 disjoint_sym. Qed.

Lemma upath_disjoint2_rev {Lv Le : Type} {G : graph Lv Le} (p q : @upath _ _ G) :
  upath_disjoint2 p q -> upath_disjoint2 (upath_rev p) q.
Proof. by rewrite /upath_disjoint2 upath_rev_fst disjoint_rev. Qed.


