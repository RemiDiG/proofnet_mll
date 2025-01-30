(* Basic operations respecting correctness *)

From Coq Require Import Bool.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From GraphTheory Require Import preliminaries mgraph setoid_bigop.

From Yalla Require Export mll_prelim graph_more upath supath mll_def mll_basic.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Section Atoms.

(** A set of atoms for building formulas *)
Context { atom : DecType }.
(* TODO meilleur moyen de récupérer les notations *)
Notation formula := (@formula atom).
Notation base_graph := (graph (flat rule) (flat (formula * bool))).



(** ** Graph with a single vertex and no edge, unit_graph *)
Lemma unit_graph_uacyclic (R : rule) : uacyclic (@switching atom (unit_graph R)).
Proof. move => ? [[ | [[] ?] ?] ?]. by apply val_inj. Qed.

Lemma unit_graph_uconnected (R : rule) : uconnected (@switching_left atom (unit_graph R)).
Proof. intros [] []. by exists (supath_nil _ _). Qed.

Lemma unit_graph_correct_weak (R : rule) : @correct_weak atom (unit_graph R).
Proof.
  split.
  - apply unit_graph_uacyclic.
  - apply unit_graph_uconnected.
Qed.

Lemma unit_graph_correct (R : rule) : @correct atom (unit_graph R).
Proof.
  apply correct_from_weak, unit_graph_correct_weak.
  by rewrite card_unit.
Qed.


(** ** Invert an edge not touching a ⅋ *)
Definition invert_edge_graph {Lv Le : Type} (G : graph Lv Le) (e : edge G) : graph Lv Le :=
  {| vertex := vertex G;
     edge := edge G;
     endpoint b a := endpoint (if a == e then ~~b else b) a;
     vlabel := @vlabel _ _ G;
     elabel := @elabel _ _ G;
  |}.

Fixpoint invert_edge_upath {Lv Le : Type} (G : graph Lv Le) (e : edge G) p :=
  match p with
  | [::] => [::]
  | a :: q => (a.1, if a.1 == e then ~~ a.2 else a.2) :: invert_edge_upath e q
  end.

Lemma invert_edge_upath_inv {Lv Le : Type} (G : graph Lv Le) (e : edge G) :
  involutive (invert_edge_upath e).
Proof.
  move=> p. induction p as [ | [? ?] ? IH] => //=.
  rewrite {}IH. case_if.
Qed.

Lemma invert_edge_switching (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  @switching _ (invert_edge_graph e) =1 @switching _ G.
Proof. move => ? ? ?. rewrite /switching /=. case_if. Qed.

Lemma invert_edge_switching_left (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  @switching_left _ (invert_edge_graph e) =1 @switching_left _ G.
Proof.
  move => /eqP/negPf-Hs /eqP/negPf-Ht a; unfold switching_left.
  destruct (eq_comparable a e) as [? | A]; [subst a | ].
  - by rewrite /= eq_refl Hs Ht.
  - by revert A => /= /eqP/negPf-->.
Qed.

Lemma invert_edge_eq_upath (G : base_graph) (e : edge G) {B} (f : _ -> B) g :
  f =1 g -> forall p,
  [seq f a.1 | a <- invert_edge_upath e p] = [seq g a.1 | a <- p].
Proof.
  intros FG p. induction p as [ | (a, b) p IH] => //=.
  by rewrite FG {}IH.
Qed.

Lemma invert_edge_uwalk (G : base_graph) (e : edge G) p (u v : G) :
  @uwalk _ _ (invert_edge_graph e) u v (invert_edge_upath e p) = uwalk u v p.
Proof.
  revert u v; induction p as [ | (a, b) p IH] => u v //=.
  rewrite IH {IH}. case_if.
Qed.

Lemma invert_edge_supath (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  forall p (u v : G), supath switching u v p =
  supath (@switching _ (invert_edge_graph e)) u v (invert_edge_upath e p).
Proof. move => *. by rewrite /supath invert_edge_uwalk (invert_edge_eq_upath e (invert_edge_switching _ _)). Qed.

Lemma invert_edge_supath_l (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  forall p (u v : G), supath switching_left u v p =
  supath (@switching_left _ (invert_edge_graph e)) u v (invert_edge_upath e p).
Proof. move => *. by rewrite /supath invert_edge_uwalk (invert_edge_eq_upath e (invert_edge_switching_left _ _)). Qed.

Lemma invert_edge_uacyclic (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  uacyclic (@switching _ (invert_edge_graph e)) <-> uacyclic (@switching _ G).
Proof.
  move => *; split => A ? [p P]; apply val_inj; simpl.
  all: enough (invert_edge_upath e p = [::]) by by destruct p as [ | (?, ?) ?].
  1: rewrite (@invert_edge_supath _ e) // in P.
  2: rewrite -(invert_edge_upath_inv e p) -(@invert_edge_supath _ e) // in P.
  all: move: A => /(_ _ (Sub _ P))-A.
  all: by inversion A.
Qed.

Lemma invert_edge_uconnected (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  uconnected (@switching_left _ (invert_edge_graph e)) <-> uconnected (@switching_left _ G).
Proof.
  move => *; split => C u v.
  all: destruct (C u v) as [[p P] _].
  1: rewrite -(invert_edge_upath_inv e p) -(@invert_edge_supath_l _ e) // in P.
  2: rewrite (@invert_edge_supath_l _ e) // in P.
  all: by exists (Sub _ P).
Qed.

Lemma invert_edge_correct_weak (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  correct_weak (invert_edge_graph e) <-> correct_weak G.
Proof.
  move => *; split => [[? ?] | [? ?]]; split.
  all: by apply (@invert_edge_uacyclic _ e) || apply (@invert_edge_uconnected _ e).
Qed.

Lemma invert_edge_correct (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  correct (invert_edge_graph e) <-> correct G.
Proof.
  move => S T; split => *.
  all: apply correct_from_weak;
  [ | by apply (invert_edge_correct_weak S T), correct_to_weak].
  - replace #|G| with #|invert_edge_graph e| by trivial.
    by apply correct_not_empty.
  - replace #|invert_edge_graph e| with #|G| by trivial.
    by apply correct_not_empty.
Qed.


(** ** Making the disjoint union and adding an edge from the first graph to the second *)
Definition union_edge_graph (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  base_graph := (G0 ⊎ G1) ∔ [inl x, A, inr y].

Lemma union_edge_switching_0_or_1 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) (i : bool) :
  let Gi (j : bool) := match j with
  | false => G0 | true => G1 end in
  let fv := match i return Gi i -> G0 ⊎ G1 with
  | false => inl | true => inr end in
  let fe := match i return edge (Gi i) -> edge (G0 ⊎ G1) with
  | false => inl | true => inr end in
  (fun e : edge (union_edge_graph x y A) * bool => switching e.1) \o
  (fun x : edge (Gi i) * bool => (Some (fe x.1), x.2)) =1
  (fun e => match e with
  | Some (inl a) => Some (inl (Some (fe a)))
  | Some (inr a) => Some (inr (fv a))
  | None => None (* never happens *)
  end) \o (fun e => switching e.1).
Proof. intros ? ? ? (?, ?). rewrite /switching /=. destruct i; case_if. Qed.

Lemma union_edge_switching_0 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  (fun e : edge (union_edge_graph x y A) * bool => switching e.1) \o
  (fun x : edge G0 * bool => (Some (inl x.1), x.2)) =1
  (fun e => match e with
  | Some (inl a) => Some (inl (Some (inl a)))
  | Some (inr a) => Some (inr (inl a))
  | None => None (* never happens *)
  end) \o (fun e => switching e.1).
Proof. apply (@union_edge_switching_0_or_1 _ _ _ _ _ false). Qed.
Lemma union_edge_switching_1 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  (fun e : edge (union_edge_graph x y A) * bool => switching e.1) \o
  (fun x : edge G1 * bool => (Some (inr x.1), x.2)) =1
  (fun e => match e with
  | Some (inl a) => Some (inl (Some (inr a)))
  | Some (inr a) => Some (inr (inr a))
  | None => None (* never happens *)
  end) \o (fun e => switching e.1).
Proof. intros (?, ?). rewrite /switching /=. case_if. Qed.


Lemma union_edge_switching_left_0_or_1 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) (i : bool) :
  let Gi (j : bool) := match j with
  | false => G0 | true => G1 end in
  let fe := match i return edge (Gi i) -> edge (G0 ⊎ G1) with
  | false => inl | true => inr end in
  (fun e : edge (union_edge_graph x y A) * bool => switching_left e.1) \o
  (fun x : edge (Gi i) * bool => (Some (fe x.1), x.2)) =1
  fun e => option_map Some (option_map fe (switching_left e.1)).
Proof. intros ? ? (?, ?). unfold switching_left; cbn. destruct i; case_if. Qed.
Notation union_edge_switching_left_0 := (fun x y A => @union_edge_switching_left_0_or_1 _ _ x y A false).
(* TODO notations comme ça, et avec i 1er argument ? *)
Lemma union_edge_switching_left_1 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  (fun e : edge (union_edge_graph x y A) * bool => switching_left e.1) \o
  (fun x : edge G1 * bool => (Some (inr x.1), x.2)) =1
  fun e => option_map Some (option_map inr (switching_left e.1)).
Proof. intros (?, ?). unfold switching_left; cbn. case_if. Qed.

Lemma union_edge_lrN (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) p u v :
  uwalk (inl u : union_edge_graph x y A) (inr v) p ->
  forward None \in p.
Proof.
  revert u v; induction p as [ | (e, b) p Hp] => u v //=.
  move => /andP[/eqP-W0 W1].
  destruct e as [[e | e] | ]; [ | by destruct b | by destruct b].
  clear W0 u.
  enough (forward None \in p) by caseb.
  destruct (utarget (Some (inl e) : edge (union_edge_graph x y A), b)) as [w | ] eqn:Hw; try by [].
  apply (Hp w v).
  by rewrite -Hw.
Qed.

Lemma union_edge_Nlr (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) {I : finType}
  (f : edge (union_edge_graph x y A) -> option I) (p : upath) (u v : union_edge_graph x y A) :
  supath f u v p -> forward None \in p -> (exists u' v', u = inl u' /\ v = inr v').
Proof.
  revert u v; induction p as [ | (e, b) p Hp] => u v //.
  rewrite supath_cons => /andP[/andP[/andP[P /eqP-?] U] /eqP-N].
  rewrite !in_cons.
  move => /orP[/andP[/= /eqP-? /eqP-?] | H].
  - subst u e b.
    destruct v as [v | v]; cbn.
    2:{ by exists x, v. }
    contradict U; apply /negP/negPn.
    assert (Hin : forward None \in upath_rev p).
    { apply (@union_edge_lrN _ _ _ _ _ _ v y).
      rewrite uwalk_rev.
      by revert P => /andP[/andP[-> _] _]. }
    rewrite (upath_rev_in p) in Hin.
    by rewrite (map_f _ Hin).
  - revert Hp => /(_ _ _ P H) {P} [u' [v' [Hu ->]]].
    destruct u as [u | u]; first by exists u, v'.
    contradict U; apply /negP/negPn.
    assert (e = None) as -> by by destruct e as [[? | ?] | ].
    by apply (@map_f _ _ (fun x => f x.1) _ (forward None)).
Qed.

Lemma union_edge_Nrl (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) {I : finType}
  (f : edge (union_edge_graph x y A) -> option I) (p : upath) (u v : union_edge_graph x y A) :
  supath f u v p -> backward None \in p -> exists u' v', u = inr u' /\ v = inl v'.
Proof.
  intros P ?.
  assert (Hin : forward None \in upath_rev p) by by rewrite (upath_rev_in p).
  destruct (union_edge_Nlr (supath_revK P) Hin) as [u' [v' [-> ->]]].
  by exists v', u'.
Qed.

Lemma union_edge_ll_or_rr (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) p (i : bool) :
  let Gi (j : bool) := match j with
  | false => G0 | true => G1 end in
  let fv := match i return Gi i -> G0 ⊎ G1 with
  | false => inl | true => inr end in
  let fe := match i return edge (Gi i) -> edge (G0 ⊎ G1) with
  | false => inl | true => inr end in
  forall (u v : Gi i), (* TODO generalize plenty of lemmas with this trick *)
  supath (@switching _ (union_edge_graph x y A)) (fv u) (fv v) p ->
  { q : upath | supath switching u v q & p = [seq (Some (fe x.1), x.2) | x <- q] }.
Proof.
  intros Gi fv fe u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn/negP => /existsP[[] N].
    - by destruct (union_edge_Nlr P N) as [? [? [? ?]]], i.
    - by destruct (union_edge_Nrl P N) as [? [? [? ?]]], i. }
  revert u v P Hin. induction p as [ | [[e | ] b] p IH] => u v P /= Hin.
  - revert P => /supath_of_nilP-P.
    exists nil; splitb. by destruct i; inversion P; simpl.
  - rewrite supath_cons in P. revert P => /andP[/andP[/andP[P /eqP-W] U] /eqP-N].
    assert (Ht : forall b, (None, b) \notin p).
    { apply /existsPn/negP => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP/negPn. caseb. }
    assert ({ e' | e = fe e' /\ bij.sumf (endpoint b) (endpoint b) (fe e') = fv (endpoint b e')})
      as [e' [? C]].
    { destruct e as [e' | e'], i; try by []; by exists e'. }
    subst e.
    assert (endpoint (~~ b) e' = u).
    { revert W => /eqP. clear. by destruct i; cbn => /eqP. }
    subst u. clear W.
    rewrite /= C in P.
    revert IH => /(_ _ _ P Ht)[p' P' ?]. subst p.
    exists ((e', b) :: p').
    + rewrite supath_cons /= P'. splitb.
      clear - U.
      destruct i.
      * rewrite -map_comp (eq_map (union_edge_switching_1 x y A) p') map_comp in U.
        assert (He := union_edge_switching_1 x y A (forward e')). simpl in He.
        rewrite He (mem_map _ _ (switching (forward e').1)) // in U.
        by move => [[? | ?] | ] [[? | ?] | ] // /eqP; cbn => ?; apply /eqP; cbn.
      * rewrite -map_comp (eq_map (union_edge_switching_0 x y A) p') map_comp in U.
        assert (He := union_edge_switching_0 x y A (forward e')). simpl in He.
        rewrite He (mem_map _ _ (switching (forward e').1)) // in U.
        by move => [[? | ?] | ] [[? | ?] | ] // /eqP; cbn => ?; apply /eqP; cbn.
    + by rewrite map_cons.
  - revert Hin => /(_ b) Hf; clear - Hf.
    contradict Hf; apply /negP/negPn.
    rewrite in_cons. caseb.
Qed.

Lemma union_edge_ll (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) p u v :
  supath (switching (G := union_edge_graph x y A)) (inl u) (inl v) p ->
  { q : upath | supath switching u v q & p = [seq (Some (inl x.1), x.2) | x <- q] }.
Proof. apply (@union_edge_ll_or_rr _ _ _ _ _ _ false). Qed.
Lemma union_edge_ll2 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) p u v :
  supath (switching_left (G := union_edge_graph x y A)) (inl u) (inl v) p ->
  { q : upath | supath switching_left u v q & p = [seq (Some (inl x.1), x.2) | x <- q] }.
Proof.
  intro P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn/negP => /existsP [[] N].
    - by destruct (union_edge_Nlr P N) as [? [? [? ?]]].
    - by destruct (union_edge_Nrl P N) as [? [? [? ?]]]. }
  revert u v P Hin. induction p as [ | [[[e | e] | ] b] p IH] => u v P //= Hin.
  - revert P => /supath_of_nilP-P.
    exists nil; splitb. by inversion P; simpl.
  - rewrite supath_cons in P. revert P => /andP[/andP[/andP[P /eqP-W] U] /eqP-N].
    assert (Ht : forall b, (None, b) \notin p).
    { apply /existsPn/negP => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP/negPn. caseb. }
    specialize (IH _ _ P Ht); destruct IH as [p' P' ?]; subst p.
    exists ((e, b) :: p').
    + rewrite supath_cons P' {P'} /=.
      inversion W. splitb.
      * clear - U.
        rewrite -map_comp (eq_map (union_edge_switching_left_0 x y A) p') map_comp in U.
        assert (He := union_edge_switching_left_0 x y A (forward e)). simpl in He.
        rewrite He -map_comp in U.
        assert (U0' : option_map Some (option_map inl (switching_left e))
          \notin [seq (option_map Some \o (option_map (@inl _ (@edge _ _ G1))))  _i
          | _i <- [seq switching_left _i.1 | _i <- p']]) by by rewrite -map_comp.
        rewrite (mem_map _ [seq switching_left _i.1 | _i <- p']
          (switching_left (forward e).1) (f:= (option_map Some \o [eta option_map inl]))) // in U0'.
        by move => [? | ] [? | ] /eqP; cbn => ?; apply /eqP; cbn.
      * clear -N. apply /eqP. revert N. move => /eqP. unfold switching_left. case_if.
    + by rewrite map_cons.
  - revert Hin => /(_ b) Hf; clear - Hf.
    contradict Hf; apply /negP/negPn.
    rewrite in_cons. caseb.
Qed.
Lemma union_edge_ll3 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) p u v :
  supath (switching_left (G := union_edge_graph x y A)) (inr u) (inr v) p ->
  { q : upath | supath switching_left u v q & p = [seq (Some (inr x.1), x.2) | x <- q] }.
Proof.
  intro P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn/negP => /existsP [[] N].
    - by destruct (union_edge_Nlr P N) as [? [? [? ?]]].
    - by destruct (union_edge_Nrl P N) as [? [? [? ?]]]. }
  revert u v P Hin. induction p as [ | [[[e | e] | ] b] p IH] => u v P //= Hin.
  - revert P => /supath_of_nilP-P.
    exists nil; splitb. by inversion P; simpl.
  - rewrite supath_cons in P. revert P => /andP[/andP[/andP[P /eqP-W] U] /eqP-N].
    assert (Ht : forall b, (None, b) \notin p).
    { apply /existsPn/negP => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP/negPn. caseb. }
    specialize (IH _ _ P Ht); destruct IH as [p' P' ?]; subst p.
    exists ((e, b) :: p').
    + rewrite supath_cons P' {P'} /=.
      inversion W. splitb.
      * clear - U.
        rewrite -map_comp (eq_map (union_edge_switching_left_1 x y A) p') map_comp in U.
        assert (He := union_edge_switching_left_1 x y A (forward e)). simpl in He.
        rewrite He -map_comp in U.
        assert (U0' : option_map Some (option_map inr (switching_left e))
          \notin [seq (option_map Some \o (option_map (@inr (@edge _ _ G0) _)))  _i
          | _i <- [seq switching_left _i.1 | _i <- p']]) by by rewrite -map_comp.
        rewrite (mem_map _ [seq switching_left _i.1 | _i <- p']
          (switching_left (forward e).1) (f:= (option_map Some \o [eta option_map inr]))) // in U0'.
        by move => [? | ] [? | ] /eqP; cbn => ?; apply /eqP; cbn.
      * clear -N. apply /eqP. revert N. move => /eqP. unfold switching_left. case_if.
    + by rewrite map_cons.
  - revert Hin => /(_ b) Hf; clear - Hf.
    contradict Hf; apply /negP/negPn.
    rewrite in_cons. caseb.
Qed.

Lemma union_edge_rr (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) p u v :
  supath (switching (G := union_edge_graph x y A)) (inr u) (inr v) p ->
  { p' : upath | supath switching u v p' & p = [seq (Some (inr x.1), x.2) | x <- p'] }.
Proof. apply (@union_edge_ll_or_rr _ _ _ _ _ _ true). Qed.


Lemma union_edge_to_ll_or_rr (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) (i : bool) p :
  let Gi (j : bool) := match j with
  | false => G0 | true => G1 end in
  let fv := match i return Gi i -> G0 ⊎ G1 with
  | false => inl | true => inr end in
  let fe := match i return edge (Gi i) -> edge (G0 ⊎ G1) with
  | false => inl | true => inr end in
  forall (u v : Gi i),
  supath switching_left u v p ->
  supath (switching_left (G := union_edge_graph x y A)) (fv u) (fv v) [seq (Some (fe x.1), x.2) | x <- p].
Proof.
  intros Gi fv fe.
  induction p as [ | (e, b) p IH] => u v.
  { by destruct i. }
  rewrite map_cons 2!supath_cons => /andP[/andP[/andP[/= P /eqP-?] U] /eqP-N]. subst u.
  revert IH => /(_ _ _ P)-P'.
  assert (I : bij.sumf (endpoint b) (endpoint b) (fe e) = fv (endpoint b e)) by by destruct i.
  rewrite I P' {I P'}.
  splitb.
  - by destruct i.
  - rewrite -map_comp (eq_map (@union_edge_switching_left_0_or_1 _ _ x y A i) p).
    assert (Hr : switching_left (Some (fe e) : edge (union_edge_graph x y A)) =
      option_map Some (option_map fe (switching_left e))).
    { replace e with ((forward e).1) by trivial. by rewrite -union_edge_switching_left_0_or_1. }
    rewrite Hr {Hr}.
    rewrite map_comp mem_map 1?map_comp 1?mem_map //.
    all: destruct i; by move => [? | ] [? | ] /eqP-?; apply /eqP.
  - assert (Hd := union_edge_switching_left_0_or_1 x y A (forward e)).
    revert Hd => /eqP; cbn => /eqP ->.
    revert N. destruct (switching_left e) eqn:E; cbnb. by rewrite E.
Qed.
Lemma union_edge_to_ll (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) p u v :
  supath switching_left u v p ->
  supath (switching_left (G := union_edge_graph x y A)) (inl u) (inl v) [seq (Some (inl x.1), x.2) | x <- p].
Proof. apply (@union_edge_to_ll_or_rr _ _ _ _ _ false). Qed.
Lemma union_edge_to_ll2 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) p u v :
  supath switching u v p ->
  supath (switching (G := union_edge_graph x y A)) (inl u) (inl v) [seq (Some (inl x.1), x.2) | x <- p].
Proof.
  revert u v; induction p as [ | (e, b) p IH] => u v //.
  rewrite map_cons 2!supath_cons => /andP[/andP[/andP[/= P /eqP-?] U] _]. subst u.
  revert IH => /(_ _ _ P)-->.
  splitb.
  rewrite -map_comp (eq_map (union_edge_switching_0 _ _ _) _).
  assert (He := union_edge_switching_0 x y A (forward e)). simpl in He.
  rewrite He map_comp (mem_map _ _ (switching (forward e).1)) //.
  by move => [[? | ?] | ] [[? | ?] | ] // /eqP; cbn => ?; apply /eqP; cbn.
Qed.
Lemma union_edge_to_ll3 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) p u v :
  supath switching u v p ->
  supath (switching (G := union_edge_graph x y A)) (inr u) (inr v) [seq (Some (inr x.1), x.2) | x <- p].
Proof.
  revert u v; induction p as [ | (e, b) p IH] => u v //.
  rewrite map_cons 2!supath_cons => /andP[/andP[/andP[/= P /eqP-?] U] _]. subst u.
  revert IH => /(_ _ _ P)-->.
  splitb.
  rewrite -map_comp (eq_map (union_edge_switching_1 _ _ _) _).
  assert (He := union_edge_switching_1 x y A (forward e)). simpl in He.
  rewrite He map_comp (mem_map _ _ (switching (forward e).1)) //.
  by move => [[? | ?] | ] [[? | ?] | ] // /eqP; cbn => ?; apply /eqP; cbn.
Qed.

Lemma union_edge_to_rr (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) p u v :
  supath switching_left u v p ->
  supath (switching_left (G := union_edge_graph x y A)) (inr u) (inr v) [seq (Some (inr x.1), x.2) | x <- p].
Proof. apply (@union_edge_to_ll_or_rr _ _ _ _ _ true). Qed.

Lemma union_edge_to_lr (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  A.2 \/ vlabel y <> ⅋ ->
  uconnected (switching_left (G := G0)) -> uconnected (switching_left (G := G1)) ->
  forall u v, Supath (switching_left (G := union_edge_graph x y A)) (inl u) (inr v).
Proof.
  move => NP C0 C1 u v.
  enough (H : exists _ : Supath (switching_left (G := union_edge_graph x y A)) (inl u) (inr v), true).
  { revert H. by move => /sigW[? _]. }
  destruct (C0 u x) as [[p0 P0] _].
  assert (Q0 := union_edge_to_ll x y A P0).
  set q0 : @upath _ _ (union_edge_graph x y A) := [seq (Some (inl x.1), x.2) | x <- p0].
  destruct (C1 y v) as [[p1 P1] _].
  assert (Q1 := union_edge_to_rr x y A P1).
  set q1 : @upath _ _ (union_edge_graph x y A) := [seq (Some (inr x.1), x.2) | x <- p1].
  set qn : @upath _ _ (union_edge_graph x y A) := [:: forward None].
  assert (Qn : supath (switching_left (G := union_edge_graph x y A)) (inl x) (inr y) qn).
  { rewrite /supath /= !eq_refl /= mem_seq1 /switching_left /=.
    case_if. destruct NP as [NP | NP]; contradict NP; [by apply/negP | by []]. }
  set L : Supath _ _ _ := Sub q0 Q0;
  set R : Supath _ _ _ := Sub q1 Q1;
  set N : Supath _ _ _ := Sub qn Qn.
  assert (Some None \notin [seq switching_left x0.1 | x0 <- q0] /\
    Some None \notin [seq switching_left x0.1 | x0 <- q1]) as [? ?].
  { rewrite /q0 /q1 -2!map_comp (eq_map (union_edge_switching_left_0 x y A))
      (eq_map (union_edge_switching_left_1 x y A)).
    split; apply /mapP; move => [[? ?] _ Heq].
    all: contradict Heq; unfold switching_left; case_if. }
  assert (None \notin [seq switching_left x0.1 | x0 <- q0] /\
    None \notin [seq switching_left x0.1 | x0 <- q1]) as [? ?].
  { split; apply /negP => Hf;
    [clear - Hf Q0; revert Q0 => /andP[/andP[_ _] /negP Hc] //
    | clear - Hf Q1; revert Q1 => /andP[/andP[_ _] /negP Hc] //]. }
  assert (upath_disjoint switching_left (val N) (val L) /\ upath_disjoint switching_left (val N) (val R)) as [Dl Dr].
  { split; apply /disjointP; move => [[e | ] | ]; cbn.
    all: try (move => _; by apply /negP).
    all: move => Hf _; revert Hf; rewrite mem_seq1 /switching_left; cbn.
    all: case_if. }
  rewrite /upath_disjoint disjoint_sym in Dl.
  assert (D : upath_disjoint switching_left (val (supath_cat Dl)) (val R)).
  { rewrite /upath_disjoint /supath_cat /= map_cat disjoint_cat. splitb.
    apply /disjointP; move => [[[e | e] | ] | ]; cbn.
    all: try (move => _; by apply /negP).
    - move => _; apply /negP.
      rewrite /q1 -map_comp (eq_map (union_edge_switching_left_1 x y A)).
      apply /mapP; move => [[? ?] _ Heq]. contradict Heq.
      unfold switching_left. case_if.
    - move => Hf _; revert Hf; apply /negP.
      rewrite /q0 -map_comp (eq_map (union_edge_switching_left_0 x y A)).
      apply /mapP; move => [[? ?] _ Heq]. contradict Heq.
      unfold switching_left. case_if. }
  by exists (supath_cat D).
Qed.

Lemma union_edge_to_rl (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  A.2 \/ vlabel y <> ⅋ ->
  uconnected (switching_left (G := G0)) -> uconnected (switching_left (G := G1)) ->
  forall u v, Supath (switching_left (G := union_edge_graph x y A)) (inr u) (inl v).
Proof. intros NP C0 C1 u v. exact (supath_rev (union_edge_to_lr x NP C0 C1 v u)). Qed.

Lemma union_edge_uacyclic (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  uacyclic (@switching _ G0) -> uacyclic (@switching _ G1) ->
  uacyclic (@switching _ (union_edge_graph x y A)).
Proof.
  intros A0 A1 [u | u] p; apply val_inj.
  - destruct (union_edge_ll (valP p)) as [q Q ->].
    assert (Hf := A0 _ (Sub q Q)).
    inversion Hf. by subst q.
  - destruct (union_edge_rr (valP p)) as [q Q ->].
    assert (Hf := A1 _ (Sub q Q)).
    inversion Hf. by subst q.
Qed.

Lemma union_edge_uconnected (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  A.2 \/ vlabel y <> ⅋ ->
  uconnected (@switching_left _ G0) -> uconnected (@switching_left _ G1) ->
  uconnected (@switching_left _ (union_edge_graph x y A)).
Proof.
  intros NP C0 C1 [u | u] [v | v].
  - destruct (C0 u v) as [[p P] _].
    by exists (Sub _ (union_edge_to_ll x y A P)).
  - by exists (union_edge_to_lr _ NP C0 C1 _ _).
  - by exists (union_edge_to_rl _ NP C0 C1 _ _).
  - destruct (C1 u v) as [[p P] _].
    by exists (Sub _ (union_edge_to_rr x y A P)).
Qed.

Lemma union_edge_correct_weak (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  A.2 \/ vlabel y <> ⅋ ->
  correct_weak G0 -> correct_weak G1 -> correct_weak (union_edge_graph x y A).
Proof.
  intros NP [A0 C0] [A1 C1]. split.
  - by apply union_edge_uacyclic.
  - by apply union_edge_uconnected.
Qed.

Lemma union_edge_correct (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  A.2 \/ vlabel y <> ⅋ ->
  correct_weak G0 -> correct_weak G1 -> correct (union_edge_graph x y A).
Proof.
  move => H C0 C1.
  apply correct_from_weak.
  - rewrite card_sum.
    enough (#|G0| <> 0) by lia.
    by apply fintype0.
  - by apply union_edge_correct_weak.
Qed.

Lemma union_edge_uacyclic2 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  uacyclic (@switching _ (union_edge_graph x y A)) ->
  uacyclic (@switching _ G0) /\ uacyclic (@switching _ G1).
Proof.
  move=> A2. split => u [p P].
  - apply val_inj. simpl.
    move: A2 => /(_ _ (Sub _ (union_edge_to_ll2 x y A P))).
    by destruct p.
  - apply val_inj. simpl.
    move: A2 => /(_ _ (Sub _ (union_edge_to_ll3 x y A P))).
    by destruct p.
Qed.

Lemma union_edge_uconnected2 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  uconnected (@switching_left _ (union_edge_graph x y A)) ->
  uconnected (@switching_left _ G0) /\ uconnected (@switching_left _ G1).
Proof.
  move=> C. split => u v.
  - specialize (C (inl u) (inl v)) as [p _].
    destruct (union_edge_ll2 (valP p)) as [q Q _].
    by exists (Sub q Q).
  - specialize (C (inr u) (inr v)) as [p _].
    destruct (union_edge_ll3 (valP p)) as [q Q _].
    by exists (Sub q Q).
Qed.

Lemma union_edge_correct_weak2 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  correct_weak (union_edge_graph x y A) ->
  correct_weak G0 /\ correct_weak G1.
Proof.
  move=> [A2 C].
  destruct (union_edge_uacyclic2 A2), (union_edge_uconnected2 C).
  by split; split.
Qed.

Lemma union_edge_correct2 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  correct_weak (union_edge_graph x y A) ->
  correct G0 /\ correct G1.
Proof.
  move=> C. destruct (union_edge_correct_weak2 C).
  split; apply correct_from_weak; assumption || by apply fintype0.
Qed.


(** Adding a node below a vertex - subcase of doing a disjoint union and adding an edge *)
Definition add_concl_graph (G : base_graph) (x : G) (R : rule) (A : formula) : base_graph :=
  G ∔ R ∔ [inl x, (A, true), inr tt]. (* = union_edge_graph x (tt : unit_graph R) (A, true) *)

Lemma add_concl_correct (G : base_graph) (x : G) (R : rule) (F : formula) :
  correct_weak G -> correct (add_concl_graph x R F).
Proof.
  intros.
  apply union_edge_correct; trivial.
  - caseb.
  - apply unit_graph_correct_weak.
Qed.

Lemma rem_concl_correct (G : base_graph) (x : G) (R : rule) (F : formula) :
  correct_weak (add_concl_graph x R F) -> correct G.
Proof. intro C. by destruct (union_edge_correct2 C). Qed.

(** Adding a parr below 2 vertices *)
Definition add_parr_graph (G : base_graph) (vl vr : G) (Al Ar : formula) : base_graph :=
  G ∔ ⅋ ∔ [inl vl, (Al, true), inr tt] ∔ [inl vr, (Ar, false), inr tt].

Lemma add_parr_switching (G : base_graph) (vl vr : G) (Al Ar : formula) :
  (fun e : edge (add_parr_graph vl vr Al Ar) * bool => switching e.1) \o
  (fun x : edge G * bool => (Some (Some (inl x.1)), x.2)) =1
  (fun e => match e with
  | Some (inl a) => Some (inl (Some (Some (inl a))))
  | Some (inr a) => Some (inr (inl a))
  | None => None (* never happens *)
  end) \o (fun e => switching e.1).
Proof. intros (?, ?). unfold switching; cbn. case_if. Qed.

Lemma add_parr_switching_left (G : base_graph) (vl vr : G) (Al Ar : formula) :
  (fun e : edge (add_parr_graph vl vr Al Ar) * bool => switching_left e.1) \o
  (fun x : edge G * bool => (Some (Some (inl x.1)), x.2)) =1
  fun e => option_map (Some \o Some) (option_map inl (switching_left e.1)).
Proof. intros (?, ?). unfold switching_left; cbn. case_if. Qed.

Lemma add_parr_lrN (G : base_graph) (vl vr : G) (Al Ar : formula)
  {I : finType} (f : edge (add_parr_graph vl vr Al Ar) -> option I) p u :
  supath f (inl u) (inr tt) p ->
  forward None \in p \/ forward (Some None) \in p.
Proof.
  revert u; induction p as [ | (e, b) p Hp].
  { by move => ? /andP[/andP[/eqP ? _] _]. }
  rewrite /supath /= !in_cons.
  move => u /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]].
  destruct e as [[[e | []] | ] | ]; [ | destruct b; caseb | destruct b; caseb].
  enough (forward None \in p \/ forward (Some None) \in p) by caseb.
  destruct (utarget (Some (Some (inl e)) : edge (add_parr_graph vl vr Al Ar), b)) as [w | w] eqn:Hw;
  try by [].
  apply (Hp w). rewrite -Hw. splitb.
Qed.

Lemma add_parr_Nlr (G : base_graph) (vl vr : G) (Al Ar : formula) (p : upath)
  (u v : add_parr_graph vl vr Al Ar) :
  supath switching u v p ->
  forward None \in p \/ forward (Some None) \in p -> (exists u', u = inl u' /\ v = inr tt).
Proof.
  revert u v; induction p as [ | (e, b) p Hp].
  { by move => ? ? ? [? | ?]. }
  rewrite /supath map_cons cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]]
    [/orP[/andP[/eqP He /eqP Hb] | H] | /orP[/andP[/eqP He /eqP Hb] | H]].
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | []]; cbn.
    2:{ by exists vr. }
    contradict U0; apply /negP/negPn.
    assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
    { apply (@add_parr_lrN _ _ _ _ _ _ (@switching _ _) _ v), supath_revK. splitb. }
    rewrite 2!(upath_rev_in p) in Hin.
    destruct Hin as [Hin | Hin];
    by rewrite (map_f _ Hin).
  - assert (Hs : supath switching (utarget (e, b)) v p) by splitb.
    revert Hp => /(_ _ _ Hs) {Hs} Hp. destruct Hp as [u' [Hu ->]]; [caseb | ].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u. }
    contradict U0; apply /negP/negPn.
    assert (H' : forward None \in p) by by [].
    destruct e as [[[e | []] | ] | ]; try by [].
    all: apply (map_f (fun x => switching x.1) H').
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | []]; cbn.
    2:{ by exists vl. }
    contradict U0; apply /negP/negPn.
    assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
    { apply (@add_parr_lrN _ _ _ _ _ _ (@switching _ _) _ v), supath_revK. splitb. }
    rewrite 2!(upath_rev_in p) in Hin.
    destruct Hin as [Hin | Hin];
    by rewrite (map_f _ Hin).
  - assert (Hs : supath switching (utarget (e, b)) v p) by splitb.
    revert Hp => /(_ _ _ Hs) {Hs} Hp. destruct Hp as [u' [Hu ->]]; [caseb | ].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u. }
    contradict U0; apply /negP/negPn.
    assert (H' : forward (Some None) \in p) by by [].
    destruct e as [[[e | []] | ] | ]; try by [];
    apply (map_f (fun x => switching x.1) H').
Qed.
Lemma add_parr_Nlr2 (G : base_graph) (vl vr : G) (Al Ar : formula) (p : upath)
  (u v : add_parr_graph vl vr Al Ar) :
  supath switching_left u v p ->
  forward None \in p \/ forward (Some None) \in p -> (exists u', u = inl u' /\ v = inr tt).
Proof.
  revert u v; induction p as [ | (e, b) p Hp].
  { by move => ? ? ? [? | ?]. }
  rewrite /supath map_cons cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]]
    [/orP[/andP[/eqP He /eqP Hb] | H] | /orP[/andP[/eqP He /eqP Hb] | H]].
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | []]; cbn.
    2:{ by exists vr. }
    contradict U0; apply /negP/negPn.
    assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
    { apply (@add_parr_lrN _ _ _ _ _ _ (@switching_left _ _) _ v), supath_revK. splitb. }
    rewrite 2!(upath_rev_in p) in Hin.
    destruct Hin as [Hin | Hin];
    by rewrite // (map_f _ Hin).
  - assert (Hs : supath switching_left (utarget (e, b)) v p) by splitb.
    revert Hp => /(_ _ _ Hs) {Hs} Hp. destruct Hp as [u' [Hu ->]]; [caseb | ].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u. }
    contradict U0; apply /negP/negPn.
    assert (H' : forward None \in p) by by [].
    destruct e as [[[e | []] | ] | ]; try by [].
    have := (map_f (fun x => switching_left x.1) H'). cbn => N1c.
    contradict N1. by rewrite N1c.
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | []]; cbn.
    2:{ by exists vl. }
    contradict U0; apply /negP/negPn.
    assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
    { apply (@add_parr_lrN _ _ _ _ _ _ (@switching_left _ _) _ v), supath_revK. splitb. }
    rewrite 2!(upath_rev_in p) in Hin.
    destruct Hin as [Hin | Hin].
    + have := (map_f (fun x => switching_left x.1) Hin). cbn => N1c.
      contradict N1. by rewrite N1c.
    + by rewrite (map_f _ Hin).
  - assert (Hs : supath switching_left (utarget (e, b)) v p) by splitb.
    revert Hp => /(_ _ _ Hs) {Hs} Hp. destruct Hp as [u' [Hu ->]]; [caseb | ].
    rewrite_all Hu.
    destruct u as [u | u]; first by exists u.
    contradict U0; apply /negP/negPn.
    assert (H' : forward (Some None) \in p) by by [].
    destruct e as [[[e | []] | ] | ]; try by [].
    apply (map_f (fun x => switching_left x.1) H').
Qed.

Lemma add_parr_Nrl (G : base_graph) (vl vr : G) (Al Ar : formula) (p : upath)
  (u v : add_parr_graph vl vr Al Ar) :
  supath switching u v p -> backward None \in p \/ backward (Some None) \in p ->
  exists v', u = inr tt /\ v = inl v'.
Proof.
  intros P Hn.
  assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
  { rewrite !(upath_rev_in p). destruct Hn; caseb. }
  destruct (add_parr_Nlr (supath_revK P) Hin) as [u' [-> ->]].
  by exists u'.
Qed.
Lemma add_parr_Nrl2 (G : base_graph) (vl vr : G) (Al Ar : formula) (p : upath)
  (u v : add_parr_graph vl vr Al Ar) :
  supath switching_left u v p -> backward None \in p \/ backward (Some None) \in p ->
  exists v', u = inr tt /\ v = inl v'.
Proof.
  intros P Hn.
  assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
  { rewrite !(upath_rev_in p). destruct Hn; caseb. }
  destruct (add_parr_Nlr2 (supath_revK P) Hin) as [u' [-> ->]].
  by exists u'.
Qed.

Lemma add_parr_ll (G : base_graph) (vl vr : G) (Al Ar : formula) p u v :
  supath (switching (G := add_parr_graph vl vr Al Ar)) (inl u) (inl v) p ->
  { q : upath | supath switching u v q & p = [seq (Some (Some (inl x.1)), x.2) | x <- q] }.
Proof.
  intro P.
  assert ((forall (b : bool), (None, b) \notin p) /\ forall (b : bool), (Some None, b) \notin p) as [Hinn Hinsn].
  { split.
    all: apply /existsPn /negP; move => /existsP [[] ?];
      [destruct (add_parr_Nlr P) as [? [? ?]] | destruct (add_parr_Nrl P) as [? [? ?]]];
      caseb. }
  move: P => /andP[/andP[W U] N].
  revert u v W U N Hinn Hinsn. induction p as [ | [[[[e | []] | ] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - rewrite /= in_cons.
    move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hinn Hinsn.
    assert ((forall b, (None, b) \notin p) /\ forall b, (Some None, b) \notin p) as [Hinn' Hinsn'].
    { split; apply /existsPn /negP; move => /existsP [bf Hf].
      - specialize (Hinn bf). contradict Hinn. rewrite in_cons. apply /negP/negPn. caseb.
      - specialize (Hinsn bf). contradict Hinsn. rewrite in_cons. apply/negP/negPn. caseb. }
    specialize (IH _ _ W U1 N1 Hinn' Hinsn'). destruct IH as [p' P' ?]; subst p.
    exists ((e, b) :: p').
    + revert P'; unfold supath; cbn => /andP[/andP[W' U'] N'].
      splitb.
      * by revert w => /eqP.
      * clear - U0.
        rewrite -map_comp (eq_map (add_parr_switching vl vr Al Ar) p') in U0.
        assert (He := add_parr_switching vl vr Al Ar (forward e)). simpl in He.
        rewrite He map_comp (mem_map _ _ (switching (forward e).1)) // in U0.
        by move => [[? | ?] | ] [[? | ?] | ] // /eqP; cbn => ?; apply /eqP; cbn.
    + by rewrite map_cons.
  - move => ? ? ? ? ? ? /(_ b) Hf; clear - Hf.
    contradict Hf; apply /negP/negPn.
    rewrite in_cons. caseb.
  - move => ? ? ? ? ? /(_ b) Hf; clear - Hf.
    contradict Hf; apply /negP/negPn.
    rewrite in_cons. caseb.
Qed.
Lemma add_parr_ll2 (G : base_graph) (vl vr : G) (Al Ar : formula) p u v :
  supath (switching_left (G := add_parr_graph vl vr Al Ar)) (inl u) (inl v) p ->
  { q : upath | supath switching_left u v q & p = [seq (Some (Some (inl x.1)), x.2) | x <- q] }.
Proof.
  intro P.
  assert ((forall b, (None, b) \notin p) /\ forall b, (Some None, b) \notin p) as [Hinn Hinsn].
  { split.
    all: apply /existsPn /negP; move => /existsP [[] ?];
      [destruct (add_parr_Nlr2 P) as [? [? ?]] | destruct (add_parr_Nrl2 P) as [? [? ?]]];
      caseb. }
  revert P; move => /andP[/andP[W U] N].
  revert u v W U N Hinn Hinsn. induction p as [ | [[[[e | []] | ] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hinn Hinsn.
    assert ((forall b, (None, b) \notin p) /\ forall b, (Some None, b) \notin p) as [Hinn' Hinsn'].
    { split; apply /existsPn /negP; move => /existsP [bf Hf].
      - specialize (Hinn bf). contradict Hinn. rewrite in_cons. apply /negP/negPn. caseb.
      - specialize (Hinsn bf). contradict Hinsn. rewrite in_cons. apply /negP/negPn. caseb. }
    specialize (IH _ _ W U1 N1 Hinn' Hinsn'). destruct IH as [p' P' ?]; subst p.
    exists ((e, b) :: p').
    + revert P'; unfold supath; cbn => /andP[/andP[W' U'] N'].
      splitb.
      * by revert w => /eqP.
      * clear - U0. apply /mapP. move => [a Ain AE].
        contradict U0. apply /negP/negPn/mapP.
        exists ((Some (Some (inl a.1)), a.2)).
        { rewrite mem_map //. by move => [? ?] [? ?] /eqP; cbnb => /andP[/eqP--> /eqP-->]. }
        simpl.
        have := ((add_parr_switching_left vl vr Al Ar) a) => /= ->.
        have := ((add_parr_switching_left vl vr Al Ar) (forward e)) => /= ->.
        by rewrite AE.
      * clear -N0. revert N0.
        have := ((add_parr_switching_left vl vr Al Ar) (forward e)) => /= ->.
        by destruct (switching_left e).
    + by rewrite map_cons.
  - move => ? ? ? ? ? ? /(_ b) Hf; clear - Hf.
    contradict Hf; apply /negP/negPn.
    rewrite in_cons. caseb.
  - move => ? ? ? ? ? /(_ b) Hf; clear - Hf.
    contradict Hf; apply /negP/negPn.
    rewrite in_cons. caseb.
Qed.

Lemma add_parr_rr (G : base_graph) (vl vr : G) (Al Ar : formula) p :
  supath (switching (G := add_parr_graph vl vr Al Ar)) (inr tt) (inr tt) p ->
  p = nil.
Proof.
  destruct p as [ | (e, b) p]; trivial; unfold supath; cbn.
  move => /andP[/andP[/andP[/eqP w W] /andP[U0 U1]] /norP[/eqP N0 N1]].
  assert (P : supath (switching (G := add_parr_graph vl vr Al Ar)) (utarget (e, b)) (inr tt) p)
    by splitb.
  destruct e as [[[e | []] | ] | ], b; try by []; cbn in P.
  all: contradict U0; apply /negP/negPn.
  all: destruct (add_parr_lrN P) as [Hin | Hin].
  all: apply (map_f (fun e => switching e.1) Hin).
Qed.

Lemma add_parr_to_ll (G : base_graph) (vl vr : G) (Al Ar : formula) p u v :
  supath switching_left u v p ->
  supath (switching_left (G := add_parr_graph vl vr Al Ar)) (inl u) (inl v)
    [seq (Some (Some (inl x.1)), x.2) | x <- p].
Proof.
  revert u v; induction p as [ | (e, b) p IH]; trivial.
  unfold supath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : supath switching_left (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH; move => /andP[/andP[W' U'] N'].
  splitb.
  - rewrite -map_comp (eq_map (add_parr_switching_left _ _ _ _) p).
    assert (Hs : switching_left (Some (Some (inl e)) : edge (add_parr_graph vl vr Al Ar)) =
      option_map (Some \o Some) (option_map inl (switching_left e))).
    { change e with ((forward e).1). by rewrite -add_parr_switching_left. }
    rewrite Hs map_comp mem_map 1?map_comp 1?mem_map //.
    all: intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
  - assert (Hd := add_parr_switching_left vl vr Al Ar (forward e)).
    revert Hd. move => /eqP Hd. cbn in Hd. revert Hd. move => /eqP ->.
    by destruct (switching_left e).
Qed.
Lemma add_parr_to_ll2 (G : base_graph) (vl vr : G) (Al Ar : formula) p u v :
  supath switching u v p ->
  supath (switching (G := add_parr_graph vl vr Al Ar)) (inl u) (inl v)
    [seq (Some (Some (inl x.1)), x.2) | x <- p].
Proof.
  revert u v; induction p as [ | (e, b) p IH]; trivial.
  unfold supath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : supath switching (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH => /andP[/andP[W' U'] N']. splitb.
  rewrite -map_comp (eq_map (add_parr_switching _ _ _ _) p).
  assert (Hs : switching (Some (Some (inl e)) : edge (add_parr_graph vl vr Al Ar)) =
    ((fun e => match e with
    | Some (inl a) => Some (inl (Some (Some (inl a))))
    | Some (inr a) => Some (inr (inl a))
    | None => None (* never happens *)
    end) \o (fun e => switching e.1)) (forward e)).
    { change e with ((forward e).1). by rewrite -add_parr_switching. }
  rewrite Hs map_comp (mem_map _ _ (switching e)) //.
  by move => [[? | ?] | ] [[? | ?] | ] // /eqP; cbn => /eqP-->.
Qed. (* TODO use supath_cons, supath_rcons, supath_of_nil *)

Lemma add_parr_to_lr (G : base_graph) (vl vr : G) (Al Ar : formula) :
  uconnected (switching_left (G := G)) -> forall u, exists _ :
  Supath (switching_left (G := add_parr_graph vl vr Al Ar)) (inl u) (inr tt), true.
Proof.
  move => C u.
  destruct (C u vl) as [[p P] _].
  assert (Q := add_parr_to_ll vl vr Al Ar P).
  set q : @upath _ _ (add_parr_graph vl vr Al Ar) := [seq (Some (Some (inl x.1)), x.2) | x <- p].
  set qn : @upath _ _ (add_parr_graph vl vr Al Ar) := [:: forward (Some None)].
  assert (Qn : supath (switching_left (G := add_parr_graph vl vr Al Ar)) (inl vl) (inr tt) qn).
  { unfold supath; cbn. splitb. }
  set L : Supath _ _ _ := Sub q Q;
  set N : Supath _ _ _ := Sub qn Qn.
  assert (D : upath_disjoint switching_left (val L) (val N)).
  { apply /disjointP; intros [[[e | ] | ] | ]; cbn.
    all: try (move => _; by apply /negP).
    move => Hf _; revert Hf; apply /negP.
    rewrite /q -map_comp (eq_map (add_parr_switching_left vl vr Al Ar)).
    apply /mapP; intros [(?, ?) _ Heq]. contradict Heq.
    unfold switching_left; case_if. }
  by exists (supath_cat D).
Qed.

Lemma add_parr_to_rl (G : base_graph) (vl vr : G) (Al Ar : formula) :
  uconnected (switching_left (G := G)) -> forall v, exists _ :
  Supath (switching_left (G := add_parr_graph vl vr Al Ar)) (inr tt) (inl v), true.
Proof.
  intros C u.
  destruct (add_parr_to_lr vl vr Al Ar C u) as [p _].
  by exists (supath_rev p).
Qed.

Lemma add_parr_uacyclic (G : base_graph) (vl vr : G) (Al Ar : formula) :
  uacyclic (@switching _ G) -> uacyclic (@switching _ (add_parr_graph vl vr Al Ar)).
Proof.
  intros A [u | []] p; apply val_inj.
  - destruct (add_parr_ll (valP p)) as [q Q ->].
    move: A => /(_ u (Sub q Q)).
    by destruct q.
  - apply (add_parr_rr (valP p)).
Qed.

Lemma add_parr_uconnected (G : base_graph) (vl vr : G) (Al Ar : formula) :
  uconnected (@switching_left _ G) -> uconnected (@switching_left _ (add_parr_graph vl vr Al Ar)).
Proof.
  intros C [u | []] [v | []].
  - destruct (C u v) as [[p P] _].
    by exists (Sub _ (add_parr_to_ll _ _ _ _ P)).
  - by apply add_parr_to_lr.
  - by apply add_parr_to_rl.
  - by exists (supath_nil switching_left (inr tt : add_parr_graph vl vr Al Ar)).
Qed.

Lemma add_parr_correct_weak (G : base_graph) (vl vr : G) (Al Ar : formula) :
  correct_weak G -> correct_weak (add_parr_graph vl vr Al Ar).
Proof.
  intros [A C]. split.
  - by apply add_parr_uacyclic.
  - by apply add_parr_uconnected.
Qed.

Lemma add_parr_correct (G : base_graph) (vl vr : G) (Al Ar : formula) :
  correct_weak G -> correct (add_parr_graph vl vr Al Ar).
Proof.
  move => C.
  apply correct_from_weak.
  - rewrite card_sum card_unit. lia.
  - by apply add_parr_correct_weak.
Qed.

Lemma rem_parr_uacyclic (G : base_graph) (vl vr : G) (Al Ar : formula) :
  uacyclic (@switching _ (add_parr_graph vl vr Al Ar)) -> uacyclic (@switching _ G).
Proof.
  move=> A u [p P].
  apply val_inj.
  move: A => /(_ _ (Sub _ (add_parr_to_ll2 vl vr Al Ar P))).
  by destruct p.
Qed.

Lemma rem_parr_uconnected (G : base_graph) (vl vr : G) (Al Ar : formula) :
  uconnected (@switching_left _ (add_parr_graph vl vr Al Ar)) -> uconnected (@switching_left _ G).
Proof.
  intros C u v.
  destruct (C (inl u) (inl v)) as [[p P] _].
  destruct (add_parr_ll2 P) as [q Q _].
  by exists (Sub q Q).
Qed.

Lemma rem_parr_correct_weak (G : base_graph) (vl vr : G) (Al Ar : formula) :
  correct_weak (add_parr_graph vl vr Al Ar) -> correct_weak G.
Proof.
  intros [A C]. split.
  - by apply (rem_parr_uacyclic A).
  - by apply (rem_parr_uconnected C).
Qed.

Lemma rem_parr_correct (G : base_graph) (vl vr : G) (Al Ar : formula) :
  correct_weak (add_parr_graph vl vr Al Ar) -> correct G.
Proof.
  move => C.
  apply correct_from_weak.
  - by apply fintype0.
  - exact (rem_parr_correct_weak C).
Qed.

(** Put a vertex in the middle of an edge *)
Definition extend_edge_graph (G : base_graph) (e : edge G) (R : rule) (As At : formula) : base_graph :=
  {| vertex := option G;
     edge := option (edge G);
     endpoint b a := match a with
      | Some a => if (a == e) && ~~b then None else Some (endpoint b a)
      | None => if b then None else Some (source e)
      end; (* e still points towards the same target *)
     vlabel v := match v with Some v => vlabel v | None => R end;
     elabel a := match a with Some a => (if a == e then At else flabel a, llabel a) | None => (As, true) end;
  |}.
(* TODO vraiment besoin de At, on pourrait reprendre flabel e non ? *)

Lemma extend_edge_switching (G : base_graph) (e : edge G) (R : rule) (As At : formula) a f :
  (switching (Some a : edge (extend_edge_graph e R As At)) ==
   switching (Some f : edge (extend_edge_graph _ _ _ _))) =
  (switching a == switching f).
Proof.
  remember (switching a == switching f) as b eqn:Hb; symmetry in Hb.
  revert Hb; case: b; cbn; case_if.
Qed.

Lemma extend_edge_switching_left (G : base_graph) (e : edge G) (R : rule) (As At : formula) a f :
  (switching_left (Some a : edge (extend_edge_graph e R As At)) ==
   switching_left (Some f : edge (extend_edge_graph _ _ _ _))) =
  (switching_left a == switching_left f).
Proof.
  remember (switching_left a == switching_left f) as b eqn:Hb; symmetry in Hb.
  revert Hb; case: b.
  all: unfold switching_left; simpl; case_if.
  all: (by destruct (llabel a)) || by destruct (llabel f).
Qed.
(* TODO long runtime for these last 2 lemmas, because we have too
many goals as done cannot conclude when we have both b and ~~b as hypothesis,
we have to destruct b by hand to conclude *)

Lemma extend_edge_None (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) u v b :
  supath switching (Some u : extend_edge_graph e R As At) (Some v) ((None, b) :: p) ->
  p = (Some e, b) :: behead p.
Proof.
  unfold supath; cbn; destruct b => //= /andP[/andP[/andP[/eqP-? W] /andP[U _]] _]; subst u.
  destruct p as [ | ([a | ], b) p]; try by [].
  - destruct (eq_comparable a e); [subst a | ].
    + destruct b; trivial.
      contradict W; apply /negP; cbn. case_if.
    + contradict W; apply /negP; cbn. case_if.
  - contradict U; apply /negP/negPn; cbn.
    rewrite in_cons. caseb.
Qed.

Lemma extend_edge_e (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) u v b :
  supath switching (Some u : extend_edge_graph e R As At) (Some v) ((Some e, b) :: p) ->
  p = (None, b) :: behead p.
Proof.
  unfold supath; cbn; rewrite !eq_refl /=.
  destruct b => //= /andP[/andP[/andP[/eqP-? W] /andP[U _]] _]; subst u.
  destruct p as [ | ([a | ], b) p]; try by [].
  - destruct (eq_comparable a e); [subst a | ].
    + contradict U; apply /negP/negPn; cbn.
      rewrite in_cons. caseb.
    + contradict W; apply /negP; cbn. case_if.
  - destruct b; trivial.
    by contradict W.
Qed.

Fixpoint extend_edge_upath_fwd (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ G) {struct p} : @upath _ _ (extend_edge_graph e R As At) :=
  match p with
  | [::] => [::]
  | (a, b) :: q =>
    (if a == e then if b then (None, b) :: (Some e, b) :: nil else (Some e, b) :: (None, b) :: nil
    else (Some a, b) :: nil)
    ++ extend_edge_upath_fwd e R As At q
  end.

Lemma extend_edge_uwalk_fwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) p u v :
  uwalk (Some u : extend_edge_graph e R As At) (Some v) (extend_edge_upath_fwd _ _ _ _ p) = uwalk u v p.
Proof.
  revert u v; induction p as [ | (a, b) p IH] => u v //=.
  rewrite -IH {IH}.
  case_if; by destruct b.
Qed.

Lemma extend_edge_upath_fwd_in_Some (G : base_graph) (e : edge G) (R : rule) (As At : formula) p a b :
  (Some a, b) \in (extend_edge_upath_fwd e R As At p) = ((a, b) \in p).
Proof.
  induction p as [ | (f, c) p IH]; trivial; cbn.
  rewrite mem_cat in_cons IH {IH}. f_equal.
  case_if.
  all: rewrite !in_cons orb_false_r; by destruct b, c.
Qed.

Lemma extend_edge_upath_fwd_in_None (G : base_graph) (e : edge G) (R : rule) (As At : formula) p b :
  (None, b) \in (extend_edge_upath_fwd e R As At p) = ((e, b) \in p).
Proof.
  induction p as [ | (f, c) p IH]; trivial; cbn.
  rewrite mem_cat in_cons IH {IH}. f_equal.
  case_if.
  all: rewrite !in_cons orb_false_r ?eq_refl; cbn.
  1,2: by destruct c, b.
  by assert (e == f = false) as -> by by apply /eqP; apply nesym.
Qed.

Lemma extend_edge_upath_fwd_uniq (G : base_graph) (e : edge G) (R : rule) (As At : formula) p :
  uniq [seq switching e.1 | e <- (extend_edge_upath_fwd e R As At p)] = uniq [seq switching e.1 | e <- p].
Proof.
  induction p as [ | (a, b) p IH]; trivial; cbn.
  rewrite map_cat cat_uniq andb_assoc IH {IH}. f_equal.
  destruct (eq_comparable a e); [subst a | ].
  - rewrite !eq_refl.
    wlog: b / b = true.
    { move => /(_ true erefl) <-. destruct b; trivial.
      rewrite /= !in_cons !orb_false_r eq_sym. f_equal.
      by rewrite has_sym /= has_sym /= !negb_or !andb_assoc !andb_true_r andb_comm. }
    move => -> {b}.
    rewrite /= !in_cons has_sym orb_false_r.
    assert (Ht : switching (None : edge (extend_edge_graph e R As At)) !=
      switching (Some e : edge (extend_edge_graph e R As At))) by (cbn; case_if).
    rewrite Ht {Ht} /= orb_false_r !negb_or /=.
    assert (Ht : switching (Some e : edge (extend_edge_graph e R As At))
      \notin [seq switching e0.1 | e0 <- extend_edge_upath_fwd e R As At p] ->
      switching (None : edge (extend_edge_graph e R As At))
      \notin [seq switching e0.1 | e0 <- extend_edge_upath_fwd e R As At p]).
    { apply contra => /mapP [[[f | ] c] In Eq]; apply /mapP.
      - contradict Eq; apply /eqP; cbn; case_if.
      - rewrite extend_edge_upath_fwd_in_None -(extend_edge_upath_fwd_in_Some e R As At) in In.
        by exists (Some e, c). }
    rewrite (andb_idl Ht) {Ht}. f_equal.
    remember (switching e \in [seq switching e0.1 | e0 <- p]) as b eqn:Hb.
    revert Hb; case: b => Hb; symmetry in Hb; rewrite Hb; revert Hb.
    + move => /mapP [[f c] In Eq]; apply /mapP.
      rewrite -(extend_edge_upath_fwd_in_Some e R As At) in In.
      exists (Some f, c); trivial.
      by apply /eqP; rewrite extend_edge_switching; apply /eqP.
    + move => /negP /negP In; apply /negP /negP; revert In; apply contra.
      move => /mapP [[[f | ] c] In Eq]; apply /mapP.
      * rewrite extend_edge_upath_fwd_in_Some in In.
        exists (f, c); trivial; cbn.
        by apply /eqP; rewrite -(extend_edge_switching e R As At); apply /eqP.
      * rewrite extend_edge_upath_fwd_in_None in In.
        by exists (e, c).
  - assert (a == e = false) as -> by by apply /eqP.
    rewrite /= {b} has_sym /= orb_false_r. f_equal.
    remember (switching a \in [seq switching f.1 | f <- p]) as b eqn:Hb.
    revert Hb; case: b => Hb; symmetry in Hb; rewrite Hb; revert Hb.
    + move => /mapP [[f c] In Eq]; apply /mapP.
      rewrite -(extend_edge_upath_fwd_in_Some e R As At) in In.
      exists (Some f, c); trivial; cbn.
      by apply /eqP; rewrite extend_edge_switching; apply /eqP.
    + move => /negP /negP In; apply /negP /negP; revert In; apply contra.
      move => /mapP [[[f | ] c] In Eq]; apply /mapP.
      * rewrite extend_edge_upath_fwd_in_Some in In.
        exists (f, c); trivial; cbn.
        by apply /eqP; rewrite -(extend_edge_switching e R As At); apply /eqP.
      * rewrite extend_edge_upath_fwd_in_None in In.
        exists (e, c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; cbn; case_if.
Qed.

Lemma extend_edge_supath_fwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) p u v :
  supath switching (Some u : extend_edge_graph _ _ _ _) (Some v) (extend_edge_upath_fwd e R As At p) =
  supath switching u v p.
Proof. by rewrite /supath extend_edge_uwalk_fwd extend_edge_upath_fwd_uniq !switching_None. Qed.

Lemma extend_edge_upath_fwd_uniq_left (G : base_graph) (e : edge G) (R : rule) (As At : formula) p :
  uniq [seq switching_left e.1 | e <- (extend_edge_upath_fwd e R As At p)] = uniq [seq switching_left e.1 | e <- p].
Proof.
  induction p as [ | (a, b) p IH]; trivial; cbn.
  rewrite map_cat cat_uniq andb_assoc IH {IH}. f_equal.
  destruct (eq_comparable a e); [subst a | ].
  - rewrite !eq_refl.
    wlog: b / b = true.
    { move => /(_ true erefl) <-. destruct b; trivial.
      rewrite /= !in_cons !orb_false_r eq_sym. f_equal.
      by rewrite has_sym /= has_sym /= !negb_or !andb_assoc !andb_true_r andb_comm. }
    move => -> {b}.
    rewrite /= !in_cons has_sym orb_false_r.
    assert (Ht : switching_left (None : edge (extend_edge_graph e R As At)) !=
      switching_left (Some e : edge (extend_edge_graph e R As At))).
    { unfold switching_left; case_if; by destruct R. }
    rewrite Ht {Ht} /= orb_false_r !negb_or /=.
    assert (Ht : switching_left (Some e : edge (extend_edge_graph e R As At))
      \notin [seq switching_left f.1 | f <- extend_edge_upath_fwd e R As At p] ->
      switching_left (None : edge (extend_edge_graph e R As At))
      \notin [seq switching_left f.1 | f <- extend_edge_upath_fwd e R As At p]).
    { apply contra => /mapP [[[f | ] c] In Eq]; apply /mapP.
      - contradict Eq; apply /eqP; unfold switching_left; case_if; by destruct R.
      - rewrite extend_edge_upath_fwd_in_None -(extend_edge_upath_fwd_in_Some e R As At) in In.
        by exists (Some e, c). }
    rewrite (andb_idl Ht) {Ht}. f_equal.
    remember (switching_left e \in [seq switching_left f.1 | f <- p]) as b eqn:Hb.
    revert Hb; case: b => Hb; symmetry in Hb; rewrite Hb; revert Hb.
    + move => /mapP [[f c] In Eq]; apply /mapP.
      rewrite -(extend_edge_upath_fwd_in_Some e R As At) in In.
      exists (Some f, c); trivial.
      by apply /eqP; rewrite extend_edge_switching_left; apply /eqP.
    + move => /negP /negP In; apply /negP /negP; revert In; apply contra.
      move => /mapP [[[f | ] c] In Eq]; apply /mapP.
      * rewrite extend_edge_upath_fwd_in_Some in In.
        exists (f, c); trivial; cbn.
        by apply /eqP; rewrite -(extend_edge_switching_left e R As At); apply /eqP.
      * rewrite extend_edge_upath_fwd_in_None in In.
        by exists (e, c).
  - assert (a == e = false) as -> by by apply /eqP.
    rewrite /= {b} has_sym /= orb_false_r. f_equal.
    remember (switching_left a \in [seq switching_left f.1 | f <- p]) as b eqn:Hb.
    revert Hb; case: b => Hb; symmetry in Hb; rewrite Hb; revert Hb.
    + move => /mapP [[f c] In Eq]; apply /mapP.
      rewrite -(extend_edge_upath_fwd_in_Some e R As At) in In.
      exists (Some f, c); trivial; cbn.
      by apply /eqP; rewrite extend_edge_switching_left; apply /eqP.
    + move => /negP /negP In; apply /negP /negP; revert In; apply contra.
      move => /mapP [[[f | ] c] In Eq]; apply /mapP.
      * rewrite extend_edge_upath_fwd_in_Some in In.
        exists (f, c); trivial; cbn.
        by apply /eqP; rewrite -(extend_edge_switching_left e R As At); apply /eqP.
      * rewrite extend_edge_upath_fwd_in_None in In.
        exists (e, c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; unfold switching_left; case_if; by destruct R.
Qed.

Lemma extend_edge_upath_fwd_N (G : base_graph) (e : edge G) (R : rule) (As At : formula) p :
  None \notin [seq switching_left e0.1 | e0 <- extend_edge_upath_fwd e R As At p] =
  (None \notin [seq switching_left e0.1 | e0 <- p]).
Proof.
  induction p as [ | (a, b) p IH]; trivial; cbn.
  rewrite in_cons map_cat mem_cat !negb_or IH {IH}. f_equal.
  destruct (eq_comparable a e); [subst a | ].
  - rewrite !eq_refl.
    wlog: b / b = true.
    { move => /(_ true erefl) <-. destruct b; trivial.
      by rewrite !in_cons !orb_false_r orb_comm. }
    move => -> {b}.
    rewrite /= !in_cons !orb_false_r. f_equal.
    remember (None == switching_left e) as b eqn:Hb.
    revert Hb; case: b => Hb; symmetry in Hb; rewrite Hb; revert Hb.
    all: unfold switching_left; cbn; case_if.
    all: try by destruct (eqb_rule (vlabel (target e)) (⅋)).
    all: try by destruct (llabel e).
  - assert (a == e = false) as -> by by apply /eqP.
    rewrite /= {b} !in_cons in_nil /= orb_false_r.
    remember (None != (switching_left a)) as b eqn:Hb.
    revert Hb; case: b => Hb; symmetry in Hb; rewrite Hb; revert Hb.
    all: unfold switching_left; cbn; case_if.
    all: try by destruct (eqb_rule (vlabel (target a)) (⅋)).
    all: try by destruct (llabel a).
Qed.

Lemma extend_edge_supath_fwd_left (G : base_graph) (e : edge G) (R : rule) (As At : formula) p u v :
  supath switching_left (Some u : extend_edge_graph e R As At) (Some v) (extend_edge_upath_fwd _ _ _ _ p) =
  supath switching_left u v p.
Proof. by rewrite /supath extend_edge_uwalk_fwd extend_edge_upath_fwd_uniq_left // extend_edge_upath_fwd_N. Qed.

Fixpoint extend_edge_upath_bwd (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) : @upath _ _ G :=
  match p with
  | [::] => [::]
  | (Some a, b) :: q => (a, b) :: extend_edge_upath_bwd q
  | (None, b) :: q => extend_edge_upath_bwd q
  end.

Lemma extend_edge_uwalk_bwd (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) (u v : extend_edge_graph e R As At) :
  uwalk u v p ->
  uwalk (match u with | Some u => u | None => source e end)
  (match v with | Some v => v | None => source e end) (extend_edge_upath_bwd p).
Proof.
  revert u v; induction p as [ | ([a | ], b) p IH] => u v /=.
  { by move => /eqP-->. }
  all: move => /andP[/eqP-? W]; subst u.
  all: specialize (IH _ _ W); revert IH.
  all: destruct b, c; case_if; splitb.
Qed.

Lemma extend_edge_upath_bwd_in_Some (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) a b :
  (Some a, b) \in p = ((a, b) \in extend_edge_upath_bwd p).
Proof. induction p as [ | ([f | ], c) p IH]; by rewrite // !in_cons IH. Qed.

Lemma extend_edge_upath_bwd_uniq (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) :
  uniq [seq switching e.1 | e <- p] -> uniq [seq switching e.1 | e <- (extend_edge_upath_bwd p)].
Proof.
  induction p as [ | ([a | ], b) p IH]; trivial; cbn;
  move => /andP[In U]; splitb; try by apply IH.
  revert In; clear.
  apply contra => /mapP [[f c] In Eq]; apply /mapP.
  rewrite -extend_edge_upath_bwd_in_Some in In.
  exists (Some f, c); trivial.
  by apply /eqP; rewrite extend_edge_switching; apply /eqP.
Qed.

Lemma extend_edge_supath_bwd (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) (u v : extend_edge_graph e R As At) :
  supath switching u v p ->
  supath switching (match u with | Some u => u | None => source e end)
  (match v with | Some v => v | None => source e end) (extend_edge_upath_bwd p).
Proof.
  move => /andP[/andP[? ?] ?]. splitb.
  - by apply extend_edge_uwalk_bwd.
  - by apply extend_edge_upath_bwd_uniq.
  - by rewrite switching_None.
Qed.

Lemma extend_edge_upath_bwd_uniq_left (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) :
  uniq [seq switching_left e.1 | e <- p] -> uniq [seq switching_left e.1 | e <- (extend_edge_upath_bwd p)].
Proof.
  induction p as [ | ([a | ], b) p IH]; trivial; cbn => /andP[In U]; splitb; try by apply IH.
  revert In; clear.
  apply contra => /mapP [[f c] In Eq]; apply /mapP.
  rewrite -extend_edge_upath_bwd_in_Some in In.
  exists (Some f, c); trivial.
  by apply /eqP; rewrite extend_edge_switching_left; apply /eqP.
Qed.

Lemma extend_edge_upath_bwd_N (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) :
  None \notin [seq switching_left e0.1 | e0 <- p] ->
  None \notin [seq switching_left e0.1 | e0 <- extend_edge_upath_bwd p].
Proof.
  induction p as [ | ([a | ], b) p IH]; trivial; cbn.
  all: rewrite !in_cons !negb_or => /andP[In ?].
  all: splitb; try by apply IH.
  revert In; clear.
  unfold switching_left; cbn; case_if.
  all: assert (Hal : left (target a) = a) by by []; by rewrite_all Hal.
Qed.

Lemma extend_edge_supath_bwd_left (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) (u v : extend_edge_graph e R As At) :
  supath switching_left u v p ->
  supath switching_left (match u with | Some u => u | None => source e end)
  (match v with | Some v => v | None => source e end) (extend_edge_upath_bwd p).
Proof.
  move => /andP[/andP[? ?] ?]. splitb.
  - by apply extend_edge_uwalk_bwd.
  - by apply extend_edge_upath_bwd_uniq_left.
  - by rewrite extend_edge_upath_bwd_N.
Qed.


Lemma extend_edge_uacyclic_fwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  uacyclic (@switching _ (extend_edge_graph e R As At)) -> uacyclic (@switching _ G).
Proof.
  move=> A v [p P].
  apply val_inj. simpl.
  rewrite -(extend_edge_supath_fwd e R As At) in P.
  move: A => /(_ _ (Sub _ P))-A.
  inversion A as [[A']]. clear A.
  destruct p as [ | (a, b) p]; trivial.
  contradict A'. simpl. by repeat case: ifP.
Qed.

Lemma extend_edge_uconnected_bwd_rl (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  uconnected (@switching_left _ G) -> forall v,
  Supath switching_left (None : extend_edge_graph e R As At) (Some v).
Proof.
  intros C v.
  revert C => /(_ (source e) v)/sigW[[p P] _].
  rewrite -(extend_edge_supath_fwd_left e R As At) in P.
  revert P; rewrite /supath /= => /andP[/andP[W _] N].
  apply (uconnected_simpl (p := backward None :: extend_edge_upath_fwd e R As At p :
    @upath _ _ (extend_edge_graph e R As At))).
  - exact switching_left_sinj.
  - splitb.
  - splitb. by destruct R.
Qed.

Lemma extend_edge_uconnected_bwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  uconnected (@switching_left _ G) ->
  uconnected (@switching_left _ (extend_edge_graph e R As At)).
Proof.
  intros C [u | ] [v | ].
  - specialize (C u v). destruct C as [[p P] _].
    rewrite -(extend_edge_supath_fwd_left e R As At) in P.
    by exists (Sub _ P).
  - by exists (supath_rev (extend_edge_uconnected_bwd_rl e R As At C u)).
  - by exists (extend_edge_uconnected_bwd_rl e R As At C v).
  - by exists (supath_nil switching_left (None : extend_edge_graph _ _ _ _)).
Qed.

Lemma extend_edge_uacyclic_bwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  uacyclic (@switching _ G) -> uacyclic (@switching _ (extend_edge_graph e R As At)).
Proof.
  move=> A v [p P].
  apply val_inj. simpl.
  move: A => /(_ _ (Sub _ (extend_edge_supath_bwd P)))-A.
  inversion A as [[A']]. clear A.
  destruct v.
  - destruct p as [ | ([? | ], ?) ?]; try by [].
    contradict A'. simpl.
    by rewrite (extend_edge_None P).
  - destruct p as [ | ([? | ], []) [ | ([? | ], []) ?]]; try by [].
    by revert P; rewrite /supath !in_cons => /andP[/andP[_ /andP[/norP[/eqP ? _] _]] _].
Qed.

Lemma extend_edge_uconnected_fwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  uconnected (@switching_left _ (extend_edge_graph e R As At)) ->
  uconnected (@switching_left _ G).
Proof.
  intros C u v.
  specialize (C (Some u) (Some v)) as [[p P] _].
  apply extend_edge_supath_bwd_left in P.
  by exists (Sub _ P).
Qed.

Lemma extend_edge_correct_weak (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  correct_weak (extend_edge_graph e R As At) <-> correct_weak G.
Proof.
  split; intros [? ?]; split.
  - by apply (@extend_edge_uacyclic_fwd _ e R As At).
  - by apply (@extend_edge_uconnected_fwd _ e R As At).
  - by apply (@extend_edge_uacyclic_bwd _ e R As At).
  - by apply (@extend_edge_uconnected_bwd _ e R As At).
Qed.

Lemma extend_edge_correct_to (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  correct_weak G -> correct (extend_edge_graph e R As At).
Proof.
  move => C.
  apply correct_from_weak.
  - simpl. by rewrite card_option.
  - destruct (extend_edge_correct_weak e R As At) as [_ I]. by apply I.
Qed.

Lemma extend_edge_correct_from (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  correct_weak (extend_edge_graph e R As At) -> correct G.
Proof.
  move => C.
  apply correct_from_weak.
  - apply fintype0, (source e).
  - by apply extend_edge_correct_weak in C.
Qed.

(* TODO voir si on peut n'utiliser que fwd et pas bwd, grace aux = *)
(* lemma de ce type pour ne pas utiliser bwd
Lemma extend_edge_upath_bwd (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall p (u v : G),
  supath switching (inl u : extend_edge_graph_left e R As At) (inl v) p ->
  exists q, p = extend_edge_upath' _ _ _ _ q.
Proof.
  enough (H : forall n (p : @upath _ _ (extend_edge_graph e R As At)), size p = n -> forall u v,
    supath switching (inl u : extend_edge_graph_left e R As At) (inl v) p ->
  exists q, p = extend_edge_upath' _ _ _ _ q).
  { intro p. by apply (H (size p)). }
  intro n; induction n as [n Hn] using lt_wf_rect.
  intros [ | ([[[[a | []] | ] | ] A], b) p] ? u v; subst n; cbn in Hn.
  { by exists nil. }
  - rewrite /supath map_cons in_cons; cbn => /andP[/andP[/andP[/eqP ? W] /andP[In U]] N]; subst.
    assert (Htp : supath switching (inl (endpoint b a) : extend_edge_graph_left e R As At) (inl v) p)
      by splitb.
    assert (Hts : (size p < (size p).+1)%coq_nat) by lia.
    specialize (Hn (size p) Hts _ erefl _ _ Htp); clear Htp Hts.
    destruct Hn as [q ?]; subst p.
    exists ((a, b) :: q); cbn.
    case: {-}_ /boolP => [A' | /negPn A'].
    2:{ by contradict A'; apply /negP. }
    by replace A' with A by apply eq_irrelevance.
  - move => P. destruct b; try by [].
    assert (Hp := extend_edge_SN P). revert P.
    rewrite Hp {Hp} /supath map_cons in_cons; cbn; simpl; cbn.
    move => /andP[/andP[/andP[/eqP ? W] /andP[_ /andP[_ U]]] N]; subst.
    assert (Htp : supath switching (inl (target e) : extend_edge_graph_left e R As At) (inl v) (behead p))
      by splitb.
    assert (Hts : (size (behead p) < (size p).+1)%coq_nat) by (rewrite size_behead; lia).
    specialize (Hn (size (behead p)) Hts _ erefl _ _ Htp); clear Htp Hts.
    destruct Hn as [q Hq].
    exists (forward e :: q); cbn.
    case: {-}_ /boolP => [A' | A'].
    { by contradict A'; apply /negP /negPn; rewrite !in_set. }
    rewrite Hq.
    by replace A with (extend_edge_SomeNone e R As At) by apply eq_irrelevance.
  - move => P. destruct b; try by [].
    assert (Hp := extend_edge_N P). revert P.
    rewrite Hp {Hp} /supath map_cons in_cons; cbn; simpl; cbn.
    move => /andP[/andP[/andP[/eqP ? W] /andP[_ /andP[_ U]]] N]; subst.
    assert (Htp : supath switching (inl (source e) : extend_edge_graph_left e R As At) (inl v) (behead p))
      by splitb.
    assert (Hts : (size (behead p) < (size p).+1)%coq_nat) by (rewrite size_behead; lia).
    specialize (Hn (size (behead p)) Hts _ erefl _ _ Htp); clear Htp Hts.
    destruct Hn as [q Hq].
    exists (backward e :: q); cbn.
    case: {-}_ /boolP => [A' | A'].
    { by contradict A'; apply /negP /negPn; rewrite !in_set. }
    rewrite Hq.
    by replace A with (extend_edge_None e R As At) by apply eq_irrelevance.
Qed.
*)

(* TODO voir dans correction ce qui peut passer en correct = correct, et dont on a besoin pour sequent
-> add_parr et ce qui en decoule, voir si besoin de plus *)
(* TODO utiliser nb_uconnected = V - E plutôt que de faire les chemins en double ? *)
End Atoms.
