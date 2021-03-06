(* Basic operations respecting correctness *)

From Coq Require Import Bool.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop.

From Yalla Require Export graph_more mll_prelim mll_def mll_basic.

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


(** ** Invert an edge not touching a ⅋ *)
Definition invert_edge_graph {Lv Le : Type} (G : graph Lv Le) (e : edge G) : graph Lv Le :=
  {| vertex := vertex G;
     edge := edge G;
     endpoint b := fun a => if a == e then endpoint (~~b) a else endpoint b a;
     vlabel := @vlabel _ _ G;
     elabel := @elabel _ _ G;
  |}.

Fixpoint invert_edge_upath {Lv Le : Type} (G : graph Lv Le) (e : edge G) p :=
  match p with
  | [::] => [::]
  | (a, b) :: q => (if a == e then (a, ~~b) else (a, b)) :: invert_edge_upath e q
  end.

Lemma invert_edge_upath_inv {Lv Le : Type} (G : graph Lv Le) (e : edge G) :
  involutive (invert_edge_upath e).
Proof.
  intro p. induction p as [ | (a, b) p IH]; trivial; cbn.
  rewrite IH {IH}. case_if.
Qed.

Lemma invert_edge_fst {Lv Le : Type} {G : graph Lv Le} (e : edge G) :
  forall p, [seq e.1 | e <- invert_edge_upath e p] = [seq e.1 | e <- p].
Proof.
  intro p; induction p as [ | (?, ?) ? IH]; trivial; cbn.
  rewrite IH {IH}. case_if.
Qed.

Lemma invert_edge_in {Lv Le : Type} {G : graph Lv Le} (e : edge G) :
  forall p a b, ((a, b) \in invert_edge_upath e p) = ((a, if a == e then ~~b else b) \in p).
Proof.
  intro p; induction p as [ | (f, c) p IH] => a b; trivial; cbn.
  rewrite !in_cons IH {IH}. case_if.
  - f_equal. by destruct b, c.
  - by assert (a == e = false) as -> by by apply /eqP.
  - by assert (e == f = false) as -> by by apply /eqP; apply nesym.
Qed.

Lemma invert_edge_switching (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  @switching _ (invert_edge_graph e) =1 @switching _ G.
Proof.
  move => ? ? ?; unfold switching; cbn. case_if.
  all: by (assert (vlabel (source e) = ⅋) by by apply /eqP)
        || assert (vlabel (target e) = ⅋) by by apply /eqP.
Qed.

Lemma invert_edge_switching_left (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  @switching_left _ (invert_edge_graph e) =1 @switching_left _ G.
Proof.
  move => /eqP/negPf-Hs /eqP/negPf-Ht a; unfold switching_left.
  destruct (eq_comparable a e) as [? | A]; [subst a | ].
  - by rewrite /= eq_refl Hs Ht.
  - by revert A => /= /eqP/negPf-->.
Qed.

Lemma invert_edge_uwalk (G : base_graph) (e : edge G) :
  forall p (u v : G),
  @uwalk _ _ (invert_edge_graph e) u v (invert_edge_upath e p) = uwalk u v p.
Proof.
  intro p. induction p as [ | (a, b) p IH]; move => u v //=.
  rewrite IH {IH}. case_if.
Qed.

Lemma invert_edge_uniq (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  forall p, uniq [seq @switching _ (invert_edge_graph e) a.1 | a <- invert_edge_upath e p] =
  uniq [seq switching a.1 | a <- p].
Proof.
  intros ? ? p. induction p as [ | (a, b) p IH]; trivial; cbn.
  assert (Ht : [seq @switching _ (invert_edge_graph e) i.1 | i <- p] =
    [seq @switching _ G a.1 | a <- p])
    by by apply eq_map => ?; rewrite invert_edge_switching.
  by rewrite IH {IH} fun_if if_same /= map_comp invert_edge_fst -map_comp Ht invert_edge_switching.
Qed.

Lemma invert_edge_uniq_l (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  forall p, uniq [seq @switching_left _ (invert_edge_graph e) a.1 | a <- invert_edge_upath e p] =
  uniq [seq switching_left a.1 | a <- p].
Proof.
  intros ? ? p; induction p as [ | (?, ?) p IH]; trivial; cbn.
  assert (Ht : [seq @switching_left _ (invert_edge_graph e) i.1 | i <- p] =
    [seq @switching_left _ G a.1 | a <- p])
    by by apply eq_map => ?; rewrite invert_edge_switching_left.
  by rewrite IH {IH} fun_if if_same /= map_comp invert_edge_fst -map_comp Ht invert_edge_switching_left.
Qed.

Lemma invert_edge_None (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  forall p, (None \in [seq @switching_left _ (invert_edge_graph e) a.1 | a <- invert_edge_upath e p]) =
  (None \in [seq switching_left a.1 | a <- p]).
Proof.
  intros ? ? p; induction p as [ | (?, ?) ? IH]; trivial; cbn.
  by rewrite !in_cons IH {IH} fun_if if_same /= invert_edge_switching_left.
Qed.

Lemma invert_edge_supath (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  forall p (u v : G), supath switching u v p =
  supath (@switching _ (invert_edge_graph e)) u v (invert_edge_upath e p).
Proof. move => *. by rewrite /supath invert_edge_uwalk !switching_None invert_edge_uniq. Qed.

Lemma invert_edge_supath_l (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  forall p (u v : G), supath switching_left u v p =
  supath (@switching_left _ (invert_edge_graph e)) u v (invert_edge_upath e p).
Proof. move => *. by rewrite /supath invert_edge_uwalk invert_edge_uniq_l // invert_edge_None. Qed.

Lemma invert_edge_uacyclic (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  uacyclic (@switching _ (invert_edge_graph e)) <-> uacyclic (@switching _ G).
Proof.
  move => *; split => A ? [p P]; cbnb.
  1: rewrite (@invert_edge_supath _ e) // in P.
  2: rewrite -(invert_edge_upath_inv e p) -(@invert_edge_supath _ e) // in P.
  all: specialize (A _ {| upval := _ ; upvalK := P |}).
  all: revert A => /eqP; cbn => /eqP A.
  all: by rewrite -(invert_edge_upath_inv e p) A.
Qed.

Lemma invert_edge_uconnected (G : base_graph) (e : edge G) :
  vlabel (source e) <> ⅋ -> vlabel (target e) <> ⅋ ->
  uconnected (@switching_left _ (invert_edge_graph e)) <-> uconnected (@switching_left _ G).
Proof.
  move => *; split => C u v; cbnb.
  all: destruct (C u v) as [[p P] _].
  1: rewrite -(invert_edge_upath_inv e p) -(@invert_edge_supath_l _ e) // in P.
  2: rewrite (@invert_edge_supath_l _ e) // in P.
  all: by exists {| upval := _ ; upvalK := P |}.
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

Lemma union_edge_switching_0 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  (fun e : edge (union_edge_graph x y A) * bool => switching e.1) \o
  (fun x : edge G0 * bool => (Some (inl x.1), x.2)) =1
  (fun e => match e with
  | Some (inl a) => Some (inl (Some (inl a)))
  | Some (inr a) => Some (inr (inl a))
  | None => None (* never happens *)
  end) \o (fun e => switching e.1).
Proof. intros (?, ?). rewrite /switching /=. case_if. Qed.
Lemma union_edge_switching_1 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  (fun e : edge (union_edge_graph x y A) * bool => switching e.1) \o
  (fun x : edge G1 * bool => (Some (inr x.1), x.2)) =1
  (fun e => match e with
  | Some (inl a) => Some (inl (Some (inr a)))
  | Some (inr a) => Some (inr (inr a))
  | None => None (* never happens *)
  end) \o (fun e => switching e.1).
Proof. intros (?, ?). rewrite /switching /=. case_if. Qed.

Lemma union_edge_switching_left_0 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  (fun e : edge (union_edge_graph x y A) * bool => switching_left e.1) \o
  (fun x : edge G0 * bool => (Some (inl x.1), x.2)) =1
  fun e => option_map Some (option_map inl (switching_left e.1)).
Proof. intros (?, ?). unfold switching_left; cbn. case_if. Qed.
Lemma union_edge_switching_left_1 (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  (fun e : edge (union_edge_graph x y A) * bool => switching_left e.1) \o
  (fun x : edge G1 * bool => (Some (inr x.1), x.2)) =1
  fun e => option_map Some (option_map inr (switching_left e.1)).
Proof. intros (?, ?). unfold switching_left; cbn. case_if. Qed.

Lemma union_edge_lrN (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  forall p u v, supath (switching (G := union_edge_graph x y A)) (inl u) (inr v) p ->
  forward None \in p.
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => u v /andP[/andP[/eqP ? _] _]. }
  rewrite /supath cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]].
  destruct e as [[e | e] | ]; [ | by destruct b | by destruct b].
  enough (forward None \in p) by caseb.
  destruct (utarget (Some (inl e) : edge (union_edge_graph x y A), b)) as [w | ] eqn:Hw; try by [].
  apply (Hp w v).
  splitb. by rewrite -Hw.
Qed.

Lemma union_edge_Nlr (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  forall (p : upath) (u v : union_edge_graph x y A), supath switching u v p ->
  forward None \in p -> (exists u' v', u = inl u' /\ v = inr v').
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => *. }
  rewrite /supath cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]]
    /orP[/andP[/eqP He /eqP Hb] | H].
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | v]; cbn.
    2:{ by exists x, v. }
    contradict U0; apply /negP/negPn.
    assert (Hin : forward None \in upath_rev p).
    { apply (@union_edge_lrN _ _ _ _ _ _ v y), supath_revK. splitb. }
    rewrite (upath_rev_in p) in Hin.
    by rewrite (map_f _ Hin).
  - assert (Hs : supath switching (utarget (e, b)) v p) by splitb.
    revert Hp => /(_ _ _ Hs H) {Hs} [u' [v' [Hu ->]]].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u, v'. }
    contradict U0; apply /negP/negPn.
    assert (e = None) as -> by by destruct e as [[e | e] | ].
    assert (H' : forward None \in p) by by [].
    apply (map_f (fun x => switching x.1) H').
Qed.

Lemma union_edge_Nrl (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  forall (p : upath) (u v : union_edge_graph x y A), supath switching u v p ->
  backward None \in p -> exists u' v', u = inr u' /\ v = inl v'.
Proof.
  intros p ? ? P ?.
  assert (Hin : forward None \in upath_rev p) by by rewrite (upath_rev_in p).
  destruct (union_edge_Nlr (supath_revK P) Hin) as [u' [v' [-> ->]]].
  by exists v', u'.
Qed.

Lemma union_edge_ll (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  forall p u v, supath (switching (G := union_edge_graph x y A)) (inl u) (inl v) p ->
  { q : upath | supath switching u v q & p = [seq (Some (inl x.1), x.2) | x <- q] }.
Proof.
  intros p u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn/negP => /existsP [[] N].
    - by destruct (union_edge_Nlr P N) as [? [? [? ?]]].
    - by destruct (union_edge_Nrl P N) as [? [? [? ?]]]. }
  revert P => /andP[/andP[W U] N].
  revert u v W U N Hin. induction p as [ | [[[e | e] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hin.
    assert (Ht : forall b, (None, b) \notin p).
    { apply /existsPn/negP => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP/negPn. caseb. }
    specialize (IH _ _ W U1 N1 Ht); destruct IH as [p' P' ?]; subst p.
    exists ((e, b) :: p').
    + revert P'; unfold supath; cbn => /andP[/andP[W' U'] N'].
      splitb.
      * by revert w => /eqP; cbn.
      * clear - U0.
        rewrite -map_comp (eq_map (union_edge_switching_0 x y A) p') map_comp in U0.
        assert (He := union_edge_switching_0 x y A (forward e)). simpl in He.
        rewrite He (mem_map _ _ (switching (forward e).1)) // in U0.
        by move => [[? | ?] | ] [[? | ?] | ] // /eqP; cbn => ?; apply /eqP; cbn.
    + by rewrite map_cons.
  - by [].
  - move => ? ? ? ? ? /(_ b) Hf; clear - Hf.
    contradict Hf; apply /negP/negPn.
    rewrite in_cons. caseb.
Qed.

Lemma union_edge_rr (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  forall p u v, supath (switching (G := union_edge_graph x y A)) (inr u) (inr v) p ->
  { p' : upath | supath switching u v p' & p = [seq (Some (inr x.1), x.2) | x <- p'] }.
Proof.
  intros p u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn/negP => /existsP [[] N].
    - by destruct (union_edge_Nlr P N) as [? [? [? ?]]].
    - by destruct (union_edge_Nrl P N) as [? [? [? ?]]]. }
  revert P => /andP[/andP[W U] N].
  revert u v W U N Hin. induction p as [ | [[[e | e] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - by [].
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hin.
    assert (Ht : forall b, (None, b) \notin p).
    { apply /existsPn/negP => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP/negPn. caseb. }
    specialize (IH _ _ W U1 N1 Ht); destruct IH as [p' P' ?]; subst p.
    exists ((e, b) :: p').
    + revert P'; unfold supath; cbn => /andP[/andP[W' U'] N'].
      splitb.
      * by revert w => /eqP; cbn.
      * clear - U0.
        rewrite -map_comp (eq_map (union_edge_switching_1 x y A) p') in U0.
        assert (He := union_edge_switching_1 x y A (forward e)). simpl in He.
        rewrite He map_comp (mem_map _ _ (switching (forward e).1)) // in U0.
        by move => [[? | ?] | ] [[? | ?] | ] // /eqP; cbn => ?; apply /eqP; cbn.
    + by rewrite map_cons.
  - move => ? ? ? ? ? /(_ b) Hf; clear - Hf.
    contradict Hf; apply /negP/negPn.
    rewrite in_cons. caseb.
Qed.

Lemma union_edge_to_ll (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  forall p u v, supath switching_left u v p ->
  supath (switching_left (G := union_edge_graph x y A)) (inl u) (inl v) [seq (Some (inl x.1), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold supath; cbn => u v /andP[/andP[/andP[/eqP ? W1] /andP[U0 U1]] /norP[N0 N1]]; subst u.
  assert (P : supath switching_left (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH => /andP[/andP[W' U'] N'].
  splitb.
  - rewrite -map_comp (eq_map (union_edge_switching_left_0 x y A) p).
    assert (switching_left (Some (inl e) : edge (union_edge_graph x y A)) =
      option_map Some (option_map inl (switching_left e))) as ->.
    { replace e with ((forward e).1) by trivial. by rewrite -union_edge_switching_left_0. }
    rewrite map_comp mem_map 1?map_comp 1?mem_map //.
    all: by move => [? | ] [? | ] /eqP-?; apply /eqP.
  - assert (Hd := union_edge_switching_left_0 x y A (forward e)).
    revert Hd => /eqP; cbn => /eqP ->.
    by destruct (switching_left e).
Qed.

Lemma union_edge_to_rr (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  forall p u v, supath switching_left u v p ->
  supath (switching_left (G := union_edge_graph x y A)) (inr u) (inr v) [seq (Some (inr x.1), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold supath; cbn => u v /andP[/andP[/andP[/eqP ? W1] /andP[U0 U1]] /norP[N0 N1]]; subst u.
  assert (P : supath switching_left (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH => /andP[/andP[W' U'] N'].
  splitb.
  - rewrite -map_comp (eq_map (union_edge_switching_left_1 x y A) p).
    assert (switching_left (Some (inr e) : edge (union_edge_graph x y A)) =
      option_map Some (option_map inr (switching_left e))) as ->.
    { replace e with ((forward e).1) by trivial. by rewrite -union_edge_switching_left_1. }
    rewrite map_comp mem_map 1?map_comp 1?mem_map //.
    all: by move => [? | ] [? | ] /eqP-?; apply /eqP.
  - assert (Hd := union_edge_switching_left_1 x y A (forward e)).
    revert Hd => /eqP; cbn => /eqP ->.
    by destruct (switching_left e).
Qed.

Lemma union_edge_to_lr (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  A.2 \/ vlabel y <> ⅋ ->
  uconnected (switching_left (G := G0)) -> uconnected (switching_left (G := G1)) ->
  forall u v, exists _ :
  Supath (switching_left (G := union_edge_graph x y A)) (inl u) (inr v), true.
Proof.
  move => NP C0 C1 u v.
  destruct (C0 u x) as [[p0 P0] _].
  assert (Q0 := union_edge_to_ll x y A P0).
  set q0 : @upath _ _ (union_edge_graph x y A) := [seq (Some (inl x.1), x.2) | x <- p0].
  destruct (C1 y v) as [[p1 P1] _].
  assert (Q1 := union_edge_to_rr x y A P1).
  set q1 : @upath _ _ (union_edge_graph x y A) := [seq (Some (inr x.1), x.2) | x <- p1].
  set qn : @upath _ _ (union_edge_graph x y A) := [:: forward None].
  assert (Qn : supath (switching_left (G := union_edge_graph x y A)) (inl x) (inr y) qn).
  { unfold supath; cbn. repeat (apply /andP; split); trivial.
    rewrite mem_seq1 /switching_left; cbn. case_if. destruct NP as [NP | NP]; contradict NP; by [apply /negP | apply /eqP]. }
  set L := {| upval := q0 ; upvalK := Q0 |};
  set R := {| upval := q1 ; upvalK := Q1 |};
  set N := {| upval := qn ; upvalK := Qn |}.
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
  assert (upath_disjoint switching_left N L /\ upath_disjoint switching_left N R) as [Dl Dr].
  { split; apply /disjointP; move => [[e | ] | ]; cbn.
    all: try (move => _; by apply /negP).
    all: move => Hf _; revert Hf; rewrite mem_seq1 /switching_left; cbn.
    all: case_if. }
  rewrite /upath_disjoint disjoint_sym in Dl.
  assert (D : upath_disjoint switching_left (supath_cat Dl) R).
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
  forall u v, exists _ : Supath (switching_left (G := union_edge_graph x y A)) (inr u) (inl v), true.
Proof.
  intros NP C0 C1 u v.
  destruct (union_edge_to_lr x NP C0 C1 v u) as [p _].
  by exists (supath_rev p).
Qed.

Lemma union_edge_uacyclic (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  uacyclic (@switching _ G0) -> uacyclic (@switching _ G1) ->
  uacyclic (@switching _ (union_edge_graph x y A)).
Proof.
  intros A0 A1 [u | u] p; cbnb.
  - destruct (union_edge_ll (upvalK p)) as [q Q Heq].
    rewrite Heq.
    enough (q = nil) as -> by trivial.
    assert (Hf := A0 _ {| upval := q ; upvalK := Q |}).
    by revert Hf => /eqP; cbn => /eqP ->.
  - destruct (union_edge_rr (upvalK p)) as [q Q Heq].
    rewrite Heq.
    enough (q = nil) as -> by trivial.
    assert (Hf := A1 _ {| upval := q ; upvalK := Q |}).
    by revert Hf => /eqP; cbn => /eqP ->.
Qed.

Lemma union_edge_uconnected (G0 G1 : base_graph) (x : G0) (y : G1) (A : formula * bool) :
  A.2 \/ vlabel y <> ⅋ ->
  uconnected (@switching_left _ G0) -> uconnected (@switching_left _ G1) ->
  uconnected (@switching_left _ (union_edge_graph x y A)).
Proof.
  intros NP C0 C1 [u | u] [v | v].
    + destruct (C0 u v) as [[p P] _].
      by exists {| upval := _ ; upvalK := (union_edge_to_ll x y A P) |}.
    + by apply union_edge_to_lr.
    + by apply union_edge_to_rl.
    + destruct (C1 u v) as [[p P] _].
      by exists {| upval := _ ; upvalK := (union_edge_to_rr x y A P) |}.
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


(** Adding a node below a vertex *)
Definition add_concl_graph (G : base_graph) (x : G) (R : rule) (A : formula) : base_graph :=
  G ∔ R ∔ [inl x, (A, true), inr tt].

Lemma add_concl_switching (G : base_graph) (x : G) (R : rule) (A : formula) :
  (fun e : edge (add_concl_graph x R A) * bool => switching e.1) \o
  (fun e : edge G * bool => (Some (inl e.1), e.2)) =1
  (fun e => match e with
  | Some (inl a) => Some (inl (Some (inl a)))
  | Some (inr a) => Some (inr (inl a))
  | None => None (* never happens *)
  end) \o (fun e => switching e.1).
Proof. intros (?, ?). rewrite /switching /=. case_if. Qed.

Lemma add_concl_switching_left (G : base_graph) (x : G) (R : rule) (A : formula) :
  (fun e : edge (add_concl_graph x R A) * bool => switching_left e.1) \o
  (fun e : edge G * bool => (Some (inl e.1), e.2)) =1
  fun e => option_map Some (option_map inl (switching_left e.1)).
Proof. intros (?, ?). rewrite /switching_left /=. case_if. Qed.

Lemma add_concl_lrN (G : base_graph) (x : G) (R : rule) (A : formula)
  {I : eqType} (f : edge (add_concl_graph x R A) -> option I) :
  forall p u, supath f (inl u) (inr tt) p ->
  forward None \in p.
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => u /andP[/andP[/eqP ? _] _]. }
  rewrite /supath cons_uniq in_cons.
  move => u /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]].
  destruct e as [[e | []] | ]; [ | by destruct b].
  enough (forward None \in p) by caseb.
  destruct (utarget (Some (inl e) : edge (add_concl_graph x R A), b)) as [w | w] eqn:Hw; try by [].
  apply (Hp w). rewrite -Hw. splitb.
Qed.

Lemma add_concl_Nlr (G : base_graph) (x : G) (R : rule) (A : formula)
  {I : finType} (f : edge (add_concl_graph x R A) -> option I) :
  forall (p : upath) (u v : add_concl_graph x R A), supath f u v p ->
  forward None \in p -> (exists u', u = inl u' /\ v = inr tt).
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => *. }
  rewrite /supath cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]] /orP[/andP[/eqP He /eqP Hb] | H].
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | []]; cbn.
    2:{ by exists x. }
    contradict U0; apply /negP/negPn.
    assert (Hin : forward None \in upath_rev p).
    { apply (@add_concl_lrN _ _ _ _ _ f _ v), supath_revK. splitb. }
    rewrite (upath_rev_in p) in Hin.
    by rewrite (map_f _ Hin).
  - assert (Hs : supath f (utarget (e, b)) v p) by splitb.
    revert Hp => /(_ _ _ Hs H) {Hs} [u' [Hu ->]].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u. }
    contradict U0; apply /negP/negPn.
    assert (e = None) as -> by by destruct e as [[? | ?] | ].
    assert (H' : forward None \in p) by by [].
    apply (map_f (fun x => f x.1) H').
Qed.

Lemma add_concl_Nrl (G : base_graph) (x : G) (R : rule) (A : formula)
  {I : finType} (f : edge (add_concl_graph x R A) -> option I) :
  forall (p : upath) (u v : add_concl_graph x R A), supath f u v p ->
  backward None \in p -> exists v', u = inr tt /\ v = inl v'.
Proof.
  intros p ? ? P ?.
  assert (Hin : forward None \in upath_rev p) by by rewrite (upath_rev_in p).
  destruct (add_concl_Nlr (supath_revK P) Hin) as [u' [-> ->]].
  by exists u'.
Qed.

Lemma add_concl_ll (G : base_graph) (x : G) (R : rule) (A : formula) :
  forall p u v, supath (switching (G := add_concl_graph x R A)) (inl u) (inl v) p ->
  { q : upath | supath switching u v q & p = [seq (Some (inl x.1), x.2) | x <- q] }.
Proof.
  intros p u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn /negP => /existsP [[] ?];
    [destruct (add_concl_Nlr P) as [? [? ?]] | destruct (add_concl_Nrl P) as [? [? ?]]];
    caseb. }
  revert P => /andP[/andP[W U] N].
  revert u v W U N Hin. induction p as [ | [[[e | []] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hin.
    assert (Hin' : forall b, (None, b) \notin p).
    { apply /existsPn /negP => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP/negPn; caseb. }
    specialize (IH _ _ W U1 N1 Hin). destruct IH as [p' P' ?]; subst p.
    exists ((e, b) :: p').
    + revert P'; unfold supath; cbn => /andP[/andP[W' U'] N'].
      splitb.
      * by revert w => /eqP.
      * clear - U0.
        rewrite -map_comp (eq_map (add_concl_switching x R A) p') map_comp in U0.
        assert (He := add_concl_switching x R A (forward e)). simpl in He.
        rewrite He (mem_map _ _ (switching (forward e).1)) // in U0.
        by move => [[? | ?] | ] [[? | ?] | ] // /eqP; cbn => ?; apply /eqP; cbn.
    + by rewrite map_cons.
  - move => ? ? ? ? ? /(_ b) Hf; clear - Hf.
    contradict Hf; apply /negP/negPn.
    rewrite in_cons. caseb.
Qed.

Lemma add_concl_rr (G : base_graph) (x : G) (R : rule) (A : formula) :
  forall p, supath (switching (G := add_concl_graph x R A)) (inr tt) (inr tt) p ->
  p = nil.
Proof.
  intro p; destruct p as [ | (e, b) p]; trivial; unfold supath; cbn.
  move => /andP[/andP[/andP[/eqP w W] /andP[U0 U1]] /norP[/eqP N0 N1]].
  assert (P : supath (switching (G := add_concl_graph x R A)) (utarget (e, b)) (inr tt) p)
    by splitb.
  destruct e as [[e | []] | ], b; try by []; cbn in P.
  contradict U0; apply /negP/negPn.
  apply (map_f (fun e => switching e.1) (add_concl_lrN P)).
Qed.

Lemma add_concl_to_ll (G : base_graph) (x : G) (R : rule) (A : formula) :
  forall p u v, supath switching_left u v p ->
  supath (switching_left (G := add_concl_graph x R A)) (inl u) (inl v)
    [seq (Some (inl x.1), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold supath; cbn => u v /andP[/andP[/andP[/eqP ? W1] /andP[U0 U1]] /norP[N0 N1]]; subst u.
  assert (P : supath switching_left (endpoint b e) v p) by splitb.
  revert IH => /(_ _ _ P) /andP[/andP[W' U'] N'].
  splitb.
  + rewrite -map_comp (eq_map (add_concl_switching_left _ _ _) p).
    assert (Hs : switching_left (Some (inl e) : edge (add_concl_graph x R A)) =
      option_map Some (option_map inl (switching_left e))).
    { replace e with ((forward e).1) by trivial. by rewrite -add_concl_switching_left. }
    rewrite Hs map_comp mem_map 1?map_comp 1?mem_map //.
    all: by move => [? | ] [? | ] /eqP H; apply /eqP.
  + assert (Hd := add_concl_switching_left x R A (forward e)).
    revert Hd => /eqP; cbn => /eqP ->.
    by destruct (switching_left e).
Qed.

Lemma add_concl_to_lr (G : base_graph) (x : G) (R : rule) (A : formula) :
  uconnected (switching_left (G := G)) -> forall u, exists _ :
  Supath (switching_left (G := add_concl_graph x R A)) (inl u) (inr tt), true.
Proof.
  move => C u.
  destruct (C u x) as [[p P] _].
  assert (Q := add_concl_to_ll x R A P).
  set q : @upath _ _ (add_concl_graph x R A) := [seq (Some (inl x.1), x.2) | x <- p].
  set qn : @upath _ _ (add_concl_graph x R A) := [:: forward None].
  assert (Qn : supath (switching_left (G := add_concl_graph x R A)) (inl x) (inr tt) qn).
  { unfold supath; cbn. repeat (apply /andP; split); trivial.
    rewrite in_cons in_nil. apply /norP; split; trivial.
    unfold switching_left. case_if. }
  set L := {| upval := q ; upvalK := Q |};
  set N := {| upval := qn ; upvalK := Qn |}.
  assert (D : upath_disjoint switching_left L N).
  { apply /disjointP; move => [[[e | []] | ] | ]; cbn.
    - move => _; apply /negP /norP; split; trivial.
      unfold switching_left. case_if.
    - move => Hf _; revert Hf; apply /negP.
      rewrite /q -map_comp (eq_map (add_concl_switching_left _ _ _)).
      apply /mapP; move => [[? ?] _ Heq]. contradict Heq.
      unfold switching_left; case_if.
    - move => _; apply /negP /norP; split; trivial.
      unfold switching_left. case_if. }
  by exists (supath_cat D).
Qed.

Lemma add_concl_to_rl (G : base_graph) (x : G) (R : rule) (A : formula) :
  uconnected (switching_left (G := G)) -> forall v, exists _ :
  Supath (switching_left (G := add_concl_graph x R A)) (inr tt) (inl v), true.
Proof.
  intros C u.
  destruct (add_concl_to_lr x R A C u) as [p _].
  by exists (supath_rev p).
Qed.

Lemma add_concl_uacyclic (G : base_graph) (x : G) (R : rule) (F : formula) :
  uacyclic (@switching _ G) -> uacyclic (@switching _ (add_concl_graph x R F)).
Proof.
  intros A [u | []] p; cbnb.
  - destruct (add_concl_ll (upvalK p)) as [q Q Heq].
    rewrite Heq.
    enough (q = nil) as -> by trivial.
    assert (Hf := A _ {| upval := _ ; upvalK := Q |}).
    by revert Hf => /eqP; cbn => /eqP ->.
  - apply (add_concl_rr (upvalK p)).
Qed.

Lemma add_concl_uconnected (G : base_graph) (x : G) (R : rule) (F : formula) :
  uconnected (@switching_left _ G) -> uconnected (@switching_left _ (add_concl_graph x R F)).
Proof.
  intros C [u | []] [v | []].
  - destruct (C u v) as [[p P] _].
    by exists {| upval := _ ; upvalK := (add_concl_to_ll _ _ _ P) |}.
  - by apply add_concl_to_lr.
  - by apply add_concl_to_rl.
  - by exists (supath_nil _ _).
Qed.

Lemma add_concl_correct_weak (G : base_graph) (x : G) (R : rule) (F : formula) :
  correct_weak G -> correct_weak (add_concl_graph x R F).
Proof.
  intros []. split.
  - by apply add_concl_uacyclic.
  - by apply add_concl_uconnected.
Qed.

Lemma add_concl_correct (G : base_graph) (x : G) (R : rule) (F : formula) :
  correct_weak G -> correct (add_concl_graph x R F).
Proof.
  move => C.
  apply correct_from_weak.
  - simpl. rewrite card_sum card_unit. lia.
  - by apply (add_concl_correct_weak x R F).
Qed.

Lemma rem_concl_to_ll (G : base_graph) (x : G) (R : rule) (A : formula) :
  forall p u v, supath switching u v p ->
  supath (switching (G := add_concl_graph x R A)) (inl u) (inl v)
    [seq (Some (inl x.1), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold supath; cbn => u v /andP[/andP[/andP[/eqP ? W1] /andP[U0 U1]] /norP[N0 N1]]; subst u.
  assert (P : supath switching (endpoint b e) v p) by splitb.
  revert IH => /(_ _ _ P) /andP[/andP[W' U'] N'].
  splitb.
  rewrite -map_comp (eq_map (add_concl_switching _ _ _) _).
  assert (He := add_concl_switching x R A (forward e)). simpl in He.
  rewrite He map_comp (mem_map _ _ (switching (forward e).1)) //.
  by move => [[? | ?] | ] [[? | ?] | ] // /eqP; cbn => ?; apply /eqP; cbn.
Qed.

Lemma rem_concl_ll (G : base_graph) (x : G) (R : rule) (A : formula) :
  forall p u v, supath (switching_left (G := add_concl_graph x R A)) (inl u) (inl v) p ->
  { q : upath | supath switching_left u v q & p = [seq (Some (inl x.1), x.2) | x <- q] }.
Proof.
  intros p u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn /negP => /existsP [[] ?];
    [destruct (add_concl_Nlr P) as [? [? ?]] | destruct (add_concl_Nrl P) as [? [? ?]]];
    caseb. }
  revert P => /andP[/andP[W U] N].
  revert u v W U N Hin. induction p as [ | [[[e | []] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hin.
    assert (Hin' : forall b, (None, b) \notin p).
    { apply /existsPn /negP => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP/negPn; caseb. }
    specialize (IH _ _ W U1 N1 Hin). destruct IH as [p' P' ?]; subst p.
    exists ((e, b) :: p').
    + revert P'; unfold supath; cbn => /andP[/andP[W' U'] N'].
      splitb.
      * by revert w => /eqP.
      * clear - U0.
        rewrite -map_comp (eq_map (add_concl_switching_left x R A) p') in U0.
        assert (He : switching_left (Some (inl e) : edge (add_concl_graph x R A)) =
          option_map Some (option_map inl (switching_left e))).
        { replace e with ((forward e).1) by trivial. by rewrite -add_concl_switching_left. }
        rewrite He 2?map_comp 2?mem_map // in U0.
        all: by move => [? | ] [? | ] /eqP ?; apply /eqP.
      * assert (Hr : switching_left (Some (inl e) : edge (add_concl_graph x R A)) =
          ((fun f : edge (add_concl_graph x R A) * _ => switching_left f.1) \o
          (fun f => (Some (inl f.1), f.2))) (forward e)) by by [].
        rewrite Hr add_concl_switching_left /= in N0.
        by destruct (switching_left e).
    + by rewrite map_cons.
  - move => ? ? ? ? ? /(_ b) Hf; clear - Hf.
    contradict Hf; apply /negP/negPn.
    rewrite in_cons. caseb.
Qed.

Lemma rem_concl_uacyclic (G : base_graph) (x : G) (R : rule) (F : formula) :
  uacyclic (@switching _ (add_concl_graph x R F)) -> uacyclic (@switching _ G).
Proof.
  intros A u p; cbnb.
  assert (H := rem_concl_to_ll x R F (upvalK p)).
  revert A => /(_ _ {| upval := _ ; upvalK := H |}) /eqP; cbn => /eqP A.
  clear - A; by induction (upval p).
Qed.

Lemma rem_concl_uconnected (G : base_graph) (x : G) (R : rule) (F : formula) :
  uconnected (@switching_left _ (add_concl_graph x R F)) -> uconnected (@switching_left _ G).
Proof.
  intros C u v.
  specialize (C (inl u) (inl v)). destruct C as [p _].
  destruct (rem_concl_ll (upvalK p)) as [q Q _].
  by exists {| upval := _ ; upvalK := Q |}.
Qed.

Lemma rem_concl_correct_weak (G : base_graph) (x : G) (R : rule) (F : formula) :
  correct_weak (add_concl_graph x R F) -> correct_weak G.
Proof.
  intros [A C]. split.
  - by apply (rem_concl_uacyclic A).
  - by apply (rem_concl_uconnected C).
Qed.

Lemma rem_concl_correct (G : base_graph) (x : G) (R : rule) (F : formula) :
  correct_weak (add_concl_graph x R F) -> correct G.
Proof.
  move => C.
  apply correct_from_weak.
  - by apply fintype0.
  - apply (rem_concl_correct_weak C).
Qed.


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

Lemma add_parr_lrN (G : base_graph) (vl vr : G) (Al Ar : formula) :
  forall p u, supath (switching (G := add_parr_graph vl vr Al Ar)) (inl u) (inr tt) p ->
  forward None \in p \/ forward (Some None) \in p.
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => ? /andP[/andP[/eqP ? _] _]. }
  rewrite /supath cons_uniq in_cons.
  move => u /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]].
  destruct e as [[[e | []] | ] | ]; [ | destruct b; caseb | destruct b; caseb].
  enough (forward None \in p \/ forward (Some None) \in p) by caseb.
  destruct (utarget (Some (Some (inl e)) : edge (add_parr_graph vl vr Al Ar), b)) as [w | w] eqn:Hw;
  try by [].
  apply (Hp w). rewrite -Hw. splitb.
Qed.

Lemma add_parr_Nlr (G : base_graph) (vl vr : G) (Al Ar : formula) :
  forall (p : upath) (u v : add_parr_graph vl vr Al Ar), supath switching u v p ->
  forward None \in p \/ forward (Some None) \in p -> (exists u', u = inl u' /\ v = inr tt).
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => ? ? ? [? | ?]. }
  rewrite /supath cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]]
    [/orP[/andP[/eqP He /eqP Hb] | H] | /orP[/andP[/eqP He /eqP Hb] | H]].
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | []]; cbn.
    2:{ by exists vr. }
    contradict U0; apply /negP/negPn.
    assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
    { apply (@add_parr_lrN _ _ _ _ _ _ v), supath_revK. splitb. }
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
    { apply (@add_parr_lrN _ _ _ _ _ _ v), supath_revK. splitb. }
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
    destruct e as [[[e | []] | ] | ]; try by [].
    all: apply (map_f (fun x => switching x.1) H').
Qed.

Lemma add_parr_Nrl (G : base_graph) (vl vr : G) (Al Ar : formula) :
  forall (p : upath) (u v : add_parr_graph vl vr Al Ar), supath switching u v p ->
  backward None \in p \/ backward (Some None) \in p -> exists v', u = inr tt /\ v = inl v'.
Proof.
  intros p ? ? P Hn.
  assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
  { rewrite !(upath_rev_in p). destruct Hn; caseb. }
  destruct (add_parr_Nlr (supath_revK P) Hin) as [u' [-> ->]].
  by exists u'.
Qed.

Lemma add_parr_ll (G : base_graph) (vl vr : G) (Al Ar : formula) :
  forall p u v, supath (switching (G := add_parr_graph vl vr Al Ar)) (inl u) (inl v) p ->
  { q : upath | supath switching u v q & p = [seq (Some (Some (inl x.1)), x.2) | x <- q] }.
Proof.
  intros p u v P.
  assert ((forall b, (None, b) \notin p) /\ forall b, (Some None, b) \notin p) as [Hinn Hinsn].
  { split.
    all: apply /existsPn /negP; move => /existsP [[] ?];
      [destruct (add_parr_Nlr P) as [? [? ?]] | destruct (add_parr_Nrl P) as [? [? ?]]];
      caseb. }
  revert P; move => /andP[/andP[W U] N].
  revert u v W U N Hinn Hinsn. induction p as [ | [[[[e | []] | ] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hinn Hinsn.
    assert ((forall b, (None, b) \notin p) /\ forall b, (Some None, b) \notin p) as [Hinn' Hinsn'].
    { split; apply /existsPn /negP; move => /existsP [bf Hf].
      - specialize (Hinn bf); contradict Hinn; apply /negP/negPn; caseb.
      - specialize (Hinsn bf); contradict Hinsn; apply /negP/negPn; caseb. }
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

Lemma add_parr_rr (G : base_graph) (vl vr : G) (Al Ar : formula) :
  forall p, supath (switching (G := add_parr_graph vl vr Al Ar)) (inr tt) (inr tt) p ->
  p = nil.
Proof.
  intro p; destruct p as [ | (e, b) p]; trivial; unfold supath; cbn.
  move => /andP[/andP[/andP[/eqP w W] /andP[U0 U1]] /norP[/eqP N0 N1]].
  assert (P : supath (switching (G := add_parr_graph vl vr Al Ar)) (utarget (e, b)) (inr tt) p)
    by splitb.
  destruct e as [[[e | []] | ] | ], b; try by []; cbn in P.
  all: contradict U0; apply /negP/negPn.
  all: destruct (add_parr_lrN P) as [Hin | Hin].
  all: apply (map_f (fun e => switching e.1) Hin).
Qed.

Lemma add_parr_to_ll (G : base_graph) (vl vr : G) (Al Ar : formula) :
  forall p u v, supath switching_left u v p ->
  supath (switching_left (G := add_parr_graph vl vr Al Ar)) (inl u) (inl v)
    [seq (Some (Some (inl x.1)), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold supath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : supath switching_left (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH; move => /andP[/andP[W' U'] N'].
  splitb.
  + rewrite -map_comp (eq_map (add_parr_switching_left _ _ _ _) p).
    assert (Hs : switching_left (Some (Some (inl e)) : edge (add_parr_graph vl vr Al Ar)) =
      option_map (Some \o Some) (option_map inl (switching_left e))).
    { replace e with ((forward e).1) by trivial. by rewrite -add_parr_switching_left. }
    rewrite Hs map_comp mem_map 1?map_comp 1?mem_map //.
    all: intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
  + assert (Hd := add_parr_switching_left vl vr Al Ar (forward e)).
    revert Hd. move => /eqP Hd. cbn in Hd. revert Hd. move => /eqP ->.
    by destruct (switching_left e).
Qed.

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
  set L := {| upval := q ; upvalK := Q |};
  set N := {| upval := qn ; upvalK := Qn |}.
  assert (D : upath_disjoint switching_left L N).
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
  intros A [u | []] p; cbnb.
  - destruct (add_parr_ll (upvalK p)) as [q Q Heq].
    rewrite Heq.
    enough (q = nil) as -> by trivial.
    assert (Hf := A u {| upval := q ; upvalK := Q |}).
    by revert Hf; move => /eqP; cbn; move => /eqP ->.
  - apply (add_parr_rr (upvalK p)).
Qed.

Lemma add_parr_uconnected (G : base_graph) (vl vr : G) (Al Ar : formula) :
  uconnected (@switching_left _ G) -> uconnected (@switching_left _ (add_parr_graph vl vr Al Ar)).
Proof.
  intros C [u | []] [v | []].
  - destruct (C u v) as [[p P] _].
    by exists {| upval := _ ; upvalK := (add_parr_to_ll _ _ _ _ P) |}.
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

(** Put a vertex in the middle of an edge *)
Definition extend_edge_graph (G : base_graph) (e : edge G) (R : rule) (As At : formula) : base_graph :=
  {| vertex := option_finType G;
     edge := option_finType (edge G);
     endpoint b a := match a with
      | Some a => if (a == e) && ~~b then None else Some (endpoint b a)
      | None => if b then None else Some (source e)
      end; (* e still points towards the same target *)
     vlabel v := match v with Some v => vlabel v | None => R end;
     elabel a := match a with Some a => (if a == e then At else flabel a, llabel a) | None => (As, true) end;
  |}.
(* TODO vraiment besoin de At, on pourrait reprendre flabel e non ? *)

Lemma extend_edge_switching (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall a f,
  (switching (Some a : edge (extend_edge_graph e R As At)) ==
   switching (Some f : edge (extend_edge_graph _ _ _ _))) =
  (switching a == switching f).
Proof.
  move => a f.
  remember (switching a == switching f) as b eqn:Hb; symmetry in Hb.
  revert Hb; case: b.
  all: cbn; case_if.
  all: try by destruct (eqb_rule (vlabel (target a)) (⅋)).
  all: try by destruct (eqb_rule (vlabel (target f)) (⅋)).
Qed.

Lemma extend_edge_switching_left (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall a f,
  (switching_left (Some a : edge (extend_edge_graph e R As At)) ==
   switching_left (Some f : edge (extend_edge_graph _ _ _ _))) =
  (switching_left a == switching_left f).
Proof.
  move => a f.
  remember (switching_left a == switching_left f) as b eqn:Hb; symmetry in Hb.
  revert Hb; case: b.
  all: unfold switching_left; simpl; case_if.
  all: try by destruct (llabel a).
  all: try by destruct (llabel f).
  all: try by destruct (eqb_rule (vlabel (target a)) (⅋)).
  all: try by destruct (eqb_rule (vlabel (target f)) (⅋)).
Qed.
(* TODO long runtime for these last 2 lemmas, because we have too
many goals as done cannot conclude when we have both b and ~~b as hypothesis,
we have to destruct b by hand to conclude *)

Lemma extend_edge_None (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) :
  forall u v b,
  supath switching (Some u : extend_edge_graph e R As At) (Some v) ((None, b) :: p) ->
  p = (Some e, b) :: behead p.
Proof.
  unfold supath; cbn => u v [] //= /andP[/andP[/andP[/eqP-? W] /andP[U _]] _]; subst u.
  destruct p as [ | ([a | ], b) p]; try by [].
  - destruct (eq_comparable a e); [subst a | ].
    + destruct b; trivial.
      contradict W; apply /negP; cbn. case_if.
    + contradict W; apply /negP; cbn. case_if.
  - contradict U; apply /negP/negPn; cbn.
    rewrite in_cons. caseb.
Qed.

Lemma extend_edge_e (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) :
  forall u v b,
  supath switching (Some u : extend_edge_graph e R As At) (Some v) ((Some e, b) :: p) ->
  p = (None, b) :: behead p.
Proof.
  unfold supath; cbn; rewrite !eq_refl /= => u v [] //= /andP[/andP[/andP[/eqP-? W] /andP[U _]] _]; subst u.
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

Lemma extend_edge_uwalk_fwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall p u v,
  uwalk (Some u : extend_edge_graph e R As At) (Some v) (extend_edge_upath_fwd _ _ _ _ p) = uwalk u v p.
Proof.
  intro p. induction p as [ | (a, b) p IH]; move => u v //=.
  rewrite -IH {IH}.
  case_if; by destruct b.
Qed.

Lemma extend_edge_upath_fwd_in_Some (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall p a b,
  (Some a, b) \in (extend_edge_upath_fwd e R As At p) = ((a, b) \in p).
Proof.
  intros p a b. induction p as [ | (f, c) p IH]; trivial; cbn.
  rewrite mem_cat in_cons IH {IH}. f_equal.
  case_if.
  all: rewrite !in_cons orb_false_r; by destruct b, c.
Qed.

Lemma extend_edge_upath_fwd_in_None (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall p b,
  (None, b) \in (extend_edge_upath_fwd e R As At p) = ((e, b) \in p).
Proof.
  intros p b. induction p as [ | (f, c) p IH]; trivial; cbn.
  rewrite mem_cat in_cons IH {IH}. f_equal.
  case_if.
  all: rewrite !in_cons orb_false_r ?eq_refl; cbn.
  1,2: by destruct c, b.
  by assert (e == f = false) as -> by by apply /eqP; apply nesym.
Qed.

Lemma extend_edge_upath_fwd_uniq (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall p,
  uniq [seq switching e.1 | e <- (extend_edge_upath_fwd e R As At p)] = uniq [seq switching e.1 | e <- p].
Proof.
  intro p; induction p as [ | (a, b) p IH]; trivial; cbn.
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

Lemma extend_edge_supath_fwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall p u v,
  supath switching (Some u : extend_edge_graph e R As At) (Some v) (extend_edge_upath_fwd _ _ _ _ p) =
  supath switching u v p.
Proof. intros. by rewrite /supath extend_edge_uwalk_fwd extend_edge_upath_fwd_uniq !switching_None. Qed.

Lemma extend_edge_upath_fwd_uniq_left (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall p,
  uniq [seq switching_left e.1 | e <- (extend_edge_upath_fwd e R As At p)] = uniq [seq switching_left e.1 | e <- p].
Proof.
  intros p; induction p as [ | (a, b) p IH]; trivial; cbn.
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

Lemma extend_edge_upath_fwd_N (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall p,
  None \notin [seq switching_left e0.1 | e0 <- extend_edge_upath_fwd e R As At p] =
  (None \notin [seq switching_left e0.1 | e0 <- p]).
Proof.
  intros p; induction p as [ | (a, b) p IH]; trivial; cbn.
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

Lemma extend_edge_supath_fwd_left (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall p u v,
  supath switching_left (Some u : extend_edge_graph e R As At) (Some v) (extend_edge_upath_fwd _ _ _ _ p) =
  supath switching_left u v p.
Proof. intros. by rewrite /supath extend_edge_uwalk_fwd extend_edge_upath_fwd_uniq_left // extend_edge_upath_fwd_N. Qed.

Fixpoint extend_edge_upath_bwd (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) : @upath _ _ G :=
  match p with
  | [::] => [::]
  | (Some a, b) :: q => (a, b) :: extend_edge_upath_bwd q
  | (None, b) :: q => extend_edge_upath_bwd q
  end.

Lemma extend_edge_uwalk_bwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) (u v : extend_edge_graph e R As At),
  uwalk u v p ->
  uwalk (match u with | Some u => u | None => source e end)
  (match v with | Some v => v | None => source e end) (extend_edge_upath_bwd p).
Proof.
  intro p. induction p as [ | ([a | ], b) p IH]; move => u v /=.
  { by move => /eqP-->. }
  all: move => /andP[/eqP-? W]; subst u.
  all: specialize (IH _ _ W); revert IH.
  all: destruct b, c; case_if; splitb.
Qed.

Lemma extend_edge_upath_bwd_in_Some (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) a b,
  (Some a, b) \in p = ((a, b) \in extend_edge_upath_bwd p).
Proof. intros p *. induction p as [ | ([f | ], c) p IH]; by rewrite // !in_cons IH. Qed.

Lemma extend_edge_upath_bwd_uniq (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)), uniq [seq switching e.1 | e <- p] ->
  uniq [seq switching e.1 | e <- (extend_edge_upath_bwd p)].
Proof.
  intro p; induction p as [ | ([a | ], b) p IH]; trivial; cbn;
  move => /andP[In U]; splitb; try by apply IH.
  revert In; clear.
  apply contra => /mapP [[f c] In Eq]; apply /mapP.
  rewrite -extend_edge_upath_bwd_in_Some in In.
  exists (Some f, c); trivial.
  by apply /eqP; rewrite extend_edge_switching; apply /eqP.
Qed.

Lemma extend_edge_supath_bwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) (u v : extend_edge_graph e R As At),
  supath switching u v p ->
  supath switching (match u with | Some u => u | None => source e end)
  (match v with | Some v => v | None => source e end) (extend_edge_upath_bwd p).
Proof.
  move => p ? ? /andP[/andP[? ?] ?]. splitb.
  - by apply extend_edge_uwalk_bwd.
  - by apply extend_edge_upath_bwd_uniq.
  - by rewrite switching_None.
Qed.

Lemma extend_edge_upath_bwd_uniq_left (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)), uniq [seq switching_left e.1 | e <- p] ->
  uniq [seq switching_left e.1 | e <- (extend_edge_upath_bwd p)].
Proof.
  intro p; induction p as [ | ([a | ], b) p IH]; trivial; cbn;
  move => /andP[In U]; splitb; try by apply IH.
  revert In; clear.
  apply contra => /mapP [[f c] In Eq]; apply /mapP.
  rewrite -extend_edge_upath_bwd_in_Some in In.
  exists (Some f, c); trivial.
  by apply /eqP; rewrite extend_edge_switching_left; apply /eqP.
Qed.

Lemma extend_edge_upath_bwd_N (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)),
  None \notin [seq switching_left e0.1 | e0 <- p] ->
  None \notin [seq switching_left e0.1 | e0 <- extend_edge_upath_bwd p].
Proof.
  intro p; induction p as [ | ([a | ], b) p IH]; trivial; cbn.
  all: rewrite !in_cons !negb_or => /andP[In ?].
  all: splitb; try by apply IH.
  revert In; clear.
  unfold switching_left; cbn; case_if.
  all: assert (Hal : left (target a) = a) by by []; by rewrite_all Hal.
Qed.

Lemma extend_edge_supath_bwd_left (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) (u v : extend_edge_graph e R As At),
  supath switching_left u v p ->
  supath switching_left (match u with | Some u => u | None => source e end)
  (match v with | Some v => v | None => source e end) (extend_edge_upath_bwd p).
Proof.
  move => p ? ? /andP[/andP[? ?] ?]. splitb.
  - by apply extend_edge_uwalk_bwd.
  - by apply extend_edge_upath_bwd_uniq_left.
  - by rewrite extend_edge_upath_bwd_N.
Qed.


Lemma extend_edge_uacyclic_fwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  uacyclic (@switching _ (extend_edge_graph e R As At)) -> uacyclic (@switching _ G).
Proof.
  intros A v [p P]; apply /eqP; cbn; apply /eqP.
  rewrite -(extend_edge_supath_fwd e R As At) in P.
  specialize (A _ {| upval := extend_edge_upath_fwd e R As At p ; upvalK := P |}).
  revert A => /eqP; cbn => /eqP A.
  destruct p as [ | (a, b) p]; trivial.
  contradict A; cbn. case_if.
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
    by exists {| upval := _ ; upvalK := P |}.
  - by exists (supath_rev (extend_edge_uconnected_bwd_rl e R As At C u)).
  - by exists (extend_edge_uconnected_bwd_rl e R As At C v).
  - by exists (supath_nil switching_left (None : extend_edge_graph _ _ _ _)).
Qed.

Lemma extend_edge_uacyclic_bwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  uacyclic (@switching _ G) -> uacyclic (@switching _ (extend_edge_graph e R As At)).
Proof.
  intros A v [p P]. apply /eqP; cbn; apply /eqP.
  specialize (A _ {| upval := _ ; upvalK := extend_edge_supath_bwd P |}).
  revert A => /eqP; cbn => /eqP A.
  destruct v.
  - destruct p as [ | ([? | ], ?) ?]; try by [].
    contradict A. cbn.
    by rewrite (extend_edge_None P).
  - destruct p as [ | ([? | ], []) [ | ([? | ], []) ?]]; try by [].
    by revert P; rewrite /supath !in_cons => /andP[/andP[_ /andP[/norP[/eqP ? _] _]] _].
Qed.

Lemma extend_edge_uconnected_fwd (G : base_graph) (e : edge G) (R : rule) (As At : formula) :
  uconnected (@switching_left _ (extend_edge_graph e R As At)) ->
  uconnected (@switching_left _ G).
Proof.
  intros C u v.
  specialize (C (Some u) (Some v)). destruct C as [[p P] _].
  apply extend_edge_supath_bwd_left in P.
  by exists {| upval := _ ; upvalK := P |}.
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
End Atoms.
