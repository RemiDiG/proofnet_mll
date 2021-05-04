(* Basic operations respecting correctness *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
From mathcomp Require Import all_ssreflect zify.
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export graph_more mll_prelim mll_def.

Import EqNotations.

Set Mangle Names.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Section Atoms.

(** A set of atoms for building formulas *)
Context { atom : DecType }.
(* TODO meilleur moyen de récupérer les notations *)
Notation formula := (@formula atom).
Notation base_graph := (graph (flat rule) (flat formula)).
Notation graph_left := (@graph_left atom).
Notation graph_data := (@graph_data atom).
Notation geos := (@geos atom).
Notation proof_structure := (@proof_structure atom).
Notation proof_net := (@proof_net atom).
Infix "≃l" := iso_left (at level 79).


(** * Basic operations respecting correctness *)
(** Making the disjoint union and adding an edge from the first graph to the second *)
Definition union_edge_graph {Lv Le : Type} (G0 G1 : graph Lv Le) (x : G0) (y : G1) (A : Le) : graph Lv Le :=
  (G0 ⊎ G1) ∔ [inl x, A, inr y].

Definition union_edge_left (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  union_edge_graph x y A -> edge (union_edge_graph x y A) :=
  fun v => Some (match v with
  | inl v => inl (left v)
  | inr v => inr (left v)
  end).

Definition union_edge_graph_left (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) : graph_left := {|
  graph_of := union_edge_graph x y A;
  left := @union_edge_left _ _ _ _ _;
  |}.

Lemma union_edge_switching_0 (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  (fun e : edge (union_edge_graph_left x y A) * bool => switching e.1) \o
  (fun x : edge G0 * bool => (Some (inl x.1), x.2)) =1 fun e => Some (option_map inl (switching e.1)).
Proof. intros (?, ?). unfold switching; cbn. case_if. Qed.

Lemma union_edge_switching_1 (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  (fun e : edge (union_edge_graph_left x y A) * bool => switching e.1) \o
  (fun x : edge G1 * bool => (Some (inr x.1), x.2)) =1 fun e => Some (option_map inr (switching e.1)).
Proof. intros (?, ?). unfold switching; cbn. case_if. Qed.

Lemma union_edge_switching_left_0 (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  (fun e : edge (union_edge_graph_left x y A) * bool => switching_left e.1) \o
  (fun x : edge G0 * bool => (Some (inl x.1), x.2)) =1
  fun e => option_map Some (option_map inl (switching_left e.1)).
Proof. intros (?, ?). unfold switching_left; cbn. case_if. Qed.

Lemma union_edge_switching_left_1 (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  (fun e : edge (union_edge_graph_left x y A) * bool => switching_left e.1) \o
  (fun x : edge G1 * bool => (Some (inr x.1), x.2)) =1
  fun e => option_map Some (option_map inr (switching_left e.1)).
Proof. intros (?, ?). unfold switching_left; cbn. case_if. Qed.

Lemma union_edge_lrN (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall p u v, supath (switching (G := union_edge_graph_left x y A)) (inl u) (inr v) p ->
  forward None \in p.
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => u v /andP[/andP[/eqP ? _] _]. }
  rewrite /supath cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]].
  destruct e as [[e | e] | ]; [ | by destruct b | by destruct b].
  enough (forward None \in p) by caseb.
  destruct (utarget (Some (inl e) : edge (union_edge_graph_left x y A), b)) as [w | w] eqn:Hw; try by [].
  apply (Hp w v).
  splitb. by rewrite -Hw.
Qed.

Lemma union_edge_Nlr (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall (p : upath) (u v : union_edge_graph_left x y A), supath switching u v p ->
  forward None \in p -> (exists u' v', u = inl u' /\ v = inr v').
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => *. }
  rewrite /supath cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]] /orP[/andP[/eqP He /eqP Hb] | H].
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | v]; cbn.
    2:{ by exists x, v. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (Hin : forward None \in upath_rev p).
    { apply (@union_edge_lrN _ _ _ _ _ _ v y), supath_revK. splitb. }
    rewrite (upath_rev_in p) in Hin.
    by rewrite (map_f _ Hin).
  - assert (Hs : supath switching (utarget (e, b)) v p) by splitb.
    specialize (Hp _ _ Hs H); clear Hs. destruct Hp as [u' [v' [Hu ->]]].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u, v'. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (e = None) as -> by by destruct e as [[e | e] | ].
    assert (H' : forward None \in p) by by [].
    apply (map_f (fun x => switching x.1) H').
Qed.

Lemma union_edge_Nrl (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall (p : upath) (u v : union_edge_graph_left x y A), supath switching u v p ->
  backward None \in p -> exists u' v', u = inr u' /\ v = inl v'.
Proof.
  intros p ? ? P ?.
  assert (Hin : forward None \in upath_rev p) by by rewrite (upath_rev_in p).
  destruct (union_edge_Nlr (supath_revK P) Hin) as [u' [v' [-> ->]]].
  by exists v', u'.
Qed.

Lemma union_edge_ll (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall p u v, supath (switching (G := union_edge_graph_left x y A)) (inl u) (inl v) p ->
  { q : upath | supath switching u v q & p = [seq (Some (inl x.1), x.2) | x <- q] }.
Proof.
  intros p u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn /negP. move => /existsP [[] N].
    - by destruct (union_edge_Nlr P N) as [u' [v' [Hu Hv]]].
    - by destruct (union_edge_Nrl P N) as [u' [v' [Hu Hv]]]. }
  revert P; move => /andP[/andP[W U] N].
  revert u v W U N Hin. induction p as [ | [[[e | e] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hin.
    assert (Ht : forall b : bool_eqType, (None, b) \notin p).
    { apply /existsPn /negP. move => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP; rewrite negb_involutive.
      caseb. }
    specialize (IH _ _ W U1 N1 Ht). destruct IH as [p' P' Hp]. subst p.
    exists ((e, b) :: p').
    + revert P'. unfold supath; cbn. move => /andP[/andP[W' U'] N'].
      splitb.
      * revert w. move => /eqP. by cbn.
      * clear - U0.
        rewrite -map_comp (eq_map (union_edge_switching_0 x y A) p') in U0.
        assert (He : switching (Some (inl e) : edge (union_edge_graph_left x y A)) =
          Some (option_map inl (switching e))).
        { replace e with ((forward e).1) by trivial. by rewrite -union_edge_switching_0. }
        rewrite He map_comp mem_map // map_comp mem_map // in U0.
        intros [a | ] [b | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
    + by rewrite map_cons.
  - by [].
  - move => ? ? ? ? ? Hf; clear - Hf.
    specialize (Hf b). contradict Hf; apply /negP.
    rewrite in_cons negb_involutive.
    caseb.
Qed.

Lemma union_edge_rr (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall p u v, supath (switching (G := union_edge_graph_left x y A)) (inr u) (inr v) p ->
  { p' : upath | supath switching u v p' & p = [seq (Some (inr x.1), x.2) | x <- p'] }.
Proof.
  intros p u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn /negP. move => /existsP [[] N].
    - by destruct (union_edge_Nlr P N) as [u' [v' [Hu Hv]]].
    - by destruct (union_edge_Nrl P N) as [u' [v' [Hu Hv]]]. }
  revert P; move => /andP[/andP[W U] N].
  revert u v W U N Hin. induction p as [ | [[[e | e] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - by [].
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hin.
    assert (Ht : forall b : bool_eqType, (None, b) \notin p).
    { apply /existsPn /negP. move => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP; rewrite negb_involutive.
      caseb. }
    specialize (IH _ _ W U1 N1 Ht). destruct IH as [p' P' Hp]. subst p.
    exists ((e, b) :: p').
    + revert P'. unfold supath; cbn. move => /andP[/andP[W' U'] N'].
      splitb.
      * revert w. move => /eqP. by cbn.
      * clear - U0.
        rewrite -map_comp (eq_map (union_edge_switching_1 x y A) p') in U0.
        assert (He : switching (Some (inr e) : edge (union_edge_graph_left x y A)) =
          Some (option_map inr (switching e))).
        { replace e with ((forward e).1) by trivial. by rewrite -(union_edge_switching_1 x y A). }
        rewrite He map_comp mem_map // map_comp mem_map // in U0.
        intros [a | ] [b | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
    + by rewrite map_cons.
  - move => ? ? ? ? ? Hf; clear - Hf.
    specialize (Hf b). contradict Hf; apply /negP.
    rewrite in_cons negb_involutive.
    caseb.
Qed. (* TODO gros copie collé, voir si on peut faire mieux *)

Lemma union_edge_to_ll (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall p u v, supath switching_left u v p ->
  supath (switching_left (G := union_edge_graph_left x y A)) (inl u) (inl v) [seq (Some (inl x.1), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold supath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : supath switching_left (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH; move => /andP[/andP[W' U'] N'].
  splitb.
  + rewrite -map_comp (eq_map (union_edge_switching_left_0 x y A) p).
    assert (switching_left (Some (inl e) : edge (union_edge_graph_left x y A)) =
      option_map Some (option_map inl (switching_left e))) as ->.
    { replace e with ((forward e).1) by trivial. by rewrite -union_edge_switching_left_0. }
    rewrite map_comp mem_map 1?map_comp 1?mem_map //.
    all: intros [a | ] [c | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
  + assert (Hd := union_edge_switching_left_0 x y A (forward e)).
    revert Hd. move => /eqP Hd. cbn in Hd. revert Hd. move => /eqP ->.
    by destruct (switching_left e).
Qed.

Lemma union_edge_to_rr (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  forall p u v, supath switching_left u v p ->
  supath (switching_left (G := union_edge_graph_left x y A)) (inr u) (inr v) [seq (Some (inr x.1), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold supath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : supath switching_left (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH; move => /andP[/andP[W' U'] N'].
  splitb.
  + rewrite -map_comp (eq_map (union_edge_switching_left_1 x y A) p).
    assert (switching_left (Some (inr e) : edge (union_edge_graph_left x y A)) =
      option_map Some (option_map inr (switching_left e))) as ->.
    { replace e with ((forward e).1) by trivial. by rewrite -union_edge_switching_left_1. }
    rewrite map_comp mem_map 1?map_comp 1?mem_map //.
    all: intros [a | ] [c | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
  + assert (Hd := union_edge_switching_left_1 x y A (forward e)).
    revert Hd. move => /eqP Hd. cbn in Hd. revert Hd. move => /eqP ->.
    by destruct (switching_left e).
Qed. (* TODO gros copie collé, voir si on peut faire mieux *)

Lemma union_edge_to_lr (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  uconnected (switching_left (G := G0)) -> uconnected (switching_left (G := G1)) ->
  forall u v, exists _ :
  Supath (switching_left (G := union_edge_graph_left x y A)) (inl u) (inr v), true.
Proof.
  move => C0 C1 u v.
  destruct (C0 u x) as [[p0 P0] _].
  assert (Q0 := union_edge_to_ll x y A P0).
  set q0 : @upath _ _ (union_edge_graph_left x y A) := [seq (Some (inl x.1), x.2) | x <- p0].
  destruct (C1 y v) as [[p1 P1] _].
  assert (Q1 := union_edge_to_rr x y A P1).
  set q1 : @upath _ _ (union_edge_graph_left x y A) := [seq (Some (inr x.1), x.2) | x <- p1].
  set qn : @upath _ _ (union_edge_graph_left x y A) := [:: forward None].
  assert (Qn : supath (switching_left (G := union_edge_graph_left x y A)) (inl x) (inr y) qn).
  { unfold supath; cbn. repeat (apply /andP; split); trivial.
    rewrite mem_seq1 /switching_left; cbn. case_if. }
  set L := {| upval := q0 ; upvalK := Q0 |};
  set R := {| upval := q1 ; upvalK := Q1 |};
  set N := {| upval := qn ; upvalK := Qn |}.
  assert (Some None \notin [seq switching_left x0.1 | x0 <- q0] /\
    Some None \notin [seq switching_left x0.1 | x0 <- q1]) as [? ?].
  { rewrite /q0 /q1 -2!map_comp (eq_map (union_edge_switching_left_0 x y A))
      (eq_map (union_edge_switching_left_1 x y A)).
    split; apply /mapP; intros [(?, ?) _ Heq].
    all: contradict Heq.
    all: unfold switching_left; case_if. }
  assert (None \notin [seq switching_left x0.1 | x0 <- q0] /\
    None \notin [seq switching_left x0.1 | x0 <- q1]) as [? ?].
  { split; apply /negP; intro Hf;
    [clear - Hf Q0; revert Q0; move => /andP[/andP[_ _] Hc]
    | clear - Hf Q1; revert Q1; move => /andP[/andP[_ _] Hc]].
    all: contradict Hf; by apply /negP. }
  assert (upath_disjoint switching_left N L /\ upath_disjoint switching_left N R) as [Dl Dr].
  { split; apply /disjointP; intros [[e | ] | ]; cbn.
    all: try (move => _; by apply /negP).
    all: move => Hf _; revert Hf; rewrite mem_seq1 /switching_left; cbn.
    all: case_if. }
    rewrite /upath_disjoint disjoint_sym in Dl.
  assert (D : upath_disjoint switching_left (supath_cat Dl) R).
  { rewrite /upath_disjoint /supath_cat /= map_cat disjoint_cat. splitb.
    apply /disjointP. intros [[[e | e] | ] | ]; cbn.
    - move => _; apply /negP.
      rewrite /q1 -map_comp (eq_map (union_edge_switching_left_1 x y A)).
      apply /mapP. intros [(?, ?) _ Heq]. contradict Heq.
      unfold switching_left. case_if.
    - move => Hf _; revert Hf; apply /negP.
      rewrite /q0 -map_comp (eq_map (union_edge_switching_left_0 x y A)).
      apply /mapP. intros [(?, ?) _ Heq]. contradict Heq.
      unfold switching_left. case_if.
    - move => _; by apply /negP.
    - move => _; by apply /negP. }
  by exists (supath_cat D).
Qed.

Lemma union_edge_to_rl (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  uconnected (switching_left (G := G0)) -> uconnected (switching_left (G := G1)) ->
  forall u v, exists _ : Supath (switching_left (G := union_edge_graph_left x y A)) (inr u) (inl v), true.
Proof.
  intros C0 C1 u v.
  destruct (union_edge_to_lr x y A C0 C1 v u) as [p _].
  by exists (supath_rev p).
Qed.

Lemma union_edge_correct (G0 G1 : graph_left) (x : G0) (y : G1) (A : formula) :
  correct G0 -> correct G1 -> correct (union_edge_graph_left x y A).
Proof.
  intros [A0 C0] [A1 C1]. split.
  - intros [u | u] p; apply /eqP; cbn; apply /eqP.
    + destruct (union_edge_ll (upvalK p)) as [q Q Heq].
      rewrite Heq.
      enough (q = nil) as -> by trivial.
      assert (Hf := A0 u {| upval := q ; upvalK := Q |}).
      by revert Hf; move => /eqP; cbn; move => /eqP ->.
    + destruct (union_edge_rr (upvalK p)) as [q Q Heq].
      rewrite Heq.
      enough (q = nil) as -> by trivial.
      assert (Hf := A1 u {| upval := q ; upvalK := Q |}).
      by revert Hf; move => /eqP; cbn; move => /eqP ->.
  - intros [u | u] [v | v].
    + destruct (C0 u v) as [[p P] _].
      by exists {| upval := [seq (Some (inl x.1), x.2) | x <- p] : @upath _ _ (union_edge_graph_left x y A) ;
        upvalK := (union_edge_to_ll x y A P) |}.
    + by apply union_edge_to_lr.
    + by apply union_edge_to_rl.
    + destruct (C1 u v) as [[p P] _].
      by exists {| upval := [seq (Some (inr x.1), x.2) | x <- p] : @upath _ _ (union_edge_graph_left x y A) ;
        upvalK := (union_edge_to_rr x y A P) |}.
Qed.


(** Adding a non-parr node below a vertex *)
Definition add_concl_graph {Lv Le : Type} (G : graph Lv Le) (x : G) (R : Lv) (A : Le) : graph Lv Le :=
  G ∔ R ∔ [inl x, A, inr tt].

Definition add_concl_left (G : graph_left) (x : G) (R : rule) (A : formula) :
  add_concl_graph x R A -> edge (add_concl_graph x R A) :=
  fun u => match u with
  | inl u => Some (inl (left u))
  | inr _ => None
  end.

Definition add_concl_graph_left (G : graph_left) (x : G) (R : rule) (A : formula) : graph_left := {|
  graph_of := add_concl_graph x R A;
  left := @add_concl_left _ _ _ _;
  |}.


Lemma add_concl_switching (G : graph_left) (x : G) (R : rule) (A : formula) :
  (fun e : edge (add_concl_graph_left x R A) * bool => switching e.1) \o
  (fun e : edge G * bool => (Some (inl e.1), e.2)) =1
  fun e => Some (option_map inl (switching e.1)).
Proof. intros (?, ?). unfold switching; cbn. case_if. Qed.

Lemma add_concl_switching_left (G : graph_left) (x : G) (R : rule) (A : formula) :
  (fun e : edge (add_concl_graph_left x R A) * bool => switching_left e.1) \o
  (fun e : edge G * bool => (Some (inl e.1), e.2)) =1
  fun e => option_map Some (option_map inl (switching_left e.1)).
Proof. intros (?, ?). unfold switching_left; cbn. case_if. Qed.

Lemma add_concl_lrN (G : graph_left) (x : G) (R : rule) (A : formula)
  {I : eqType} (f : edge (add_concl_graph_left x R A) -> option I) :
  forall p u, supath f (inl u) (inr tt) p ->
  forward None \in p.
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => u /andP[/andP[/eqP ? _] _]. }
  rewrite /supath cons_uniq in_cons.
  move => u /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]].
  destruct e as [[e | []] | ]; [ | by destruct b].
  enough (forward None \in p) by caseb.
  destruct (utarget (Some (inl e) : edge (add_concl_graph_left x R A), b)) as [w | w] eqn:Hw; try by [].
  apply (Hp w).
  splitb. by rewrite -Hw. 
Qed.

Lemma add_concl_Nlr (G : graph_left) (x : G) (R : rule) (A : formula)
  {I : finType} (f : edge (add_concl_graph_left x R A) -> option I) :
  forall (p : upath) (u v : add_concl_graph_left x R A), supath f u v p ->
  forward None \in p -> (exists u', u = inl u' /\ v = inr tt).
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => *. }
  rewrite /supath cons_uniq in_cons.
  move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]] /orP[/andP[/eqP He /eqP Hb] | H].
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | []]; cbn.
    2:{ by exists x. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (Hin : forward None \in upath_rev p).
    { apply (@add_concl_lrN _ _ _ _ _ f _ v), supath_revK. splitb. }
    rewrite (upath_rev_in p) in Hin.
    by rewrite (map_f _ Hin).
  - assert (Hs : supath f (utarget (e, b)) v p) by splitb.
    specialize (Hp _ _ Hs H); clear Hs. destruct Hp as [u' [Hu ->]].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (e = None) as -> by by destruct e as [[e | e] | ].
    assert (H' : forward None \in p) by by [].
    apply (map_f (fun x => f x.1) H').
Qed.

Lemma add_concl_Nrl (G : graph_left) (x : G) (R : rule) (A : formula)
  {I : finType} (f : edge (add_concl_graph_left x R A) -> option I) :
  forall (p : upath) (u v : add_concl_graph_left x R A), supath f u v p ->
  backward None \in p -> exists v', u = inr tt /\ v = inl v'.
Proof.
  intros p ? ? P ?.
  assert (Hin : forward None \in upath_rev p) by by rewrite (upath_rev_in p).
  destruct (add_concl_Nlr (supath_revK P) Hin) as [u' [-> ->]].
  by exists u'.
Qed.

Lemma add_concl_ll (G : graph_left) (x : G) (R : rule) (A : formula) :
  forall p u v, supath (switching (G := add_concl_graph_left x R A)) (inl u) (inl v) p ->
  { q : upath | supath switching u v q & p = [seq (Some (inl x.1), x.2) | x <- q] }.
Proof.
  intros p u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn /negP; move => /existsP [[] ?];
    [destruct (add_concl_Nlr P) as [? [? ?]] | destruct (add_concl_Nrl P) as [? [? ?]]];
    caseb. }
  revert P; move => /andP[/andP[W U] N].
  revert u v W U N Hin. induction p as [ | [[[e | []] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hin.
    assert (Hin' : forall b, (None, b) \notin p).
    { apply /existsPn /negP; move => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP; rewrite negb_involutive; caseb. }
    specialize (IH _ _ W U1 N1 Hin). destruct IH as [p' P' Hp]. subst p.
    exists ((e, b) :: p').
    + revert P'. unfold supath; cbn. move => /andP[/andP[W' U'] N'].
      splitb.
      * revert w. move => /eqP. by cbn.
      * clear - U0.
        rewrite -map_comp (eq_map (add_concl_switching x R A) p') in U0.
        assert (He : switching (Some (inl e) : edge (add_concl_graph_left x R A)) =
          Some (option_map inl (switching e))).
        { replace e with ((forward e).1) by trivial. by rewrite -add_concl_switching. }
        rewrite He map_comp mem_map // map_comp mem_map // in U0.
        intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
    + by rewrite map_cons.
  - move => ? ? ? ? ? Hf; clear - Hf.
    specialize (Hf b). contradict Hf; apply /negP.
    rewrite in_cons negb_involutive.
    caseb.
Qed.

Lemma add_concl_rr (G : graph_left) (x : G) (R : rule) (A : formula) :
  forall p, supath (switching (G := add_concl_graph_left x R A)) (inr tt) (inr tt) p ->
  p = nil.
Proof.
  intro p; destruct p as [ | (e, b) p]; trivial; unfold supath; cbn.
  move => /andP[/andP[/andP[/eqP w W] /andP[U0 U1]] /norP[/eqP N0 N1]].
  assert (P : supath (switching (G := add_concl_graph_left x R A)) (utarget (e, b)) (inr tt) p)
    by splitb.
  destruct e as [[e | []] | ], b; try by []; cbn in P.
  contradict U0; apply /negP; rewrite negb_involutive.
  apply (map_f (fun e => switching e.1) (add_concl_lrN P)).
Qed.

Lemma add_concl_to_ll (G : graph_left) (x : G) (R : rule) (A : formula) :
  forall p u v, supath switching_left u v p ->
  supath (switching_left (G := add_concl_graph_left x R A)) (inl u) (inl v)
    [seq (Some (inl x.1), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold supath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : supath switching_left (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH; move => /andP[/andP[W' U'] N'].
  splitb.
  + rewrite -map_comp (eq_map (add_concl_switching_left _ _ _) p).
    assert (Hs : switching_left (Some (inl e) : edge (add_concl_graph_left x R A)) =
      option_map Some (option_map inl (switching_left e))).
    { replace e with ((forward e).1) by trivial. by rewrite -add_concl_switching_left. }
    rewrite Hs map_comp mem_map 1?map_comp 1?mem_map //.
    all: intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
  + assert (Hd := add_concl_switching_left x R A (forward e)).
    revert Hd. move => /eqP Hd. cbn in Hd. revert Hd. move => /eqP ->.
    by destruct (switching_left e).
Qed.

Lemma add_concl_to_lr (G : graph_left) (x : G) (R : rule) (A : formula) :
  R <> ⅋ -> uconnected (switching_left (G := G)) -> forall u, exists _ :
  Supath (switching_left (G := add_concl_graph_left x R A)) (inl u) (inr tt), true.
Proof.
  move => HR C u.
  destruct (C u x) as [[p P] _].
  assert (Q := add_concl_to_ll x R A P).
  set q : @upath _ _ (add_concl_graph_left x R A) := [seq (Some (inl x.1), x.2) | x <- p].
  set qn : @upath _ _ (add_concl_graph_left x R A) := [:: forward None].
  assert (Qn : supath (switching_left (G := add_concl_graph_left x R A)) (inl x) (inr tt) qn).
  { unfold supath; cbn. repeat (apply /andP; split); trivial.
    rewrite in_cons in_nil. apply /norP; split; trivial.
    unfold switching_left. case_if.
    contradict HR. apply /eqP. cbn. by apply /eqP. }
  set L := {| upval := q ; upvalK := Q |};
  set N := {| upval := qn ; upvalK := Qn |}.
  assert (D : upath_disjoint switching_left L N).
  { apply /disjointP; intros [[[e | []] | ] | ]; cbn.
    - move => _; apply /negP.
      rewrite in_cons in_nil. apply /norP; split; trivial.
      unfold switching_left. case_if.
    - move => Hf _; revert Hf; apply /negP.
      rewrite /q -map_comp (eq_map (add_concl_switching_left _ _ _)).
      apply /mapP; intros [(?, ?) _ Heq]. contradict Heq.
      unfold switching_left; case_if.
    - move => _; apply /negP.
      rewrite in_cons in_nil. apply /norP; split; trivial.
      unfold switching_left. case_if.
      contradict HR. apply /eqP. cbn. by apply /eqP. }
  by exists (supath_cat D).
Qed.

Lemma add_concl_to_rl (G : graph_left) (x : G) (R : rule) (A : formula) :
  R <> ⅋ -> uconnected (switching_left (G := G)) -> forall v, exists _ :
  Supath (switching_left (G := add_concl_graph_left x R A)) (inr tt) (inl v), true.
Proof.
  intros HR C u.
  destruct (add_concl_to_lr x A HR C u) as [p _].
  by exists (supath_rev p).
Qed.

Lemma add_concl_correct (G : graph_left) (x : G) (R : rule) (F : formula) :
  R <> ⅋ -> correct G -> correct (add_concl_graph_left x R F).
Proof.
  intros HR [A C]. split.
  - intros [u | []] p; apply /eqP; cbn; apply /eqP.
    + destruct (add_concl_ll (upvalK p)) as [q Q Heq].
      rewrite Heq.
      enough (q = nil) as -> by trivial.
      assert (Hf := A u {| upval := q ; upvalK := Q |}).
      by revert Hf; move => /eqP; cbn; move => /eqP ->.
    + apply (add_concl_rr (upvalK p)).
  - intros [u | []] [v | []].
    + destruct (C u v) as [[p P] _].
      by exists {| upval := [seq (Some (inl x.1), x.2) | x <- p] : @upath _ _ (add_concl_graph_left x R F) ;
        upvalK := (add_concl_to_ll _ _ _ P) |}.
    + by apply add_concl_to_lr.
    + by apply add_concl_to_rl.
    + by exists (supath_nil switching_left (inr tt : add_concl_graph_left x R F)).
Qed.

Lemma rem_concl_to_ll (G : graph_left) (x : G) (R : rule) (A : formula) :
  forall p u v, supath switching u v p ->
  supath (switching (G := add_concl_graph_left x R A)) (inl u) (inl v)
    [seq (Some (inl x.1), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold supath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : supath switching (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH; move => /andP[/andP[W' U'] N'].
  splitb.
  rewrite -map_comp (eq_map (add_concl_switching _ _ _) p).
  assert (Hs : switching (Some (inl e) : edge (add_concl_graph_left x R A)) =
    Some (option_map inl (switching e))).
  { replace e with ((forward e).1) by trivial. by rewrite -add_concl_switching. }
  rewrite Hs map_comp mem_map 1?map_comp 1?mem_map //.
  all: intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
Qed.

Lemma rem_concl_ll (G : graph_left) (x : G) (R : rule) (A : formula) :
  forall p u v, supath (switching_left (G := add_concl_graph_left x R A)) (inl u) (inl v) p ->
  { q : upath | supath switching_left u v q & p = [seq (Some (inl x.1), x.2) | x <- q] }.
Proof.
  intros p u v P.
  assert (Hin : forall b, (None, b) \notin p).
  { apply /existsPn /negP; move => /existsP [[] ?];
    [destruct (add_concl_Nlr P) as [? [? ?]] | destruct (add_concl_Nrl P) as [? [? ?]]];
    caseb. }
  revert P; move => /andP[/andP[W U] N].
  revert u v W U N Hin. induction p as [ | [[[e | []] | ] b] p IH]; cbn.
  - exists nil; splitb.
  - move => u v /andP[/eqP w W] /andP[U0 U1] /norP[/eqP N0 N1] Hin.
    assert (Hin' : forall b, (None, b) \notin p).
    { apply /existsPn /negP; move => /existsP [bf Hf].
      specialize (Hin bf); contradict Hin; apply /negP; rewrite negb_involutive; caseb. }
    specialize (IH _ _ W U1 N1 Hin). destruct IH as [p' P' Hp]. subst p.
    exists ((e, b) :: p').
    + revert P'. unfold supath; cbn. move => /andP[/andP[W' U'] N'].
      splitb.
      * revert w. move => /eqP. by cbn.
      * clear - U0.
        rewrite -map_comp (eq_map (add_concl_switching_left x R A) p') in U0.
        assert (He : switching_left (Some (inl e) : edge (add_concl_graph_left x R A)) =
          option_map Some (option_map inl (switching_left e))).
        { replace e with ((forward e).1) by trivial. by rewrite -add_concl_switching_left. }
        rewrite He 2?map_comp 2?mem_map // in U0.
        all: intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
      * assert (Hr : switching_left (Some (inl e) : edge (add_concl_graph_left x R A)) =
          ((fun f : edge (add_concl_graph_left x R A) * _ => switching_left f.1) \o
          (fun f => (Some (inl f.1), f.2))) (forward e)) by by [].
        rewrite Hr add_concl_switching_left /= in N0.
        by destruct (switching_left e).
    + by rewrite map_cons.
  - move => ? ? ? ? ? Hf; clear - Hf.
    specialize (Hf b). contradict Hf; apply /negP.
    rewrite in_cons negb_involutive.
    caseb.
Qed.

Lemma rem_concl_correct (G : graph_left) (x : G) (R : rule) (F : formula) :
  correct (add_concl_graph_left x R F) -> correct G.
Proof.
  intros [A C]. split.
  - intros u p; apply /eqP; cbn; apply /eqP.
    assert (H := rem_concl_to_ll x R F (upvalK p)).
    specialize (A _ {| upval := [seq (Some (inl e.1) : edge (add_concl_graph_left x R F), e.2)
      | e <- upval p] ; upvalK := H |}).
  revert A; move => /eqP; cbn; move => /eqP A.
  clear - A; by induction (upval p).
  - intros u v.
    specialize (C (inl u) (inl v)). destruct C as [p _].
    destruct (rem_concl_ll (upvalK p)) as [q Q _].
    by exists {| upval := q ; upvalK := Q |}.
Qed.


(** Adding a parr below 2 vertices *)
Definition add_parr_graph (G : base_graph) (vl vr : G) (Al Ar : formula) : base_graph :=
  G ∔ ⅋ ∔ [inl vl, Al, inr tt] ∔ [inl vr, Ar, inr tt].

Definition add_parr_left (G : graph_left) (vl vr : G) (Al Ar : formula) :
  add_parr_graph vl vr Al Ar -> edge (add_parr_graph vl vr Al Ar) :=
  fun u => match u with
  | inl u => Some (Some (inl (left u)))
  | inr _ => Some None
  end.

Definition add_parr_graph_left (G : graph_left) (vl vr : G) (Al Ar : formula) : graph_left := {|
  graph_of := add_parr_graph vl vr Al Ar;
  left := @add_parr_left _ _ _ _ _;
  |}.

Lemma add_parr_switching (G : graph_left) (vl vr : G) (Al Ar : formula) :
  (fun e : edge (add_parr_graph_left vl vr Al Ar) * bool => switching e.1) \o
  (fun x : edge G * bool => (Some (Some (inl x.1)), x.2)) =1
  fun e => Some (Some (option_map inl (switching e.1))).
Proof. intros (?, ?). unfold switching; cbn. case_if. Qed.

Lemma add_parr_switching_left (G : graph_left) (vl vr : G) (Al Ar : formula) :
  (fun e : edge (add_parr_graph_left vl vr Al Ar) * bool => switching_left e.1) \o
  (fun x : edge G * bool => (Some (Some (inl x.1)), x.2)) =1
  fun e => option_map (Some \o Some) (option_map inl (switching_left e.1)).
Proof. intros (?, ?). unfold switching_left; cbn. case_if. Qed.

Lemma add_parr_lrN (G : graph_left) (vl vr : G) (Al Ar : formula) :
  forall p u, supath (switching (G := add_parr_graph_left vl vr Al Ar)) (inl u) (inr tt) p ->
  forward None \in p \/ forward (Some None) \in p.
Proof.
  intro p; induction p as [ | (e, b) p Hp].
  { by move => u /andP[/andP[/eqP ? _] _]. }
  rewrite /supath cons_uniq in_cons.
  move => u /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[/eqP N0 N1]].
  destruct e as [[[e | []] | ] | ]; [ | destruct b; caseb | destruct b; caseb].
  enough (forward None \in p \/ forward (Some None) \in p) by caseb.
  destruct (utarget (Some (Some (inl e)) : edge (add_parr_graph_left vl vr Al Ar), b)) as [w | w] eqn:Hw; try by [].
  apply (Hp w).
  splitb. by rewrite -Hw.
Qed.

Lemma add_parr_Nlr (G : graph_left) (vl vr : G) (Al Ar : formula) :
  forall (p : upath) (u v : add_parr_graph_left vl vr Al Ar), supath switching u v p ->
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
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
    { apply (@add_parr_lrN _ _ _ _ _ _ v), supath_revK. splitb. }
    rewrite 2!(upath_rev_in p) in Hin.
    destruct Hin as [Hin | Hin];
    by rewrite (map_f _ Hin).
  - assert (Hs : supath switching (utarget (e, b)) v p) by splitb.
    specialize (Hp _ _ Hs); clear Hs. destruct Hp as [u' [Hu ->]]; [caseb | ].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (H' : forward None \in p) by by [].
    destruct e as [[[e | []] | ] | ]; try by [].
    all: apply (map_f (fun x => switching x.1) H').
  - simpl in He; simpl in Hb; subst e b u. cbn in W1.
    destruct v as [v | []]; cbn.
    2:{ by exists vl. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
    { apply (@add_parr_lrN _ _ _ _ _ _ v), supath_revK. splitb. }
    rewrite 2!(upath_rev_in p) in Hin.
    destruct Hin as [Hin | Hin];
    by rewrite (map_f _ Hin).
  - assert (Hs : supath switching (utarget (e, b)) v p) by splitb.
    specialize (Hp _ _ Hs); clear Hs. destruct Hp as [u' [Hu ->]]; [caseb | ].
    rewrite_all Hu.
    destruct u as [u | u].
    { by exists u. }
    contradict U0; apply /negP; rewrite negb_involutive.
    assert (H' : forward (Some None) \in p) by by [].
    destruct e as [[[e | []] | ] | ]; try by [].
    all: apply (map_f (fun x => switching x.1) H').
Qed.

Lemma add_parr_Nrl (G : graph_left) (vl vr : G) (Al Ar : formula) :
  forall (p : upath) (u v : add_parr_graph_left vl vr Al Ar), supath switching u v p ->
  backward None \in p \/ backward (Some None) \in p -> exists v', u = inr tt /\ v = inl v'.
Proof.
  intros p ? ? P Hn.
  assert (Hin : forward None \in upath_rev p \/ forward (Some None) \in upath_rev p).
  { rewrite !(upath_rev_in p). destruct Hn; caseb. }
  destruct (add_parr_Nlr (supath_revK P) Hin) as [u' [-> ->]].
  by exists u'.
Qed.

Lemma add_parr_ll (G : graph_left) (vl vr : G) (Al Ar : formula) :
  forall p u v, supath (switching (G := add_parr_graph_left vl vr Al Ar)) (inl u) (inl v) p ->
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
      - specialize (Hinn bf); contradict Hinn; apply /negP; rewrite negb_involutive; caseb.
      - specialize (Hinsn bf); contradict Hinsn; apply /negP; rewrite negb_involutive; caseb. }
    specialize (IH _ _ W U1 N1 Hinn' Hinsn'). destruct IH as [p' P' Hp]. subst p.
    exists ((e, b) :: p').
    + revert P'. unfold supath; cbn. move => /andP[/andP[W' U'] N'].
      splitb.
      * revert w. move => /eqP. by cbn.
      * clear - U0.
        rewrite -map_comp (eq_map (add_parr_switching vl vr Al Ar) p') in U0.
        assert (He : switching (Some (Some (inl e)) : edge (add_parr_graph_left vl vr Al Ar)) =
          Some (Some (option_map inl (switching e)))).
        { replace e with ((forward e).1) by trivial. by rewrite -add_parr_switching. }
        rewrite He map_comp mem_map // map_comp mem_map // map_comp mem_map // in U0.
        intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
    + by rewrite map_cons.
  - move => ? ? ? ? ? ? Hf; clear - Hf.
    specialize (Hf b). contradict Hf; apply /negP.
    rewrite in_cons negb_involutive.
    caseb.
  - move => ? ? ? ? ? Hf; clear - Hf.
    specialize (Hf b). contradict Hf; apply /negP.
    rewrite in_cons negb_involutive.
    caseb.
Qed.

Lemma add_parr_rr (G : graph_left) (vl vr : G) (Al Ar : formula) :
  forall p, supath (switching (G := add_parr_graph_left vl vr Al Ar)) (inr tt) (inr tt) p ->
  p = nil.
Proof.
  intro p; destruct p as [ | (e, b) p]; trivial; unfold supath; cbn.
  move => /andP[/andP[/andP[/eqP w W] /andP[U0 U1]] /norP[/eqP N0 N1]].
  assert (P : supath (switching (G := add_parr_graph_left vl vr Al Ar)) (utarget (e, b)) (inr tt) p)
    by splitb.
  destruct e as [[[e | []] | ] | ], b; try by []; cbn in P.
  all: contradict U0; apply /negP; rewrite negb_involutive.
  all: destruct (add_parr_lrN P) as [Hin | Hin].
  all: apply (map_f (fun e => switching e.1) Hin).
Qed.

Lemma add_parr_to_ll (G : graph_left) (vl vr : G) (Al Ar : formula) :
  forall p u v, supath switching_left u v p ->
  supath (switching_left (G := add_parr_graph_left vl vr Al Ar)) (inl u) (inl v)
    [seq (Some (Some (inl x.1)), x.2) | x <- p].
Proof.
  intro p; induction p as [ | (e, b) p IH]; trivial.
  unfold supath; cbn. move => u v /andP[/andP[/andP[/eqP W0 W1] /andP[U0 U1]] /norP[N0 N1]].
  subst u.
  assert (P : supath switching_left (endpoint b e) v p) by splitb.
  specialize (IH _ _ P). revert IH; move => /andP[/andP[W' U'] N'].
  splitb.
  + rewrite -map_comp (eq_map (add_parr_switching_left _ _ _ _) p).
    assert (Hs : switching_left (Some (Some (inl e)) : edge (add_parr_graph_left vl vr Al Ar)) =
      option_map (Some \o Some) (option_map inl (switching_left e))).
    { replace e with ((forward e).1) by trivial. by rewrite -add_parr_switching_left. }
    rewrite Hs map_comp mem_map 1?map_comp 1?mem_map //.
    all: intros [? | ] [? | ]; cbn; move => /eqP H //; cbn in H; apply /eqP; by cbn.
  + assert (Hd := add_parr_switching_left vl vr Al Ar (forward e)).
    revert Hd. move => /eqP Hd. cbn in Hd. revert Hd. move => /eqP ->.
    by destruct (switching_left e).
Qed.

Lemma add_parr_to_lr (G : graph_left) (vl vr : G) (Al Ar : formula) :
  uconnected (switching_left (G := G)) -> forall u, exists _ :
  Supath (switching_left (G := add_parr_graph_left vl vr Al Ar)) (inl u) (inr tt), true.
Proof.
  move => C u.
  destruct (C u vr) as [[p P] _].
  assert (Q := add_parr_to_ll vl vr Al Ar P).
  set q : @upath _ _ (add_parr_graph_left vl vr Al Ar) := [seq (Some (Some (inl x.1)), x.2) | x <- p].
  set qn : @upath _ _ (add_parr_graph_left vl vr Al Ar) := [:: forward None].
  assert (Qn : supath (switching_left (G := add_parr_graph_left vl vr Al Ar)) (inl vr) (inr tt) qn).
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

Lemma add_parr_to_rl (G : graph_left) (vl vr : G) (Al Ar : formula) :
  uconnected (switching_left (G := G)) -> forall v, exists _ :
  Supath (switching_left (G := add_parr_graph_left vl vr Al Ar)) (inr tt) (inl v), true.
Proof.
  intros C u.
  destruct (add_parr_to_lr vl vr Al Ar C u) as [p _].
  by exists (supath_rev p).
Qed.

Lemma add_parr_correct (G : graph_left) (vl vr : G) (Al Ar : formula) :
  correct G -> correct (add_parr_graph_left vl vr Al Ar).
Proof.
  intros [A C]. split.
  - intros [u | []] p; apply /eqP; cbn; apply /eqP.
    + destruct (add_parr_ll (upvalK p)) as [q Q Heq].
      rewrite Heq.
      enough (q = nil) as -> by trivial.
      assert (Hf := A u {| upval := q ; upvalK := Q |}).
      by revert Hf; move => /eqP; cbn; move => /eqP ->.
    + apply (add_parr_rr (upvalK p)).
  - intros [u | []] [v | []].
    + destruct (C u v) as [[p P] _].
      by exists {| upval := [seq (Some (Some (inl x.1)), x.2) | x <- p] : @upath _ _ (add_parr_graph_left vl vr Al Ar) ;
        upvalK := (add_parr_to_ll _ _ _ _ P) |}.
    + by apply add_parr_to_lr.
    + by apply add_parr_to_rl.
    + by exists (supath_nil switching_left (inr tt : add_parr_graph_left vl vr Al Ar)).
Qed.

(* TODO *)
Unset Mangle Names.

Definition extend_edge_graph {Lv Le : Type} (G : graph Lv Le) (e : edge G) (R : Lv) (As At : Le) : graph Lv Le :=
  remove_edges [set Some (Some (inl e)) : edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])].

Lemma extend_edge_None (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  None \notin [set Some (Some (inl e)) : edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])].
Proof. by rewrite !in_set. Qed.

Lemma extend_edge_SomeNone (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  Some None \notin [set Some (Some (inl e)) : edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])].
Proof. by rewrite !in_set. Qed.

Lemma extend_edge_SomeSome (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (a : edge G),
  (Some (Some (inl a)) : edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)]))
  \in [set Some (Some (inl e))] = (a == e).
Proof. intros. by rewrite !in_set. Qed.

Definition extend_edge_left (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  extend_edge_graph e R As At -> edge (extend_edge_graph e R As At) :=
  fun v => match v with
  | inl v => if @boolP (Some (Some (inl (left v))) \notin [set Some (Some (inl e))])
    is AltTrue p then Sub (Some (Some (inl (left v)))) p
    else Sub None (extend_edge_None _ _ _ _)
  | inr v => Sub (Some None) (extend_edge_SomeNone _ _ _ _)
  end.

Definition extend_edge_graph_left (G : graph_left) (e : edge G) (R : rule) (As At : formula) : graph_left := {|
  graph_of := extend_edge_graph e R As At;
  left := @extend_edge_left _ _ _ _ _;
  |}.

Lemma extend_edge_SN (G : graph_left) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) :
  forall u v b In,
  supath switching (inl u : extend_edge_graph_left _ _ _ _) (inl v) ((Sub (Some None) In, b) :: p) ->
  p = (Sub None (extend_edge_None _ _ _ _), b) :: behead p.
Proof.
  unfold supath; cbn => u v [] In //= /andP[/andP[/andP[/eqP-? W] /andP[U _]] _]; subst u.
  destruct p as [ | ([[[[f | []] | ] | ] F], c) p]; try by [].
  - contradict U; apply /negP; rewrite negb_involutive; cbn.
    rewrite in_cons. replace F with In by apply eq_irrelevance. caseb.
  - destruct c; [ | by []]; cbn.
    by replace F with (extend_edge_None e R As At) by apply eq_irrelevance.
Qed.

Lemma extend_edge_N (G : graph_left) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) :
  forall u v b In,
  supath switching (inl u : extend_edge_graph_left _ _ _ _) (inl v) ((Sub None In, b) :: p) ->
  p = (Sub (Some None) (extend_edge_SomeNone _ _ _ _), b) :: behead p.
Proof.
  unfold supath; cbn => u v [] In //= /andP[/andP[/andP[/eqP-? W] /andP[U _]] _]; subst u.
  destruct p as [ | ([[[[f | []] | ] | ] F], c) p]; try by [].
  - destruct c; [by [] | ]; cbn.
    by replace F with (extend_edge_SomeNone e R As At) by apply eq_irrelevance.
  - contradict U; apply /negP; rewrite negb_involutive; cbn.
    rewrite in_cons. replace F with In by apply eq_irrelevance. caseb.
Qed.

Fixpoint extend_edge_upath (G : graph_left) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) {struct p} : @upath _ _ G :=
  match p with
  | [::] => [::]
  | (exist (Some (Some (inl a))) _, b) :: q => (a, b) :: extend_edge_upath q
  | (exist (Some (Some (inr a))) _, b) :: q => match a with end
  | (exist (Some None) _, b) :: q => extend_edge_upath q
  | (exist None _, b) :: q => (e, b) :: extend_edge_upath q
  end.

Lemma extend_edge_uwalk (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) (u v : extend_edge_graph_left e R As At), uwalk u v p ->
  uwalk (match u with | inl u => u | inr _ => source e end) (match v with | inl v => v | inr _ => source e end)
    (extend_edge_upath p).
Proof.
  intro p. induction p as [ | ([[[[f | []] | ] | ] F], c) p IH]; move => u v /=.
  { by move => /eqP-->. }
  all: move => /andP[/eqP-? W]; subst u.
  all: specialize (IH _ _ W).
  all: destruct c; splitb.
Qed.

Lemma extend_edge_upath_in_SomeSome (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) a A b,
  (Sub (Some (Some (inl a))) A, b) \in p = ((a, b) \in extend_edge_upath p).
Proof.
  intros p a A b. induction p as [ | ([[[[f | []] | ] | ] F], c) p IH]; trivial; cbn.
  all: rewrite !in_cons IH //; cbn.
  assert (Hae : a == e = false) by by apply /eqP /eqP; rewrite -(extend_edge_SomeSome _ R As At).
  by rewrite Hae.
Qed.

Lemma extend_edge_uwalk_in_None (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) b,
  (Sub None (extend_edge_None e R As At), b) \in p = ((e, b) \in extend_edge_upath p).
Proof.
  intros p b; induction p as [ | ([[[[a | []] | ] | ] A], c) p H]; trivial; cbn.
  - rewrite !in_cons H; cbn; rewrite SubK; cbn.
    assert (e == a = false) as ->.
    { apply /eqP; apply nesym; apply /eqP. by rewrite -(extend_edge_SomeSome _ R As At). }
    by [].
  - by rewrite !in_cons H; cbn; rewrite SubK eq_refl.
Qed.

Lemma extend_edge_uwalk_in_SomeNone (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall p u v b, supath switching (inl u : extend_edge_graph_left e R As At) (inl v) p ->
  (Sub (Some None) (extend_edge_SomeNone _ _ _ _), b) \in p = ((Sub None (extend_edge_None _ _ _ _), b) \in p).
Proof.
  enough (H : forall n (p : @upath _ _ (extend_edge_graph e R As At)), size p = n -> forall u v b,
    supath switching (inl u : extend_edge_graph_left e R As At) (inl v) p ->
    (Sub (Some None) (extend_edge_SomeNone _ _ _ _), b) \in p = ((Sub None (extend_edge_None _ _ _ _), b) \in p)).
  { intro p. by apply (H (size p)). }
  intro n; induction n as [n Hn] using lt_wf_rect. intros p ? u v b; subst n.
  destruct p as [ | ([[[[a | []] | ] | ] A], c) p]; trivial; cbn.
  - rewrite /supath; cbn; rewrite !in_cons.
    move => /andP[/andP[/andP[/eqP-? W] /andP[_ U]] /norP[_ N]]; subst u.
    assert (P : supath switching (inl (endpoint c a) : extend_edge_graph_left _ _ _ _) (inl v) p)
      by splitb.
    assert (Hs : (size p < (size p).+1)%coq_nat) by lia.
    by rewrite (Hn (size p) Hs p erefl _ _ b P).
  - destruct c; try by [].
    intro P; assert (Hp := extend_edge_SN P); revert P.
    rewrite Hp /supath; cbn; rewrite SubK; cbn; rewrite !in_cons /=; cbn.
    move =>/andP[/andP[/andP[/eqP-? W] /andP[_ /andP[_ U]]] N]; subst u; cbn.
    rewrite !SubK; cbn. f_equal.
    refine (Hn (size (behead p)) _ (behead p) erefl (target e) v b _).
    + rewrite size_behead /=. lia.
    + splitb.
  - destruct c; try by [].
    intro P; assert (Hp := extend_edge_N P); revert P.
    rewrite Hp /supath; cbn; rewrite SubK; cbn; rewrite !in_cons /=; cbn.
    move =>/andP[/andP[/andP[/eqP-? W] /andP[_ /andP[_ U]]] N]; subst u; cbn.
    rewrite !SubK; cbn. f_equal.
    refine (Hn (size (behead p)) _ (behead p) erefl (source e) v b _).
    + rewrite size_behead /=. lia.
    + splitb.
Qed.

Lemma extend_edge_uwalk_in_switching_None (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph_left e R As At)),
  switching (Sub None (extend_edge_None e R As At) : edge (extend_edge_graph_left e R As At))
    \notin [seq switching e0.1 | e0 <- p] ->
  switching e \notin [seq switching e0.1 | e0 <- extend_edge_upath p].
Proof.
  intros p. apply contra => /mapP [[a b] In Eq]. apply /mapP. cbn in Eq.
  destruct (eq_comparable a e) as [ | A]; [subst a | ].
  - exists (Sub None (extend_edge_None e R As At), b); trivial.
    by rewrite extend_edge_uwalk_in_None.
  - revert A => /eqP A. rewrite -(extend_edge_SomeSome _ R As At) in A.
    exists (Sub (Some (Some (inl a))) A, b).
    { by rewrite extend_edge_upath_in_SomeSome. }
    revert Eq => /eqP. unfold switching; cbn.
    case_if; subst; apply /eqP; cbn; rewrite !SubK; cbn.
    + case: {-}_ /boolP => [L | L]; cbn; rewrite !SubK; cbn; case: {-}_ /boolP => [L' | L']; cbn.
      * rewrite !SubK; cbn. by apply /eqP.
      * contradict L'; apply /negP /negPn. by replace (left (target a)) with (left (target e)).
      * contradict L; apply /negP /negPn. by replace (left (target e)) with (left (target a)).
      * rewrite !SubK; cbn. by apply /eqP.
    + assert (Hc : vlabel (target e) = ⅋) by by apply /eqP; cbn; apply /eqP.
      assert (Hc' : vlabel (target (left (target e))) <> ⅋) by by apply /eqP; cbn; apply /negPf /eqP.
      case: {-}_ /boolP => [L | L]; cbn; rewrite !SubK; cbn; trivial.
      revert L; rewrite negb_involutive !in_set; cbn => /eqP L.
      by rewrite L in Hc'.
    + assert (Hc : vlabel (target a) = ⅋) by by apply /eqP; cbn; apply /eqP.
      assert (Hc' : vlabel (target (left (target a))) <> ⅋) by by apply /eqP; cbn; apply /negPf /eqP.
      case: {-}_ /boolP => [L | L]; cbn; rewrite !SubK; cbn; trivial.
      by revert L; rewrite !in_set; cbn => /eqP ?.
    + contradict A; apply /negP /negPn. by rewrite !in_set.
Qed.

Lemma extend_edge_uwalk_uniq (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph_left e R As At)), uniq [seq switching e.1 | e <- p] ->
  uniq [seq switching e.1 | e <- (extend_edge_upath p)].
Proof.
  intro p; induction p as [ | ([[[[a | []] | ] | ] A], b) p IH]; trivial; cbn;
  move => /andP[In U]; splitb; try by apply IH.
  - revert In; clear. apply contra => /mapP [[f c] In Eq]. apply /mapP. cbn in Eq.
    destruct (eq_comparable f e) as [ | F]; [subst f | ].
    + exists (Sub None (extend_edge_None e R As At), c).
      { by rewrite extend_edge_uwalk_in_None. }
      revert Eq => /eqP. unfold switching; cbn.
      case_if; subst; apply /eqP; cbn; rewrite SubK; cbn.
      * case: {-}_ /boolP => [Hc | ?]; cbn.
        { contradict Hc. rewrite (extend_edge_SomeSome _ R As At). by apply /negP /negPn. }
        by rewrite !SubK; cbn.
      * case: {-}_ /boolP => [? | Hc]; cbn.
        2:{ contradict Hc. by apply /negP /negPn. }
        by rewrite !SubK; cbn.
      * contradict A. rewrite (extend_edge_SomeSome _ R As At). by apply /negP /negPn.
    + revert F => /eqP F. rewrite -(extend_edge_SomeSome _ R As At) in F.
      exists (Sub (Some (Some (inl f))) F, c).
      { by rewrite extend_edge_upath_in_SomeSome. }
      revert Eq => /eqP. unfold switching; cbn.
      case_if; subst; apply /eqP; cbn.
      * case: {-}_ /boolP => [? | Hc]; cbn.
        2:{ contradict Hc. by apply /negP /negPn. }
        by rewrite !SubK; cbn.
      * rewrite !SubK; cbn.
        case: {-}_ /boolP => [? | Hc]; cbn.
        2:{ contradict Hc. by apply /negP /negPn. }
        by rewrite !SubK; cbn.
      * by rewrite !SubK; cbn.
  - revert In; clear. apply contra => /mapP [[f c] In Eq]. apply /mapP. cbn in Eq.
    destruct (eq_comparable f e) as [ | F]; [subst f | ].
    + exists (Sub None (extend_edge_None e R As At), c).
      { by rewrite extend_edge_uwalk_in_None. }
      revert Eq => /eqP. unfold switching; cbn.
      case_if; subst; by apply /eqP.
    + revert F => /eqP F. rewrite -(extend_edge_SomeSome _ R As At) in F.
      exists (Sub (Some (Some (inl f))) F, c).
      { by rewrite extend_edge_upath_in_SomeSome. }
      revert Eq => /eqP. unfold switching; cbn.
      case_if; subst; apply /eqP; cbn.
      * case: {-}_ /boolP => [? | Hc]; cbn.
        2:{ contradict Hc. by apply /negP /negPn. }
        by rewrite !SubK; cbn.
      * rewrite !SubK; cbn.
        case: {-}_ /boolP => [Hc | ?]; cbn.
        1:{ contradict Hc. apply /negP /negPn. by rewrite !in_set. }
        by rewrite !SubK; cbn.
      * contradict F. apply /negP /negPn. by rewrite !in_set.
Qed.

Lemma extend_edge_supath (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) (u v : extend_edge_graph_left e R As At),
  supath switching u v p ->
  supath switching (match u with | inl u => u | inr _ => source e end)
  (match v with | inl v => v | inr _ => source e end) (extend_edge_upath p).
Proof.
  move => p ? ? /andP[/andP[? ?] ?]. splitb.
  - by apply extend_edge_uwalk.
  - by apply extend_edge_uwalk_uniq.
  - generalize (extend_edge_upath p) as q; clear.
    intro q; by induction q.
Qed.

Lemma extend_edge_uacyclic (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  uacyclic (switching (G := G)) -> uacyclic (switching (G := extend_edge_graph_left e R As At)).
Proof.
  intros A v [p P]. apply /eqP; cbn; apply /eqP.
  specialize (A _ {| upval := extend_edge_upath p ; upvalK := extend_edge_supath P |}).
  revert A => /eqP; cbn => /eqP A.
  destruct v.
  - destruct p as [ | ([[[[? | []] | ] | ] ?], ?) ?]; try by [].
    contradict A.
    by rewrite (extend_edge_SN P).
  - destruct p as [ | ([[[[? | []] | ] | ] A0], []) [ | ([[[[? | []] | ] | ] A1], []) p]]; try by [].
    clear - P; exfalso. revert P; rewrite /supath !in_cons => /andP[/andP[_ /andP[/norP[In _] _]] _].
    contradict In; apply /negP /negPn.
    by replace A0 with A1 by apply eq_irrelevance.
Qed.


(* TODO ça compile ................................ et mon ordi crash
Fixpoint extend_edge_upath' (G : base_graph) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ G) {struct p} : @upath _ _ (extend_edge_graph e R As At) :=
  match p with
  | [::] => [::]
  | (a, b) :: q =>
    (if @boolP (Some (Some (inl a)) \notin [set Some (Some (inl e))]) is AltTrue p then (Sub (Some (Some (inl a))) p, b) :: nil
    else if b then (Sub (Some None) (extend_edge_SomeNone _ _ _ _), b) :: (Sub None (extend_edge_None _ _ _ _), b) :: nil
    else (Sub None (extend_edge_None _ _ _ _), b) :: (Sub (Some None) (extend_edge_SomeNone _ _ _ _), b) :: nil)
    ++ extend_edge_upath' _ _ _ _ q
  end.
*)

(* TODO equiv des lemmes d'avant avec = si possible plutot que -> *)

End Atoms.
