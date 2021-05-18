(* Basic operations respecting correctness *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
From mathcomp Require Import all_ssreflect zify.
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export graph_more mll_prelim mll_def.

Import EqNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Section Atoms.

(** A set of atoms for building formulas *)
Context { atom : DecType }.
Notation formula := (@formula atom).
Notation base_graph := (graph (flat rule) (flat formula)).
Notation graph_left := (@graph_left atom).
Notation graph_data := (@graph_data atom).
Notation geos := (@geos atom).
Notation proof_structure := (@proof_structure atom).
Notation proof_net := (@proof_net atom).
Infix "≃l" := iso_left (at level 79).

(*
(** * Axiom - cut reduction *)
Definition red_ax_graph_1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : base_graph :=
  G ∔ [source (other_cut Hcut) , dual (elabel e) , target (other_ax Hax)].

Definition red_ax_graph (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : base_graph :=
  induced ([set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e)).

Lemma red_ax_degenerate_source (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  source e = source (other_cut Hcut) <-> other_cut Hcut = other_ax Hax.
Proof.
  split; intro H.
  - apply other_ax_eq.
    rewrite H. splitb.
    apply /eqP; apply other_cut_in_neq.
  - rewrite H.
    by destruct (other_ax_in_neq Hax) as [-> _].
Qed.

Lemma red_ax_degenerate_target (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  target e = target (other_ax Hax) <-> other_cut Hcut = other_ax Hax.
Proof.
  split; intro H.
  - symmetry; apply other_cut_eq.
    rewrite H. splitb.
    apply /eqP; apply other_ax_in_neq.
  - rewrite -H.
    by destruct (other_cut_in_neq Hcut) as [-> _].
Qed.

Lemma red_ax_degenerate_None (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  None \notin edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)
  <-> other_cut Hcut = other_ax Hax.
Proof.
  rewrite !in_set; cbn. split.
  - move => /nandP[/nandP[/negPn /eqP H | /nandP[/negPn /eqP H | //]]
                 | /nandP[/negPn /eqP H | /nandP[/negPn /eqP H | //]]].
    + assert (Hf := p_deg_out (target e)).
      rewrite Hcut in Hf; cbn in Hf.
      assert (Hdone : other_cut Hcut \in set0) by by rewrite -(cards0_eq Hf) in_set H.
      contradict Hdone; by rewrite in_set.
    + by apply red_ax_degenerate_source.
    + by apply red_ax_degenerate_target.
    + assert (Hf := p_deg_in (source e)).
      rewrite Hax in Hf; cbn in Hf.
      assert (Hdone : other_ax Hax \in set0) by by rewrite -(cards0_eq Hf) in_set H.
      contradict Hdone; by rewrite in_set.
    - move => ->.
      destruct (other_ax_in_neq Hax) as [-> _].
      caseb.
Qed.

Definition red_ax_left_1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : red_ax_graph_1 Hcut Hax -> edge (red_ax_graph_1 Hcut Hax) :=
  fun (v : red_ax_graph_1 Hcut Hax) =>
    if (left v == e) || (left v == other_cut Hcut) || (left v == other_ax Hax) then
      if source e == source (other_cut Hcut) then Some (pick_edge_at v)
      else None
    else Some (left v).

Lemma red_ax_consistent_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) :
  let S := [set: red_ax_graph_1 Hcut Hax] :\ (source e) :\ (target e) in
  forall (v : red_ax_graph Hcut Hax), red_ax_left_1 (val v) \in edge_set S.
Proof.
  intros S [v Hv].
  rewrite !in_set /red_ax_left_1; cbn.
  destruct (other_cut_in_neq Hcut) as [Htc Hneqc];
  destruct (other_ax_in_neq Hax) as [Hsa Hneqa].
  assert ((forall a, source a != target e) /\ forall a, target a != source e) as [? ?].
  { split; intro a; apply /eqP => Hc.
    1: assert (Hf := p_deg_out (target e)).
    2: assert (Hf := p_deg_in (source e)).
    all: rewrite ?Hcut ?Hax in Hf; cbn in Hf.
    all: assert (Hf' : a \in set0) by by rewrite -(cards0_eq Hf) in_set Hc.
    all: contradict Hf'; by rewrite in_set. }
  assert (Hm : source e = source (other_cut Hcut) -> forall b b',
    endpoint b (pick_edge_at v) != endpoint b' (other_cut Hcut)).
  { intros Hs b b'; apply /eqP => Hc.
    assert (Hc' : pick_edge_at v \in edges_at_outin b (endpoint b' e)) by
      (destruct b'; by rewrite in_set Hc ?Htc ?Hs).
    destruct (red_ax_degenerate_source Hcut Hax) as [Ho _].
    specialize (Ho Hs).
    contradict Hv; apply /negP.
    assert (Hvin := pick_edge_at_some v).
    revert Hvin; rewrite !in_set; move => /orP[/eqP Heq | /eqP Heq];
    destruct b, b';
    apply /nandP; rewrite andb_true_r !negb_involutive.
    all: try (contradict Hc'; apply /negP; by rewrite in_set).
    all: revert Hc'; rewrite ?other_cut_set ?other_ax_set !in_set; move => /orP[/eqP Hd | /eqP Hd];
      rewrite -Heq Hd ?Hs -?Htc ?Ho; caseb. }
  assert (Hm2 : source e <> source (other_cut Hcut) -> target (other_ax Hax) != target e).
  { intro Hs; apply /eqP => Hc.
    enough (Hdone : other_cut Hcut = other_ax Hax) by by rewrite Hdone Hsa in Hs.
    assert (Hm2 : other_ax Hax \in edges_at_in (target e)) by by rewrite in_set Hc.
    revert Hm2; rewrite other_cut_set !in_set; move => /orP[/eqP Hd | /eqP Hd //].
    contradict Hd; apply /eqP; apply other_ax_in_neq. }
  splitb; case_if.
  all: try (apply /eqP; by apply nesym).
  all: try (rewrite -?Htc; by apply Hm).
  all: try by apply Hm2.
  - apply /eqP => Hc.
    assert (Hf : left v \in edges_at_out (source e)) by by rewrite in_set Hc.
    contradict Hf; apply /negP.
    rewrite other_ax_set !in_set.
    splitb; by apply /eqP.
  - apply /eqP => Hc.
    assert (Hf : left v \in edges_at_in (target e)) by by rewrite in_set Hc.
    contradict Hf; apply /negP.
    rewrite other_cut_set !in_set.
    splitb; by apply /eqP.
Qed. (* TODO essayer de simplifier (ça et les autres preuves de cette partie red) *)

Definition red_ax_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : red_ax_graph Hcut Hax -> edge (red_ax_graph Hcut Hax) :=
  fun v => Sub (red_ax_left_1 (val v)) (red_ax_consistent_left v).

Definition red_ax_graph_left (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax) : graph_left := {|
  graph_of := red_ax_graph Hcut Hax;
  left := @red_ax_left _ _ _ _;
  |}.


Definition invert_edge_graph {Lv Le : Type} (G : graph Lv Le) (e : edge G) : graph Lv Le :=
  {| vertex := vertex G;
     edge := edge G;
     endpoint b := fun a => if a == e then endpoint (~~b) a else endpoint b a;
     vlabel := @vlabel _ _ G;
     elabel := @elabel _ _ G;
  |}.

Definition invert_edge_graph_left (G : graph_left) (e : edge G) : graph_left := {|
  graph_of := invert_edge_graph e;
  left := @left _ G;
  |}.

(*****************************************Previous def below***************************************************)
(** Put a vertex in the middle of an edge *)
Definition extend_edge_graph {Lv Le : Type} (G : graph Lv Le) (e : edge G) (R : Lv) (As At : Le) : graph Lv Le :=
  remove_edges [set Some (Some (inl e)) : edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])].

Lemma extend_edge_None {Lv Le : Type} (G : graph Lv Le) (e : edge G) (R : Lv) (As At : Le) :
  None \notin [set Some (Some (inl e)) : edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])].
Proof. by rewrite !in_set. Qed.

Lemma extend_edge_SomeNone {Lv Le : Type} (G : graph Lv Le) (e : edge G) (R : Lv) (As At : Le) :
  Some None \notin [set Some (Some (inl e)) : edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])].
Proof. by rewrite !in_set. Qed.

Lemma extend_edge_SomeSome {Lv Le : Type} (G : graph Lv Le) (e : edge G) (R : Lv) (As At : Le) :
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
(*
Lemma extend_edge_SN (G : graph_left) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph e R As At)) :
  forall u v b In,
  supath switching (inl u : extend_edge_graph_left _ _ _ _) (inl v) ((Sub (Some None) In, b) :: p) ->
  p = (Sub None (extend_edge_None _ _ _ _), b) :: behead p.
Proof.
  unfold supath; cbn => u v [] In //= /andP[/andP[/andP[/eqP-? W] /andP[U _]] _]; subst u.
  destruct p as [ | ([[[[f | []] | ] | ] F], c) p]; try by [].
  - contradict U; apply /negP/negPn; cbn.
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
  - contradict U; apply /negP/negPn; cbn.
    rewrite in_cons. replace F with In by apply eq_irrelevance. caseb.
Qed.


Fixpoint extend_edge_upath_fwd (G : graph_left) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ G) {struct p} : @upath _ _ (extend_edge_graph_left e R As At) :=
  match p with
  | [::] => [::]
  | (a, b) :: q =>
    (if @boolP (Some (Some (inl a)) \notin [set Some (Some (inl e)) : edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])])
    is AltTrue p then (Sub (Some (Some (inl a))) p, b) :: nil
    else if b then (Sub (Some None) (extend_edge_SomeNone _ _ _ _), b) :: (Sub None (extend_edge_None _ _ _ _), b) :: nil
    else (Sub None (extend_edge_None e R As At), b) :: (Sub (Some None) (extend_edge_SomeNone e R As At), b) :: nil)
    ++ extend_edge_upath_fwd e R As At q
  end.

Lemma extend_edge_uwalk_fwd (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall p (u v : G),
  uwalk (inl u : extend_edge_graph_left e R As At) (inl v) (extend_edge_upath_fwd _ _ _ _ p) = uwalk u v p.
Proof.
  intro p. induction p as [ | (a, b) p IH]; move => u v //=.
  case: {-}_ /boolP => [A | Eq]; cbn.
  - by rewrite SubK IH.
  - rewrite (extend_edge_SomeSome e R As At) in Eq.
    revert Eq => /negPn /eqP ->.
    destruct b; cbn; by rewrite !SubK IH.
Qed.

Lemma extend_edge_upath_fwd_in_SomeSome (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall p a A b,
  (Sub (Some (Some (inl a))) A, b) \in (extend_edge_upath_fwd e R As At p) = ((a, b) \in p).
Proof.
  intros p a A b. induction p as [ | (f, c) p IH]; trivial; cbn.
  rewrite mem_cat in_cons IH {IH}. f_equal.
  case: {-}_ /boolP => [F | Eq]; cbn.
  - by rewrite !in_cons orb_false_r.
  - rewrite (extend_edge_SomeSome e R As At) in Eq.
    revert Eq => /negPn /eqP ->.
    assert (Hae : a == e = false) by by rewrite (extend_edge_SomeSome e R As At) in A; by apply /eqP /eqP.
    rewrite Hae {Hae}.
    by destruct c.
Qed.

Lemma extend_edge_upath_fwd_in_SomeNone (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall p b,
  (Sub (Some None) (extend_edge_SomeNone _ _ _ _), b) \in (extend_edge_upath_fwd e R As At p) = ((e, b) \in p).
Proof.
  intros p b. induction p as [ | (f, c) p IH]; trivial; cbn.
  rewrite mem_cat in_cons IH {IH}. f_equal.
  case: {-}_ /boolP => [F | Eq]; cbn.
  - rewrite !in_cons; cbn; rewrite !SubK; cbn.
    rewrite (extend_edge_SomeSome e R As At) in F.
    by revert F => /eqP F; apply nesym in F; revert F => /eqP /negPf ->.
  - rewrite (extend_edge_SomeSome e R As At) in Eq.
    revert Eq => /negPn /eqP ->.
    by destruct c; rewrite eq_refl !in_cons orb_false_r.
Qed.

Lemma extend_edge_upath_fwd_in_None (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall p b,
  (Sub None (extend_edge_None _ _ _ _), b) \in (extend_edge_upath_fwd e R As At p) = ((e, b) \in p).
Proof.
  intros p b. induction p as [ | (f, c) p IH]; trivial; cbn.
  rewrite mem_cat in_cons IH {IH}. f_equal.
  case: {-}_ /boolP => [F | Eq]; cbn.
  - rewrite !in_cons; cbn; rewrite !SubK; cbn.
    rewrite (extend_edge_SomeSome e R As At) in F.
    by revert F => /eqP F; apply nesym in F; revert F => /eqP /negPf ->.
  - rewrite (extend_edge_SomeSome e R As At) in Eq.
    revert Eq => /negPn /eqP ->.
    by destruct c; rewrite eq_refl !in_cons orb_false_r.
Qed. (* proof exactly the same as for SomeNone ... *)

(* Tactic to make cases on switching or switching_left in this graph *)
Ltac extend_edge_switching_case e R As At :=
  unfold switching, switching_left; cbnb;
  repeat (case: ifP); cbnb;
  repeat (let L := fresh "L" in
    case: {-}_ /boolP => [L | /negPn L]; cbnb;
    rewrite (extend_edge_SomeSome e R As At) in L; revert L => /eqP L;
    symmetry in L || apply nesym in L);
  repeat (move => /eqP ? //); apply /eqP; subst; try done.

Lemma extend_edge_upath_fwd_uniq (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall p,
  uniq [seq switching e.1 | e <- (extend_edge_upath_fwd e R As At p)] = uniq [seq switching e.1 | e <- p].
Proof.
  intro p; induction p as [ | (a, b) p IH]; trivial; cbn.
  rewrite map_cat cat_uniq andb_assoc IH {IH}. f_equal.
  case: {-}_ /boolP => [A | Eq]; cbn.
  - assert (a <> e) by by apply /eqP; rewrite -(extend_edge_SomeSome e R As At).
    rewrite {b} has_sym /= orb_false_r. f_equal.
    remember (switching a \in [seq switching e0.1 | e0 <- p]) as b eqn:Hb.
    revert Hb; case: b => Hb; symmetry in Hb; rewrite Hb; revert Hb.
    + move => /mapP [[f c] In Eq]; apply /mapP.
      destruct (eq_comparable f e); [subst f | ].
      * rewrite -(extend_edge_upath_fwd_in_None _ R As At) in In.
        exists (Sub None (extend_edge_None e R As At), c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
        -- by replace (left (target a)) with (left (target e)) in *.
        -- by replace (left (target e)) with e in *.
      * assert (F : Some (Some (inl f)) \notin [set Some (Some (inl e)) :
          edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])])
          by by rewrite extend_edge_SomeSome //; apply /eqP.
        rewrite -(extend_edge_upath_fwd_in_SomeSome _ F) in In.
        exists (Sub (Some (Some (inl f))) F, c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
        by replace (left (target a)) with (left (target f)) in *.
    + move => /negP /negP In; apply /negP /negP; revert In; apply contra.
      move => /mapP [[[[[[f | []] | ] | ] F] c] In Eq]; apply /mapP.
      * assert (f <> e) by by apply /eqP; rewrite -(extend_edge_SomeSome e R As At).
        rewrite extend_edge_upath_fwd_in_SomeSome in In.
        exists (f, c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
      * contradict Eq; apply /eqP; extend_edge_switching_case e R As At.
      * assert (F = extend_edge_None e R As At) by by apply eq_irrelevance. subst F.
        rewrite extend_edge_upath_fwd_in_None in In.
        exists (e, c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
  - rewrite (extend_edge_SomeSome e R As At) in Eq. revert Eq => /negPn /eqP ?; subst a.
    wlog: b / b = true.
    { move => /(_ true erefl) <-. destruct b; trivial.
      rewrite /= !in_cons !orb_false_r eq_sym. f_equal.
      by rewrite has_sym /= has_sym /= !negb_or !andb_assoc !andb_true_r andb_comm. }
    move => -> {b}.
    rewrite /= !in_cons has_sym orb_false_r.
    assert (Ht : switching (Sub (Some None) (extend_edge_SomeNone _ _ _ _) : edge (extend_edge_graph_left e R As At))
      != switching (Sub None (extend_edge_None _ _ _ _) : edge (extend_edge_graph_left e R As At)))
      by extend_edge_switching_case e R As At.
    rewrite Ht {Ht} /= orb_false_r !negb_or /=.
    assert (Ht : switching (Sub None (extend_edge_None e R As At) : edge (extend_edge_graph_left e R As At))
      \notin [seq switching e0.1 | e0 <- extend_edge_upath_fwd e R As At p] ->
      switching (Sub (Some None) (extend_edge_SomeNone e R As At) : edge (extend_edge_graph_left e R As At))
      \notin [seq switching e0.1 | e0 <- extend_edge_upath_fwd e R As At p]).
    { apply contra => /mapP [[[[[[f | []] | ] | ] F] c] In Eq]; apply /mapP.
      - contradict Eq; apply /eqP. extend_edge_switching_case e R As At.
      - assert (F = extend_edge_SomeNone e R As At) by apply eq_irrelevance. subst F.
        rewrite extend_edge_upath_fwd_in_SomeNone -(extend_edge_upath_fwd_in_None e R As At) in In.
        by exists (Sub None (extend_edge_None e R As At), c).
      - assert (F = extend_edge_None e R As At) by apply eq_irrelevance. subst F.
        by exists (Sub None (extend_edge_None e R As At), c). }
    rewrite (andb_idl Ht) {Ht}. f_equal.
    remember (switching e \in [seq switching e0.1 | e0 <- p]) as b eqn:Hb.
    revert Hb; case: b => Hb; symmetry in Hb; rewrite Hb; revert Hb.
    + move => /mapP [[f c] In Eq]; apply /mapP.
      destruct (eq_comparable f e); [subst f | ].
      * rewrite -(extend_edge_upath_fwd_in_None _ R As At) in In.
        by exists (Sub None (extend_edge_None e R As At), c).
      * assert (F : Some (Some (inl f)) \notin [set Some (Some (inl e)) :
          edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])])
          by by rewrite extend_edge_SomeSome //; apply /eqP.
        rewrite -(extend_edge_upath_fwd_in_SomeSome _ F) in In.
        exists (Sub (Some (Some (inl f))) F, c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
        -- by replace (left (target (left (target f)))) with (left (target f)) in *.
        -- by replace (left (target e)) with (left (target f)) in *.
        -- by replace (left (target e)) with e in *.
    + move => /negP /negP In; apply /negP /negP; revert In; apply contra.
      move => /mapP [[[[[[f | []] | ] | ] F] c] In Eq]; apply /mapP.
      * rewrite extend_edge_upath_fwd_in_SomeSome in In.
        exists (f, c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
      * assert (F = extend_edge_SomeNone e R As At) by apply eq_irrelevance. subst F.
        rewrite extend_edge_upath_fwd_in_SomeNone in In.
        by exists (e, c).
      * assert (F = extend_edge_None e R As At) by apply eq_irrelevance. subst F.
        rewrite extend_edge_upath_fwd_in_None in In.
        by exists (e, c).
Qed.

Lemma extend_edge_supath_fwd (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall p u v,
  supath switching (inl u : extend_edge_graph_left e R As At) (inl v) (extend_edge_upath_fwd _ _ _ _ p) =
  supath switching u v p.
Proof. intros. by rewrite /supath extend_edge_uwalk_fwd extend_edge_upath_fwd_uniq !switching_None. Qed.

Lemma extend_edge_upath_fwd_uniq_l (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  R <> ⅋ -> forall p,
  uniq [seq switching_left e.1 | e <- (extend_edge_upath_fwd e R As At p)] = uniq [seq switching_left e.1 | e <- p].
Proof.
  intros HR p; induction p as [ | (a, b) p IH]; trivial; cbn.
  rewrite map_cat cat_uniq andb_assoc IH {IH}. f_equal.
  case: {-}_ /boolP => [A | Eq]; cbn.
  - assert (a <> e) by by apply /eqP; rewrite -(extend_edge_SomeSome e R As At).
    rewrite {b} has_sym /= orb_false_r. f_equal.
    remember (switching_left a \in [seq switching_left e0.1 | e0 <- p]) as b eqn:Hb.
    revert Hb; case: b => Hb; symmetry in Hb; rewrite Hb; revert Hb.
    + move => /mapP [[f c] In Eq]; apply /mapP.
      destruct (eq_comparable f e); [subst f | ].
      * rewrite -(extend_edge_upath_fwd_in_None _ R As At) in In.
        exists (Sub None (extend_edge_None e R As At), c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
      * assert (F : Some (Some (inl f)) \notin [set Some (Some (inl e)) :
          edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])])
          by by rewrite extend_edge_SomeSome //; apply /eqP.
        rewrite -(extend_edge_upath_fwd_in_SomeSome _ F) in In.
        exists (Sub (Some (Some (inl f))) F, c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
    + move => /negP /negP In; apply /negP /negP; revert In; apply contra.
      move => /mapP [[[[[[f | []] | ] | ] F] c] In Eq]; apply /mapP.
      * assert (f <> e) by by apply /eqP; rewrite -(extend_edge_SomeSome e R As At).
        rewrite extend_edge_upath_fwd_in_SomeSome in In.
        exists (f, c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
      * contradict Eq; apply /eqP; extend_edge_switching_case e R As At.
        by destruct R.
      * assert (F = extend_edge_None e R As At) by by apply eq_irrelevance. subst F.
        rewrite extend_edge_upath_fwd_in_None in In.
        exists (e, c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
  - rewrite (extend_edge_SomeSome e R As At) in Eq. revert Eq => /negPn /eqP ?; subst a.
    wlog: b / b = true.
    { move => /(_ true erefl) <-. destruct b; trivial.
      rewrite /= !in_cons !orb_false_r eq_sym. f_equal.
      by rewrite has_sym /= has_sym /= !negb_or !andb_assoc !andb_true_r andb_comm. }
    move => -> {b}.
    rewrite /= !in_cons has_sym orb_false_r.
    assert (Ht : switching_left (Sub (Some None) (extend_edge_SomeNone _ _ _ _) : edge (extend_edge_graph_left e R As At))
      != switching_left (Sub None (extend_edge_None _ _ _ _) : edge (extend_edge_graph_left e R As At))).
      { extend_edge_switching_case e R As At. by destruct R. }
    rewrite Ht {Ht} /= orb_false_r !negb_or /=.
    assert (Ht : switching_left (Sub None (extend_edge_None e R As At) : edge (extend_edge_graph_left e R As At))
      \notin [seq switching_left e0.1 | e0 <- extend_edge_upath_fwd e R As At p] ->
      switching_left (Sub (Some None) (extend_edge_SomeNone e R As At) : edge (extend_edge_graph_left e R As At))
      \notin [seq switching_left e0.1 | e0 <- extend_edge_upath_fwd e R As At p]).
    { apply contra => /mapP [[[[[[f | []] | ] | ] F] c] In Eq]; apply /mapP.
      - contradict Eq; apply /eqP. extend_edge_switching_case e R As At. by destruct R.
      - assert (F = extend_edge_SomeNone e R As At) by apply eq_irrelevance. subst F.
        rewrite extend_edge_upath_fwd_in_SomeNone -(extend_edge_upath_fwd_in_None e R As At) in In.
        by exists (Sub None (extend_edge_None e R As At), c).
      - assert (F = extend_edge_None e R As At) by apply eq_irrelevance. subst F.
        by exists (Sub None (extend_edge_None e R As At), c). }
    rewrite (andb_idl Ht) {Ht}. f_equal.
    remember (switching_left e \in [seq switching_left e0.1 | e0 <- p]) as b eqn:Hb.
    revert Hb; case: b => Hb; symmetry in Hb; rewrite Hb; revert Hb.
    + move => /mapP [[f c] In Eq]; apply /mapP.
      destruct (eq_comparable f e); [subst f | ].
      * rewrite -(extend_edge_upath_fwd_in_None _ R As At) in In.
        by exists (Sub None (extend_edge_None e R As At), c).
      * assert (F : Some (Some (inl f)) \notin [set Some (Some (inl e)) :
          edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])])
          by by rewrite extend_edge_SomeSome //; apply /eqP.
        rewrite -(extend_edge_upath_fwd_in_SomeSome _ F) in In.
        exists (Sub (Some (Some (inl f))) F, c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
        all: by replace (left (target f)) with f in *.
    + move => /negP /negP In; apply /negP /negP; revert In; apply contra.
      move => /mapP [[[[[[f | []] | ] | ] F] c] In Eq]; apply /mapP.
      * rewrite extend_edge_upath_fwd_in_SomeSome in In.
        exists (f, c); trivial; cbn.
        apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
      * assert (F = extend_edge_SomeNone e R As At) by apply eq_irrelevance. subst F.
        rewrite extend_edge_upath_fwd_in_SomeNone in In.
        by exists (e, c).
      * assert (F = extend_edge_None e R As At) by apply eq_irrelevance. subst F.
        rewrite extend_edge_upath_fwd_in_None in In.
        by exists (e, c).
Qed.

Lemma extend_edge_upath_fwd_N (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  R <> ⅋ -> forall p,
  None \notin [seq switching_left e0.1 | e0 <- extend_edge_upath_fwd e R As At p] =
  (None \notin [seq switching_left e0.1 | e0 <- p]).
Proof.
  intros HR p; induction p as [ | (a, b) p IH]; trivial; cbn.
  rewrite in_cons map_cat mem_cat !negb_or IH {IH}. f_equal.
  case: {-}_ /boolP => [A | Eq]; cbn.
  - assert (a <> e) by by apply /eqP; rewrite -(extend_edge_SomeSome e R As At).
    rewrite {b} !in_cons in_nil /= orb_false_r. f_equal.
    remember (opt_eq None (switching_left a)) as b eqn:Hb.
    revert Hb; case: b => Hb; symmetry in Hb; rewrite Hb; revert Hb;
    extend_edge_switching_case e R As At.
  - rewrite (extend_edge_SomeSome e R As At) in Eq. revert Eq => /negPn /eqP ?; subst a.
    wlog: b / b = true.
    { move => /(_ true erefl) <-. destruct b; trivial.
      by rewrite !in_cons !orb_false_r orb_comm. }
    move => -> {b}.
    rewrite /= !in_cons !orb_false_r. f_equal.
    remember (opt_eq None (switching_left e)) as b eqn:Hb.
    revert Hb; case: b => Hb; symmetry in Hb; rewrite Hb; revert Hb;
    extend_edge_switching_case e R As At.
    all: by destruct R.
Qed.

Lemma extend_edge_supath_fwd_l (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  R <> ⅋ -> forall p u v,
  supath switching_left (inl u : extend_edge_graph_left e R As At) (inl v) (extend_edge_upath_fwd _ _ _ _ p) =
  supath switching_left u v p.
Proof. intros. by rewrite /supath extend_edge_uwalk_fwd extend_edge_upath_fwd_uniq_l // extend_edge_upath_fwd_N. Qed.

Fixpoint extend_edge_upath_bwd (G : graph_left) (e : edge G) (R : rule) (As At : formula)
  (p : @upath _ _ (extend_edge_graph_left e R As At)) {struct p} : @upath _ _ G :=
  match p with
  | [::] => [::]
  | (exist (Some (Some (inl a))) _, b) :: q => (a, b) :: extend_edge_upath_bwd q
  | (exist (Some (Some (inr a))) _, b) :: q => match a with end
  | (exist (Some None) _, b) :: q => extend_edge_upath_bwd q
  | (exist None _, b) :: q => (e, b) :: extend_edge_upath_bwd q
  end.

Lemma extend_edge_uwalk_bwd (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) (u v : extend_edge_graph_left e R As At),
  uwalk u v p ->
  uwalk (match u with | inl u => u | inr _ => source e end)
  (match v with | inl v => v | inr _ => source e end) (extend_edge_upath_bwd p).
Proof.
  intro p. induction p as [ | ([[[[f | []] | ] | ] F], c) p IH]; move => u v /=.
  { by move => /eqP-->. }
  all: move => /andP[/eqP-? W]; subst u.
  all: specialize (IH _ _ W).
  all: destruct c; splitb.
Qed.

Lemma extend_edge_upath_bwd_in_SomeSome (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) a A b,
  (Sub (Some (Some (inl a))) A, b) \in p = ((a, b) \in extend_edge_upath_bwd p).
Proof.
  intros p a A b. induction p as [ | ([[[[f | []] | ] | ] F], c) p IH]; trivial; cbn.
  all: rewrite !in_cons IH //; cbn.
  assert (Hae : a == e = false) by by apply /eqP /eqP; rewrite -(extend_edge_SomeSome _ R As At).
  by rewrite Hae.
Qed.

Lemma extend_edge_upath_bwd_in_None (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) b,
  (Sub None (extend_edge_None e R As At), b) \in p = ((e, b) \in extend_edge_upath_bwd p).
Proof.
  intros p b; induction p as [ | ([[[[a | []] | ] | ] A], c) p H]; trivial; cbn.
  - rewrite !in_cons H; cbn; rewrite SubK; cbn.
    enough (e == a = false) as -> by by [].
    apply /eqP; apply nesym; apply /eqP. by rewrite -(extend_edge_SomeSome _ R As At).
  - by rewrite !in_cons H; cbn; rewrite SubK eq_refl.
Qed.

Lemma extend_edge_upath_bwd_uniq (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph_left e R As At)), uniq [seq switching e.1 | e <- p] ->
  uniq [seq switching e.1 | e <- (extend_edge_upath_bwd p)].
Proof.
  intro p; induction p as [ | ([[[[a | []] | ] | ] A], b) p IH]; trivial; cbn;
  move => /andP[In U]; splitb; try by apply IH.
  - revert In; clear.
    assert (a <> e) by by apply /eqP; rewrite -(extend_edge_SomeSome e R As At).
    apply contra => /mapP [[f c] In Eq]; apply /mapP.
    destruct (eq_comparable f e); [subst f | ].
    + exists (Sub None (extend_edge_None e R As At), c).
      { by rewrite extend_edge_upath_bwd_in_None. }
      apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
      * by replace (left (target a)) with (left (target e)) in *.
      * by replace (left (target e)) with e in *.
    + assert (F : Some (Some (inl f)) \notin [set Some (Some (inl e)) :
        edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])])
        by by rewrite extend_edge_SomeSome //; apply /eqP.
      exists (Sub (Some (Some (inl f))) F, c).
      { by rewrite extend_edge_upath_bwd_in_SomeSome. }
      apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
      * by replace (left (target a)) with (left (target f)) in *.
  - revert In; clear. apply contra => /mapP [[f c] In Eq]; apply /mapP.
    destruct (eq_comparable f e); [subst f | ].
    + exists (Sub None (extend_edge_None e R As At), c).
      { by rewrite extend_edge_upath_bwd_in_None. }
      apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
    + assert (F : Some (Some (inl f)) \notin [set Some (Some (inl e)) :
        edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])])
        by by rewrite extend_edge_SomeSome //; apply /eqP.
      exists (Sub (Some (Some (inl f))) F, c).
      { by rewrite extend_edge_upath_bwd_in_SomeSome. }
      apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
      * by replace (left (target (left (target f)))) with (left (target f)) in *.
      * by replace (left (target f)) with (left (target e)) in *.
      * by replace (left (target e)) with e in *.
Qed.

Lemma extend_edge_supath_bwd (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) (u v : extend_edge_graph_left e R As At),
  supath switching u v p ->
  supath switching (match u with | inl u => u | inr _ => source e end)
  (match v with | inl v => v | inr _ => source e end) (extend_edge_upath_bwd p).
Proof.
  move => p ? ? /andP[/andP[? ?] ?]. splitb.
  - by apply extend_edge_uwalk_bwd.
  - by apply extend_edge_upath_bwd_uniq.
  - by rewrite switching_None.
Qed.

Lemma extend_edge_upath_bwd_uniq_l (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph_left e R As At)), uniq [seq switching_left e.1 | e <- p] ->
  uniq [seq switching_left e.1 | e <- (extend_edge_upath_bwd p)].
Proof.
  intro p; induction p as [ | ([[[[a | []] | ] | ] A], b) p IH]; trivial; cbn;
  move => /andP[In U]; splitb; try by apply IH.
  - revert In; clear.
    assert (a <> e) by by apply /eqP; rewrite -(extend_edge_SomeSome e R As At).
    apply contra => /mapP [[f c] In Eq]; apply /mapP.
    destruct (eq_comparable f e); [subst f | ].
    + exists (Sub None (extend_edge_None e R As At), c).
      { by rewrite extend_edge_upath_bwd_in_None. }
      apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
    + assert (F : Some (Some (inl f)) \notin [set Some (Some (inl e)) :
        edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])])
        by by rewrite extend_edge_SomeSome //; apply /eqP.
      exists (Sub (Some (Some (inl f))) F, c).
      { by rewrite extend_edge_upath_bwd_in_SomeSome. }
      apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
  - revert In; clear. apply contra => /mapP [[f c] In Eq]; apply /mapP.
    destruct (eq_comparable f e); [subst f | ].
    + exists (Sub None (extend_edge_None e R As At), c).
      { by rewrite extend_edge_upath_bwd_in_None. }
      apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
    + assert (F : Some (Some (inl f)) \notin [set Some (Some (inl e)) :
        edge (G ∔ R ∔ [inl (source e), As, inr tt] ∔ [inr tt, At, inl (target e)])])
        by by rewrite extend_edge_SomeSome //; apply /eqP.
      exists (Sub (Some (Some (inl f))) F, c).
      { by rewrite extend_edge_upath_bwd_in_SomeSome. }
      apply /eqP; revert Eq => /eqP; extend_edge_switching_case e R As At.
      all: by replace (left (target f)) with f in *.
Qed.

Lemma extend_edge_upath_bwd_N (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph_left e R As At)),
  None \notin [seq switching_left e0.1 | e0 <- p] ->
  None \notin [seq switching_left e0.1 | e0 <- extend_edge_upath_bwd p].
Proof.
  intro p; induction p as [ | ([[[[a | []] | ] | ] A], b) p IH]; trivial; cbn.
  all: rewrite !in_cons !negb_or => /andP[In ?].
  all: splitb; try by apply IH.
  all: clear - In; revert In.
  all: extend_edge_switching_case e R As At.
  by assert (a <> (left (target a))) by by apply /eqP; rewrite -(extend_edge_SomeSome (left (target a)) R As At).
Qed.

Lemma extend_edge_supath_bwd_l (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  forall (p : @upath _ _ (extend_edge_graph e R As At)) (u v : extend_edge_graph_left e R As At),
  supath switching_left u v p ->
  supath switching_left (match u with | inl u => u | inr _ => source e end)
  (match v with | inl v => v | inr _ => source e end) (extend_edge_upath_bwd p).
Proof.
  move => p ? ? /andP[/andP[? ?] ?]. splitb.
  - by apply extend_edge_uwalk_bwd.
  - by apply extend_edge_upath_bwd_uniq_l.
  - by rewrite extend_edge_upath_bwd_N.
Qed.


Lemma extend_edge_uacyclic_fwd (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  uacyclic (switching (G := extend_edge_graph_left e R As At)) -> uacyclic (switching (G := G)).
Proof.
  intros A v [p P]; apply /eqP; cbn; apply /eqP.
  rewrite -(extend_edge_supath_fwd e R As At) in P.
  specialize (A _ {| upval := extend_edge_upath_fwd e R As At p ; upvalK := P |}).
  revert A => /eqP; cbn => /eqP A.
  destruct p as [ | (a, b) p]; trivial.
  contradict A; cbn. by case: {-}_ /boolP; destruct b.
Qed.

Lemma extend_edge_uconnected_bwd_rl (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  R <> ⅋ -> uconnected (switching_left (G := G)) -> forall v,
  exists _ : Supath switching_left (inr tt : extend_edge_graph_left e R As At) (inl v), true.
Proof.
  intros HR C v.
  destruct (C (source e) v) as [[p P] _].
  apply uconnected_simpl.
  rewrite -(extend_edge_supath_fwd_l e As At HR) in P.
  exists (backward ((Sub (Some None) (extend_edge_SomeNone e R As At))) :: extend_edge_upath_fwd e R As At p).
  revert P; rewrite /supath map_cons in_cons; cbn => /andP[/andP[W _] N].
  splitb. by destruct R.
Qed.

Lemma extend_edge_uconnected_bwd (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  R <> ⅋ -> uconnected (switching_left (G := G)) ->
  uconnected (switching_left (G := extend_edge_graph_left e R As At)).
Proof.
  intros HR C [u | []] [v | []].
  - specialize (C u v). destruct C as [[p P] _].
    rewrite -(extend_edge_supath_fwd_l e As At HR) in P.
    by exists {| upval := _ ; upvalK := P |}.
  - destruct (extend_edge_uconnected_bwd_rl e As At HR C u) as [P _].
    by exists (supath_rev P).
  - destruct (extend_edge_uconnected_bwd_rl e As At HR C v) as [P _].
    by exists P.
  - by exists (supath_nil switching_left (inr tt : extend_edge_graph_left _ _ _ _)).
Qed.

Lemma extend_edge_uacyclic_bwd (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  uacyclic (switching (G := G)) -> uacyclic (switching (G := extend_edge_graph_left e R As At)).
Proof.
  intros A v [p P]. apply /eqP; cbn; apply /eqP.
  specialize (A _ {| upval := extend_edge_upath_bwd p ; upvalK := extend_edge_supath_bwd P |}).
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

Lemma extend_edge_uconnected_fwd (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  uconnected (switching_left (G := extend_edge_graph_left e R As At)) ->
  uconnected (switching_left (G := G)).
Proof.
  intros C u v.
  specialize (C (inl u) (inl v)). destruct C as [[p P] _].
  apply extend_edge_supath_bwd_l in P.
  by exists {| upval := extend_edge_upath_bwd p ; upvalK := P |}.
Qed.

Lemma extend_edge_correct (G : graph_left) (e : edge G) (R : rule) (As At : formula) :
  R <> ⅋ -> correct (extend_edge_graph_left e R As At) <-> correct G.
Proof.
  intro; split; intros [? ?]; split.
  - by apply (@extend_edge_uacyclic_fwd _ e R As At).
  - by apply (@extend_edge_uconnected_fwd _ e R As At).
  - by apply (@extend_edge_uacyclic_bwd _ e R As At).
  - by apply (@extend_edge_uconnected_bwd _ e R As At).
Qed.
*)
Print true.

Definition red_ax_G (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut) (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :=
  @invert_edge_graph_left
  (@extend_edge_graph_left
    (@extend_edge_graph_left (red_ax_graph_left Hcut Hax) (Sub None N) cut (dual (elabel e)) (elabel e))
    (Sub None (extend_edge_None _ _ _ _)) ax (elabel e) (dual (elabel e)))
  (Sub (Some None) (extend_edge_SomeNone _ _ _ _)).

Definition red_ax_iso_v_bij_fwd (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  red_ax_G N -> G :=
  fun v => match v with
  | inl (inl (exist u _)) => u
  | inl (inr tt)          => target e
  | inr tt                => source e
  end.

Definition red_ax_iso_v_bij_bwd (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  G -> red_ax_G N :=
  fun v => if @boolP (v \in [set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)
  is AltTrue p then inl (inl (Sub v p)) else if v == source e then inr tt else inl (inr tt).

Lemma red_ax_iso_v_bijK (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  cancel (@red_ax_iso_v_bij_fwd _ _ _ _ N) (red_ax_iso_v_bij_bwd N).
Proof.
  intros [[[v V] | []] | []]; cbn; unfold red_ax_iso_v_bij_bwd.
  - case: {-}_ /boolP => [? | /negP ? //]. cbnb.
  - case: {-}_ /boolP => [Hc | ?].
    + contradict Hc; apply /negP.
      rewrite !in_set. caseb.
    + case: ifP; trivial.
      clear - Hcut Hax => /eqP H.
      contradict Hcut. by rewrite H Hax.
  - case: {-}_ /boolP => [Hc | ?].
    + contradict Hc; apply /negP.
      rewrite !in_set. caseb.
    + case_if.
Qed.

Lemma red_ax_iso_v_bijK' (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  cancel (red_ax_iso_v_bij_bwd N) (@red_ax_iso_v_bij_fwd _ _ _ _ N).
Proof.
  intro v; unfold red_ax_iso_v_bij_bwd.
  case: {-}_ /boolP => [// | ].
  rewrite !in_set => /nandP[/negPn /eqP ? | /nandP[/negPn /eqP ? | //]]; subst; case_if.
Qed.

Definition red_ax_iso_v (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) := {|
  bij_fwd := @red_ax_iso_v_bij_fwd _ _ _ _ N;
  bij_bwd:= red_ax_iso_v_bij_bwd N;
  bijK:= @red_ax_iso_v_bijK _ _ _ _ _;
  bijK':= red_ax_iso_v_bijK' _;
  |}.

Definition red_ax_iso_e_bij_fwd (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  edge (red_ax_G N) -> edge G :=
  fun a => match a with
  | exist (Some (Some (inl (exist (Some (Some (inl (exist (Some a) _)))) _)))) _ => a
  | exist None _ => other_ax Hax
  | exist (Some (Some (inl (exist (Some None) _)))) _ => other_cut Hcut
  | _ => e (* exist (Some None) _ & Never happening cases *)
  end.

Definition red_ax_iso_e_bij_bwd_helper_a0 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)))
  (a : edge G) (p0 : Some a \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)) :
  Some (Some (inl (Sub (Some a) p0))) \notin
  [set Some (Some (inl (Sub None N : edge (red_ax_graph Hcut Hax)))) : edge (red_ax_graph Hcut Hax ∔ cut ∔
  [inl (source (Sub None N : edge (red_ax_graph Hcut Hax))), dual (elabel e), inr tt] ∔
  [inr tt, elabel e, inl (target (Sub None N : edge (red_ax_graph Hcut Hax)))])].
Proof. by rewrite !in_set. Qed.

Definition red_ax_iso_e_bij_bwd_helper_a1 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)))
  (a : edge G) (p0 : Some a \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)) :
  (Some (Some (inl (Sub (Some (Some (inl (Sub (Some a) p0)))) (red_ax_iso_e_bij_bwd_helper_a0 N p0) : edge
  (@extend_edge_graph _ _ (red_ax_graph Hcut Hax) _ _ _ _))))) \notin
  [set Some (Some (inl (Sub None (extend_edge_None _ _ _ _)))) :
  edge (_ ∔ ax ∔ [inl (source (Sub None (extend_edge_None _ _ _ _) : edge (extend_edge_graph _ _ _ _))), elabel e, inr tt] ∔
  [inr tt, dual (elabel e), inl (target (Sub None (extend_edge_None _ _ _ _) :
  edge (extend_edge_graph (Sub None N : edge (red_ax_graph Hcut Hax)) cut (dual (elabel e)) (elabel e))))])].
Proof. by rewrite !in_set. Qed.

Definition red_ax_iso_e_bij_bwd_helper_a (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)))
  (a : edge G) (p0 : Some a \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)) : edge (red_ax_G N) :=
  Sub (Some (Some (inl (Sub (Some (Some (inl (Sub (Some a) p0)))) (red_ax_iso_e_bij_bwd_helper_a0 N p0) : edge (@extend_edge_graph rule formula (red_ax_graph Hcut Hax)
  (Sub None N) cut (dual (elabel e)) (elabel e))))) : edge ((@extend_edge_graph rule formula (red_ax_graph Hcut Hax)
  (Sub None N) cut (dual (elabel e)) (elabel e)) ∔ ax ∔
  [inl (source (Sub None (extend_edge_None (Sub None N : edge (red_ax_graph Hcut Hax))
  cut (dual (elabel e)) (elabel e)) : edge (extend_edge_graph (Sub None N : edge (red_ax_graph Hcut Hax))
  cut (dual (elabel e)) (elabel e)))), elabel e, inr tt] ∔
  [inr tt, dual (elabel e), inl (target (Sub None (extend_edge_None (Sub None N : edge (red_ax_graph Hcut Hax))
  cut (dual (elabel e)) (elabel e)) : edge (extend_edge_graph (Sub None N : edge (red_ax_graph Hcut Hax)) cut
  (dual (elabel e)) (elabel e))))])) (red_ax_iso_e_bij_bwd_helper_a1 N p0).

Lemma red_ax_iso_e_bij_bwd_helper_ssn0 (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  (Some (Some (inl (Sub (Some None) (extend_edge_SomeNone _ _ _ _) : edge (@extend_edge_graph rule formula (red_ax_graph Hcut Hax)
  (Sub None N) cut (dual (elabel e)) (elabel e))))) : edge ((@extend_edge_graph rule formula (red_ax_graph Hcut Hax)
  (Sub None N) cut (dual (elabel e)) (elabel e)) ∔ ax ∔
  [inl (source (Sub None (extend_edge_None (Sub None N : edge (red_ax_graph Hcut Hax))
  cut (dual (elabel e)) (elabel e)) : edge (extend_edge_graph (Sub None N : edge (red_ax_graph Hcut Hax))
  cut (dual (elabel e)) (elabel e)))), elabel e, inr tt] ∔
  [inr tt, dual (elabel e), inl (target (Sub None (extend_edge_None (Sub None N : edge (red_ax_graph Hcut Hax))
  cut (dual (elabel e)) (elabel e)) : edge (extend_edge_graph (Sub None N : edge (red_ax_graph Hcut Hax)) cut
  (dual (elabel e)) (elabel e))))])) \notin
  [set Some (Some (inl (Sub None (extend_edge_None (Sub None N : edge (red_ax_graph Hcut Hax))
  cut (dual (elabel e)) (elabel e))))) : edge ((@extend_edge_graph rule formula (red_ax_graph Hcut Hax)
  (Sub None N) cut (dual (elabel e)) (elabel e)) ∔ ax ∔
  [inl (source (Sub None (extend_edge_None (Sub None N : edge (red_ax_graph Hcut Hax))
  cut (dual (elabel e)) (elabel e)) : edge (extend_edge_graph (Sub None N : edge (red_ax_graph Hcut Hax))
  cut (dual (elabel e)) (elabel e)))), elabel e, inr tt] ∔
  [inr tt, dual (elabel e), inl (target (Sub None (extend_edge_None (Sub None N : edge (red_ax_graph Hcut Hax))
  cut (dual (elabel e)) (elabel e)) : edge (extend_edge_graph (Sub None N : edge (red_ax_graph Hcut Hax)) cut
  (dual (elabel e)) (elabel e))))])].
Proof. by rewrite !in_set. Qed.

Definition red_ax_iso_e_bij_bwd_helper_ssn (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) : edge (red_ax_G N) :=
  Sub (Some (Some (inl (Sub (Some None) (extend_edge_SomeNone _ _ _ _))))) (red_ax_iso_e_bij_bwd_helper_ssn0 N).

Definition red_ax_iso_e_bij_bwd_helper_sn (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) : edge (red_ax_G N) :=
  Sub (Some None) (extend_edge_SomeNone _ _ _ _).

Definition red_ax_iso_e_bij_bwd_helper_n (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) : edge (red_ax_G N) :=
  Sub None (extend_edge_None _ _ _ _).
(* TODO voir dans les helper ce qu'on peut passer en _ *)

Definition red_ax_iso_e_bij_bwd (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  edge G -> edge (red_ax_G N) :=
  fun a =>
  if @boolP (Some a \in edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e)) is
    AltTrue p0 then red_ax_iso_e_bij_bwd_helper_a N p0
  else
    if a == e then red_ax_iso_e_bij_bwd_helper_sn N
    else if a == other_ax Hax then red_ax_iso_e_bij_bwd_helper_n N
    else red_ax_iso_e_bij_bwd_helper_ssn N.
(* If we do not use these helpers, COQ fails with a Stack overflow. *)

Lemma red_ax_iso_e_bijK (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  cancel (@red_ax_iso_e_bij_fwd _ _ _ _ N) (@red_ax_iso_e_bij_bwd _ _ _ _ N).
Proof.
(*
  intros [[[[[[[[[[a | ] A''] | []] | ] | ] A'] | []] | ] | ] A]; cbn.
  - unfold red_ax_iso_e_bij_bwd. case: {-}_ /boolP => [? | /negP ? //].
    unfold red_ax_iso_e_bij_bwd_helper_a; apply /eqP; by repeat (cbn; rewrite ?SubK).
  - exfalso; clear - A'; contradict A'; apply /negP /negPn.
    by rewrite !in_set.
  - unfold red_ax_iso_e_bij_bwd. case: {-}_ /boolP => [Hc | ?].
    { contradict Hc; apply /negP.
      rewrite !in_set; cbn; destruct (other_cut_in_neq Hcut) as [-> _]. caseb. }
    assert (other_cut Hcut == e = false) as -> by (apply /negP/negP; apply (other_cut_in_neq Hcut)).
    assert (other_cut Hcut == other_ax Hax = false) as ->.
    { apply /eqP => Hc. apply red_ax_degenerate_None in Hc. by contradict Hc; apply /negP/negPn. }
    unfold red_ax_iso_e_bij_bwd_helper_ssn; apply /eqP; by repeat (cbn; rewrite ?SubK).
  - exfalso; clear - A; contradict A; apply /negP /negPn.
    by rewrite !in_set.
  - unfold red_ax_iso_e_bij_bwd. case: {-}_ /boolP => [Hc | ?].
    { contradict Hc; apply /negP.
      rewrite !in_set; cbn. caseb. }
    rewrite eq_refl /red_ax_iso_e_bij_bwd_helper_sn; apply /eqP; by repeat (cbn; rewrite ?SubK).
  - unfold red_ax_iso_e_bij_bwd. case: {-}_ /boolP => [Hc | ?].
    { contradict Hc; apply /negP.
      rewrite !in_set; cbn; destruct (other_ax_in_neq Hax) as [-> _]. caseb. }
    assert (other_ax Hax == e = false) as -> by (apply /negP/negP; apply (other_ax_in_neq Hax)).
    rewrite eq_refl /red_ax_iso_e_bij_bwd_helper_n; apply /eqP; by repeat (cbn; rewrite ?SubK).
Qed. *)
Admitted.

Lemma red_ax_iso_e_bijK' (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  cancel (@red_ax_iso_e_bij_bwd _ _ _ _ N) (@red_ax_iso_e_bij_fwd _ _ _ _ N).
Proof.
  intro a.
  unfold red_ax_iso_e_bij_bwd. case: {-}_ /boolP => [Hc | ?].
  - unfold red_ax_iso_e_bij_bwd_helper_a; apply /eqP; by repeat (cbn; rewrite ?SubK).
  - case_if.
    unfold red_ax_iso_e_bij_bwd_helper_ssn, red_ax_iso_e_bij_fwd; cbv.
    enough (a = other_cut Hcut) as -> by by [].
    assert (Hm : Some a \notin edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e
      :\ target e)) by by [].
    revert Hm; rewrite !in_set /= => /nandP[/nandP[/negPn/eqP Ha | /nandP[/negPn/eqP Ha | //]]
                                          | /nandP[/negPn/eqP Ha | /nandP[/negPn/eqP Ha | //]]].
    + enough (Hf : a \in set0) by (contradict Hf; by rewrite in_set).
      assert (Hc := p_deg_out (target e)).
      rewrite Hcut /= in Hc.
      by rewrite -(cards0_eq Hc) in_set Ha.
    + enough (a = other_ax Hax) by by [].
      by apply other_ax_eq.
    + by apply other_cut_eq.
    + enough (Hf : a \in set0) by (contradict Hf; by rewrite in_set).
      assert (Hc := p_deg_in (source e)).
      rewrite Hax /= in Hc.
      by rewrite -(cards0_eq Hc) in_set Ha.
Qed.

Definition red_ax_iso_e (G : geos) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) := {|
  bij_fwd := @red_ax_iso_e_bij_fwd _ _ _ _ N;
  bij_bwd:= @red_ax_iso_e_bij_bwd _ _ _ _ _;
  bijK:= @red_ax_iso_e_bijK _ _ _ _ _;
  bijK':= red_ax_iso_e_bijK' _;
  |}.

Lemma red_ax_iso_ihom (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
  is_ihom (red_ax_iso_v N) (red_ax_iso_e N) pred0.
Proof.
  split.
  - intros [[[[[[[[[[a | ] A''] | []] | ] | ] A'] | []] | ] | ] A] b; cbn.
    + rewrite !SubK; by apply /eqP; cbn; apply /eqP.
    + clear - A'; contradict A'; apply /negP /negPn.
      by rewrite !in_set.
    + rewrite !SubK; cbn.
      destruct b; trivial.
      by destruct (other_cut_in_neq Hcut) as [-> _].
    + clear - A; contradict A; apply /negP /negPn.
      by rewrite !in_set.
    + rewrite !SubK; cbn.
      by destruct b.
    + rewrite !SubK; cbn.
      destruct b; trivial; cbn.
      by destruct (other_ax_in_neq Hax) as [-> _].
  - by intros [[[? ?] | []] | []].
  - intros [[[[[[[[[[a | ] A''] | []] | ] | ] A'] | []] | ] | ] A]; try by []; cbn.
    + clear - A'; contradict A'; apply /negP /negPn.
      by rewrite !in_set.
    + destruct (proper_ax_cut_bis G) as [_ Hpcut].
      specialize (Hpcut _ Hcut _ (target_in_edges_at_in e)).
      by revert Hpcut => /eqP Hpcut.
    + destruct (proper_ax_cut_bis G) as [Hpax _].
      specialize (Hpax _ Hax _ (source_in_edges_at_out e)).
      by revert Hpax => /eqP Hpax.
Qed.

Definition red_ax_iso (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) := {|
  iso_v := red_ax_iso_v N;
  iso_e := red_ax_iso_e _;
  iso_d := pred0;
  iso_ihom := red_ax_iso_ihom _ |}.

Lemma red_ax_isol (G : proof_structure) (e : edge G) (Hcut : vlabel (target e) = cut)
  (Hax : vlabel (source e) = ax)
  (N : None \in (edge_set ([set: red_ax_graph_1 Hcut Hax] :\ source e :\ target e))) :
   red_ax_G N ≃l G.
Proof.
  exists (red_ax_iso N).
  intros [[[v V] | []] | []]; try by []; unfold red_ax_iso_v_bij_bwd; cbn.
  cbn in v. intro Hl.
  assert (left v <> e).
  { intros ?; subst e.
    clear - Hcut Hl; contradict Hcut.
    rewrite left_e ?Hl; caseb. }
  assert (left v <> other_cut Hcut).
  { intro Hc.
    clear - Hcut Hl Hc. enough (vlabel (target e) <> cut) by by [].
    destruct (other_cut_in_neq Hcut) as [<- _].
    rewrite -Hc left_e ?Hl; caseb. }
  case: {-}_ /boolP => [p0 | /negPn p0]; revert p0;
  case: {-}_ /boolP => [p1 | /negPn p1]; revert p1; cbn.
  - move => p0 p1.
    apply /eqP; unfold red_ax_iso_e_bij_fwd; cbn; apply /eqP; rewrite !SubK /red_ax_left_1.
    assert (left v <> other_ax Hax).
    { intro Hc.
      clear p1; contradict p0; apply /negP /negPn.
      unfold red_ax_left, red_ax_left_1.
      rewrite !in_set; cbn; rewrite !SubK.
      case_if.
      contradict N; apply /negP.
      by apply red_ax_degenerate_None, red_ax_degenerate_source. }
    case_if.
  - move => _ p1.
    contradict p1; apply /negP /negPn.
    by rewrite !in_set.
  - move => ? p1.
    contradict p1; apply /negP.
    by rewrite !in_set.
  - move => p0 _.
    apply /eqP; unfold red_ax_iso_e_bij_fwd; cbn; apply /eqP.
    revert p0. rewrite !in_set; cbn; rewrite !SubK /red_ax_left_1.
    case_if.
Qed.
*)
End Atoms.
