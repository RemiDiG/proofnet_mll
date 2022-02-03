(* Extension for [mgraph] of the library GraphTheory
   About Directed Acyclic Multigraphs, in which the relation being linked by a walk is well-founded
 *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import mgraph.
From Yalla Require Import mll_prelim graph_more.

Import EqNotations.

Set Mangle Names.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


(** ** Directed paths in a multigraph *)
Definition path {Lv Le : Type} {G : graph Lv Le} := seq (edge G).

Definition path_endpoint {Lv Le : Type} {G : graph Lv Le} (b : bool) (s : G) (p : path) :=
  match b with
  | false => head s [seq source e | e <- p]
  | true => last s [seq target e | e <- p]
  end.
Notation path_source := (path_endpoint false).
Notation path_target := (path_endpoint true).


(** ** Directed walks in a multigraph *)
(*
Fixpoint walk {Lv Le : Type} {G : graph Lv Le} (x y : G) (w : path) :=
  if w is e :: w' then (source e == x) && walk (target e) y w' else x == y.
*)
(* TODO beaucoup de doublon avec uwalk : généraliser ? demander à DP *)
Lemma walk_endpoint {Lv Le : Type} {G : graph Lv Le} (p : path) :
  forall (x y : G), walk x y p -> path_source x p = x /\ path_target x p = y.
Proof.
  induction p as [ | e p IH] => x y /=.
  { by move => /eqP-->. }
  move => /andP[/eqP--> W]. split; trivial.
  by destruct (IH _ _ W) as [_ <-].
Qed.

Lemma walk_cat {Lv Le : Type} {G : graph Lv Le} (s i t : G) (p q : path) :
  walk s i p -> walk i t q -> walk s t (p ++ q).
Proof.
  revert s i t q; induction p as [ | e p Hp] => s i t q Wp Wq; revert Wp; cbn.
  - by move => /eqP ->.
  - move => /andP[/eqP <- ?]. apply /andP; split; trivial. by apply (Hp _ i).
Qed.

Lemma walk_sub_middle {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q : path) :
  walk s t (p ++ q) -> path_target s p = path_source t q.
Proof.
  revert s t q; induction p as [ | e p Hp] => s t q; cbn in *.
  - destruct q; cbn; [by move => /eqP -> | by move => /andP[/eqP -> _]].
  - move =>/andP[_ W]. apply (Hp _ _ _ W).
Qed.

Lemma walk_subK {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q : path) :
  walk s t (p ++ q) -> walk s (path_target s p) p /\ walk (path_source t q) t q.
Proof.
  revert s t q; induction p as [ | e p Hp] => s t q W.
  - cbn. split; trivial.
    assert (H := walk_sub_middle W). cbn in H. by rewrite -H.
  - cbn in *. revert W => /andP[/eqP -> W].
    splitb; apply (Hp _ _ _ W).
Qed.

Lemma walk_sub {Lv Le : Type} {G : graph Lv Le} (s t : G) (p q r : path) :
  walk s t (p ++ q ++ r) -> walk (path_target s p) (path_source t r) q.
Proof.
  intro W.
  assert (W' : walk (path_target s p) t (q ++ r)).
  { rewrite (walk_sub_middle W). by destruct (walk_subK W) as [_ ->]. }
  rewrite -(walk_sub_middle W'). by destruct (walk_subK W') as [-> _].
Qed.

Lemma walk_rcons {Lv Le : Type} {G : graph Lv Le} (s t : G) (p : path) (e : edge G) :
  walk s t (rcons p e) = (walk s (source e) p) && (target e == t).
Proof.
  revert s t e; induction p as [ | ep p IH] => s t e /=.
  all: apply /eqP; cbn; apply /eqP; case: ifP => /eqP-H; subst.
  all: rewrite ?eq_refl //.
  - apply nesym in H. revert H => /eqP-H. symmetry. caseb.
  - apply IH.
  - revert H => /eqP-H. symmetry. caseb.
Qed.

Lemma walk_subgraph {Lv Le : Type} (G : graph Lv Le) V E C (s t : @subgraph_for _ _ G V E C) p :
  walk s t p -> walk (val s) (val t) [seq val e | e <- p].
Proof.
  revert s t. induction p as [ | [a A] p IH] => s t //=.
  cbnb. move => /andP[-> W]. splitb.
  replace (target a) with (val (Sub (target a) (C _ _ (valP (exist _ a A))) : subgraph_for C))
    by by [].
  by apply IH.
Qed.

Lemma walk_dual {Lv Le : Type} (G : graph Lv Le) :
  forall p u v,
  @walk _ _ (dual G) u v p = @walk _ _ G v u (rev p).
Proof.
  intro p. induction p as [ | e p IH] => u v //=.
  by rewrite rev_cons walk_rcons IH andb_comm.
Qed.

Definition acyclic {Lv Le : Type} (G : graph Lv Le) :=
  forall (x : G) (p : path), walk x x p -> p = [::].

(** ** Directed Acyclic Multigraph *)
Record dam (Lv Le : Type) : Type := Dam {
    mgraph_of :> graph Lv Le;
    acy : acyclic mgraph_of;
  }.

(** ** Acyclicity is preserved by taking subgraphs *)
Lemma acy_subdam {Lv Le : Type} (G : dam Lv Le) :
  forall V E C, acyclic (@subgraph_for _ _ G V E C).
Proof.
  intros ? ? ? ? ? P.
  assert (A := acy (walk_subgraph P)).
  by revert A => /eqP; rewrite map_eq_nil => /eqP-->.
Qed.

Definition subdam_for {Lv Le : Type} {G : dam Lv Le} {V : {set G}} E C :=
  Dam (@acy_subdam _ _ _ V E C).

Definition remove_vertex_dam {Lv Le : Type} {G : dam Lv Le} (z : G) :=
  subdam_for (@consistent_del1 _ _ _ z).

(** ** Acyclicity is preserved by duality *)
Lemma dual_acy {Lv Le : Type} (G : graph Lv Le) :
  acyclic G -> acyclic (dual G).
Proof.
  intros C v p W.
  rewrite walk_dual in W.
  specialize (C _ _ W).
  by apply /eqP; rewrite -rev_nil; apply /eqP.
Qed.

Definition dual_dam {Lv Le : Type} (G : dam Lv Le) := Dam (dual_acy (@acy _ _ G)).


(** ** The relation being linked by a walk is well-founded in dam *)
Definition is_connected_strict {Lv Le : Type} {G : graph Lv Le} (t s : G) :=
  exists p, (p != [::]) && walk s t p.

Definition is_connected_strict_rev {Lv Le : Type} {G : graph Lv Le} (s t : G) :=
  is_connected_strict t s.

Lemma well_founded_dam_edges {Lv Le : Type} (G : graph Lv Le) :
  forall (u : G), (forall e, source e = u -> Acc is_connected_strict (target e)) ->
  Acc is_connected_strict u.
Proof.
  intros u H.
  constructor => v [p /andP[/eqP-P W]].
  destruct p as [ | e p]; first by []. clear P.
  revert W => /= /andP[/eqP-E W].
  specialize (H _ E).
  destruct p as [ | f p].
  { by revert W => /= /eqP-<-. }
  apply (Acc_inv H).
  exists (f :: p). rewrite W. splitb.
Qed.

Lemma well_founded_dam_empty {Lv Le : Type} (G : graph Lv Le) :
  #|G| = 0 -> well_founded (@is_connected_strict _ _ G).
Proof. intros N x. apply card0_eq in N. by specialize (N x). Qed.

Lemma well_founded_dam_below {Lv Le : Type} (G : dam Lv Le) (v : G) :
  well_founded (@is_connected_strict _ _ (remove_vertex_dam v)) ->
  forall (u : remove_vertex v) p, walk v (val u) p ->
  Acc is_connected_strict (val u).
Proof.
  intros Rwf u. induction u as [[u U] IH] using (well_founded_ind Rwf).
  move => p /= VU.
  constructor => w [q /andP[/eqP-? UW]].
  assert (W : w \in [set~ v]).
  { rewrite !in_set. apply /eqP => ?. subst w.
    assert (VV := walk_cat VU UW). apply acy in VV.
    by revert VV => /eqP; rewrite cat_nil => /andP[_ /eqP-?]. }
  revert UW. replace w with (val (Sub w W : remove_vertex v)) by by []. intro UW.
  refine (IH _ _ _ (walk_cat VU UW)). clear IH.
  unfold is_connected_strict.
  revert w W UW. induction q as [ | q e IH] using last_ind => w W UW //.
  rewrite walk_rcons in UW. revert UW => /= /andP[US /eqP-?]. subst w.
  assert (S : source e \in [set~ v]).
  { rewrite !in_set. apply /eqP => S.
    rewrite S in US.
    assert (VV := walk_cat VU US). apply acy in VV.
    revert VV => /eqP; rewrite cat_nil => /andP[/eqP-? _]. subst p.
    revert VU => /= /eqP-?. subst u.
    clear -U. contradict U; apply /negP. by rewrite !in_set negb_involutive. }
  assert (E : e \in ~: edges_at v).
  { rewrite in_set edges_at_eq. splitb.
    all: apply /eqP => ?; subst v.
    - contradict S; apply /negP. by rewrite !in_set negb_involutive.
    - contradict W; apply /negP. by rewrite !in_set negb_involutive. }
  destruct q as [ | f q].
  { exists [:: (Sub e E)]. revert US. cbnb. move => /eqP-->. splitb. }
  assert (FQ : f :: q <> [::]) by by [].
  revert IH => /(_ FQ _ S US) [r /andP[R USr]].
  exists (rcons r (Sub e E)). splitb.
  - apply /eqP. apply rcons_nil.
  - rewrite walk_rcons. splitb. simpl.
    enough (Sub (source e) S = Sub (source e) _) as <- by by [].
    cbnb. simpl. cbnb.
Qed.

Lemma well_founded_dam_removed {Lv Le : Type} (G : dam Lv Le) (v : G) :
  well_founded (@is_connected_strict _ _ (remove_vertex_dam v)) ->
  Acc is_connected_strict v.
Proof.
  intro W. constructor => u [p /andP[/eqP-? VU]].
  assert (U : u \in [set~ v]).
  { rewrite !in_set. apply /eqP => ?. subst u.
    by assert (H := acy VU). }
  now refine (@well_founded_dam_below _ _ _ _ _ (Sub u U) _ VU).
Qed.

Lemma well_founded_dam_all {Lv Le : Type} (G : dam Lv Le) (v : G) :
  well_founded (@is_connected_strict _ _ (remove_vertex_dam v)) ->
  forall (u : remove_vertex v), Acc is_connected_strict (val u).
Proof.
  intros Rwf u.
  induction u as [u IH] using (well_founded_ind Rwf).
  apply well_founded_dam_edges.
  intros e E.
  destruct (target e \in [set~ v]) eqn:T; first last.
  - revert T. rewrite !in_set => /negP/negP/eqP-?. subst v.
    by apply well_founded_dam_removed.
  - apply (IH (Sub (target e) T)).
    unfold is_connected_strict.
    assert (E' : e \in ~: edges_at v).
    { rewrite in_set edges_at_eq. splitb.
      all: apply /eqP => ?; subst v.
      - destruct u as [u U]. simpl in E. subst u. clear IH.
        contradict U; apply /negP. by rewrite !in_set negb_involutive.
      - contradict T; apply /negP. by rewrite !in_set negb_involutive. }
    exists [:: Sub e E']. splitb; cbnb. by rewrite E.
Qed.

Lemma well_founded_remove_vertex_dam {Lv Le : Type} (G : dam Lv Le) (v : G) :
  well_founded (@is_connected_strict _ _ (remove_vertex_dam v)) ->
  well_founded (@is_connected_strict _ _ G).
Proof.
  intros Rwf u.
  destruct (u \in [set~ v]) eqn:U; first last.
  - revert U. rewrite !in_set => /negP/negP/eqP-?. subst u.
    by apply well_founded_dam_removed.
  - by refine (well_founded_dam_all _ (Sub u U)).
Qed.

Lemma well_founded_dam {Lv Le : Type} (G : dam Lv Le) :
  well_founded (@is_connected_strict _ _ G).
Proof.
  revert G.
  enough (H : forall n (G : dam Lv Le), #|G| = n -> well_founded (@is_connected_strict _ _ G))
    by (intro G; by apply (H #|G|)).
  intro n; induction n as [ | n IH]; intros G N.
  { by apply well_founded_dam_empty. }
  destruct (set_0Vmem [set:G]) as [F | [v _]].
  { contradict N. by rewrite -cardsT F cards0. }
  apply (@well_founded_remove_vertex_dam _ _ _ v), IH.
  rewrite -(remove_vertex_card v) in N. simpl in *. lia.
Qed.

Lemma dual_rev {Lv Le : Type} (G : dam Lv Le) :
  forall u v,
  @is_connected_strict _ _ (dual_dam G) u v <-> @is_connected_strict_rev _ _ G u v.
Proof.
  intros. rewrite /is_connected_strict_rev /is_connected_strict /=.
  split; move => [p P].
  all: exists (rev p); by rewrite -walk_dual rev_nil.
Qed.

Lemma well_founded_dam_rev' {Lv Le : Type} (G : dam Lv Le) :
  well_founded (@is_connected_strict_rev _ _ G).
Proof. apply (well_founded_eq (@dual_rev _ _ G)), well_founded_dam. Qed.


(* BEGIN OLD
(** ** Walks from a node in a dam form a finite type *)
Record Walk {Lv Le : Type} {G : graph Lv Le} (s : G) :
  predArgType := {wval :> path; wvalK : [exists t, walk s t wval]}.
Canonical Walk_subType {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  [subType for (@wval _ _ _ s)].
Definition Walk_eqMixin {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  Eval hnf in [eqMixin of Walk s by <:].
Canonical Walk_eqType {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  Eval hnf in EqType (Walk s) (Walk_eqMixin s).
Definition Walk_choiceMixin {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  Eval hnf in [choiceMixin of (Walk s) by <:].
Canonical Walk_choiceType {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  Eval hnf in ChoiceType (Walk s) (Walk_choiceMixin s).
Definition Walk_countMixin {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  Eval hnf in [countMixin of (Walk s) by <:].
Canonical Walk_countType {Lv Le : Type} {G : graph Lv Le} (s : G) :=
  Eval hnf in CountType (Walk s) (Walk_countMixin s).

Lemma walk_uniq {Lv Le : Type} {G : dam Lv Le} p :
  forall (s t : G), walk s t p -> uniq [seq source e | e <- p].
Proof.
  induction p as [ | e p IH]; trivial.
  move => s t /= /andP[/eqP-? W]. subst s.
  splitb; first last.
  { exact (IH _ _ W). }
  apply /mapP. intros [f F S].
  apply in_elt_sub in F. destruct F as [n P].
  assert (C := @acy _ _ _ (source e) (e :: take n p)).
  enough (W' : walk (source e) (source e) (e :: take n p)) by by apply C in W'.
  simpl. splitb.
  rewrite P in W. apply (@walk_sub _ _ _ _ _ [::]) in W.
  by rewrite /= -S in W.
Qed.

Lemma walk_size {Lv Le : Type} {G : dam Lv Le} (s t : G) p :
  walk s t p -> size p < S #|G|.
Proof.
  move => W.
  assert (U := walk_uniq W).
  revert U => /card_uniqP-U.
  rewrite size_map in U.
  rewrite -U.
  exact: max_card.
Qed.

Definition Walk_tuple {Lv Le : Type} {G : dam Lv Le} (s : G) (p : Walk s) :
  {n : 'I_(S #|G|) & n.-tuple (edge G)} :=
  let (w, W) := p in let (t, W') := sigW (existsP W) in existT _ (Ordinal (walk_size W')) (in_tuple w).

Definition tuple_Walk {Lv Le : Type} {G : graph Lv Le} (s : G)
  (m : {n : 'I_(S #|G|) & n.-tuple (edge G)}) : option (Walk s) :=
  let (_, p) := m in match boolP [exists t, walk s t p] with
  | AltTrue W => Some (Sub (val p) W)
  | AltFalse _ => None
  end.

Lemma Walk_tupleK {Lv Le : Type} {G : dam Lv Le} (s : G) :
  pcancel (@Walk_tuple _ _ _ s) (tuple_Walk s).
Proof.
  move => [w W] /=. destruct (sigW (existsP W)) as [t ?]. simpl.
  case: {-}_ / boolP; last by rewrite W.
  move => *. cbnb.
Qed.

Definition Walk_finMixin {Lv Le : Type} {G : dam Lv Le} (s : G) :=
  Eval hnf in PcanFinMixin (@Walk_tupleK _ _ _ s).
Canonical Walk_finType {Lv Le : Type} {G : dam Lv Le} (s : G) :=
  Eval hnf in FinType (Walk s) (Walk_finMixin s).

(** ** Well-founded *)
Lemma Walk_nilK {Lv Le : Type} {G : graph Lv Le} (s : G) :
  [exists t, walk s t [::]].
Proof. apply /existsP. exists s. by unfold walk. Qed.

Definition Walk_nil {Lv Le : Type} (G : graph Lv Le) (x : G) : Walk x :=
  {| wval := _ ; wvalK := Walk_nilK x |}.

Definition size_walk {Lv Le : Type} {G : dam Lv Le} {x : G} : Walk x -> nat :=
  fun w => size (wval w).

(* Rank of a node : size of the bigger walk starting from it *)
Definition dam_rank {Lv Le : Type} (G : dam Lv Le) : G -> nat :=
  fun x => size_walk [arg max_(w > Walk_nil x) size_walk w].

Lemma dam_rank_monotone {Lv Le : Type} (G : dam Lv Le) :
  forall (x y : G), is_connected_strict x y -> (dam_rank x < dam_rank y)%coq_nat.
Proof.
  move => x y /sigW-[p /andP[/eqP-P W]]. unfold dam_rank.
  enough (E : size_walk [arg max_(w0 > Walk_nil y) size_walk w0] >=
          size_walk [arg max_(w0 > Walk_nil x) size_walk w0] + size p).
  { destruct p as [ | ? p]; try by [].
    simpl in E.
    assert (Hr : (size p).+1 = size p + 1) by lia.
    rewrite Hr {Hr} in E.
    enough (size_walk [arg max_(w0 > Walk_nil x) size_walk w0] + 1 <=
      size_walk [arg max_(w0 > Walk_nil y) size_walk w0]) by lia.
    assert (E' : size_walk [arg max_(w0 > Walk_nil x) size_walk w0] + 1 <=
      size_walk [arg max_(w0 > Walk_nil x) size_walk w0] + (size p + 1)) by lia.
    apply (leq_trans E' E). }
  destruct [arg max_(w0 > Walk_nil x) size_walk w0] as [v V].
  rewrite {1}/size_walk /=.
  revert V => /existsP/sigW[t V].
  assert (WV : [exists t, walk y t (p ++ v)]).
  { apply /existsP. exists t. exact (walk_cat W V). }
  assert (Hr : size_walk {| wval := _ ; wvalK := WV |} = size v + size p).
  { rewrite /size_walk /= size_cat. lia. }
  rewrite -Hr {Hr}.
  case: arg_maxnP; trivial.
  intros ? _ H. by apply H.
Qed.

Lemma well_founded_dam {Lv Le : Type} (G : dam Lv Le) :
  well_founded (@is_connected_strict _ _ G).
Proof. exact (Wf_nat.well_founded_lt_compat _ _ _ (@dam_rank_monotone _ _ G)). Qed.

Lemma dam_rank_max {Lv Le : Type} (G : dam Lv Le) :
  forall (x : G), dam_rank x <= #|G|.
Proof.
  intro x. unfold dam_rank.
  destruct [arg max_(_ > _)_ _] as [p P].
  rewrite /size_walk /=.
  revert P => /existsP/sigW[? P].
  by apply (walk_size P).
Qed.

Definition dam_rank_rev {Lv Le : Type} (G : dam Lv Le) : G -> nat :=
  fun x => #|G| - dam_rank x.

Lemma dam_rank_to_rev {Lv Le : Type} (G : dam Lv Le) :
  forall (x y : G), (dam_rank x > dam_rank y)%coq_nat ->
  (dam_rank_rev x < dam_rank_rev y)%coq_nat.
Proof.
  intros x y. unfold dam_rank_rev, dam_rank.
  enough (size_walk [arg max_(w > Walk_nil x)size_walk w] <= #|G|
    /\ size_walk [arg max_(w > Walk_nil y)size_walk w] <= #|G|) by lia.
  split; apply dam_rank_max.
Qed.

Lemma dam_rank_monotone_rev {Lv Le : Type} (G : dam Lv Le) :
  forall (x y : G), is_connected_strict_rev x y -> (dam_rank_rev x < dam_rank_rev y)%coq_nat.
Proof. intros. by apply dam_rank_to_rev, dam_rank_monotone. Qed.

Lemma well_founded_dam_rev {Lv Le : Type} (G : dam Lv Le) :
  well_founded (@is_connected_strict_rev _ _ G).
Proof. exact (Wf_nat.well_founded_lt_compat _ _ _ (@dam_rank_monotone_rev _ _ G)). Qed.
END OLD *)
