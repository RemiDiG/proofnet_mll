(* Sequentialisation - Splitting tensor lemma *)
(* From a Proof Net, return a LL proof of the same sequent *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export mll_prelim graph_more mgraph_tree mll_def mll_basic mll_seq_to_pn
  mll_pn_to_seq_def.

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
Notation graph_data := (@graph_data atom).
Notation proof_structure := (@proof_structure atom).
Notation proof_net := (@proof_net atom).
Notation switching := (@switching atom).
Notation switching_left := (@switching_left atom).

Lemma utree_switching_left {G : proof_net} : utree (@switching_left G).
Proof. split; [apply uacyclic_swithching_left, G | apply uconnected_from_nb1, G]. Qed.


Section Splitting_tens.
Context {G : proof_net} {v : G} (V : vlabel v = ⊗) (T : terminal v).

Local Notation F := (@switching_left_sinj _ G).
Local Notation TL := utree_switching_left.
Local Notation TP := (utree_part F TL v).

Lemma partition_terminal_ccl x :
  utree_part (@switching_left_sinj _ G) utree_switching_left v x = Some (ccl_tens V) ->
  pblock (preim_partition TP [set: G]) x = [set target (ccl_tens V)].
Proof.
  revert T. rewrite (terminal_tens_parr (or_introl V)) => /eqP-C.
  intro X. apply /setP => y.
  assert (Spart := preim_partitionP TP [set: G]).
  revert Spart => /andP[/eqP-Cov /andP[Triv _]].
  rewrite in_set -eq_pblock // ?Cov {Cov Triv} // preim_partition_pblock_eq // X {X}.
  destruct (eq_comparable y (target (ccl_tens V))) as [? | Y].
  - subst y. rewrite eq_refl. apply /eqP.
    unfold utree_part. destruct (utree_unique_path F TL v (target (ccl_tens V))) as [P Pu].
    assert (S : supath switching_left v (target (ccl_tens V)) [:: forward (ccl_tens V)]).
    { rewrite /supath /= in_cons negb_orb ccl_e. splitb.
      by rewrite /switching_left C. }
    specialize (Pu {| upvalK := S |}). by subst P.
  - transitivity false; last by (symmetry; apply /eqP).
    apply /eqP.
    unfold utree_part. destruct (utree_unique_path F TL v y) as [[p P] _].
    destruct p as [ | (e1, b1) p]; first by []. cbnb.
    destruct (eq_comparable e1 (ccl_tens V)); last by apply nesym.
    subst e1. exfalso.
    rewrite supath_cons in P. revert P => /andP[/andP[/andP[P1 /eqP-Vb1] U1] /eqP-N1].
    assert (b1 = true).
    { destruct b1; trivial. exfalso. destruct (@utree_switching_left G) as [A _].
      contradict Vb1. simpl.
      apply nesym in N1. simpl in N1.
      rewrite -[in RHS](ccl_e (or_introl V)).
      by apply nesym, (uacyclic_loop A). }
    subst b1. clear Vb1. simpl in *.
    destruct p as [ | e2 p].
    { clear - P1 Y. revert P1. rewrite /supath /=. introb. }
    rewrite supath_cons in P1. revert P1 => /andP[/andP[/andP[_ /eqP-Vb2] _] _].
    clear - U1 Vb2 C.
    destruct e2 as (e2, []); simpl in Vb2.
    + contradict Vb2. by apply no_source_c.
    + revert U1. rewrite map_cons in_cons => /norP[U1 _].
      contradict U1. apply /negP/negPn/eqP.
      simpl. f_equal.
      apply one_target_c; by rewrite Vb2.
Qed.

Lemma partition_terminal_utree_part (x : G) :
  TP x \in [set None; Some (left_tens V); Some (right_tens V); Some (ccl_tens V)].
Proof.
(* Do not need terminal v *)
  unfold utree_part. destruct (utree_unique_path F TL v x) as [[[ | e p] P] _].
  { by rewrite !in_set. }
  rewrite supath_cons in P. revert P => /andP[/andP[/andP[_ /eqP-EV] _] _].
  destruct e as (e, []); simpl in EV.
  - assert (E := ccl_eq (or_introl V) EV). subst e.
    rewrite !in_set. caseb.
  - enough (E : e \in [set left_tens V; right_tens V]).
    { revert E. rewrite !in_set => /orP[/eqP--> | /eqP-->]; caseb. }
    by rewrite -right_set in_set EV.
Qed.

Lemma partition_terminal_utree_part_ccl :
  TP (target (ccl_tens V)) = Some (ccl_tens V).
Proof.
  revert T. rewrite (terminal_tens_parr (or_introl V)) => /eqP-C.
  unfold utree_part. destruct (utree_unique_path F TL v (target (ccl_tens V))) as [P Pu].
  assert (S : supath switching_left v (target (ccl_tens V)) [:: forward (ccl_tens V)]).
  { rewrite /supath /= in_cons negb_orb ccl_e /switching_left C. splitb. }
  specialize (Pu {| upvalK := S |}). by subst P.
Qed.

Lemma partition_terminal_utree_part_left :
  TP (source (left_tens V)) = Some (left_tens V).
Proof.
(* Do not need terminal v *)
  unfold utree_part. destruct (utree_unique_path F TL v (source (left_tens V))) as [P Pu].
  assert (S : supath switching_left v (source (left_tens V)) [:: backward (left_tens V)]).
  { rewrite /supath /= in_cons negb_orb left_e /switching_left left_e V. splitb. }
  specialize (Pu {| upvalK := S |}). by subst P. (* TODO tout simplifier comme ça ! *)
Qed.

Lemma partition_terminal_utree_part_right :
  TP (source (right_tens V)) = Some (right_tens V).
Proof.
(* Do not need terminal v *)
  unfold utree_part. destruct (utree_unique_path F TL v (source (right_tens V))) as [P Pu].
  assert (S : supath switching_left v (source (right_tens V)) [:: backward (right_tens V)]).
  { rewrite /supath /= in_cons negb_orb right_e /switching_left right_e V. splitb. }
  specialize (Pu {| upvalK := S |}). by subst P.
Qed.

Lemma partition_terminal_eq :
  preim_partition TP [set: G] =
  [set pblock (preim_partition TP [set: G]) (source (left_tens V));
       pblock (preim_partition TP [set: G]) (source (right_tens V));
       [set v]; [set target (ccl_tens V)]].
Proof.
  rewrite [in LHS]preim_partition_eq.
  apply /setP => P.
  symmetry.
  destruct (P \in [set pblock (preim_partition TP [set: G]) x
    | x in [set: G]]) eqn:Pin.
  - revert Pin => /imsetP[x _ ?]. subst P.
    assert (Imx := partition_terminal_utree_part x).
    revert Imx. rewrite !in_set => /orP[/orP[/orP[/eqP-X | /eqP-X] | /eqP-X] | /eqP-X].
    + apply utree_part_None in X. subst x.
      rewrite utree_part_v. caseb.
    + enough (pblock (preim_partition TP [set: G]) x =
              pblock (preim_partition TP [set: G]) (source (left_tens V)))
        as -> by caseb.
      apply /eqP. by rewrite preim_partition_pblock_eq // X partition_terminal_utree_part_left.
    + enough (pblock (preim_partition TP [set: G]) x =
              pblock (preim_partition TP [set: G]) (source (right_tens V)))
        as -> by caseb.
      apply /eqP. by rewrite preim_partition_pblock_eq // X partition_terminal_utree_part_right.
    + rewrite (partition_terminal_ccl X). caseb.
  - revert Pin => /negP/negP-Pin.
    apply /negP/negP.
    rewrite !in_set !negb_orb -(utree_part_v F TL)
      -(partition_terminal_ccl partition_terminal_utree_part_ccl).
    splitb.
    all: apply /eqP => ?; subst P.
    all: contradict Pin; apply /negP/negPn.
    all: by apply imset_f.
Qed.
(* TODO this is a general lemma on trees, prove it purely in the graph part *)
(* généraliser : dans utree_part, un pblock par arete (la target / source non v) + pblock de v, qui est lui même *)

(* The two blocks which are respectively on the left and right of v *)
Local Notation Sl := (pblock (preim_partition TP [set: G]) (source (left_tens V))).
Local Notation Sr := (pblock (preim_partition TP [set: G]) (source (right_tens V))).

(* In the switching graph without any right premise, there is a partition separating the tree into
   the vertices on the left of v, and on its right *)
Lemma partition_terminal : partition [set Sl; Sr; [set v]; [set target (ccl_tens V)]] [set: G].
Proof. rewrite -partition_terminal_eq. apply tree_partition. Qed.

Lemma uconnected_Sl : uconnected (@switching_left (induced Sl)).
Proof.
  apply (@uconnected_utree_part _ _ _ _ _ _ _ _ F TL v
    (@switching_left_induced_None_to _ _ _) (@switching_left_induced_eq_to _ _ _)).
  rewrite {2}partition_terminal_eq !in_set. caseb.
Qed.

Lemma uconnected_Sr : uconnected (@switching_left (induced Sr)).
Proof.
  apply (@uconnected_utree_part _ _ _ _ _ _ _ _ F TL v
    (@switching_left_induced_None_to _ _ _) (@switching_left_induced_eq_to _ _ _)).
  rewrite {2}partition_terminal_eq !in_set. caseb.
Qed.

Lemma source_left_Sl : source (left_tens V) \in Sl.
Proof.
  rewrite mem_pblock.
  assert (Spart := preim_partitionP TP [set: G]).
  by revert Spart => /andP[/eqP--> _].
Qed.

Lemma source_right_Sr : source (right_tens V) \in Sr.
Proof.
  rewrite mem_pblock.
  assert (Spart := preim_partitionP TP [set: G]).
  by revert Spart => /andP[/eqP--> _].
Qed.

Lemma partition_disjoint :
  [disjoint Sl & Sr] /\ [disjoint [set v] & Sl] /\ [disjoint [set v] & Sr] /\
  [disjoint [set target (ccl_tens V)] & Sl] /\ [disjoint [set target (ccl_tens V)] & Sr] /\
  [disjoint [set v] & [set target (ccl_tens V)]].
Proof.
  assert (Spart := preim_partitionP TP [set: G]).
  revert Spart => /andP[/eqP-Cov /andP[TI ?]].
  assert (TI' := TI). revert TI => /trivIsetP-TI.
  assert ({in [set: G] & &, equivalence_rel (fun x y : G => TP x == TP y)}).
  { intros ? ? ? _ _ _. splitb. by move => /eqP-->. }
  repeat split; apply TI; try by (rewrite !in_set; caseb).
  all: rewrite -?(utree_part_v F TL v)
    -?(partition_terminal_ccl  (partition_terminal_utree_part_ccl )).
  all: try (apply pblock_mem; by rewrite Cov).
  all: rewrite eq_pblock // ?Cov // pblock_equivalence_partition //
    ?utree_part_v_v ?partition_terminal_utree_part_left
    ?partition_terminal_utree_part_right ?partition_terminal_utree_part_ccl //;
    cbn; apply /eqP.
  - apply left_neq_right.
  - intro C.
    enough (H : source (ccl_tens V) = target (ccl_tens V)) by by apply (no_selfloop H).
    by rewrite ccl_e C left_e.
  - intro C.
    enough (H : source (ccl_tens V) = target (ccl_tens V)) by by apply (no_selfloop H).
    by rewrite ccl_e C right_e.
Qed.
(* TODO disjointness should be the corollary of a general lemma : part of partitions are disjoint; even on the tree part *)

(*
Lemma partition_terminal :
  partition [set Sl; Sr; [set v]; [set target (ccl_tens V)]] [set: G]. /\
    uconnected (@switching_left (induced Sl)) /\ uconnected (@switching_left (induced Sr)) /\
    source (left_tens V) \in Sl /\ source (right_tens V) \in Sr /\
    [disjoint Sl & Sr] /\ [disjoint [set v] & Sl] /\ [disjoint [set v] & Sr] /\
    [disjoint [set target (ccl_tens V)] & Sl] /\ [disjoint [set target (ccl_tens V)] & Sr] /\
    [disjoint [set v] & [set target (ccl_tens V)]]}.
Proof.
  set T := utree_switching_left. set F := @switching_left_sinj _ G.
  intro VT.
  assert (Spart := preim_partitionP (utree_part F T v) [set: G]).
  revert Spart => /andP[/eqP-Cov TI].
  exists (pblock (preim_partition (utree_part F T v) [set: G]) (source (left_tens V)),
          pblock (preim_partition (utree_part F T v) [set: G]) (source (right_tens V))).
  split; [ | split; [ | split; [ | split; [ | split]]]]; trivial.
  - rewrite -(partition_terminal_eq V VT). apply tree_partition.
  - apply (@uconnected_utree_part _ _ _ _ _ _ _ _ F T v
      (@switching_left_induced_None_to _ _ _) (@switching_left_induced_eq_to _ _ _)).
    rewrite {2}(partition_terminal_eq V VT) !in_set. caseb.
  - apply (@uconnected_utree_part _ _ _ _ _ _ _ _ F T v
      (@switching_left_induced_None_to _ _ _) (@switching_left_induced_eq_to _ _ _)).
    rewrite {2}(partition_terminal_eq V VT) !in_set. caseb.
  - by rewrite mem_pblock Cov.
  - by rewrite mem_pblock Cov.
  - revert TI => /andP[TI ?]. assert (TI' := TI). revert TI => /trivIsetP-TI.
    assert ({in [set: G] & &,
      equivalence_rel (fun x y : G => utree_part F T v x == utree_part F T v y)}).
    { intros ? ? ? _ _ _. splitb. by move => /eqP-->. }
    repeat split; apply TI; try by (rewrite !in_set; caseb).
    all: rewrite -?(utree_part_v F T v)
                 -?(partition_terminal_ccl VT (partition_terminal_utree_part_ccl V VT)).
    all: try (apply pblock_mem; by rewrite Cov).
    all: rewrite eq_pblock // ?Cov // pblock_equivalence_partition //
      ?utree_part_v_v ?partition_terminal_utree_part_left
      ?partition_terminal_utree_part_right ?partition_terminal_utree_part_ccl //;
      cbn; apply /eqP.
    + apply left_neq_right.
    + intro C.
      enough (H : source (ccl_tens V) = target (ccl_tens V)) by by apply (no_selfloop H).
      by rewrite ccl_e C left_e.
    + intro C.
      enough (H : source (ccl_tens V) = target (ccl_tens V)) by by apply (no_selfloop H).
      by rewrite ccl_e C right_e.
Qed.
*)

(* We can do a case study on this, but not on sequentializing : Type *)
Definition splitting_tens_prop :=
  forall (p : G) (P : vlabel p = ⅋), (p \in Sl -> source (right_parr P) \in Sl)
                                  /\ (p \in Sr -> source (right_parr P) \in Sr).


Definition splitting_tens_bool :=
  [forall p : G, if @boolP (vlabel p == ⅋) is AltTrue P then ((p \in Sl) ==> (source (right_parr (eqP P)) \in Sl))
                                  && ((p \in Sr) ==> (source (right_parr (eqP P)) \in Sr)) else true].

Lemma splitting_tensP :
  reflect splitting_tens_prop splitting_tens_bool.
Proof.
  unfold splitting_tens_bool, splitting_tens_prop.
  apply (iffP idP).
  - move => /forallP H p P.
    specialize (H p).
    revert H.
    case: {-}_ /boolP => P'.
    2:{ contradict P; by apply /eqP. }
    assert (eqP P' = P) as -> by apply eq_irrelevance.
    move => /andP[/implyP-? /implyP-?]. by split.
  - move => H.
    apply /forallP => p.
    case: {-}_ /boolP => P' //.
    specialize (H p (eqP P')). destruct H.
    apply /andP. split; by apply /implyP.
Qed.

Lemma splitting_tens_prop_is_sequentializing :
  splitting_tens_prop -> sequentializing v.
Proof.
  rewrite /sequentializing /splitting_tens_prop /= V.
  intro H.
(* Taking induced of Sl (resp Sr).
Adding a concl on source (left_tens V).
This graph is correct: acyclicity is preserved by induced (lemma uacyclic_induced);
connectivity by hypothesis (Sl and Sr connected).
Pb : need to add concl edge, ok for correction with the good operatiosn
This graph is a proof structure: heavy, but should not be too hard (but
we need to add some concl edge ...).
Difficult part: G is isomorphic to add_tens ... with the usual problems of timeout
from Coq in this case, how to escape it ?
Should use an intermediate lemma of the form "there is no edges between Sl and Sr".
And of course, this will be divided across plenty of lemmas. *)
(* Admitted for now, to check that this is a good notion of splitting,
before doing this no-fun proof; maybe we do not need it? *)
Admitted.

(* Si on ne suppose pas v est terminal, mais seq -> terminal *)
Lemma sequentializing_tens_is_splitting_prop :
  sequentializing v -> splitting_tens_prop.
Proof.
(* same as the proof above, but normally in a easier way (well, we still have an iso to
manipulate); by contradiction ? *)
Admitted.

(* A tensor is non-splitting because there is some ⅋ with its right edge in the other part
  of the partition *)
Lemma non_splitting_tens :
  ~splitting_tens_prop -> {p : {p : G | vlabel p = ⅋} &
  (projT1 p \in Sl /\ source (right_parr (projT2 p)) \in Sr) \/
  (projT1 p \in Sr /\ source (right_parr (projT2 p)) \in Sl)}.
Proof.
  move => /splitting_tensP.
  unfold splitting_tens_bool.
  assert (Sp := partition_terminal).
  apply cover_partition in Sp.
  move => /forallPn/sigW[p P].
  revert P. case: {-}_ /boolP => P' //.
  set (P := eqP P'). clearbody P. clear P'.
  rewrite negb_and.
  revert Sp. generalize Sl, Sr => Sl Sr Sp H.
  wlog: Sl Sr Sp H / ~~ ((p \in Sl) ==> (source (right_parr P) \in Sl)).
  { elim: (orb_sum H) => H'.
    - by move => /(_ Sl Sr Sp H H').
    - move => /(_ Sr Sl _ _ H').
      assert ([set Sr; Sl; [set v]; [set target (ccl_tens V)]] =
        [set Sl; Sr; [set v]; [set target (ccl_tens V)]]) as ->.
      { apply /setP => x. rewrite !in_set. f_equal. f_equal. by rewrite orb_comm. }
      rewrite orb_comm => /(_ Sp H) [pw Pw].
      exists pw. destruct Pw as [? | ?]; [by right | by left]. }
  clear H. rewrite negb_imply => /andP[In S].
  exists (exist _ p P). simpl.
  assert (Hr : ssrfun.svalP (exist (fun p => vlabel p = ⅋) p P) = P) by apply eq_irrelevance.
  rewrite Hr {Hr}.
  left. split; trivial.
  assert (In2 : source (right_parr P) \in cover [set Sl; Sr; [set v]; [set target (ccl_tens V)]])
    by by rewrite Sp in_set.
  revert In2.
  rewrite /cover !bigcup_setU !bigcup_set1 !in_set.
  move => /orP[/orP[/orP[In2 | //] | /eqP-In2] | /eqP-In2].
  - by rewrite In2 in S.
  - assert (H := terminal_source T In2). by rewrite right_e P in H.
  - contradict In2. apply no_source_c, (terminal_source T), ccl_e.
Qed.

Section Non_splitting_tens.
Hypothesis (NS : ~splitting_tens_prop).

Local Notation blocking_parr := (projT1 (projT1 (non_splitting_tens NS))).
Local Notation blocking_parrK := (projT2 (projT1 (non_splitting_tens NS))).

(* TODO c'est le vrai disjoint, l'autre est plutôt un f-disjoint *)
(* TODO renommer et mettre ailleurs *)
Definition upath_disjoint2 {Lv Le : Type} {G : graph Lv Le}
  (p q : @upath _ _ G) := [disjoint [seq x.1 | x <- p] & [seq x.1 | x <- q]].

Lemma upath_disjoint2_sym {Lv Le : Type} {G' : graph Lv Le} (p q : @upath _ _ G') :
  upath_disjoint2 p q = upath_disjoint2 q p.
Proof. by rewrite /upath_disjoint2 disjoint_sym. Qed.

Lemma upath_disjoint2_rev {Lv Le : Type} {G' : graph Lv Le} (p q : @upath _ _ G') :
  upath_disjoint2 p q -> upath_disjoint2 (upath_rev p) q.
Proof. by rewrite /upath_disjoint2 upath_rev_fst disjoint_rev. Qed.

Lemma HP' : ((blocking_parr \in Sl) && (source (right_parr blocking_parrK) \in Sr)) ||
     ((blocking_parr \in Sr) && (source (right_parr blocking_parrK) \in Sl)).
Proof.
  destruct (non_splitting_tens NS) as [[p P] HP].
simpl.
  simpl in HP.
  { destruct HP as [[? ?] | [? ?]]; apply /orP; [left | right]; by apply /andP. }
Qed.

Lemma HP'' : (blocking_parr \in Sl) || (source (right_parr blocking_parrK) \in Sl).
Proof. elim: (orb_sum HP') => /andP[Pin Spin]; caseb. Qed.

(* Left correctness path when blocking_parr \in Sl:
   take the (switching) path given by the connectivity of Sl from the source of left v
   to the blocking parr, and add left v at the beginning. *)
Definition correctness_path_left_1 (In : (blocking_parr \in Sl) && (source (right_parr blocking_parrK) \in Sr)) : @upath _ _ G :=
match andP In with
| conj In _ =>
  backward (left_tens V) :: [seq (val _a.1, _a.2) | _a <- upval (projT1 (sigW (
    uconnected_Sl (Sub (source (left_tens V)) source_left_Sl) (Sub blocking_parr In))))] end.

(* Left correctness path when source right blocking_parr \in Sl:
   take the (switching) path given by the connectivity of Sl from the source of left v
   to the source of right blocking_parr, and add left v at the beginning and right blocking_parr at the end. *)
Definition correctness_path_left_2 (In : (blocking_parr \in Sr) && (source (right_parr blocking_parrK) \in Sl)) : @upath _ _ G :=
match andP In with
| conj _ In =>
  backward (left_tens V) :: (rcons [seq (val _a.1, _a.2) | _a <- upval (projT1 (sigW (
    uconnected_Sl (Sub (source (left_tens V)) source_left_Sl) (Sub (source (right_parr blocking_parrK)) In))))]
  (forward (right_parr blocking_parrK))) end.

Definition correctness_path_left : @upath _ _ G :=
  sum_rect (fun=> upath) correctness_path_left_1 correctness_path_left_2 (orb_sum HP').

(* OLD

Definition correctness_path_left_1 (Pin : blocking_parr \in Sl) : @upath _ _ G :=
  backward (left_tens V) :: [seq (val _a.1, _a.2) | _a <- upval (projT1 (sigW (
    uconnected_Sl (Sub (source (left_tens V)) source_left_Sl) (Sub blocking_parr Pin))))] .

(* Left correctness path when source right blocking_parr \in Sl:
   take the (switching) path given by the connectivity of Sl from the source of left v
   to the source of right blocking_parr, and add left v at the beginning. *)
Definition correctness_path_left_2 (Spin : (source (right_parr blocking_parrK) \in Sl)) : @upath _ _ G :=
  backward (left_tens V) :: [seq (val _a.1, _a.2) | _a <- upval (projT1 (sigW (
    uconnected_Sl (Sub (source (left_tens V)) source_left_Sl) (Sub (source (right_parr blocking_parrK)) Spin))))] .

Definition correctness_path_left : @upath _ _ G :=
  sum_rect (fun=> upath) correctness_path_left_1 correctness_path_left_2 (orb_sum HP'').

Definition correctness_path_left2 : @upath _ _ G.
Proof.
  elim: (orb_sum HP') => /andP[Pin Spin].
  - exact (correctness_path_left_1 Pin).
  - exact (correctness_path_left_2 Spin).
Defined.
*)

(* Right correctness path when source right blocking_parr \in Sr:
   take the (switching) path given by the connectivity of Sr from the source of right v
   to the source of right blocking parr, and add right v at the beginning. *)
Definition correctness_path_right_1 (In : (blocking_parr \in Sl) && (source (right_parr blocking_parrK) \in Sr)) : @upath _ _ G :=
match andP In with
| conj _ In =>
  backward (right_tens V) :: (rcons [seq (val _a.1, _a.2) | _a <- upval (projT1 (sigW (
    uconnected_Sr (Sub (source (right_tens V)) source_right_Sr) (Sub (source (right_parr blocking_parrK)) In))))]
(forward (right_parr blocking_parrK))) end.

(* Left correctness path when blocking_parr \in Sr:
   take the (switching) path given by the connectivity of Sr from the source of right v
   to the blocking_parr, and add right v at the beginning and right blocking_parr at the end. *)
Definition correctness_path_right_2 (In : (blocking_parr \in Sr) && (source (right_parr blocking_parrK) \in Sl)) : @upath _ _ G :=
match andP In with
| conj In _ =>
  backward (right_tens V) :: [seq (val _a.1, _a.2) | _a <- upval (projT1 (sigW (
    uconnected_Sr (Sub (source (right_tens V)) source_right_Sr) (Sub blocking_parr In))))]
 end.

Definition correctness_path_right : @upath _ _ G :=
  sum_rect (fun=> upath) correctness_path_right_1 correctness_path_right_2 (orb_sum HP').

Lemma left_tens_not_Sl : left_tens V \notin edge_set Sl.
Proof.
  rewrite in_set left_e. apply /nandP. right.
  destruct partition_disjoint as [_ [D _]].
  by rewrite disjoints1 in D.
Qed.

Lemma left_tens_not_Sr : left_tens V \notin edge_set Sr.
Proof.
  rewrite in_set left_e. apply /nandP. right.
  destruct partition_disjoint as [_ [_ [D _]]].
  by rewrite disjoints1 in D.
Qed.

Lemma right_tens_not_Sl : right_tens V \notin edge_set Sl.
Proof.
  rewrite in_set right_e. apply /nandP. right.
  destruct partition_disjoint as [_ [D _]].
  by rewrite disjoints1 in D.
Qed.

Lemma right_tens_not_Sr : right_tens V \notin edge_set Sr.
Proof.
  rewrite in_set right_e. apply /nandP. right.
  destruct partition_disjoint as [_ [_ [D _]]].
  by rewrite disjoints1 in D.
Qed.


Lemma correctness_path_left_1_supath In : supath switching v blocking_parr (correctness_path_left_1 In).
Proof.
  unfold correctness_path_left_1.
  destruct (non_splitting_tens NS) as [[p P] HP]. simpl in *. clear HP.
  destruct (andP In) as [In' _]. clear In P.
  set Ul := sigW (uconnected_Sl (Sub (source (left_tens V)) source_left_Sl) (Sub p In')).
  destruct Ul as [Ul UlK]. simpl. clear UlK.
  rewrite supath_cons /= left_e eq_refl 2!andb_true_r.
  apply /andP; split.
  { apply supath_switching_from_leftK, (@supath_from_induced_switching_left _ _ _
      (Sub (source (left_tens V)) source_left_Sl) (Sub p In')). }
  apply /mapP. move => [[e b] Ein].
  rewrite /switching left_e V /= => /eqP. case_if.
  contradict Ein. apply /negP/mapP. move => [[[a A] ba] /= _ As].
  inversion As. subst a ba. clear As.
  contradict A. apply /negP. exact left_tens_not_Sl.
Qed.

Lemma correctness_path_left_2_supath In : supath switching v blocking_parr (correctness_path_left_2 In).
Proof.
  unfold correctness_path_left_2.
  destruct (non_splitting_tens NS) as [[p P] HP]. simpl in *. clear HP.
  destruct (andP In) as [In'' In']. clear In. simpl in In'.
  set Ul := sigW (uconnected_Sl (Sub (source _) source_left_Sl) (Sub (source _) In')).
  destruct Ul as [Ul UlK]. simpl. clear UlK.
  rewrite supath_cons supath_rcons /= right_e left_e !eq_refl !andb_true_r.
  apply /andP; split; [apply /andP; split | ].
  { apply supath_switching_from_leftK, (@supath_from_induced_switching_left _ _ _
      (Sub (source _) source_left_Sl) (Sub (source _) In')). }
  - apply /mapP. move => [[e b] Ein].
    rewrite /switching right_e P /= => /eqP. case_if.
    contradict Ein. apply /negP/mapP. move => [[[a A] ba] /= _ As].
    inversion As. subst a ba. clear As.
    contradict A. apply /negP.
    rewrite !in_set. apply /nandP. right. apply /negP => In'''.
    destruct partition_disjoint as [D _].
    exact (disjointE D In''' In'').
  - apply /mapP. move => [[e b] Ein].
    rewrite /switching left_e V /= => /eqP. case_if.
    contradict Ein. apply /negP.
    rewrite mem_rcons in_cons. cbn.
    apply /norP. split.
    + clear. apply /nandP. left. clear b. apply /eqP => C.
      assert (F : vlabel (target (left_tens V)) = vlabel (target (right_parr ((ssrfun.svalP
        (exist (fun p : G => vlabel p = ⅋) p P)))))) by by rewrite C.
      clear C. contradict F.
      by rewrite left_e right_e /= V P.
    + apply /mapP. move => [[[a A] ba] /= _ As].
      inversion As. subst a ba. clear As.
      contradict A. apply /negP. exact left_tens_not_Sl.
Qed.

Lemma correctness_path_left_supath : supath switching v blocking_parr correctness_path_left.
Proof.
  unfold correctness_path_left.
  elim: (orb_sum HP') => In.
  - apply correctness_path_left_1_supath.
  - apply correctness_path_left_2_supath.
Qed.


Lemma correctness_path_right_1_supath In : supath switching v blocking_parr (correctness_path_right_1 In).
Proof.
  unfold correctness_path_right_1.
  destruct (non_splitting_tens NS) as [[p P] HP]. simpl in *. clear HP.
  destruct (andP In) as [In'' In']. clear In. simpl in In'.
  set Ur := sigW (uconnected_Sr (Sub (source _) source_right_Sr) (Sub (source _) In')).
  destruct Ur as [Ur UrK]. simpl. clear UrK.
  rewrite supath_cons supath_rcons map_rcons mem_rcons in_cons /= !right_e !eq_refl !andb_true_r.
  apply /andP; split; [apply /andP; split | apply /norP; split ].
  - apply supath_switching_from_leftK, (@supath_from_induced_switching_left _ _ _
      (Sub (source _) source_right_Sr) (Sub (source _) In')).
  - apply /mapP. move => [[e b] Ein].
    rewrite /switching right_e P /= => /eqP. case_if.
    contradict Ein. apply /negP/mapP. move => [[[a A] ba] /= _ As].
    inversion As. subst a ba. clear As.
    contradict A. apply /negP.
    rewrite !in_set. apply /nandP. right. apply /negP => In'''.
    destruct partition_disjoint as [D _].
    exact (disjointE D In'' In''').
  - by rewrite /switching !right_e V P.
  - apply /mapP. move => [[e b] Ein].
    rewrite /switching right_e V /= => /eqP. case_if.
    contradict Ein. apply /negP/mapP. move => [[[a A] ba] /= _ As].
    inversion As. subst a ba. clear As.
    contradict A. apply /negP.
    rewrite !in_set right_e.
    apply /nandP. right.
    destruct partition_disjoint as [_ [_ [D _]]].
    by rewrite disjoints1 in D.
Qed.

Lemma correctness_path_right_2_supath In : supath switching v blocking_parr (correctness_path_right_2 In).
Proof.
  unfold correctness_path_right_2.
  destruct (non_splitting_tens NS) as [[p P] HP]. simpl in *. clear HP.
  destruct (andP In) as [In' _]. clear In P.
  set U := sigW (uconnected_Sr (Sub (source (right_tens V)) source_right_Sr) (Sub p In')).
  destruct U as [U UK]. simpl. clear UK.
  rewrite supath_cons /= right_e eq_refl 2!andb_true_r.
  apply /andP; split.
  { apply supath_switching_from_leftK, (@supath_from_induced_switching_left _ _ _
      (Sub (source _) source_right_Sr) (Sub p In')). }
  apply /mapP. move => [[e b] Ein].
  rewrite /switching right_e V /= => /eqP. case_if.
  contradict Ein. apply /negP/mapP. move => [[[a A] ba] /= _ As].
  inversion As. subst a ba. clear As.
  contradict A. apply /negP. exact right_tens_not_Sr.
Qed.

Lemma correctness_path_right_supath : supath switching v blocking_parr correctness_path_right.
Proof.
  unfold correctness_path_right.
  elim: (orb_sum HP') => In.
  - apply correctness_path_right_1_supath.
  - apply correctness_path_right_2_supath.
Qed.

Lemma correctness_path_left_1_strong In : strong (correctness_path_left_1 In).
Proof. rewrite /strong /correctness_path_left_1. destruct (andP In). rewrite left_e V. caseb. Qed.

Lemma correctness_path_left_2_strong In : strong (correctness_path_left_2 In).
Proof. rewrite /strong /correctness_path_left_2. destruct (andP In). rewrite left_e V. caseb. Qed.

Lemma correctness_path_left_strong : strong correctness_path_left.
Proof.
  rewrite /strong /correctness_path_left.
  elim: (orb_sum HP') => In /=.
  - apply correctness_path_left_1_strong.
  - apply correctness_path_left_2_strong.
Qed.

Lemma correctness_path_right_1_strong In : strong (correctness_path_right_1 In).
Proof. rewrite /strong /correctness_path_right_1. destruct (andP In). rewrite right_e V. caseb. Qed.

Lemma correctness_path_right_2_strong In : strong (correctness_path_right_2 In).
Proof. rewrite /strong /correctness_path_right_2. destruct (andP In). rewrite right_e V. caseb. Qed.

Lemma correctness_path_right_strong : strong correctness_path_right.
Proof.
  rewrite /strong /correctness_path_right.
  elim: (orb_sum HP') => In /=.
  - apply correctness_path_right_1_strong.
  - apply correctness_path_right_2_strong.
Qed.

(* These paths are not disjoint for switching because they both use in-edges of the blocking parr *)
Lemma correctness_path_disjoint : upath_disjoint2 correctness_path_left correctness_path_right.
Proof.
  unfold upath_disjoint2, correctness_path_left, correctness_path_right.
  elim: (orb_sum HP') => In /=.
  - unfold correctness_path_left_1, correctness_path_right_1.
    destruct (non_splitting_tens NS) as [[p P] HP]. simpl in *. clear HP.
    destruct (andP In) as [In0 In1]. clear In. simpl in *.
    set Ul := sigW (uconnected_Sl (Sub (source _) source_left_Sl) (Sub p In0)).
    set Ur := sigW (uconnected_Sr (Sub (source _) source_right_Sr) (Sub (source _) In1)).
    destruct Ul as [Ul UlK], Ur as [Ur UrK]. simpl. clear UlK UrK.
    rewrite map_rcons disjoint_cons disjoint_sym disjoint_cons disjoint_rcons in_cons in_rcons.
    splitb.
    + apply /eqP. apply left_neq_right.
    + apply /eqP. move => /= F.
      assert (F' : vlabel (target (left_tens V)) = ⅋) by by rewrite F right_e P.
      by rewrite left_e V in F'.
    + apply /mapP. move => [[e b] Ein /= ?]. subst e.
      contradict Ein. apply /negP/mapP. move => [[[a A] ba] /= _ As].
      inversion As. subst a ba. clear As.
      contradict A. apply /negP.
      exact left_tens_not_Sr.
    + apply /mapP. move => [[e b] Ein /= ?]. subst e.
      contradict Ein. apply /negP/mapP. move => [[[a A] ba] /= _ As].
      inversion As. subst a ba. clear As.
      contradict A. apply /negP.
      exact right_tens_not_Sl.
    + apply /mapP. move => [[e b] Ein /= ?]. subst e.
      contradict Ein. apply /negP/mapP. move => [[[a A] ba] /= _ As].
      inversion As. subst a ba. clear As.
      contradict A. apply /negP.
      rewrite !in_set. apply /nandP. left. apply /negP => C.
      destruct partition_disjoint as [D _].
      exact (disjointE D C In1).
    + apply /disjointP => e /mapP[[ar br] /= Ar ?] /mapP[[al bl] /= Al ?]. subst ar al.
      revert Ar Al. move => /mapP[[[jr Inr] bjr] /= _ EJR]  /mapP[[[jl Inl] bjl] /= _ EJL].
      inversion EJR. inversion EJL. subst jr bjr jl bjl. clear EJR EJL.
      revert Inl Inr. rewrite !in_set => /andP[Inl _] /andP[Inr _].
      destruct partition_disjoint as [D _].
      exact (disjointE D Inl Inr).
  - unfold correctness_path_left_2, correctness_path_right_2.
    destruct (non_splitting_tens NS) as [[p P] HP]. simpl in *. clear HP.
    destruct (andP In) as [In0 In1]. clear In. simpl in *.
    set Ul := sigW (uconnected_Sl (Sub (source _) source_left_Sl) (Sub (source _) In1)).
    set Ur := sigW (uconnected_Sr (Sub (source _) source_right_Sr) (Sub p In0)).
    destruct Ul as [Ul UlK], Ur as [Ur UrK]. simpl. clear UlK UrK.
    rewrite map_rcons disjoint_cons disjoint_rcons disjoint_sym disjoint_cons !in_cons.
    splitb.
    + apply /eqP. apply left_neq_right.
    + apply /mapP. move => [[e b] Ein /= ?]. subst e.
      contradict Ein. apply /negP/mapP. move => [[[a A] ba] /= _ As].
      inversion As. subst a ba. clear As.
      contradict A. apply /negP.
      exact left_tens_not_Sr.
    + apply /eqP. move => /= F.
      assert (F' : vlabel (target (right_tens V)) = ⅋) by by rewrite -F right_e P.
      by rewrite right_e V in F'.
    + apply /mapP. move => [[e b] Ein /= ?]. subst e.
      contradict Ein. apply /negP/mapP. move => [[[a A] ba] /= _ As].
      inversion As. subst a ba. clear As.
      contradict A. apply /negP.
      rewrite !in_set. apply /nandP. left. apply /negP => C.
      destruct partition_disjoint as [D _].
      exact (disjointE D In1 C).
    + apply /mapP. move => [[e b] Ein /= ?]. subst e.
      contradict Ein. apply /negP/mapP. move => [[[a A] ba] /= _ As].
      inversion As. subst a ba. clear As.
      contradict A. apply /negP.
      exact right_tens_not_Sl.
    + apply /disjointP => e /mapP[[ar br] /= Ar ?] /mapP[[al bl] /= Al ?]. subst ar al.
      revert Ar Al. move => /mapP[[[jr Inr] bjr] /= _ EJR]  /mapP[[[jl Inl] bjl] /= _ EJL].
      inversion EJR. inversion EJL. subst jr bjr jl bjl. clear EJR EJL.
      revert Inl Inr. rewrite !in_set => /andP[Inl _] /andP[Inr _].
      destruct partition_disjoint as [D _].
      exact (disjointE D Inl Inr).
Qed.

Lemma correctness_path_left_neq_nil : correctness_path_left <> [::].
Proof.
  intro QN.
  assert (Q := correctness_path_left_supath).
  revert Q. rewrite {}QN => /supath_of_nilP.
  destruct (non_splitting_tens NS) as [[p P] ?]. simpl. clear - P V.
  intros. subst p. by rewrite V in P.
Qed.

Lemma correctness_path_right_neq_nil : correctness_path_right <> [::].
Proof.
  intro QN.
  assert (Q := correctness_path_right_supath).
  revert Q. rewrite {}QN => /supath_of_nilP.
  destruct (non_splitting_tens NS) as [[p P] ?]. simpl. clear - P V.
  intros. subst p. by rewrite V in P.
Qed.

(* TODO montrer que les aretes de fin de ces chemins sont les aretes entrantes de p *)


(* Definition upath_simpl {Lv Le : Type} {G' : graph Lv Le}
  (p : @upath _ _ G') := uniq [seq utarget x | x <- p]. *)

(* Lemma supath_simplK {G' : proof_net} {s t : G'} (p : upath) :
  supath switching s t p -> upath_simpl p /\ s \notin [seq utarget x | x <- p].
Proof.
  intro S. split.
  - unfold upath_simpl.
    apply /(uniqP s). intros n m. rewrite /in_mem /=. intros N M NM.
    assert (N' := mem_nth s N).
    assert (M' := mem_nth s M).
    revert N' M' NM.
    set a := nth s [seq utarget _x | _x <- p] n.
    set b := nth s [seq utarget _x | _x <- p] m.

Check mem_nth.
Check uniqP.
Admitted. *)

(* Là il faudrait une notion de chemins simple = ne passe pas 2 fois par le même sommet *)
(* TODO dans basic ? un fichier strong et upath_disjoint2 ? *)
Lemma strong_test1 {G' : proof_net} {s i t : G'} (P : Supath switching s i)
  (Q : Supath switching i t) :
(*   t \notin [seq usource e | e <- (upval P)] -> *)
  (t \notin [seq usource e | e <- (upval P)]) || (vlabel t != ⅋) ->
  strong P -> strong Q -> upath_disjoint2 P Q -> forall a b, a \in upval P -> b \in upval Q ->
switching a.1 <> switching b.1.
Proof. clear.
(* 1st hyp : sinon peut casser *)
(* Preuve : si ce n'est pas le cas, prendre le dernier a de P et le premier b de Q tel que c'est le cas.
P_{a->} . Q_{->b} est un switching cycle, non vide car Q strong *)
  move => T SP SQ D [a ab] [e eb] Ain Ein /= AE.
  destruct P as [p P], Q as [q Q]. simpl in *.
  assert (Ra : (fun f => [exists f', (f'\in q) && (switching f.1 == switching f'.1)]) (a, ab)).
  { apply /existsP. exists (e, eb). by rewrite Ein /= AE !eq_refl. }
  destruct (in_elt_sub_last Ra Ain) as [k [[ke keb] [PK [Ke Kl']]]]. clear Ra a ab e eb Ain Ein AE.
  revert Ke => /existsP[ke' /andP[Ke Tke]].
  assert (Rb : (fun f => switching ke == switching f.1) ke') by assumption.
  destruct (in_elt_sub_fst Rb Ke) as [n [[ne neb] [QN [Ne Nf]]]]. clear ke' Rb Ke Tke.
  revert Ne => /= /eqP-Ne.
  set p' := (if keb then [::] else [:: backward ke]) ++ drop k.+1 p.
  set q' := take n q ++ (if neb then [:: forward ne] else [::]).
  assert (KN : ke <> ne).
  { intros ?. subst ne.
    revert D. unfold upath_disjoint2 => /disjointP/(_ ke)-D. apply D.
    - change ke with (ke, keb).1. apply map_f.
      rewrite PK mem_cat in_cons. caseb.
    - change ke with (ke, neb).1. apply map_f.
      rewrite QN mem_cat in_cons. caseb. }
  assert (Teq := switching_eq Ne).
  revert Ne. unfold switching. rewrite -Teq. case:ifP => /eqP-Vtke; last by cbnb. move => _.
  assert (K_or_N : keb || ~~neb).
 (* idée : c'est le cas où les 2 utilisent les aretes entrantes du parr ; dq = ccl de parr, qui est aussi dans P car P est strong et sort par une arete de ce parr, contradict disjoint *)
  { destruct keb, neb; try by [].
    contradict T. apply /negP/norP. rewrite !negb_involutive.
    enough (t = usource (backward ke)) as ->.
    { split.
      - apply (@map_f _ _ (fun e => usource e)).
        rewrite PK mem_cat in_cons. caseb.
      - by rewrite /= Vtke. }
    simpl.
    destruct (drop n.+1 q) as [ | d dq] eqn:DQ; rewrite DQ in QN.
    { rewrite QN cats1 in Q.
      destruct (supath_endpoint {| upvalK := Q |}) as [_ <-].
      by rewrite /= map_rcons last_rcons -Teq. }
    assert (d = forward (ccl_parr Vtke)).
    { assert (QN' : q = take n q ++ [:: forward ne ; d] ++ dq) by by rewrite {1}QN.
      clear QN.
      rewrite {}QN' in Q. apply supath_subK in Q.
      revert Q. rewrite !supath_cons supath_of_nil /= in_cons in_nil !andb_true_r orb_false_r -Teq
        => /andP[/andP[/andP[_ /eqP-Sd] _]].
      rewrite /switching -Teq Vtke /= => S.
      destruct d as [d []]; simpl in Sd.
      - f_equal. by apply ccl_eq.
      - revert S. by rewrite /= Sd Vtke /= eq_refl. }
    subst d.
    destruct (take k p) as [ | tp d _] eqn:TP using last_ind; rewrite TP in PK.
    { contradict SP. apply /negP. by rewrite /strong PK /= Vtke. }
    rewrite cat_rcons in PK.
    assert (d = backward (ccl_parr Vtke)).
    { assert (PK' : p = tp ++ [:: d ; backward ke] ++ drop k.+1 p) by by rewrite {1}PK.
      clear PK.
      rewrite {}PK' in P. apply supath_subK in P.
      revert P. rewrite !supath_cons supath_of_nil /= in_cons in_nil !andb_true_r orb_false_r
        => /andP[/andP[/andP[_ /eqP-Sd] _]].
      rewrite /switching Vtke /= => S.
      destruct d as [d []]; simpl in Sd.
      - revert S. by rewrite /= -Sd Vtke /= eq_refl.
      - f_equal. by apply ccl_eq. }
    subst d.
    contradict D. unfold upath_disjoint2. apply /negP/disjointP => /(_ (ccl_parr Vtke))-D.
    apply D.
    * change (ccl_parr Vtke) with (backward (ccl_parr Vtke)).1.
      apply map_f. rewrite PK mem_cat !in_cons. caseb.
    * change (ccl_parr Vtke) with (forward (ccl_parr Vtke)).1.
      apply map_f. rewrite QN mem_cat !in_cons. caseb. }
  assert (Kl : forall z f', z \in p' -> f' \in q' -> switching z.1 <> switching f'.1).
  { intros z f Z F.
    revert F Z. rewrite /p' /q' !mem_cat => /orP-F /orP[Z | Z].
    - destruct keb; try by [].
      revert Z. rewrite in_cons in_nil orb_false_r => /eqP-?; subst z. simpl.
      destruct F as [F | F].
      + apply /eqP. by apply Nf.
      + by destruct neb.
    - revert Kl' => /(_ z Z)/existsPn/(_ f)/nandP[F' | /eqP-? //].
      contradict F'. apply /negP/negPn.
      rewrite QN mem_cat in_cons.
      destruct F as [-> | F]; first by [].
      destruct neb; last by [].
      revert F. rewrite in_cons in_nil orb_false_r => /eqP-?; subst f. caseb. }
  clear T SP D Kl'.
  assert (Nf' : forall z, z \in q' -> switching ke <> switching z.1 \/ z = forward ne).
  { intro z. rewrite /p' mem_cat => /orP[Z | Z]; [left | right].
    - apply /eqP. by apply Nf.
    - destruct neb; try by [].
      revert Z. by rewrite in_cons in_nil orb_false_r => /eqP-->. }
  clear Nf.
  assert (P' : supath switching (target ke) i p').
  { rewrite /p'. destruct keb; simpl.
    - assert (PK' : p = rcons (take k p) (forward ke) ++ drop k.+1 p ++ [::])
        by by rewrite cats0 cat_rcons.
      rewrite {}PK' in P. apply supath_subK in P. by rewrite /= map_rcons last_rcons in P.
    - assert (PK' : p = take k p ++ (backward ke :: drop k.+1 p) ++ [::]) by by rewrite cats0.
      rewrite {}PK' in P. apply supath_subK in P. simpl in P.
      destruct (supath_endpoint {| upvalK := P |}) as [Hr _]. simpl in Hr.
      by rewrite /= -{}Hr /= in P. }
  clear P PK.
  assert (Q' : supath switching i (target ke) q').
  { rewrite /q'. destruct neb.
    - rewrite cats1.
      assert (QN' : q = [::] ++ rcons (take n q) (forward ne) ++ drop n.+1 q)
        by by rewrite /= cat_rcons.
      rewrite {}QN' in Q. apply supath_subK in Q. simpl in Q.
      destruct (supath_endpoint {| upvalK := Q |}) as [_ Hr]. rewrite /= map_rcons last_rcons /= in Hr.
      by rewrite /= -{}Hr /= -Teq in Q.
    - rewrite cats0.
      assert (QN' : q = [::] ++ take n q ++ backward ne :: drop n.+1 q) by by [].
      rewrite {}QN' in Q. apply supath_subK in Q. by rewrite /= -Teq in Q. }
  clear Q.
  assert (PQ : p' ++ q' <> [::]).
  { rewrite /p' /q'. destruct keb, neb, (take n q) eqn:TQ, (drop k.+1 p) eqn:DP; try by [].
    rewrite TQ /= in QN.
    contradict SQ. apply /negP.
    by rewrite /strong QN /= -Teq Vtke. }
  clear SQ QN.
  revert P' Q'  Nf' Kl PQ. generalize p' q'. clear p' q' p q. intros p q P Q Nf Kl PQ.
  enough (D : upath_disjoint switching {| upvalK := P |} {| upvalK := Q |}). (* TODO define upath_disjoint on path instead of supath *)
  { destruct (p_correct G') as [Ac _].
    assert (F := Ac _ (supath_cat D)). contradict F.
    cbnb. }
  rewrite /upath_disjoint /=.
  apply /disjointP => f /mapP[x Xq ?] /mapP[y Yp]. subst f.
  by apply Kl.
Qed.

Lemma strong_test {G' : proof_net} {s i t : G'} (P : Supath switching s i)
  (Q : Supath switching i t) :
  (t \notin [seq usource e | e <- (upval P)]) || (vlabel t != ⅋) ->
  strong P -> strong Q -> upath_disjoint2 P Q -> upath_disjoint switching P Q.
Proof. clear.
  intros T SP SQ D.
  rewrite /upath_disjoint.
  apply /disjointP.
  move => E /mapP[a A AE] /mapP[b B BE]. subst E.
  contradict BE. by apply (strong_test1 T SP SQ).
Qed. (* TODO à utiliser pour ce servir de disjoint2 *)

Lemma strong_rev {G' : base_graph} (p : @upath _ _ G') :
  strong (upath_rev p) = last true [seq (vlabel (utarget e) != ⅋) || ~~e.2 | e <- p]. (* TODO écrire strong comme ça? *)
Proof.
  case: (lastP p) => {p} [ // | p e].
  by rewrite upath_rev_rcons map_rcons last_rcons /= negb_involutive.
Qed.

Lemma last_correctness_path_left_not_ccl :
  (last (forward (left_tens V)) (correctness_path_left)).1 <> ccl_parr blocking_parrK.
Proof.
  intro F.
  enough (D : upath_disjoint switching
     {| upvalK := correctness_path_right_supath |}
    (supath_rev {| upvalK := correctness_path_left_supath |})).
  { destruct (p_correct G) as [A _]. specialize (A _ (supath_cat D)). contradict A. cbnb.
    apply /eqP. rewrite cat_nil upath_rev_nil. apply /nandP. right. apply /eqP.
    apply correctness_path_left_neq_nil. }
  assert (L : last (forward (left_tens V)) correctness_path_left =
    backward (ccl_parr (projT2 (projT1 (non_splitting_tens NS))))).
  { destruct (last (forward (left_tens V)) correctness_path_left) as [e []] eqn:EB;
      last by f_equal.
    exfalso. simpl in F. subst e.
    destruct (supath_endpoint {| upvalK := correctness_path_left_supath |}) as [_ Hr].
    contradict Hr. simpl.
    set f := fun e => utarget e.
    assert (Hr : v = f (forward (left_tens V))) by by rewrite /f left_e.
    rewrite {1}Hr {Hr} last_map /f {f} EB /=.
    destruct (non_splitting_tens NS) as [[p P] HP]. simpl. clear HP.
    replace (ssrfun.svalP (exist (fun _p : G => vlabel _p = ⅋) p P)) with P
      by apply eq_irrelevance.
    assert (Hr : p = source (ccl_parr P)) by by rewrite ccl_e.
    rewrite [in RHS]Hr {Hr}.
    apply nesym, no_selfloop. }
  clear F.
  apply strong_test; simpl.
  - by rewrite V /= orb_true_r.
  - apply correctness_path_right_strong.
  - rewrite strong_rev.
    set f := fun e => (vlabel (utarget e) != ⅋) || ~~ e.2.
    replace true with (f (forward (left_tens V))) by by rewrite /f left_e V.
    by rewrite last_map /f {f} /= L orb_true_r.
  - rewrite upath_disjoint2_sym. apply upath_disjoint2_rev, correctness_path_disjoint.
Qed.

Lemma last_correctness_path_right_not_ccl :
  (last (forward (left_tens V)) (correctness_path_right)).1 <> ccl_parr blocking_parrK.
Proof.
  intro F.
  enough (D : upath_disjoint switching
     {| upvalK := correctness_path_left_supath |}
    (supath_rev {| upvalK := correctness_path_right_supath |})).
  { destruct (p_correct G) as [A _]. specialize (A _ (supath_cat D)). contradict A. cbnb.
    apply /eqP. rewrite cat_nil. apply /nandP. left. apply /eqP.
    apply correctness_path_left_neq_nil. }
  assert (L : last (forward (left_tens V)) correctness_path_right =
    backward (ccl_parr (projT2 (projT1 (non_splitting_tens NS))))).
  { destruct (last (forward (left_tens V)) correctness_path_right) as [e []] eqn:EB;
      last by f_equal.
    exfalso. simpl in F. subst e.
    destruct (supath_endpoint {| upvalK := correctness_path_right_supath |}) as [_ Hr].
    contradict Hr. simpl.
    set f := fun e => utarget e.
    assert (Hr : v = f (forward (left_tens V))) by by rewrite /f left_e.
    rewrite {1}Hr {Hr} last_map /f {f} EB /=.
    destruct (non_splitting_tens NS) as [[p P] HP]. simpl. clear HP.
    replace (ssrfun.svalP (exist (fun _p : G => vlabel _p = ⅋) p P)) with P
      by apply eq_irrelevance.
    assert (Hr : p = source (ccl_parr P)) by by rewrite ccl_e.
    rewrite [in RHS]Hr {Hr}.
    apply nesym, no_selfloop. }
  clear F.
  apply strong_test; simpl.
  - by rewrite V /= orb_true_r.
  - apply correctness_path_left_strong.
  - rewrite strong_rev.
    set f := fun e => (vlabel (utarget e) != ⅋) || ~~ e.2.
    replace true with (f (forward (left_tens V))) by by rewrite /f left_e V.
    by rewrite last_map /f {f} /= L orb_true_r.
  - rewrite upath_disjoint2_sym. apply upath_disjoint2_rev.
    rewrite upath_disjoint2_sym. apply correctness_path_disjoint.
Qed.

Corollary test001 :
  ((last (forward (left_tens V)) (correctness_path_left) == forward (left_parr blocking_parrK)) &&
  (last (forward (left_tens V)) (correctness_path_right) == forward (right_parr blocking_parrK))) ||
  ((last (forward (left_tens V)) (correctness_path_left) == forward (right_parr blocking_parrK)) &&
  (last (forward (left_tens V)) (correctness_path_right) == forward (left_parr blocking_parrK))).
Proof.
  destruct (supath_endpoint {| upvalK := correctness_path_left_supath |}) as [_ L].
  destruct (supath_endpoint {| upvalK := correctness_path_right_supath |}) as [_ R].
  revert L R. rewrite /=.
  assert (last v = last (utarget (forward (left_tens V)))) as -> by by rewrite left_e.
  rewrite !(last_map (fun e => utarget e)).
  assert (Hl := last_correctness_path_left_not_ccl).
  assert (Hr := last_correctness_path_right_not_ccl).
  revert Hl Hr.
  destruct (non_splitting_tens NS) as [[p P] HP]. simpl. clear HP.
  replace (ssrfun.svalP (exist (fun _p : G => vlabel _p = ⅋) p P)) with P
    by apply eq_irrelevance.
  set el' := last (forward (left_tens V)) correctness_path_left.
  destruct el' as [el []] eqn:El; unfold el' in El; clear el'; simpl.
  2:{ intros Hl _ S. contradict Hl. by apply ccl_eq. }
  set er' := last (forward (left_tens V)) correctness_path_right.
  destruct er' as [er []] eqn:Er; unfold er' in Er; clear er'; simpl.
  2:{ intros _ Hr _ S. contradict Hr. by apply ccl_eq. }
  intros _ _ Tl Tr.
  assert (el \in [set left (or_intror P); right (or_intror P)] /\
    er \in [set left (or_intror P); right (or_intror P)]) as [Lin Rin]
    by by rewrite -right_set !in_set Tl Tr.
  clear Tl Tr.
  assert (el <> er).
  { intros ?. subst er.
    assert (F := correctness_path_disjoint). contradict F.
    rewrite /upath_disjoint2. apply /negP/disjointP => /(_ el)-H. apply H; clear H.
    - change el with (forward el).1. apply map_f.
      rewrite -El. apply mem3_last, correctness_path_left_neq_nil.
    - change el with (forward el).1. apply map_f.
      rewrite -Er. apply mem3_last, correctness_path_right_neq_nil. }
  revert Lin Rin. rewrite !in_set => /orP[/eqP-? | /eqP-?] /orP[/eqP-? | /eqP-?]; subst el er;
  rewrite !eq_refl /= ?andb_true_r ?orb_true_r //.
(* idée : last arrive à blocking_parr, ne peut pas être ccl ; par disjointness, l'un
est let et l'autre est parr *)
Qed.

(* Conclusion : on a 2 strong paths disjoints de in-edges de V vers in-edges de P ;
  c'est ce qu'on voulait, pas besoin de plus (enfin si, de remplacer les vlabel v = tens
  par tens ou cut *)


(* TODO define generally and use this : + warning *)(*
Coercion supath_to_Supath {s t : G} {p : upath} : supath switching s t p -> Supath switching s t :=
  (fun S => {| upvalK := S |}). *)


(* And then, descending path, followed by critical path *)
(* Sketch of the end:
- for a non-terminal vertex -> descending path to a terminal one (see mll_basic)
- correctness and descending path are strong
- concat of strong paths is a strong path
- strong cycle -> switching cycle -> incorrect
- build a critical path by concatenating these paths, strong, can be prolonged while target is not sequentializing
- but this gives an infinite supath, absurd by finType (hard?)
*)
(* TODO follow the proof I wrote on MALL *)


(* TODO use tens case to conclude on cut ? is it enough to just rework the proof above, mainly replacing
vlabel v = ⊗ with vlabel v = ⊗ \/ vlabel v = cut? *)

End Non_splitting_tens.

(* TODO now ''just'' to build the critical path, in mll_pn_to_seq_th *)

End Splitting_tens.

End Atoms.