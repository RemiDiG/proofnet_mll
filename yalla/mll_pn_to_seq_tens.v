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


Section Splitting_tens.
Context {G : proof_net}.

Lemma utree_switching_left : utree (@switching_left G).
Proof. split; [apply uacyclic_swithching_left, G | apply uconnected_from_nb1, G]. Qed.

Lemma partition_terminal_ccl {v : G} (V : vlabel v = ⊗) :
  terminal v ->
  forall x, utree_part (@switching_left_sinj _ G) utree_switching_left v x = Some (ccl_tens V) ->
  pblock (preim_partition (utree_part (@switching_left_sinj _ G) utree_switching_left v) [set: G]) x
    = [set target (ccl_tens V)].
Proof.
  set F := @switching_left_sinj _ G.
  rewrite (terminal_tens_parr (or_introl V)) => /eqP-C.
  intros x X. apply /setP => y.
  assert (Spart := preim_partitionP (utree_part F utree_switching_left v) [set: G]).
  revert Spart => /andP[/eqP-Cov /andP[Triv _]].
  rewrite in_set -eq_pblock // ?Cov {Cov Triv} // preim_partition_pblock_eq // X {X}.
  destruct (eq_comparable y (target (ccl_tens V))) as [? | Y].
  - subst y. rewrite eq_refl. apply /eqP.
    unfold utree_part. destruct (utree_unique_path F utree_switching_left v (target (ccl_tens V))) as [P Pu].
    assert (S : supath switching_left v (target (ccl_tens V)) [:: forward (ccl_tens V)]).
    { rewrite /supath /= in_cons negb_orb ccl_e. splitb.
      by rewrite /switching_left C. }
    specialize (Pu {| upvalK := S |}). by subst P.
  - transitivity false; last by (symmetry; apply /eqP).
    apply /eqP.
    unfold utree_part. destruct (utree_unique_path F utree_switching_left v y) as [[p P] _].
    destruct p as [ | (e1, b1) p]; first by []. cbnb.
    destruct (eq_comparable e1 (ccl_tens V)); last by apply nesym.
    subst e1. exfalso.
    rewrite supath_cons in P. revert P => /andP[/andP[/andP[P1 /eqP-Vb1] U1] /eqP-N1].
    assert (b1 = true).
    { destruct b1; trivial. exfalso. destruct utree_switching_left as [A _].
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

Lemma partition_terminal_utree_part {v : G} (V : vlabel v = ⊗) (x : G) :
  utree_part (@switching_left_sinj _ G) utree_switching_left v x
    \in [set None; Some (left_tens V); Some (right_tens V); Some (ccl_tens V)].
Proof.
  set F := @switching_left_sinj _ G.
  unfold utree_part. destruct (utree_unique_path F utree_switching_left v x) as [[[ | e p] P] _].
  { by rewrite !in_set. }
  rewrite supath_cons in P. revert P => /andP[/andP[/andP[_ /eqP-EV] _] _].
  destruct e as (e, []); simpl in EV.
  - assert (E := ccl_eq (or_introl V) EV). subst e.
    rewrite !in_set. caseb.
  - enough (E : e \in [set left_tens V; right_tens V]).
    { revert E. rewrite !in_set => /orP[/eqP--> | /eqP-->]; caseb. }
    by rewrite -right_set in_set EV.
Qed.

Lemma partition_terminal_utree_part_ccl {v : G} (V : vlabel v = ⊗) :
  terminal v ->
  utree_part (@switching_left_sinj _ G) utree_switching_left v (target (ccl_tens V))
    = Some (ccl_tens V).
Proof.
  set F := @switching_left_sinj _ G.
  rewrite (terminal_tens_parr (or_introl V)) => /eqP-C.
  unfold utree_part. destruct (utree_unique_path F utree_switching_left v (target (ccl_tens V))) as [P Pu].
  assert (S : supath switching_left v (target (ccl_tens V)) [:: forward (ccl_tens V)]).
  { rewrite /supath /= in_cons negb_orb ccl_e /switching_left C. splitb. }
  specialize (Pu {| upvalK := S |}). by subst P.
Qed.

Lemma partition_terminal_utree_part_left {v : G} (V : vlabel v = ⊗) :
  utree_part (@switching_left_sinj _ G) utree_switching_left v (source (left_tens V))
    = Some (left_tens V).
Proof.
  set F := @switching_left_sinj _ G.
  unfold utree_part. destruct (utree_unique_path F utree_switching_left v (source (left_tens V))) as [P Pu].
  assert (S : supath switching_left v (source (left_tens V)) [:: backward (left_tens V)]).
  { rewrite /supath /= in_cons negb_orb left_e /switching_left left_e V. splitb. }
  specialize (Pu {| upvalK := S |}). by subst P. (* TODO tout simplifier comme ça ! *)
Qed.

Lemma partition_terminal_utree_part_right {v : G} (V : vlabel v = ⊗) :
  utree_part (@switching_left_sinj _ G) utree_switching_left v (source (right_tens V))
    = Some (right_tens V).
Proof.
  set F := @switching_left_sinj _ G.
  unfold utree_part. destruct (utree_unique_path F utree_switching_left v (source (right_tens V))) as [P Pu].
  assert (S : supath switching_left v (source (right_tens V)) [:: backward (right_tens V)]).
  { rewrite /supath /= in_cons negb_orb right_e /switching_left right_e V. splitb. }
  specialize (Pu {| upvalK := S |}). by subst P.
Qed.

Lemma partition_terminal_eq {v : G} (V : vlabel v = ⊗) :
  terminal v ->
  preim_partition (utree_part (@switching_left_sinj _ G) utree_switching_left v) [set: G] =
  [set pblock (preim_partition (utree_part (@switching_left_sinj _ G) utree_switching_left v) [set: G])
         (source (left_tens V));
       pblock (preim_partition (utree_part (@switching_left_sinj _ G) utree_switching_left v) [set: G])
         (source (right_tens V));
       [set v]; [set target (ccl_tens V)]].
Proof.
  set T := utree_switching_left.
  set F := @switching_left_sinj _ G.
  intro VT.
  rewrite [in LHS]preim_partition_eq.
  apply /setP => P.
  symmetry.
  destruct (P \in [set pblock (preim_partition (utree_part F T v) [set: G]) x
    | x in [set: G]]) eqn:Pin.
  - revert Pin => /imsetP[x _ ?]. subst P.
    assert (Imx := partition_terminal_utree_part V x).
    revert Imx. rewrite !in_set => /orP[/orP[/orP[/eqP-X | /eqP-X] | /eqP-X] | /eqP-X].
    + apply utree_part_None in X. subst x.
      rewrite utree_part_v. caseb.
    + enough (pblock (preim_partition (utree_part F T v) [set: G]) x =
              pblock (preim_partition (utree_part F T v) [set: G]) (source (left_tens V)))
        as -> by caseb.
      apply /eqP. by rewrite preim_partition_pblock_eq // X partition_terminal_utree_part_left.
    + enough (pblock (preim_partition (utree_part F T v) [set: G]) x =
              pblock (preim_partition (utree_part F T v) [set: G]) (source (right_tens V)))
        as -> by caseb.
      apply /eqP. by rewrite preim_partition_pblock_eq // X partition_terminal_utree_part_right.
    + rewrite (partition_terminal_ccl VT X). caseb.
  - revert Pin => /negP/negP-Pin.
    apply /negP/negP.
    rewrite !in_set !negb_orb -(utree_part_v F)
      -(partition_terminal_ccl VT (partition_terminal_utree_part_ccl V VT)).
    splitb.
    all: apply /eqP => ?; subst P.
    all: contradict Pin; apply /negP/negPn.
    all: by apply imset_f.
Qed.
(* TODO this is a general lemma on trees, prove it purely in the graph part *)
(* généraliser : dans utree_part, un pblock par arete (la target / source non v) + pblock de v, qui est lui même *)


(* In the switching graph without any right premise, there is a partition separating the tree into
   the vertices on the left of v, and on its right *)
Lemma partition_terminal {v : G} (V : vlabel v = ⊗) :
  terminal v ->
  {'(Sl, Sr) : {set G} * {set G} & partition [set Sl; Sr; [set v]; [set target (ccl_tens V)]] [set: G] /\
    uconnected (@switching_left (induced Sl)) /\ uconnected (@switching_left (induced Sr)) /\
    source (left_tens V) \in Sl /\ source (right_tens V) \in Sr}.
Proof.
  set T := utree_switching_left. set F := @switching_left_sinj _ G.
  intro VT.
  assert (Spart := preim_partitionP (utree_part F T v) [set: G]).
  revert Spart => /andP[/eqP-Cov _].
  exists (pblock (preim_partition (utree_part F T v) [set: G]) (source (left_tens V)),
          pblock (preim_partition (utree_part F T v) [set: G]) (source (right_tens V))).
  split; [ | split; [ | split; [ | split]]]; trivial.
  - rewrite -(partition_terminal_eq V VT). apply tree_partition.
  - apply (@uconnected_utree_part _ _ _ _ _ _ _ _ F T v
      (@switching_left_induced_None_to _ _ _) (@switching_left_induced_eq_to _ _ _)).
    rewrite {2}(partition_terminal_eq V VT) !in_set. caseb.
  - apply (@uconnected_utree_part _ _ _ _ _ _ _ _ F T v
      (@switching_left_induced_None_to _ _ _) (@switching_left_induced_eq_to _ _ _)).
    rewrite {2}(partition_terminal_eq V VT) !in_set. caseb.
  - by rewrite mem_pblock Cov.
  - by rewrite mem_pblock Cov.
Qed.

(* We can do a case study on this, but not on sequentializing : Type *)
Definition splitting_tens_prop {v : G} (V : vlabel v = ⊗) (T : terminal v) :=
  let (SS, _) := (partition_terminal V T) in let (Sl, Sr) := SS in
  forall (p : G) (P : vlabel p = ⅋), (p \in Sl -> source (right_parr P) \in Sl)
                                  /\ (p \in Sr -> source (right_parr P) \in Sr).


Definition splitting_tens_bool {v : G} (V : vlabel v = ⊗) (T : terminal v) :=
  let (SS, _) := (partition_terminal V T) in let (Sl, Sr) := SS in
  [forall p : G, if @boolP (vlabel p == ⅋) is AltTrue P then ((p \in Sl) ==> (source (right_parr (eqP P)) \in Sl))
                                  && ((p \in Sr) ==> (source (right_parr (eqP P)) \in Sr)) else true].

Lemma splitting_tensP {v : G} (V : vlabel v = ⊗) (T : terminal v) :
  reflect (splitting_tens_prop V T) (splitting_tens_bool V T).
Proof.
  unfold splitting_tens_bool, splitting_tens_prop.
  destruct (partition_terminal V T) as [[Sl Sr] _].
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

Lemma splitting_tens_prop_is_sequentializing {v : G} (V : vlabel v = ⊗) (T : terminal v) :
  splitting_tens_prop V T -> sequentializing v.
Proof.
(* Taking induced of Sl (resp Sr).
Adding a concl on source (left_tens V).
This graph is correct: acyclicity is preserved by induced (lemma uacyclic_induced);
connectivity by hypothesis (Sl and Sr connected).
This graph is a proof structure: heavy, but should not be too hard (but
we need to add some concl edge ...).
Difficult part: G is isomorphic to add_tens ... with the usual problems of timeout
from Coq in this case, how to escape it ?
Should use an intermediate lemma of the form "there is no edges between Sl and Sr".
And of course, this will be divided across plenty of lemmas. *)
(* Admitted for now, to check that this is a good notion of splitting,
before doing this no-fun proof *)
Admitted.

Lemma sequentializing_tens_is_splitting_prop {v : G} (V : vlabel v = ⊗) :
  sequentializing v -> {T : terminal v | splitting_tens_prop V T}.
Proof.
(* same as the proof above, but normally in a easier way (well, we still have an iso to
manipulate); by contradiction ? *)
Admitted.

(* A tensor is non-splitting because there is some ⅋ with its right edge in the other part
  of the partition *)
Lemma non_splitting_tens {v : G} (V : vlabel v = ⊗) (T : terminal v) :
  ~(splitting_tens_prop V T) -> {p : {p : G | vlabel p = ⅋} &
  let (SS, _) := (partition_terminal V T) in let (Sl, Sr) := SS in
  (projT1 p \in Sl /\ source (right_parr (projT2 p)) \in Sr) \/
  (projT1 p \in Sr /\ source (right_parr (projT2 p)) \in Sl)}.
Proof.
  move => /splitting_tensP.
  unfold splitting_tens_bool.
  destruct (partition_terminal V T) as [[Sl Sr] [Sp _]].
  apply cover_partition in Sp.
  move => /forallPn/sigW[p P].
  revert P. case: {-}_ /boolP => P' //.
  set (P := eqP P'). clearbody P. clear P'.
  rewrite negb_and => H.
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

Lemma correctness_parr {v : G} (V : vlabel v = ⊗) (T : terminal v)
  (NS : ~(splitting_tens_prop V T)) :
  let (P, _) := (non_splitting_tens NS) in let (p, P) := P in
  {'(k, k') : Supath switching v p * Supath switching v p &
  upath_disjoint switching k k'}.
Proof.
  destruct (non_splitting_tens NS) as [[p P] HP].
  destruct (partition_terminal V T) as [[Sl Sr] [Sp S]]. simpl in HP.
  assert (Hr : ssrfun.svalP (exist (fun p => vlabel p = ⅋) p P) = P) by apply eq_irrelevance.
  rewrite Hr {Hr} in HP.
  destruct S as [Ul [Ur [Inl Inr]]].
  specialize (Ul (Sub (source (left_tens V)) Inl)).
  specialize (Ur (Sub (source (right_tens V)) Inr)).
  assert (HP' : ((p \in Sl) && (source (right_parr P) \in Sr)) ||
     ((p \in Sr) && (source (right_parr P) \in Sl))).
  { destruct HP as [[? ?] | [? ?]]; apply /orP; [left | right]; by apply /andP. }
(* Do a wlog here, by generalizing Inl and Inr with a || ? seems hard du to Ul and Ur *)
  clear HP. elim: (orb_sum HP') => {HP'} /andP[Pin Spin].
  - specialize (Ul (Sub p Pin)).
    specialize (Ur (Sub (source (right_parr P)) Spin)).
    revert Ul => /sigW[MuL _].
    revert Ur => /sigW[MuR _].
    assert (KL := supath_from_induced_switching_left MuL). simpl in KL.
    assert (KR := supath_from_induced_switching_left MuR). simpl in KR.
    apply supath_switching_from_leftK in KL, KR.
    assert (SlvMuL : switching (left_tens V) \notin
      [seq switching b.1 | b <- [seq (val a.1, a.2) | a <- upval MuL]]).
    { rewrite {1}/switching left_e V /= -map_comp.
      apply /mapP. move => [[[a A] _] _ /= SA].
      assert (a = left_tens V).
      { revert SA. move => /eqP. unfold switching. case_if. }
      clear SA. subst a.
      clear - Sp Inl A.
      revert A. rewrite in_set left_e => /andP[_ Vin].
assert ([disjoint Sl & Sr] /\ [disjoint [set v] & Sl] /\ [disjoint [set target (ccl_tens V)] & Sl]
/\ [disjoint [set v] & Sr] /\ [disjoint [set target (ccl_tens V)] & Sr]
 /\ [disjoint [set v] & [set target (ccl_tens V)]]).
{ (* TODO do it for all pairs, in a(some) lemma(s) *) admit. }
rewrite !disjoints1 !in_set in _H.
      assert (T := partition_trivIset Sp). (* TODO lemma to prove all elems here are not only trivIset, but disjoint (even on the tree part) *)
      revert T => /trivIsetP /(_ Sl [set v]).
      rewrite !in_set 2!eq_refl orb_true_r /=.
      move => /(_ is_true_true is_true_true).
      assert (SV : Sl != [set v]).
      { apply /eqP => ?. subst Sl.
        contradict Inl. apply /negP.
        rewrite !in_set. apply /eqP.
        rewrite -[in RHS](left_e (or_introl V)).
        apply no_selfloop. }
      move => /(_ SV) {SV}.
      rewrite disjoint_sym disjoints1.
      by apply /negP/negPn. }
(* now: concatenate left and right of v to k and k' respectively, and prove they are disjoint *)
    assert (KL' : supath switching v p (backward (left_tens V) ::
      [seq (val a.1, a.2) | a <- upval MuL])).
    { by rewrite supath_cons KL left_e eq_refl !andb_true_r /=. }
    assert (KR' : supath switching v p (rcons (backward (right_tens V) ::
      [seq (val a.1, a.2) | a <- upval MuR]) (forward (right_parr P)))).
    { rewrite supath_rcons supath_cons KR !right_e !eq_refl map_cons in_cons !andb_true_r /=.
      splitb.
      - admit. (* idem before *)
      - by rewrite /switching !right_e P V.
      - admit. (* idem before *) }
    exists ({| upvalK := KL' |}, {| upvalK := KR' |}). simpl.
    unfold upath_disjoint.
    rewrite !map_cons map_rcons.
    rewrite disjoint_cons disjoint_sym disjoint_cons disjoint_rcons.
    rewrite in_cons in_rcons /=.
    splitb.
    + rewrite /switching left_e right_e V. cbn.
      apply /eqP. apply left_neq_right.
    + by rewrite /switching left_e right_e V P.
    + (* similar to the proof of SlvMuL *) admit.
    + (* similar to what is above *) admit.
    + (* ok as this edge go from Sr to Sl *) admit.
    + (* ok as they are in the disjoint Sl and Sr *) admit.
  - (* almost exactly the proof above - try to generalize *) admit.
Admitted.

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
(* use exists_seq_or_no_seq *)

(* A switching path is strong if it does not start from a ⅋-vertex through
   one of its switch edges *)
Definition is_strong {u v : G} (P : Supath switching u v) : bool :=
  match upval P with
  | [::] => true
  | e :: p => (vlabel (usource e) != ⅋) || ~~e.2
  end.

Lemma concat_strong {s i t : G} (P : Supath switching s i) (Q : Supath switching i t)
  (D : upath_disjoint switching P Q) :
  is_strong P -> is_strong Q -> is_strong (supath_cat D).
Proof.
Abort.

(* TODO Lemma a prefix of a strong path is strong *)

(* TODO Lemma a correctness path is strong *)

(* TODO Lemma a descending path is strong *)

(* TODO traiter cut comme des tens ? *)

End Splitting_tens.

End Atoms.