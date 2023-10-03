(* Collection of unused lemmas corresponding to general properties *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries bij.

From Yalla Require Import mll_prelim.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(** * About set *)

Lemma finset_of_pred_of_set (T : finType) (S : {set T}) : finset (pred_of_set S) = S.
Proof. apply/setP => ?. by rewrite !in_set. Qed.

Lemma set2D1 {T : finType} (a b : T) : b != a -> [set a; b] :\ a = [set b].
Proof.
  move=> H. apply/setP => e.
  rewrite !in_set !in_set1 andb_orb_distrib_r andNb /= andbC.
  by case/boolP: (e == b) => /= [/eqP--> | _].
Qed.

Lemma cardsUmax [T : finType] (A B : {set T}) : #|A| <= #|A :|: B| /\ #|B|  <= #|A :|: B|.
Proof. split; apply subset_leq_card; [apply subsetUl | apply subsetUr]. Qed.

Lemma finset0 {T : finType} {S : {set T}} (t : T) :
  t \in S -> #|S| <> 0.
Proof.
  move=> I C. contradict I. apply/negP.
  by rewrite (cards0_eq C) in_set.
Qed.

Lemma pick1 {T : finType} (t : T) : [pick x in [set t]] = Some t.
Proof.
  case: pickP.
  - move=> ?.
    by rewrite in_set1 => /eqP-->.
  - move=> /(_ t).
    by rewrite in_set1 eq_refl.
Qed.



(** * About seq *)

Lemma in_notin {T : eqType} (l : seq T) (x y : T) :
  x \in l -> y \notin l -> x != y.
Proof.
  move=> Hx Hy.
  destruct (eq_comparable x y) as [-> | ].
  - by contradict Hx; apply/negP.
  - by apply/eqP.
Qed.

Lemma inr_seq_inl_filter {L R : eqType} (l : seq L) (P : pred L) (b : R) :
  (inr b : L + R) \notin [seq (inl a : L + R) | a <- l & P a].
Proof. induction l as [ | a ? ?]; cbn; trivial. by case: (P a). Qed.

Lemma eqseq_rev {T : eqType} (l m : seq T) :
  (rev l == rev m) = (l == m).
Proof.
  move: l. induction m as [ | x m IH] => l /=.
  - by rewrite rev_nil.
  - rewrite rev_cons. destruct l as [ | y l].
    + transitivity false; [ | by symmetry]. apply/eqP.
      apply nesym, rcons_nil.
    + by rewrite rev_cons eqseq_rcons IH eqseq_cons andbC.
Qed.

Lemma head_map {T1 T2 : Type} {f : T1 -> T2} (s : seq T1) (x : T1) :
  head (f x) [seq f i | i <- s] = f (head x s).
Proof. by destruct s. Qed.

(* Take the last element in a list respecting some property *)
Lemma in_elt_sub_last {T : eqType} (l : seq T) (P : T -> bool) (x : T) :
  P x -> x \in l ->
  exists (n : 'I_(size l)) y,
  l = take n l ++ y :: drop n.+1 l /\ P y /\ forall z, z \in drop n.+1 l -> ~~ P z.
Proof.
  move=> Px X.
  assert (X' : x \in rev l) by by rewrite in_rev.
  destruct (in_elt_sub_fst Px X') as [[n N] [y [L [Py H]]]].
  move: L H. rewrite take_rev drop_rev -rev_rcons -rev_cat /=.
  move=> /eqP. rewrite eqseq_rev cat_rcons => /eqP-L H.
  rewrite size_rev in N.
  assert (N' : size l - n.+1 < size l) by lia.
  exists (Ordinal N'), y. simpl.
  assert ((size l - n.+1).+1 = size l - n) as -> by lia.
  repeat split; trivial.
  move=> *. apply H. by rewrite mem_rev.
Qed.



(** * About equivalence relations and partitions *)

Lemma mem_pblock2 {T : finType} {rT : eqType} {f : T -> rT} {S : {set T}} {x y : T} :
  y \in pblock (preim_partition f S) x -> y \in S.
Proof.
  move=> Y.
  assert (Spart := preim_partitionP f S).
  by rewrite -(cover_partition Spart) -mem_pblock (same_pblock (partition_trivIset Spart) Y).
Qed.

Lemma equivalence_rel_preim {T : finType} {rT : eqType} {f : T -> rT} {S : {set T}} :
  {in S & &, equivalence_rel (fun x y : T => f x == f y)}.
Proof. by split => // /eqP-->. Qed.

Lemma preim_partition_im_eq {T : finType} {rT : eqType} (f : T -> rT) (S : {set T}) (P : {set T}) :
  P \in preim_partition f S -> forall x y, x \in P -> y \in S -> f y = f x -> y \in P.
Proof.
  move=> Pin x y Px Sy YX.
  assert (Spart := preim_partitionP f S).
  assert (P = pblock (preim_partition f S) x).
  { symmetry; apply def_pblock; trivial. apply (partition_trivIset Spart). }
  subst P.
  rewrite pblock_equivalence_partition //.
  - by apply/eqP.
  - exact equivalence_rel_preim.
  - exact (mem_pblock2 Px).
Qed.

Lemma preim_partition_in_eq {T : finType} {rT : eqType} (f : T -> rT) (S : {set T}) (P : {set T}) :
  P \in preim_partition f S -> forall x y, x \in P -> y \in P -> f x = f y.
Proof.
  move=> Pin x y X Y.
  assert (Spart := preim_partitionP f S).
  assert (P = pblock (preim_partition f S) x).
  { symmetry; apply def_pblock; trivial. apply (partition_trivIset Spart). }
  subst P.
  assert (Y2 := Y). rewrite pblock_equivalence_partition in Y2.
  - by apply/eqP.
  - exact equivalence_rel_preim.
  - exact (mem_pblock2 X).
  - exact (mem_pblock2 Y).
Qed.

Lemma preim_partition_pblock_eq {T : finType} {rT : eqType} (f : T -> rT) (S : {set T}) x y :
  x \in S -> y \in S ->
  (pblock (preim_partition f S) x == pblock (preim_partition f S) y) = (f x == f y).
Proof.
  have /andP[/eqP-Cov /andP[Triv Zero]] := preim_partitionP f S.
  move=> X Y.
  rewrite eq_pblock //; last by rewrite Cov.
  destruct (eq_comparable (f x) (f y)) as [F | F].
  - rewrite F eq_refl.
    symmetry in F.
    eapply (preim_partition_im_eq _ _ Y F). Unshelve.
    + apply pblock_mem. by rewrite Cov.
    + by rewrite mem_pblock Cov.
  - transitivity false; last by (symmetry; apply/eqP).
    apply/negP => Y'.
    contradict F.
    eapply (@preim_partition_in_eq _ _ _ S _ _ _ _ _ Y'). Unshelve.
    + apply pblock_mem. by rewrite Cov.
    + by rewrite mem_pblock Cov.
Qed.

Lemma equivalence_partition_eq {T : finType} (r : rel T) (S : {set T}) :
  {in S & &, equivalence_rel r} ->
  equivalence_partition r S = [set (pblock (equivalence_partition r S) x) | x in S].
Proof.
  move=> R.
  assert (Spart := equivalence_partitionP R).
  move: Spart => /andP[/eqP-Cov /andP[Triv Zero]].
  apply/setP => P.
  symmetry. destruct (P \in equivalence_partition r S) eqn:Pin.
  - assert {x | x \in P} as [x X].
    { destruct (set_0Vmem P); trivial.
      exfalso. subst P.
      contradict Zero. by apply/negP/negPn. }
    assert (Peq := def_pblock Triv Pin X). subst P.
    apply imset_f.
    by rewrite mem_pblock Cov in X.
  - apply/imsetP. move=> [x X Peq]. subst P.
    move: Pin => /negP/negP => Pin.
    contradict Pin. apply/negP/negPn.
    apply pblock_mem. by rewrite Cov.
Qed.

Lemma preim_partition_eq {T : finType} {rT : eqType} (f : T -> rT) (S : {set T}) :
  preim_partition f S = [set (pblock (preim_partition f S) x) | x in S].
Proof. apply equivalence_partition_eq, equivalence_rel_preim. Qed.

