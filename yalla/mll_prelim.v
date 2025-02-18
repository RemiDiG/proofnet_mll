(* Preliminaries for proof nets in MLL *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From GraphTheory Require Import preliminaries bij.
From HB Require Import structures.

Import EqNotations.
Import Order.POrderTheory. (* Theory of partial ordered finite sets *)

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


(** * For simplification *)
Lemma SubK' {T : Type} {P : pred T} (u : T) (U : P u) : valP (exist _ u U) = U.
Proof. apply eq_irrelevance. Qed. (* TODO to use *)

Lemma subn_0 (n : nat) : n - 0 = n.
Proof. lia. Qed. (* TODO very weird it is not already there... *)

(** * Useful tactics *)
(** Break hypothesys, try to rewrite them, and simplify *)
Ltac introb := repeat (let H := fresh "Hif" in let H' := fresh "Hif" in
  match goal with
  | |- is_true (~~ ~~ ?x)      -> _ => move=> /negPn //
  | |- (~~ ?x) = false         -> _ => move=> /negPn //
  | |- ~~ (?x = false)         -> _ => move=> /negPn //
  | |- is_true (?x && ?y)      -> _ => move=> /andP[H H'] //; move: H H'
  | |- is_true (~~ (?x && ?y)) -> _ => move=> /nandP[H | H] //; move: H
  | |- (?x && ?y) = false      -> _ => move=> /nandP[H | H] //; move: H
  | |- is_true (?x || ?y)      -> _ => move=> /orP[H | H] //; move: H
  | |- is_true (~~ (?x || ?y)) -> _ => move=> /norP[H H'] //; move: H H'
  | |- (?x || ?y) = false      -> _ => move=> /norP[H H'] //; move: H H'
  | |- is_true ?x              -> _ => move=> /eqP-H //; rewrite 1?H //
  | |- ?x = false              -> _ => move=> /eqP-H //; rewrite 1?H //
  | |- ?x = ?y                 -> _ => move=> H //; rewrite 1?H //
  | |- _                       -> _ => move=> H //
  end);
  rewrite_all eqbF_neg; rewrite_all eqb_id; rewrite_all eq_refl;
  rewrite_all negb_involutive; try subst; try done.

(** Make cases on if *)
(* Make all cases, try to rewrite the equality condition and conserve the conditions
  under the form _ = _ or _ <> _, folding trivial cases *)
Ltac case_if1 := repeat (case: ifP); cbn; introb.
Ltac case_if := repeat case_if1.

(** Split both /\ and && and ~~||, folding trivial cases *)
Ltac splitb := repeat (split || apply/andP || apply/norP); trivial.

(** Solve trivial \/ and || and ~~&& *)
Ltac caseb :=
  try done;
  try ((by left; caseb) || (by right; caseb));
  try (apply/orP; (by left; caseb) || (by right; caseb));
  try (apply/nandP; (by left; rewrite ?negb_involutive //; caseb)
                  || (by right; rewrite ?negb_involutive //; caseb)).

(** Try to simplify the goal *)
Ltac cbnb := repeat (cbn; try (apply/eqP; cbn; apply/eqP); rewrite //=).




(** * About bool *)
Lemma eq_or_eq_negb (b c : bool) :
  (c = b) \/ (c = ~~ b).
Proof. destruct b, c; auto. Qed.




(** * About set *)
Lemma enum_subset {T : finType} P : enum [set x | P x] = filter P (enum T).
Proof.
  rewrite enumT.
  apply eq_filter. hnf.
  apply in_set.
Qed.


Lemma eq_mem_sym {T : Type} (M : mem_pred T) (N : mem_pred T) :
  M =i N -> N =i M.
Proof. move=> ? ?. by symmetry. Qed.


(** Both visions of a set as set or subset have the same cardinal *)
Lemma card_set_subset {T : finType} (P : pred T) :
  #|({e : T | P e} : finType)| = #|[set e | P e]|.
Proof. by rewrite card_sig cardsE. Qed.


Lemma setC2 {T : finType} (a b : T) :
  ~: [set a; b] = setT :\ a :\ b.
Proof. apply/setP => ?. by rewrite !in_set negb_orb andb_true_r andb_comm. Qed.


Lemma setCn {T : finType} (P : pred T) :
  [set x | ~~ P x] = ~: [set x | P x].
Proof. apply/setP => ?. by rewrite !in_set. Qed.


Lemma set1I {T : finType} (x : T) (S : {set T}) :
  [set x] :&: S = if x \in S then [set x] else set0.
Proof.
  apply/setP => y.
  rewrite in_set in_set1.
  case/boolP: (y == x) => [/eqP--> | y_x] /=;
  case:ifP.
  - by rewrite in_set1 eq_refl.
  - by rewrite in_set0.
  - by rewrite in_set1 (negPf y_x).
  - by rewrite in_set0.
Qed.


Lemma setT_in_pred {T : finType} (P : pred T) :
  [set x in setT | P x] = [set x | P x].
Proof. apply/setP => ?. by rewrite !in_set. Qed.


Lemma imsetUCr {aT rT : finType} (f : aT -> rT) (P : pred aT) :
  [set f a | a : aT & ~~ P a] :|: [set f a | a : aT & P a] = [set f a | a in setT].
Proof. by rewrite -imsetU setUC setCn setUCr. Qed.


Lemma sum_pred {A B : finType} (P : pred (A + B)) :
  [set x : A + B | P x] = inl @: [set x | P (inl x)] :|: inr @: [set x | P (inr x)].
Proof.
  apply/setP => x.
  rewrite !in_set.
  symmetry. destruct (P x) eqn:H, x.
  - rewrite mem_imset; last by apply inl_inj.
    by rewrite in_set H.
  - rewrite mem_imset; last by apply inr_inj.
    by rewrite in_set H orb_true_r.
  - apply/norP. split.
    + rewrite mem_imset; last by apply inl_inj.
      by rewrite in_set H.
    + apply/imsetP. by move=> [? ? ?].
  - apply/norP. split.
    + apply/imsetP. by move=> [? ? ?].
    + rewrite mem_imset; last by apply inr_inj.
      by rewrite in_set H.
Qed.


Lemma inlr_pred_I {R S : finType} (P : pred R) (Q : pred S) :
  [set inl x | x : R & P x] :&: [set inr x | x : S & Q x] = set0.
Proof.
  apply/setP => x.
  rewrite !in_set.
  apply/nandP.
  destruct x; [right | left]; apply/imsetP; by move=> [? ? ?].
Qed.


Lemma cards_sum_pred {A B : finType} P :
  #|[set x : A + B | P x]| = #|[set x | P (inl x)]| + #|[set x | P (inr x)]|.
Proof. rewrite sum_pred cardsU inlr_pred_I cards0 subn_0 !card_imset //; apply inr_inj || apply inl_inj. Qed.


Lemma set1C {T : finType} (x : T) : [set~ x] = setT :\ x.
Proof. apply/setP => ?. by rewrite !in_set andb_true_r. Qed.


Lemma set1CI {T : finType} (S : {set T}) (x : T) : S :&: [set~ x] = S :\ x.
Proof. by rewrite set1C setIDA setIT. Qed.


(** Function picking the only element of a singleton *)
Definition pick_unique := fun {T : finType} {S : {set T}}
  (H : #|S| = 1) => sval (mem_card1 H).

Lemma pick_unique_in {T : finType} {S : {set T}} (H : #|S| = 1) :
  pick_unique H \in S.
Proof.
  rewrite -subset_pred1.
  apply eq_subxx.
  rewrite /pick_unique.
  by destruct (mem_card1 H).
Qed.

Lemma pick_unique_set {T : finType} {S : {set T}} (H : #|S| = 1) :
  S = [set pick_unique H].
Proof.
  symmetry. apply/setP/subset_cardP.
  - by rewrite cards1 H.
  - by rewrite sub1set pick_unique_in.
Qed.

Lemma pick_unique_eq {T : finType} {S : {set T}} (H : #|S| = 1) s :
  s \in S -> s = pick_unique H.
Proof.
  move=> Sin.
  apply/set1P.
  by rewrite -(pick_unique_set H).
Qed.


(** Function picking the 2nd element of a 2-elements set *)
Definition unique_other {T : finType} (S : {set T}) (x : T) :
  #|S| = 2 -> x \in S -> #|S :\ x| = 1.
Proof. rewrite (cardsD1 x S). lia. Qed.

Definition other {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :=
  pick_unique (unique_other Hs Hin).

Lemma other_in_neq {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :
  other Hs Hin \in S /\ other Hs Hin != x.
Proof. by destruct (setD1P (pick_unique_in (unique_other Hs Hin))). Qed.

Lemma other_set {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :
  S = [set x; other Hs Hin].
Proof.
  symmetry. apply/setP/subset_cardP.
  - rewrite cards2 Hs eq_sym.
    by destruct (other_in_neq Hs Hin) as [_ ->].
  - replace (pred_of_set S) with (pred_of_set (S :|: S)) by (f_equal; apply setUid).
    apply setUSS; rewrite sub1set //.
    apply other_in_neq.
Qed.

Lemma other_setD {T : finType} {S : {set T}} {x : T} (Hs : #|S| = 2) (Hin : x \in S) :
  S :\ x = [set other Hs Hin].
Proof.
  apply/setP => ?.
  by rewrite (proj2_sig (mem_card1 (unique_other _ _))) in_set1.
Qed.

Lemma other_eq {T : finType} {S : {set T}} {x y : T} (Hs : #|S| = 2) (Hx : x \in S) :
  y \in S -> y <> x -> y = other Hs Hx.
Proof. move=> Hy /eqP-Hneq. apply pick_unique_eq. by rewrite in_set in_set1 Hneq Hy. Qed.


(** Results on 'I_n *)
(* Tactic to distinguish cases in 'I_n for n <= 10, n arbitrary *)
Ltac destruct_I i := let I := fresh "I" in
  destruct i as [i I]; do 10 (try (destruct i as [ | i])); try by [].
(* Ltac nsplit n i :=
  match n with
  | 0 => idtac
  | S ?m => destruct i as [ | i]; [ | nsplit m]
  end. TODO possible to do better with something like this ? *)

(* Tactic computing cardinals of subsets of 'I_n, with n fixed to a constant *)
Lemma enum_I0 : enum 'I_0 = [::].
Proof. rewrite -enum0. apply eq_enum, card0_eq, card_ord. Qed.

Ltac compute_card_subIn := rewrite cardE enum_subset; cbn;
                           repeat (rewrite enum_ordSl; cbn);
                           now rewrite enum_I0.


(** Symmetric property on set with 2 elements *)
Definition true_on2 {T : finType} {S : {set T}} (P : rel T) (HS : #|S| = 2) :=
  forall (t : T) (Ht : t \in S), P t (other HS Ht).

(* Proving a symmetric property on one suffices to prove it on all *)
Lemma simpl_sym {T : finType} {S : {set T}} (HS : #|S| = 2) (P : rel T)
  (HP : symmetric P) (t : T) (Ht : t \in S) : P t (other HS Ht) -> true_on2 P HS.
Proof.
  move=> H s.
  case/boolP: (t == s) => [/eqP-<- | /eqP-Hneq] Hs.
  - by replace Hs with Ht by apply eq_irrelevance.
  - by rewrite -(other_eq HS Hs Ht Hneq) HP (other_eq HS Ht Hs (nesym Hneq)).
Qed.



(** * About seq *)
Lemma cat_eq_l {T : Type} (s r t : seq T) :
  s ++ r = s ++ t -> r = t.
Proof.
  move: r t. induction s as [ | s x IH] using last_ind => r t //.
  rewrite !cat_rcons.
  move=> H. specialize (IH _ _ H).
  by inversion IH.
Qed.

Lemma cat_eq_r {T : Type} (s r t : seq T) :
  s ++ r = t ++ r -> s = t.
Proof.
  move: s t. induction r as [ | x r IH] => s t.
  { by rewrite !cats0. }
  rewrite -!cat_rcons.
  move=> H. specialize (IH _ _ H).
  apply rcons_inj in IH. by inversion IH.
Qed.

Lemma in_seq_sig {T : eqType} {P : pred T} (a : {x : T | P x}) (l : seq ({x : T | P x})) :
  (a \in l) = (sval a \in [seq sval v | v <- l]).
Proof. induction l as [ | ? ? H]; trivial. by rewrite !in_cons H. Qed.

Lemma uniq_seq_sig {T : eqType} {P : pred T} (l : seq ({x : T | P x})) :
  (uniq l) = (uniq [seq sval v | v <- l]).
Proof.
  induction l as [ | ? ? IH]; first by [].
  by rewrite map_cons !cons_uniq -IH in_seq_sig.
Qed.

Lemma not_uniq_map {T U : eqType} (f : T -> U) (s : seq T) x y :
  x \in s -> y \in s -> x <> y -> f x = f y -> ~~ uniq (map f s).
Proof.
  move=> X Y N E.
  apply/(uniqPn (f x)).
  enough (O : index x s < index y s \/ index y s < index x s).
  { destruct O; [exists (index x s), (index y s) | exists (index y s), (index x s)].
    all: by rewrite size_map !(nth_map x) ?nth_index ?index_mem. }
  destruct (index x s < index y s) eqn:H; [caseb | ].
  enough (index y s <> index x s) by lia.
  move=> Hc. contradict N.
  by rewrite -(nth_index x X) -(nth_index x Y) Hc.
Qed.

Lemma rcons_nil {T : Type} (s : seq T) (x : T) :
  rcons s x <> [::].
Proof. by destruct s. Qed.

Lemma in_rcons {T : eqType} (y : T) (s : seq T) (x : T) :
  x \in rcons s y = (x == y) || (x \in s).
Proof. by rewrite mem_rcons in_cons. Qed. (* TODO duplicate mem_rcons *)

Lemma in_rev {T : eqType} (s : seq T) (x : T) :
  x \in rev s = (x \in s).
Proof. by rewrite mem_rev. Qed. (* TODO duplicate mem_rev *)

Lemma map_nil {T U : eqType} (s : seq T) (f : T -> U) :
  ([seq f x | x <- s] == [::]) = (s == [::]).
Proof. by destruct s. Qed. (* TODO in Prop without eqType? and the next ones too *)

Lemma cat_nil {T : eqType} (s r : seq T) :
  (s ++ r == [::]) = (s == [::]) && (r == [::]).
Proof. by destruct s, r. Qed.

Lemma rev_nil {A : eqType} (l : seq A) :
  (rev l == [::]) = (l == [::]).
Proof. destruct l; first by []. rewrite rev_cons. apply/eqP. apply rcons_nil. Qed.

Lemma head_cat {T : Type} (x : T) (s1 s2 : seq T) :
  head x (s1 ++ s2) = head (head x s2) s1.
Proof. by destruct s1, s2. Qed.

Lemma head_rcons {T : Type} (s : seq T) (x y : T) :
  head x (rcons s y) = head y s.
Proof. destruct s; by rewrite // rcons_cons. Qed.

Lemma head_rev {T : Type} (s : seq T) (x : T) :
  head x (rev s) = last x s.
Proof. move: x. induction s as [ | y s IH] => x //=. by rewrite rev_cons head_rcons IH. Qed.

Lemma last_rev {T : Type} (s : seq T) (x : T) :
  last x (rev s) = head x s.
Proof. destruct s; by rewrite // rev_cons last_rcons. Qed.

Lemma head_take {T : Type} (s : seq T) (x : T) (n : nat) :
  head x (take n s) = if n == 0 then x else head x s.
Proof. by destruct n, s. Qed.

Lemma eq_seq_sig {T : eqType} {P : pred T} (l r : seq ({x : T | P x})) :
  [seq sval v | v <- l] = [seq sval v | v <- r] -> l = r.
Proof.
  move: l. induction r as [ | ? ? IH] => l /=.
  { move=> /eqP. by rewrite map_nil => /eqP-->. }
  destruct l; simpl; first by by [].
  move=> H. inversion H as [[H0 H1]].
  rewrite (IH _ H1). apply/eqP. cbn. rewrite H0. splitb. by apply/eqP.
Qed.

Lemma in_map_fst {T1 T2 : eqType} (x : T1) (s : seq (T1 * T2)) :
  x \in [seq y.1 | y <- s] -> exists b, ((x, b) \in s).
Proof. move=> /mapP[[y b] /= X ?]. subst y. by exists b. Qed.
(* TODO with (x \in [seq y.1 | y <- s]) = [exists b, ((x, b) \in s)] ?*)

Lemma mem3_head {T : eqType} (x : T) (s : seq T) :
  s <> [::] -> head x s \in s.
Proof. by destruct s; rewrite //= in_cons eq_refl. Qed.

Lemma mem3_last (T : eqType) (x : T) (s : seq T) :
  s <> [::] -> last x s \in s.
Proof. destruct s => //= _. apply mem_last. Qed.

Lemma head_eq {T : Type} (x y : T) (l : seq T) :
  l <> [::] -> head x l = head y l.
Proof. by destruct l. Qed.

Lemma last_eq {T : Type} (x y : T) (l : seq T) :
  l <> [::] -> last x l = last y l.
Proof. case: (lastP l) => {l} [ // | z l]. by rewrite !last_rcons. Qed.

Lemma forall_notincons {A : eqType} {B : finType} (P : B -> A) (f : A) p :
  [forall b, P b \notin f :: p] = [forall b, P b != f] && [forall b, P b \notin p].
Proof.
  symmetry. destruct [forall b, P b \notin f :: p] eqn:H; move: H.
  - move=> /forallP-H.
    splitb; apply/forallP => a; move: H => /(_ a); rewrite in_cons; introb.
  - move=> /forallPn[a /negPn].
    rewrite in_cons => /orP[/eqP-H | H];  apply/nandP; [left | right]; apply/forallPn; exists a;
    rewrite H; by apply/negPn.
Qed.

Lemma disjoint_rcons {T : finType} (x : T) (s : seq T) (B : {pred T}) :
  [disjoint (rcons s x) & B] = (x \notin B) && [disjoint s & B].
Proof. by rewrite -cats1 disjoint_cat disjoint_cons disjoint0 andb_true_r andb_comm. Qed.

Lemma disjoint_nil {T : finType} (B : {pred T}) : [disjoint [::] & B].
Proof. apply/disjointP => ?. by rewrite in_nil. Qed.

Lemma disjoint_rev {T : finType} (l : seq T) (B : {pred T}) :
  [disjoint (rev l) & B] = [disjoint l & B].
Proof.
  induction l as [ | x l IH]; first by [].
  by rewrite rev_cons disjoint_rcons disjoint_cons IH andbC.
Qed.

Lemma in_elt_sub {T : eqType} (s : seq T) (x : T) :
  (x \in s) = [exists n : 'I_(size s), (s == (take n s) ++ x :: (drop n.+1 s))].
Proof.
  symmetry. destruct (x \in s) eqn:X.
  - move: X => /(nthP x)[n N E].
    apply/existsP. exists (Ordinal N).
    by rewrite /= -{1}(cat_take_drop n s) -E -drop_nth.
  - apply/existsPn. move=> [n N].
    apply/eqP => S.
    move: X => /negP-X. contradict X.
    rewrite {}S mem_cat in_cons eq_refl. caseb.
Qed.

(* Take the first element in a list respecting some property *)
Lemma in_elt_sub_fst {T : eqType} (l : seq T) (P : T -> bool) (x : T) :
  P x -> x \in l ->
  exists (n : 'I_(size l)) y,
  l = take n l ++ y :: drop n.+1 l /\ P y /\ forall z, z \in take n l -> ~~ P z.
Proof.
  move: x. induction l as [ | y l IH] => // x Px.
  rewrite in_cons.
  destruct (P y) eqn:Py.
  - move=> _. exists ord0, y. splitb.
    + by rewrite /= drop0.
    + by [].
  - assert (x == y = false) as ->.
    { apply/eqP; move=> *; subst. by rewrite Px in Py. }
    move=> /= In.
    specialize (IH _ Px In). destruct IH as [n [z [L [Z IH]]]].
    exists (lift ord0 n), z.
    rewrite lift0 /= -L. splitb.
    move=> ?. rewrite in_cons => /orP[/eqP--> | ?].
    + by rewrite Py.
    + by apply IH.
Qed.

Lemma take_nth_drop {T : Type} (x : T) (n : nat) (s : seq T) :
  n < size s ->
  s = take n s ++ nth x s n :: drop (n + 1) s.
Proof.
  move: n. induction s as [ | y s IH] => n //= n_lt.
  destruct n as [ | n] => /=.
  - by rewrite drop0.
  - f_equal. exact (IH n n_lt).
Qed.

Lemma take_nth_drop2 {T : Type} (x : T) (n : nat) (s : seq T) :
  n + 1 < size s ->
  s = take n s ++ nth x s n :: nth x s (n + 1) :: drop (n + 2) s.
Proof.
  move=> n_lt.
  rewrite [in LHS](@take_nth_drop _ x n s); last by lia.
  repeat f_equal.
  rewrite [in LHS](@take_nth_drop _ x 0 (drop (n + 1) s)) ?size_drop; last by lia.
  rewrite take0 nth_drop drop_drop /=.
  replace (n + 1 + 0) with (n + 1) by lia.
  by replace (0 + 1 + (n + 1)) with (n + 2) by lia.
Qed.

Lemma nth_eq {T : Type} (x y : T) (s : seq T) (n : nat) :
  n < size s -> nth x s n = nth y s n.
Proof.
  move: s. induction n as [ | n IH] => s; destruct s => //= n_lt.
  apply IH. lia.
Qed.



(** * About permutations *)
(** Function taking two lists l1 l2 permutations of one another, and returning a
polymorphic permutation sending l1 to l2 *)
Fixpoint perm_of {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) {B : Type} {struct sigma} :
  seq B -> seq B :=
  match sigma with
  | Permutation_Type_nil_nil => id
  | Permutation_Type_skip _ _ _ tau => fun b => match b with
    | d :: e => d :: (perm_of tau e)
    | [::] => [::]
    end
  | Permutation_Type_swap _ _ _ => fun b => match b with
    | f :: d :: e => d :: f :: e
    | _ => b
    end
  | Permutation_Type_trans _ _ _ tau1 tau2 => fun b => perm_of tau2 (perm_of tau1 b)
  end.

Lemma perm_of_consistent {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) :
  perm_of sigma l1 = l2.
Proof. unfold perm_of. by induction sigma as [ | ? ? ? ? -> | | ? ? ? ? -> ? ->]. Qed.

Lemma perm_of_map {A B S : Type}  {l1 l2 : seq S} (sigma : Permutation_Type l1 l2)
  (l : seq A) (f : A -> B) :
  perm_of sigma [seq f i | i <- l] = [seq f i | i <- perm_of sigma l].
Proof.
  move: A B l f.
  induction sigma as [ | ? ? ? ? H | | ? ? ? ? H ? H'] => A B l0 f; trivial; cbn.
  - destruct l0; trivial. by rewrite /= H.
  - by destruct l0 as [ | ? [ | ? ?]].
  - by rewrite H H'.
Qed.

Lemma perm_of_in {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2)
  {B : finType} (l : seq B) (b : B) :
  (b \in perm_of sigma l) = (b \in l).
Proof.
  move: B l b; induction sigma as [ | ? ? ? ? H | | ? ? ? ? H ? H'] => B l b; trivial; cbn.
  - destruct l; trivial. by rewrite !in_cons H.
  - destruct l as [ | a [ | a' l0]]; trivial.
    rewrite !in_cons !orb_assoc.
    by replace ((b == a') || (b == a)) with ((b == a) || (b == a')) by by rewrite orb_comm.
  - by rewrite H' H.
Qed.

Lemma perm_of_uniq {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2) {B : finType}
  (l : seq B) :
  uniq (perm_of sigma l) = uniq l.
Proof.
  move: B l.
  induction sigma as [ | ? ? ? ? H | | ? ? ? ? H ? H'] => B l0; trivial; cbn.
  - destruct l0; trivial. by rewrite /= perm_of_in H.
  - destruct l0 as [ | ? [ | ? ?]]; trivial; cbn.
    rewrite !in_cons !negb_or !andb_assoc; apply andb_id2r => _.
    rewrite andb_comm andb_assoc; apply andb_id2r => _.
    rewrite andb_comm; apply andb_id2r => _.
    apply/eqP; case_if. by apply nesym.
  - by rewrite H' H.
Qed.

Lemma perm_of_rew_r {A : Type} {l1 l2 : seq A} (sigma : Permutation_Type l1 l2)
  (l3 : seq A) (Heq : l2 = l3) (B : Type) :
  @perm_of A l1 l3 (rew Heq in sigma) B =1 perm_of sigma.
Proof. by subst. Qed.


(** Permutation for maps, defined (as opposed as in OLlibs) ... *)
Fixpoint Permutation_Type_map_def {A B : Type} (f : A -> B) (l l' : seq A)
  (sigma : Permutation_Type l l') : Permutation_Type (map f l) (map f l') :=
  match sigma with
  | Permutation_Type_nil_nil => Permutation_Type_nil_nil _
  | Permutation_Type_skip x _ _ tau => Permutation_Type_skip (f x) (Permutation_Type_map_def f tau)
  | Permutation_Type_swap x y l0 => Permutation_Type_swap (f x) (f y) (map f l0)
  | Permutation_Type_trans _ _ _ tau1 tau2 =>
      Permutation_Type_trans (Permutation_Type_map_def f tau1) (Permutation_Type_map_def f tau2)
  end.

(* ... in order to prove the following lemma *)
Lemma perm_of_Permutation_Type_map {S : Type}  {l1 l2 : seq S} (sigma : Permutation_Type l1 l2)
  {A B : Type} (l : seq A) (f : S -> B) :
  perm_of (Permutation_Type_map_def f sigma) l = perm_of sigma l.
Proof.
  move: l. induction sigma as [ | ? ? ? ? H | | ? ? ? ? H ? H'] => l //=.
  - destruct l; first by []. by rewrite H.
  - by rewrite H H'.
Qed.


(** Permutation between two lists without duplicate and linked by a bijection *)
Definition Permutation_Type_bij_uniq {A B : eqType} (h : bij A B) (l : seq A) (l' : seq B) :
  uniq l -> uniq l' -> (forall x, x \in l <-> h x \in l') ->
  Permutation_Type l' [seq h x | x <- l].
Proof.
  move: l'. induction l as [ | e l IH] => /= l' U U' In.
  - enough (l' = [::]) as -> by exact (Permutation_Type_nil_nil _).
    destruct l' as [ | e' l']; first by []. exfalso.
    specialize (In (h^-1 e')).
    rewrite in_nil in_cons bijK' eq_refl /= in In.
    by assert false by by apply In.
  - move: U => /= /andP[Nin U].
    assert (Ine : h e \in l').
    { apply In. by rewrite in_cons eq_refl. }
    move: Ine. rewrite in_elt_sub => /existsP/sigW[[n /= _] /eqP-N].
    set l1' := take n l'.
    set l2' := drop n.+1 l'.
    fold l1' l2' in N.
    assert (In2 : forall a, a \in l <-> h a \in l1' ++ l2').
    { move=> a.
      destruct (eq_comparable a e) as [? | Hneq]; [subst a | ].
      - split => H.
        + by contradict H; apply/negP.
        + contradict U'; apply/negP.
          rewrite N.
          change (h e :: l2') with ([:: h e] ++ l2').
          rewrite uniq_catCA cat_uniq has_sym /=. caseb.
      - specialize (In a).
        move: In.
        rewrite N !mem_cat !in_cons bij_eq //.
        by replace (a == e) with false by by symmetry; apply/eqP. }
    assert (U'2 : uniq (l1' ++ l2')).
    { move: U'. rewrite N !cat_uniq /=. introb. splitb. }
    specialize (IH _ U U'2 In2).
    rewrite N.
    by symmetry; apply Permutation_Type_cons_app; symmetry.
Defined.



(** * A DecType (from OLlibs) is the same as an eqType (from ssreflect) *)
HB.instance Definition _ (X : DecType) := hasDecEq.Build X eq_dt_reflect.

Lemma eq_op_iff {T : eqType} : forall (x y : T), x == y <-> x = y.
Proof. exact: (fun x y => iff_sym (rwP eqP)). Qed.
Definition DecType_of_eqType (T : eqType) : DecType := {|
  car := T;
  dectype.eqb := @eq_op T;
  eqb_eq := eq_op_iff |}.
Coercion DecType_of_eqType : eqType >-> DecType.
(* Now we can have for instance ((bool : eqType) : DecType) *)



(** * About image of a set through a bijection *)
Lemma bij_imset_invert (aT rT : finType) (f : bij aT rT) (A : {set aT}) (B : {set rT}) :
  B = [set f x | x in A] -> A = [set f^-1 x | x in B].
Proof.
  move=> ->. rewrite -imset_comp -{1}(imset_id A).
  apply eq_imset => ?. by rewrite /= bijK.
Qed.



(** * Finite Partial Orders are well-founded *)
Section FinPOrderTheoryWf.

Open Scope order_scope.

Context {disp : unit} {T : finPOrderType disp}.

Lemma lt_wf :
  well_founded (fun (x y : T) => x < y).
Proof.
  apply (well_founded_lt_compat T (fun (x : T) => #|[set y | y < x]|)).
  move=> x y x_lt_y.
  enough (#|[set z | (z < x)%O]| < #|[set z | (z < y)%O]|) by lia.
  apply proper_card. apply/properP. split.
  - apply/subsetP => z.
    rewrite !in_set => z_lt_x.
    exact (lt_trans z_lt_x x_lt_y).
  - exists x.
    + by rewrite in_set.
    + by rewrite in_set ltxx.
Qed.

Lemma gt_wf :
  well_founded (fun (x y : T) => x > y).
Proof.
  apply (well_founded_lt_compat _ (fun x => #|[set y | y > x]|)).
  move=> x y y_lt_x.
  enough (#|[set z | (x < z)%O]| < #|[set z | (y < z)%O]|) by lia.
  apply proper_card. apply/properP. split.
  - apply/subsetP => z.
    rewrite !in_set.
    by apply lt_trans.
  - exists x.
    + by rewrite in_set.
    + by rewrite in_set ltxx.
Qed.

(* TODO gt_wf should be obtained from lt_wf by reversing the order,
which preserves being a partial order.
/!\ [finPOrderType of T^d] is a copy T, not T with the reversed order... or is it? to check again *)
(* TODO surprising it is not in the library, as well as that there is a
   maximal element in a finPOrderType... *)
End FinPOrderTheoryWf.
