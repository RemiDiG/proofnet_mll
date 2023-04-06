(* Sequentialisation - Prove the theorem *)
(* From a Proof Net, return a LL proof of the same sequent *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export mll_prelim graph_more mgraph_tree mll_def mll_basic mll_seq_to_pn
  mll_pn_to_seq_def mll_pn_to_seq_ax mll_pn_to_seq_parr mll_pn_to_seq_tens.

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


Section Critical_path.
Context {G : proof_net}.

(* Critical path *)
(* Build a strong path the following way :
From a non-ax vertex, go with a descending path to a terminal vertex.
If it is sequentializing, we are done.
Otherwise, it is a tensor (or a cut) and we have correctness paths.
One of them start from another edge than the one by which the descending path arrive.
We have disjointness of edges of this correctness path with the critical path, for otherwise
we can build a switching cycle.
We repeat (descending - correctness paths) until reaching a sequentilizing vertex.
As the size of a strong switching path is bounded, by induction on max - size we cannot expand
the critical path at some point, meaning we found a sequentializing vertex. *)


(* Pour ça il faut montrer que len q < len p, pour l'utiliser en argument
structurel *)
(* Fixpoint critical_path {s t : G} (p : Supath switching s t) :=
  (upval p == nil) ||
  [exists u, [exists k : Supath switching u t, [exists q : Supath switching s u,
  (critical_path q) && (upval p == upval q ++ upath_of_path (descending_path3 u) ++ upval k)]]]. *)
(* Fixpoint critical_path {s t : G} (p : Supath switching s t) {struct p} : bool :=
  (upval p == [::]) || (
  [exists t' : G, [exists v : G, vlabel v == tens &&
  [exists p' : Supath switching s t', (critical_path p') &&
  [exists d : Supath t' v, d == descending_path ? &&
  [exists k : ?, k == correctness_path_left ? ? ? &&
  p == p' ++ d ++ k]]]]]) *)

(* TODO in the file about tens, this is the goal of the last section *)
(* A correctness triple for a tens v is a par p with two edge-disjoint strong paths kl and kr (called
  correctness paths) from v to p which both start with a premise of v and end with a premise of p.
  Only used for v a tensor and p a parr. *)
Definition correctness_triple (v p : G) (kl kr : upath) : bool :=
  (supath switching v p kl) && (supath switching v p kr) &&
  (strong kl) && (strong kr) &&
  (upath_disjoint2 kl kr) &&
  (kl != [::]) && (kr != [::]) && (* Always the case -> make it a lemma *)
  let e := forward (exists_edge G) in (* could be any edge *)
  ~~(head e kl).2 && ~~(head e kr).2 &&
  ((head e kl).1 \in edges_at_in v) && ((head e kr).1 \in edges_at_in v) &&
  (last e kl).2 && (last e kr).2 &&
  ((last e kl).1 \in edges_at_in p) && ((last e kr).1 \in edges_at_in p).

(* TODO corollaries : kl neq 0, kr too, one start from left and the other right, and idem for target *)

Lemma test (v : G) (V : vlabel v = ⊗) (T : terminal v) (NS : ~splitting_tens_prop V) :
  { '(p, kl, kr): G * upath * upath & { P : vlabel p = ⅋ | correctness_triple v p kl kr } }.
Proof.
destruct (non_splitting_tens T NS) as [[p P] HP].
exists (p, correctness_path_left T HP, correctness_path_right T HP), P.
unfold correctness_triple.
rewrite correctness_path_left_supath correctness_path_right_supath
correctness_path_left_strong correctness_path_right_strong
correctness_path_disjoint.
repeat (apply /andP; split; trivial).
- apply /eqP. apply correctness_path_left_neq_nil.
- apply /eqP. apply correctness_path_right_neq_nil.
(*
- (* lemma 1 in tens *) admit.
- (* lemma 1 in tens *) admit.
- (* lemma 2 in tens *) admit.
- (* lemma 2 in tens *) admit.
- assert (H := test001 T HP).
  revert H. generalize (correctness_path_left T HP), (correctness_path_right T HP) => ? ?.
  by replace (projT2 (exist (fun _p : G => vlabel _p = ⅋) p P)) with P by apply eq_irrelevance.
*)
Admitted.


Definition descending_path2 (G' : proof_net) (s : G') (S : vlabel s != c) : @path _ _ G'.
Proof. revert S => /eqP-S. exact(descending_path S). Defined.

Definition descending_path3 (G : proof_net) (s : G) :=
  if @boolP (vlabel s != c) is AltTrue P then descending_path2 P else [::].
(* TODO ne pas s'embeter, t definir descending_path avec vlabel s != c directement;
ou prendre ça comme définition de descending_path *)
Lemma descending_path3_eq (G' : proof_net) (s : G') (S : vlabel s <> c) :
  descending_path3 s = descending_path S.
Proof.
unfold descending_path3.
case: {-}_ /boolP => [S' | /negPn/eqP-S']; last by exfalso; by rewrite S' in S.
unfold descending_path2.
f_equal. simpl.
 Check @eq_irrelevance rule_eqType _ _.
Admitted. (* TODO useless? *)

(* TODO do not use splitting_tens_prop2, only bool *)

(* A critical path is either empty or is a critical path concatenated to
   the descending path of its target then to
   kl or kr, for kl and kr correctness paths (i.e. strong edge-disjoint
   paths from in-edges of a tensor to in-edges of a par) *)
(* Here a critical path start from an arbitrary non conclusion vertex,
   arbitrary chosen to be (projT1 (has_terminal G)). *)
Fixpoint path_of_critical_path (l : seq (upath * upath * @upath _ _ G * G)) : @upath _ _ G :=
  match l with
  | [::] => [::]
  | (d, k, _, _) :: l' => path_of_critical_path l' ++ d ++ k
  end.

Definition source_of_critical_path : G := projT1 (has_terminal G).
Definition target_of_critical_path l :=
  (upath_target source_of_critical_path (path_of_critical_path l)).

Fixpoint critical_path (l : seq (upath * upath * upath * G)) : bool :=
  match l with
  | [::] => true
  | (d, k, k', v_parr) :: l' =>
    (* A critical path is empty or is a critical path l' concatenated to *)
    (critical_path l') &&
    (* the descending path starting from the target of l' *)
    (d == upath_of_path (descending_path3 (target_of_critical_path l'))) &&
    (* then a correctness path from the terminal non-sequentializing vertex it arrives into *)
    (vlabel (upath_target (target_of_critical_path l') d) == ⊗) && (* It is also non-splitting, but we do not need it here *)
    (vlabel v_parr == ⅋) &&
    (correctness_triple (upath_target (target_of_critical_path l') d) v_parr k k') &&
    let e := forward (exists_edge G) in (* could be any edge *)
    ((last e d).1 != (head e k).1) (* i.e. k' use the last edge of d, so k does not *)
  end.
(* TOTHINK is it better to directly replace d by the descending path? *)

(* Lemma terminal_utarget_critical_path l :
  critical_path l ->
  terminal (upath_target (projT1 (has_terminal G)) (path_of_critical_path l)).
Proof.
  destruct l as [ | [[[[d k] k'] p] t] l]; simpl.
  { by destruct (has_terminal G). }
  move => /andP[/andP[/andP[/andP[/andP[CP /eqP-?] /eqP-V] /eqP-P] CT] _]. subst d.
  rewrite !map_cat !last_cat descending_path3_eq ?P // => Pc.
  unfold descending_path. destruct (descending_couple _) as [[u c] W U].
  destruct (walk_endpoint W) as [_ Tcu].
  rewrite -endpoint_upath_path in Tcu.
  unfold upath_target in Tcu.
  destruct c; simpl in *; last by rewrite Tcu.
  subst u. clear W.
  revert CT. unfold correctness_triple.
  move => /andP[/andP[/andP[_ /eqP-knil] _] /andP[/andP[/andP[/andP[_ kb] _] ke] _]].
  replace (last _ _) with (last (utarget ((forward (exists_edge G)))) [seq utarget e | e <- k]).
  2:{ apply last_eq. apply /eqP. rewrite map_nil. by apply /eqP. }
  rewrite (last_map (fun e => utarget e)) /=.
  revert kb ke.
  destruct (forward (exists_edge G)) as [? ?].
  by rewrite !in_set /= => -> /eqP-->.
Qed. *)
(* TODO Faux maintenant *)

Lemma concat_strong_nil {G' : base_graph} (p q : @upath _ _ G') :
  strong p -> p <> [::] -> strong (p ++ q).
Proof. by destruct p. Qed. (* TODO in mll_basic *)

Lemma head_cat {T : Type} (x : T) (s1 s2 : seq T) :
  head x (s1 ++ s2) = head (head x s2) s1.
Proof. by destruct s1, s2. Qed. (* TODO in mll_prelim *)

Lemma critical_path_strong l :
  critical_path l -> strong (path_of_critical_path l).
Proof.
  induction l as [ | [[[d k] k'] p] l IH]; simpl; first by [].
  move => /andP[/andP[/andP[/andP[/andP[CP /eqP-?] /eqP-T] /eqP-P] CT] _]. subst d.
  specialize (IH CP). clear CP.
  repeat apply concat_strong; trivial.
  - unfold descending_path3. case: {-}_ /boolP => V' //.
    unfold descending_path2. apply descending_path_strong.
  - revert CT. unfold correctness_triple. introb.
Qed.

(* Main result: a critical path is a switching path *)
(* Corrolary from the following:
   there are no strong path starting from the target of a critical,
   from another edge than the one its arrive to, and reaching
   the critical path, unless it stops on a (terminal) ⅋. *)
Lemma critical_path_cat_supath l :
  critical_path l ->
  supath switching source_of_critical_path (target_of_critical_path l) (path_of_critical_path l) ->
  forall mu t, supath switching (target_of_critical_path l) t mu ->
  strong mu ->
(*   (last (forward (exists_edge G)) (path_of_critical_path l_paths)).1 != (head (forward (exists_edge G)) p).1 -> *)
(* lemma to do: target of crit path is a parr, unless it is empty, so
do not need thid hypothesis *)
(*   vlabel (upath_target t (path_of_critical_path l_paths)) <> ⅋ -> *)
  upath_disjoint switching (path_of_critical_path l) mu.
  (* pas de switching path partant de target de crit path
et intersectant crit path, si part de l'autre arete *)
Proof.
  intros CP L mu t Mu Smu.



  destruct [disjoint ([seq usource e | e <- path_of_critical_path l]
    ++ [seq utarget e | e <- path_of_critical_path l]) &
    [seq utarget e | e <- mu]] eqn:D.
  - apply (@strong_upath_disjoint2 _ _ _ _ _ {| upvalK := L |} {| upvalK := Mu |});
    trivial; simpl.
    + admit.
    + by apply critical_path_strong.
    + clear -D. admit. (* TODO lemma for this - used in the other subcase too *)
  - exfalso.
    revert D => /negP/negP. rewrite disjoint_has negb_involutive => /hasP[v Vl /= Vmu].
    rewrite mem_cat in Vl.
    destruct (@in_elt_sub_fst _ _ (fun u => (u \in [seq usource e | e <- path_of_critical_path l])
     || (u \in [seq utarget e | e <- path_of_critical_path l])) v Vl Vmu) as [n [u [Mueq [Ul Ufst]]]].
    clear v Vl Vmu.
    assert (D : upath_disjoint2 (path_of_critical_path l) (take n.+1 mu)).
    { admit. }
    assert (Mu' : supath switching (target_of_critical_path l) u (take n.+1 mu)).
    { revert Mu.
      rewrite -{1}(cat_take_drop (n.+1) mu).
      enough (upath_target (target_of_critical_path l) (take n.+1 mu) = u) as <-
        by apply supath_prefixK.
        unfold upath_target.
        rewrite map_take.
        rewrite Mueq -cat_rcons take_size_cat ?last_rcons //.
        rewrite size_rcons. rewrite size_take.
(* et là meme difficulté qu'à un autre endroit : 
il faut ajouter n < size dans fst_elt_sub et autres *)
        admit. }
(* TODO upath_dsijoint -> supath_disjoint
upath_disjoint2 -> upath_edge_disjoint *)
Restart.
(* old - other try *)
  intros CP L mu t Mu Smu.
  destruct (upath_disjoint2 (path_of_critical_path l) mu) eqn:D.
  - apply (@strong_upath_disjoint2 _ _ _ _ _ {| upvalK := L |} {| upvalK := Mu |});
    trivial; simpl.
    + admit.
    +  by apply critical_path_strong.
  - rewrite /upath_disjoint2 disjoint_has in D.
    revert D => /negP/negP/hasP[e El /= Emu].
(*     apply in_map_fst in El. destruct El as [bl El]. *)
    apply in_map_fst in Emu. destruct Emu as [bmu Emu].
    destruct (@in_elt_sub_fst _ _ (fun e => e.1 \in [seq x.1 | x <- path_of_critical_path l])
      (e, bmu) El Emu) as [n [a [Mueq [Al Afst]]]].
    clear e bmu El Emu.
    assert (D : upath_disjoint2 (path_of_critical_path l) (take n mu)).
    { unfold upath_disjoint2. apply /disjointP.
      intros x Xl Xmu.
      apply in_map_fst in Xmu. destruct Xmu as [bmu Xmu].
      specialize (Afst _ Xmu).
      contradict Afst. by apply /negP/negPn. }
    
(* TODO en vrai il faudrait un lemme qui dit que si pas upath_dsjoint2,
alors existe suffixe et prefixe upath_disjoint2 ... pour une propriété quelconque
prendre le suffixe et le préfixe tels que ça donne pile *)
(* Commencer par un wlog on a disjoint2, quitte à raccourcir mu pour que ça soit le cas *)

(* TODO may need a lemma of the kind no vertex c in a critical path *)
Admitted.

Lemma critical_path_supath l :
  critical_path l ->
  supath switching source_of_critical_path (target_of_critical_path l) (path_of_critical_path l).
Proof.
  induction l as [ | [[[d k] k'] p] l IH]; simpl.
  { intros _. apply supath_nilK. }
  move => /andP[/andP[/andP[/andP[/andP[CP /eqP-?] /eqP-T] /eqP-P] CT] LH]. subst d.
  specialize (IH CP).
  assert (S : supath switching (target_of_critical_path l) p (upath_of_path (descending_path3 (target_of_critical_path l)) ++ k)).
  { admit. }
(* besoin d'un lemme descending path concat to qqch = switching, utilisé là et
pour le gros lemme d'avant *)
  revert CT. unfold correctness_triple. introb.
  assert (St : strong (upath_of_path (descending_path3 (target_of_critical_path l)) ++ k)).
  { apply concat_strong; trivial.
    unfold descending_path3. case: {-}_ /boolP => V' //.
    unfold descending_path2. apply descending_path_strong. }
  replace (target_of_critical_path ((upath_of_path (descending_path3 (target_of_critical_path l)),
    k, k', p) :: l)) with p.
  2:{ rewrite /target_of_critical_path /= !map_cat !last_cat.
      transitivity (last (utarget (forward (exists_edge G))) [seq utarget _e | _e <- k]).
      2:{ apply last_eq. apply /eqP. rewrite map_nil. by apply /eqP. }
      rewrite (last_map (fun e => utarget e)) /=.
      revert _Hif10 _Hif12. (* TODO Mangle *)
      clear. generalize (last (forward (exists_edge G)) k) => e.
      destruct e as [e []] => //= _.
      by rewrite !in_set => /eqP-->. }
  assert (D2 : upath_disjoint switching {| upvalK := IH |} {| upvalK := S |}).
  { exact (critical_path_cat_supath CP S St). }
  exact (supath_catK D2).
Admitted.

Lemma critical_path_desc_terminal l :
  critical_path l ->
  terminal (upath_target (target_of_critical_path l) (descending_path3 (target_of_critical_path l))).
Proof.
(* TODO use descending_node instead of target of descending_path? *)
  intro L.
  unfold descending_path3. case: {-}_ /boolP => [V | /negPn/eqP-V].
  - unfold descending_path2, descending_path.
    destruct (descending_couple (elimNTF eqP V)) as [[t p] W T].
    rewrite endpoint_upath_path.
    by destruct (walk_endpoint W) as [_ ->].
  - contradict V.
    revert L. destruct l as [ | [[[d k] k'] p] l]; simpl.
    + rewrite /target_of_critical_path /source_of_critical_path /=.
      destruct (has_terminal G) as [v V]. move => _ /= V'.
      revert V. by rewrite /terminal V'.
    + move => /andP[/andP[/andP[_ /eqP-P] /andP[/andP[/andP[_ knil] _] /= /andP[/andP[/andP[/andP[_ k2] _] k1] _]]] _].
      enough (target_of_critical_path ((d, k, k', p) :: l) = p) as -> by by rewrite P.
      rewrite /target_of_critical_path /= !map_cat !last_cat.
      transitivity (last (utarget (forward (exists_edge G))) [seq utarget e | e <- k]).
      * apply last_eq. apply /eqP. by rewrite map_nil.
      * rewrite (last_map (fun e => utarget e)).
        revert k1 k2.
        rewrite !in_set.
        by destruct (last (forward (exists_edge G)) k) as [e []] => //= /eqP-->.
Qed.

Lemma critical_path_extend l :
  critical_path l ->
  forall (V : vlabel (upath_target (target_of_critical_path l) (descending_path3 (target_of_critical_path l))) = ⊗),
  ~ splitting_tens_prop V ->
  { '(p, k, k', d) | critical_path ((d, k, k', p) :: l) && (k != [::])}.
Proof.
  intros C V NS.
  assert (T : terminal (upath_target (target_of_critical_path l) (descending_path3 (target_of_critical_path l)))).
  { by apply critical_path_desc_terminal. }
  destruct (test T NS) as [[[p k] k'] [P CT]].
  exists (p, k, k', upath_of_path (descending_path3 (target_of_critical_path l))). simpl.
  rewrite C V P CT !eq_refl {C} /=.
  revert CT. unfold correctness_triple.
(* TODO avant le exist un wlog entre k et k' pour assurer ça *) 
Admitted.

Lemma critical_path_extend_size l :
  critical_path l ->
  forall (V : vlabel (upath_target (target_of_critical_path l) (descending_path3 (target_of_critical_path l))) = ⊗),
  ~ splitting_tens_prop V ->
  {l_ext | critical_path l_ext && (size (path_of_critical_path l) < size (path_of_critical_path l_ext))}.
Proof.
  intros C V NS.
  destruct (critical_path_extend C NS) as [[[[p k] k'] d] CP]. revert CP => /andP[CP knil].
  exists ((d, k, k', p) :: l).
  rewrite CP /= !size_cat.
  enough (size k <> 0) by lia.
  apply /eqP. by rewrite size_eq0.
Qed.


(* Sketch of the end:
- for a non-terminal vertex -> descending path to a terminal one (see mll_basic)
- correctness and descending path are strong
- concat of strong paths is a strong path
- strong cycle -> switching cycle -> incorrect
- build a critical path by concatenating these paths, strong, can be prolonged while target is not sequentializing
- but this gives an infinite supath, absurd
*)
(* TODO follow the proof I wrote on MALL *)

(* TODO idea: write splitting_tens_bool with a vlabel v == tens ==> ...  so not to
have boolP here*)
Lemma has_sequentializing :
  {v : G & sequentializing v}.
Proof.
  (* 1st step: we get out of Type and into bool *)
  enough (E : ~~ [forall v : G, (vlabel v == c) || ~~ terminal v ||
    (if @boolP (vlabel v == ⊗) is AltTrue V then ~~ splitting_tens_bool (eqP V) else false)]).
  { revert E => /forallPn/sigW[v /norP[/norP[VC /negPn-T] S]].
    exists v.
    revert S. case: {-}_ /boolP => V.
    - move => /negPn/splitting_tensP.
      by apply splitting_tens_prop_is_sequentializing.
    - move => _.
      destruct (vlabel v) eqn:V'; try by [].
      + by apply terminal_ax_is_sequentializing.
      + by apply terminal_parr_is_sequentializing.
      + admit. (* cut case -> to treat similarly as a tens / replace cut by tens to assume no cuts, with lemma
seq in replaced give seq original *) }
  apply /negP => /forallP-H.
  (* 2nd step: we build a switching path of arbitrary size, a contradiction *)
  enough (E : forall n, {l | critical_path l && (size (path_of_critical_path l) >= n)}).
  { clear - E.
    destruct (E (S #|edge G|)) as [l CP]. revert CP => /andP[CP Scp].
    assert (F := upath_size (critical_path_supath CP)).
    lia. }
  intro n. induction n as [ | n IH].
  { by exists [::]. }
  destruct IH as [l CP]. revert CP => /andP[CP Scp].
  assert (Term : terminal (upath_target (target_of_critical_path l) (descending_path3 (target_of_critical_path l)))).
  { by apply critical_path_desc_terminal. }
  specialize (H (upath_target (target_of_critical_path l) (descending_path3 (target_of_critical_path l)))).
  revert H.
  rewrite Term.
  replace (vlabel (upath_target (target_of_critical_path l) (descending_path3 (target_of_critical_path l)))
      == c) with false.
  2:{ revert Term. clear. unfold terminal. by destruct (vlabel _). }
  case: {-}_ /boolP => V //= /splitting_tensP-NS.
  destruct (critical_path_extend_size CP NS) as [l' Hl].
  exists l'. revert Hl => /andP[-> Sl] /=. lia.
(* TODO seems round about, especially the beginning *)
Admitted.

End Critical_path.

(* ax : pas iso a G mais ps p iso à ax exp G *)
(* TODO ne séquentializer que des réseaux atomiques ! ou mettre preuve avec ax on A, ce qui me parait mieux *)
(** ** Sequentialization Theorem *)
Definition sequentialize (G : proof_net) : { p : ll (sequent G) & ps p ≃d G }.
Proof.
  revert G.
  enough (Hm : forall n (G : proof_net), #|edge G| = n -> { p : ll (sequent G) & ps p ≃d G })
    by by intro G; apply (Hm #|edge G|).
  intro n; induction n as [n IH] using lt_wf_rect; intros G ?; subst n.
  destruct (@has_sequentializing G) as [v V].
  unfold sequentializing in V. destruct (vlabel v); try by [].
  - destruct V as [A h].
    set pi := ax_exp A : ⊢ sequent (ax_graph_data A).
    exists (ex_r pi (sequent_iso_perm h)). simpl. unfold pi.
    unfold ax_exp.
    assert {x | A = var x} as [? ?] by admit. (* easy case where A is an atomic axiom TODO define proof with generalized axioms *)
    subst A. simpl.
    symmetry. exact (iso_to_isod h).
  - destruct V as [[G0 G1] h].
    assert (C : correct (add_node_ps_tens G0 G1)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_tens_correct_contra C) as [[[[e0 l0] e1] l1] [Hl0 Hl1]].
    assert ((#|edge G0| < #|edge G|)%coq_nat /\ (#|edge G1| < #|edge G|)%coq_nat) as [C0 C1].
    { rewrite (card_bij h.e) add_node_ps_tens_ecard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    assert (IH1 := IH _ C1 G1 erefl).
    revert IH0 IH1. rewrite {IH C C0 C1} /sequent Hl0 Hl1 /= => IH0 IH1.
    destruct IH0 as [IH0 h0]. destruct IH1 as [IH1 h1].
    assert (H : flabel e0 ⊗ flabel e1 :: [seq flabel e | e <- l1] ++ [seq flabel e | e <- l0]
      = sequent (add_node_ps_tens G0 G1))
      by by rewrite add_node_sequent union_sequent /sequent /= /union_order Hl0 Hl1.
    exists (ex_r (rew H in tens_r IH0 IH1) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_tens_isod.
  - destruct V as [G0 h].
    assert (C : correct (add_node_ps_parr G0)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_parr_correct_contra C) as [[[e0 e1] l] Hl].
    assert (C0 : (#|edge G0| < #|edge G|)%coq_nat).
    { rewrite (card_bij h.e) add_node_ps_parr_ecard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    revert IH0. rewrite {IH C C0} /sequent Hl /= => IH0.
    destruct IH0 as [IH0 h0].
    assert (H : flabel e0 ⅋ flabel e1 :: [seq flabel e | e <- l]
      = sequent (add_node_ps_parr G0))
      by by rewrite add_node_sequent /sequent /= Hl.
    exists (ex_r (rew H in parr_r IH0) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_parr_isod.
  - destruct V as [[G0 G1] h].
    assert (C : correct (add_node_ps_cut G0 G1)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_cut_correct_contra C) as [[[[e0 l0] e1] l1] [Hl0 [Hl1 Hf]]].
    assert (Hf2 : flabel e1 = flabel e0^) by by apply /eqP.
    assert ((#|edge G0| < #|edge G|)%coq_nat /\ (#|edge G1| < #|edge G|)%coq_nat) as [C0 C1].
    { rewrite (card_bij h.e) add_node_ps_cut_ecard //.
      assert (E0 := card_edge_proof_net G0).
      assert (E1 := card_edge_proof_net G1).
      lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    assert (IH1 := IH _ C1 G1 erefl).
    revert IH0 IH1. rewrite {IH C C0 C1} /sequent Hl0 Hl1 /= Hf2 => IH0 IH1.
    destruct IH0 as [IH0 h0]. destruct IH1 as [IH1 h1].
    assert (H : [seq flabel e | e <- l1] ++ [seq flabel e | e <- l0]
      = sequent (add_node_ps_cut G0 G1))
      by by rewrite add_node_sequent union_sequent /sequent /= /union_order Hl0 Hl1 Hf.
    exists (ex_r (rew H in cut_r IH0 IH1) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_cut_isod.
(*
Restart.
  revert G.
  enough (Hm : forall n (G : proof_net), r#|G| = n -> { p : ll (sequent G) & ps p ≃d G })
    by by intro G; apply (Hm r#|G|).
  intro n; induction n as [n IH] using lt_wf_rect; intros G ?; subst n.
  destruct (has_sequentializing G) as [v V].
  unfold sequentializing in V. destruct (vlabel v); try by [].
  - destruct V as [A h].
    set pi := ax_exp A : ⊢ sequent (ax_graph_data A).
    exists (ex_r pi (sequent_iso_perm h)). simpl. unfold pi.
    unfold ax_exp.
    assert({x | A = var x}) as [? ?]. admit. (* easy case where A is an atomic axiom *)
    subst A. simpl.
    symmetry. exact (iso_to_isod h).
  - destruct V as [[G0 G1] h].
    assert (C : correct (add_node_ps_tens G0 G1)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_tens_correct_contra C) as [[[[e0 l0] e1] l1] [Hl0 Hl1]].
    assert ((r#|G0| < r#|G|)%coq_nat /\ (r#|G1| < r#|G|)%coq_nat) as [C0 C1].
    { rewrite (rcard_iso h) add_node_ps_tens_rcard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    assert (IH1 := IH _ C1 G1 erefl).
    revert IH0 IH1. rewrite {IH C C0 C1} /sequent Hl0 Hl1 /= => IH0 IH1.
    destruct IH0 as [IH0 h0]. destruct IH1 as [IH1 h1].
    assert (H : flabel e0 ⊗ flabel e1 :: [seq flabel e | e <- l1] ++ [seq flabel e | e <- l0]
      = sequent (add_node_ps_tens G0 G1))
      by by rewrite add_node_sequent union_sequent /sequent /= /union_order Hl0 Hl1.
    exists (ex_r (rew H in tens_r IH0 IH1) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_tens_isod.
  - destruct V as [G0 h].
    assert (C : correct (add_node_ps_parr G0)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_parr_correct_contra C) as [[[e0 e1] l] Hl].
    assert (C0 : (r#|G0| < r#|G|)%coq_nat).
    { rewrite (rcard_iso h) add_node_ps_parr_rcard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    revert IH0. rewrite {IH C C0} /sequent Hl /= => IH0.
    destruct IH0 as [IH0 h0].
    assert (H : flabel e0 ⅋ flabel e1 :: [seq flabel e | e <- l]
      = sequent (add_node_ps_parr G0))
      by by rewrite add_node_sequent /sequent /= Hl.
    exists (ex_r (rew H in parr_r IH0) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_parr_isod.
  - destruct V as [[G0 G1] h].
    assert (C : correct (add_node_ps_cut G0 G1)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_cut_correct_contra C) as [[[[e0 l0] e1] l1] [Hl0 [Hl1 Hf]]].
    assert (Hf2 : flabel e1 = flabel e0^) by by apply /eqP.
    assert ((r#|G0| < r#|G|)%coq_nat /\ (r#|G1| < r#|G|)%coq_nat) as [C0 C1].
    { rewrite (rcard_iso h) add_node_ps_cut_rcard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    assert (IH1 := IH _ C1 G1 erefl).
    revert IH0 IH1. rewrite {IH C C0 C1} /sequent Hl0 Hl1 /= Hf2 => IH0 IH1.
    destruct IH0 as [IH0 h0]. destruct IH1 as [IH1 h1].
    assert (H : [seq flabel e | e <- l1] ++ [seq flabel e | e <- l0]
      = sequent (add_node_ps_cut G0 G1))
      by by rewrite add_node_sequent union_sequent /sequent /= /union_order Hl0 Hl1 Hf.
    exists (ex_r (rew H in cut_r IH0 IH1) (sequent_iso_perm h)).
    rewrite /= ps_rew {H}.
    refine (iso_data_comp _ (iso_data_sym (iso_to_isod h))).
    apply perm_isod. simpl ps.
    by apply add_node_ps_cut_isod.
*)
Admitted.
(* TODO voir derniere quest exam et focalisation + seqpn *)

(* TOTHINK on utilise seulement connexité left si tout va bien *)



Fixpoint nb_cut {l : list formula} (pi : ⊢ l) := match pi with
  | ax_r x                 => 0
  | ex_r _ _ pi0 _         => nb_cut pi0
  | tens_r _ _ _ _ pi0 pi1 => nb_cut pi0 + nb_cut pi1
  | parr_r _ _ _ pi0       => nb_cut pi0
  | cut_r _ _ _ pi0 pi1    => nb_cut pi0 + nb_cut pi1 + 1
  end.
(*
Lemma ps_nb_cut {l : list formula} (pi : ⊢ l) : #|[set v : ps pi | vlabel v == cut]| = nb_cut pi.
Proof.
  induction pi as [x | | A B l0 l1 pi0 H0 pi1 H1 | A B l0 pi0 H0 | A l0 l1 pi0 H0 pi1 H1].
  - enough (H : [set v : ax_ps x | vlabel v == cut] = set0) by by rewrite H cards0.
    apply /setP; intro v; destruct_I v;
    by rewrite !in_set.
  - by [].
  - rewrite /= -H0 -H1.
Abort. *)
(* TODO Lemma : nb cut ps (pi) = nb cut pi, idem other rules, et dans le sens sequentialisation aussi -> déductible de p = ps pi ! *)
End Atoms.