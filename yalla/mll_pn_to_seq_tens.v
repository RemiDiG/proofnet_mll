(* Sequentialisation - Splitting tensor lemma *)
(* From a Proof Net, return a LL proof of the same sequent *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export mll_prelim graph_more upath supath mgraph_tree mll_def mll_basic mll_correct mll_seq_to_pn
  mll_pn_to_seq_def mll_pn_to_seq.

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


(** NEW TRY **)


Section Splitting_tens.
Context {G : proof_net} {v : G} (vlabel_v : vlabel v = ⊗)
  (splitting_v : splitting bridge v) (terminal_v : terminal v).

Local Notation concl_v := (target (ccl_tens vlabel_v)).

Definition Sl : {set G} := [set u | [exists p : Simple_upath G,
  (upath_source v p == v) && (upath_target v p == u) &&
  (head (forward (left_tens vlabel_v)) (supval p) == backward (left_tens vlabel_v))]].

Definition Sr : {set G} := setT :\: Sl :\ v :\ concl_v.

Lemma source_left_Sl : source (left_tens vlabel_v) \in Sl.
Proof.
  rewrite /Sl in_set.
  apply/existsP.
  assert (S : simple_upath [:: backward (left_tens vlabel_v)])
    by by rewrite simple_upath_edge.
  exists {| supvalK := S |}. by rewrite /= left_e !eq_refl.
Qed.

Lemma source_right_Sr : source (right_tens vlabel_v) \in Sr.
Proof.
  rewrite /Sr !in_set andb_true_r.
  assert (source_r_neq_v : source (right_tens vlabel_v) != v).
  { apply/eqP.
    rewrite -{2}(right_e (or_introl vlabel_v)).
    apply no_selfloop. }
  assert (source_l_neq_v : source (left_tens vlabel_v) != v).
  { apply/eqP.
    rewrite -{2}(left_e (or_introl vlabel_v)).
    apply no_selfloop. }
  assert (left_right : left_tens vlabel_v == right_tens vlabel_v = false).
  { apply/eqP. apply left_neq_right. }
  rewrite source_r_neq_v /=.
  apply/andP; split.
  { apply/eqP. apply no_source_c.
    apply (terminal_source terminal_v), ccl_e. }
  apply/existsPn. move=> [[ | [e b] p] simple_p] /=.
  { cbn. by rewrite !andb_false_r. }
  rewrite !negb_andb.
  case/boolP: (endpoint (~~ b) e == v) => //= source_e.
  case/boolP: (last (endpoint b e) [seq utarget e | e <- p] == source (right_tens vlabel_v))
    => //= target_p.
  case/boolP: (e == left_tens vlabel_v) => //= /eqP-?. subst e.
  destruct b; first by []. simpl in *. clear source_e.
  enough (simple_pe : simple_upath (rcons (backward (left_tens vlabel_v) :: p) (forward (right_tens vlabel_v)))).
  { move: splitting_v => /forallP/(_ {| supvalK := simple_pe |}) /=.
    by rewrite /bridge left_e map_rcons !last_rcons right_e eq_refl vlabel_v /= left_right. }
  rewrite simple_upath_rcons simple_p /= left_e right_e (eqP target_p) eq_refl in_cons negb_orb
    !(eq_sym v) source_r_neq_v source_l_neq_v !andb_true_r /=.
  repeat (apply/andP; split).
  - destruct p as [ | p e _] using last_ind => //=.
    { by rewrite eq_sym left_right. }
    move: simple_p target_p.
    rewrite simple_upath_cons simple_upath_rcons !map_rcons !last_rcons in_rcons negb_orb left_e.
    move=> /andP[/andP[_ /andP[source_e _]] _] target_e.
    destruct e as [e b].
    apply/eqP. move => /= ?. subst e.
    move: target_e source_e.
    destruct b; rewrite /= right_e ?eq_refl //.
    move=> /eqP-<-. by rewrite eq_refl.
  - move: simple_p. rewrite simple_upath_cons /= left_e.
    move=> /andP[/andP[/andP[/andP[simple_p head_p] source_p] v_notin_sources_p]
      /orP[/eqP--> // | no_cyclic_p]].
    apply/negP => v_in_targets_p.
    assert (F : v \in upath_target v p :: [seq usource _e | _e <- p])
      by by rewrite (mem_usource_utarget_uwalk (uwalk_of_simple_upath simple_p v))
      in_cons v_in_targets_p orb_true_r.
    move: F. rewrite in_cons (negPf v_notin_sources_p) orb_false_r /=.
    rewrite (@last_eq _ _ (source (left_tens vlabel_v))); last by destruct p.
    by rewrite (eqP target_p) eq_sym (negPf source_r_neq_v).
Qed.

(* Our two connected components, with a conclusion replacing v *)
Definition Gl : base_graph := @add_concl_graph _ (induced Sl)
  (Sub (source (left_tens vlabel_v)) source_left_Sl) c (flabel (left_tens vlabel_v)).
Definition Gr : base_graph := @add_concl_graph _ (induced Sr)
  (Sub (source (right_tens vlabel_v)) source_right_Sr) c (flabel (right_tens vlabel_v)).
(* TODO : in all this part we do things in double, try to merge them when possible:
define Glr b = if b then Gl else Gr, and prove this is a proof structure *)

(* Function sending a list of edges of G to a list of edges of Gl *)
Fixpoint to_Gl (l : seq (edge G)) : seq (edge Gl) :=
  match l with
  | [::] => [::]
  | e :: l' => (if @boolP (e \in edge_set Sl) is AltTrue E then [:: Some (inl (Sub e E))] else [::]) ++ to_Gl l'
  end.
(* Function sending a list of edges of G to a list of edges of Gr *)
Fixpoint to_Gr (l : seq (edge G)) : seq (edge Gr) :=
  match l with
  | [::] => [::]
  | e :: l' => (if @boolP (e \in edge_set Sr) is AltTrue E then [:: Some (inl (Sub e E))] else [::]) ++ to_Gr l'
  end.

Definition Gl_graph_data : graph_data := {|
  graph_of := Gl;
  order := None :: to_Gl (order G);
  |}.
Definition Gr_graph_data : graph_data := {|
  graph_of := Gr;
  order := None :: to_Gr (order G);
  |}.

Definition edge_to_Gl (e : edge G) : edge Gl :=
  if @boolP (e \in edge_set Sl) is AltTrue E then Some (inl (Sub e E)) else None.
Definition edge_to_Gr (e : edge G) : edge Gr :=
  if @boolP (e \in edge_set Sr) is AltTrue E then Some (inl (Sub e E)) else None.

Lemma edge_to_Gl_inj b u : u \in Sl -> {in edges_at_outin b u &, injective edge_to_Gl}.
Proof.
  move=> U e f Ein Fin.
  rewrite /edge_to_Gl.
  case: {-}_ /boolP => [E | E]; case: {-}_ /boolP => [F | F] //.
  - move=> H. by inversion H.
  - move=> _.
    transitivity (left_tens V); [ | symmetry].
    + by apply (out_Sl U Ein).
    + by apply (out_Sl U Fin).
Qed.
Lemma edge_to_Gr_inj b u : u \in Sr -> {in edges_at_outin b u &, injective edge_to_Gr}.
Proof.
  intros U e f Ein Fin.
  unfold edge_to_Gr.
  case: {-}_ /boolP => [E | E]; case: {-}_ /boolP => [F | F] //.
  - intro H. by inversion H.
  - intros _.
    transitivity (right_tens V); [ | symmetry].
    + by apply (out_Sr U Ein).
    + by apply (out_Sr U Fin).
Qed.

(* TODO graphs induits donnent iso add_tens *)

End Splitting_tens.


(** END NEW TRY **)

(* TODO this uses connectivity! *)
Lemma utree_switching_left {G : proof_net} : utree (@switching_left G).
Proof. split; [apply uacyclic_swithching_left, G | apply uconnected_from_nb1, G]. Qed.


Section Splitting_tens.
Context {G : proof_net} {v : G} (V : vlabel v = ⊗) (T : terminal v).

Local Notation F := (@switching_left_sinj _ G).
Local Notation TL := utree_switching_left.
Local Notation TP := (utree_part F TL v).

Lemma vlabel_target_ccl : vlabel (target (ccl_tens V)) = c.
Proof. revert T. by rewrite (terminal_tens_parr (or_introl V)) => /eqP-->. Qed.

Lemma partition_terminal_ccl x :
  utree_part (@switching_left_sinj _ G) utree_switching_left v x = Some (ccl_tens V) ->
  pblock (preim_partition TP [set: G]) x = [set target (ccl_tens V)].
Proof.
  intro X. apply /setP => y.
  assert (Spart := preim_partitionP TP [set: G]).
  revert Spart => /andP[/eqP-Cov /andP[Triv _]].
  rewrite in_set -eq_pblock // ?Cov {Cov Triv} // preim_partition_pblock_eq // X {X}.
  destruct (eq_comparable y (target (ccl_tens V))) as [? | Y].
  - subst y. rewrite eq_refl. apply /eqP.
    unfold utree_part. destruct (utree_unique_path F TL v (target (ccl_tens V))) as [P Pu].
    assert (S : supath switching_left v (target (ccl_tens V)) [:: forward (ccl_tens V)]).
    { rewrite /supath /= in_cons negb_orb ccl_e. splitb.
      by rewrite /switching_left vlabel_target_ccl. }
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
    clear - U1 Vb2 T.
    destruct e2 as (e2, []); simpl in Vb2.
    + contradict Vb2. apply no_source_c, vlabel_target_ccl.
    + revert U1. rewrite map_cons in_cons => /norP[U1 _].
      contradict U1. apply /negP/negPn/eqP.
      simpl. f_equal.
      apply one_target_c; by rewrite Vb2 // vlabel_target_ccl.
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
  unfold utree_part. destruct (utree_unique_path F TL v (target (ccl_tens V))) as [P Pu].
  assert (S : supath switching_left v (target (ccl_tens V)) [:: forward (ccl_tens V)]).
  { rewrite /supath /= in_cons negb_orb ccl_e /switching_left vlabel_target_ccl. splitb. }
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
    -?(partition_terminal_ccl  partition_terminal_utree_part_ccl).
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

(* TODO s'en servir plutôt que le reprouver à chaque fois *)
Lemma left_tens_Sr : left_tens V \notin edge_set Sl.
Proof.
  rewrite !in_set left_e. apply /negP => /andP[_ E].
  destruct partition_disjoint as [_ [D _]].
  refine (disjointE D _ E). by rewrite in_set.
Qed.

(* TODO what follows uses connexity, find a way not to use it! *)
(* Our two connected components, with a conclusion replacing v *)
Definition Gl : base_graph := @add_concl_graph _ (induced Sl)
  (Sub (source (left_tens V)) source_left_Sl) c (flabel (left_tens V)).
Definition Gr : base_graph := @add_concl_graph _ (induced Sr)
  (Sub (source (right_tens V)) source_right_Sr) c (flabel (right_tens V)).
(* TODO : in all this part we do things in double, try to merge them when possible:
define Glr b = if b then Gl else Gr, and prove this is a proof structure *)

(* Function sending a list of edges of G to a list of edges of Gl *)
Fixpoint to_Gl (l : seq (edge G)) : seq (edge Gl) :=
  match l with
  | [::] => [::]
  | e :: l' => (if @boolP (e \in edge_set Sl) is AltTrue E then [:: Some (inl (Sub e E))] else [::]) ++ to_Gl l'
  end.
(* Function sending a list of edges of G to a list of edges of Gr *)
Fixpoint to_Gr (l : seq (edge G)) : seq (edge Gr) :=
  match l with
  | [::] => [::]
  | e :: l' => (if @boolP (e \in edge_set Sr) is AltTrue E then [:: Some (inl (Sub e E))] else [::]) ++ to_Gr l'
  end.

Definition Gl_graph_data : graph_data := {|
  graph_of := Gl;
  order := None :: to_Gl (order G);
  |}.
Definition Gr_graph_data : graph_data := {|
  graph_of := Gr;
  order := None :: to_Gr (order G);
  |}.

Definition edge_to_Gl (e : edge G) : edge Gl :=
  if @boolP (e \in edge_set Sl) is AltTrue E then Some (inl (Sub e E)) else None.
Definition edge_to_Gr (e : edge G) : edge Gr :=
  if @boolP (e \in edge_set Sr) is AltTrue E then Some (inl (Sub e E)) else None.

Section Splitting_is_sequentializing.
(* We prove here that splitting_tens_prop -> sequentializing v. *)
(* Hypothesis (NS : splitting_tens_prop). *)
Hypothesis (splitting_v : splitting bridge v) (terminal_v : terminal v).

Lemma no_crossing (e : edge G) (b : bool) :
  e \notin edge_set Sl -> e \notin edge_set Sr -> e <> left_tens V ->
  e <> right_tens V -> usource (e, b) \in Sl -> utarget (e, b) \in Sr -> False.
Proof.
  move=> El Er Eleft Eright Se Te.
  destruct partition_disjoint as [Dlr [Dvl [Dvr _]]].
  destruct (uconnected_Sl (Sub (source (left_tens V)) source_left_Sl) (Sub (usource (e, b)) Se))
    as [[p1' P1'] _].
  revert P1' => /andP[/andP[P1' _] _].
  apply uwalk_to_no_cyclic in P1' as [[p1 simple_1] [source_1 [target_1 non_cyclic_1]]].
  clear p1'.
  destruct (uconnected_Sr (Sub (utarget (e, b)) Te) (Sub (source (right_tens V)) source_right_Sr))
    as [[p2' P2'] _].
  revert P2' => /andP[/andP[P2' _] _].
  apply uwalk_to_no_cyclic in P2' as [[p2 simple_2] [source_2 [target_2 non_cyclic_2]]].
  clear p2'.
  enough (S : simple_upath ([:: backward (left_tens V)] ++ [seq (val a.1, a.2) | a <- p1] ++
    [:: (e, b)] ++ [seq (val a.1, a.2) | a <- p2] ++ [:: forward (right_tens V)])).
  { contradict splitting_v.
    apply/negP/forallPn.
    exists {| supval := _ ; supvalK := S |}.
    rewrite /= !negb_imply left_e eq_refl /= !map_cat /= map_cat !last_cat /=
      !last_cat /= right_e eq_refl /= /bridge negb_orb negb_andb left_e V /=
      orb_true_r andb_true_r.
    apply/eqP. apply left_neq_right. }
  repeat apply simple_upath_cat.
  - apply simple_upath_edge.
  - by rewrite -simple_upath_in_subgraph.
  - apply simple_upath_edge.
  - by rewrite -simple_upath_in_subgraph.
  - apply simple_upath_edge.
  - move: target_2.
    destruct p2 as [ | ? ? _] using last_ind; first by [].
    rewrite /= !map_rcons !last_rcons.
    move=> H. inversion H as [[H']]. by rewrite H'.
  - rewrite disjoint_sym disjoint_cons disjoint_nil andb_true_r /=.
    assert (Hr : source (right_tens V) = upath_target (utarget (e, b)) [seq (sval e.1, e.2) | e <- p2]).
    { move: target_2 => /eqP. cbn. rewrite -last_map /= => /eqP-target_2.
      by rewrite -[in LHS]target_2 -!map_comp. }
    rewrite {1}Hr {Hr}.
    assert (simple_2' : simple_upath [seq (sval e.1, e.2) | e <- p2])
      by by rewrite -simple_upath_in_subgraph simple_2.
    apply/negP => t_in_s.
    assert (F := simple_upath_target_in_sources simple_2' t_in_s).
    contradict F. apply/eqP.
    destruct non_cyclic_2 as [p2_nil | non_cyclic_2]; first by (simpl in p2_nil; by subst p2).
    move: non_cyclic_2 => /eqP.
    rewrite -target_2 -source_2 /=. cbn.
    rewrite -last_map -head_map /= -!map_comp.
    by destruct p2.
  - rewrite /= right_e.
    clear - Dvr.
    induction p2 as [ | [[e2 E2] b2] p2 IH]; first by [].
    rewrite /= in_cons negb_orb {}IH andb_true_r {p2}.
    apply/eqP => ?. subst v.
    move: E2. rewrite in_set => /andP[SE2 TE2].
    destruct b2.
    + refine (disjointE Dvr _ TE2). by rewrite in_set.
    + refine (disjointE Dvr _ SE2). by rewrite in_set.
  - clear - Dvr.
    destruct p2 as [ | e22 p2]; first by []. simpl.
    case/lastP: p2 => [ | p2 e22'] /=.
    + destruct e22 as [[e22 E22] b22].
      simpl. apply/eqP => ?. subst e22.
      contradict E22. apply/negP.
      rewrite in_set right_e negb_andb.
      apply/orP. right. apply/negP => F.
      refine (disjointE Dvr _ F). by rewrite in_set.
    + rewrite map_rcons last_rcons /=.
      destruct e22' as [[e22' E22'] b22'].
      simpl. apply/eqP => ?. subst e22'.
      contradict E22'. apply/negP.
      rewrite in_set right_e negb_andb.
      apply/orP. right. apply/negP => F.
      refine (disjointE Dvr _ F). by rewrite in_set.
  - destruct p2 as [ | e2 p2]; simpl.
    + move: target_2 => /eqP.
      by rewrite sub_val_eq.
    + move: source_2 => /eqP.
      by rewrite sub_val_eq eq_sym.
  - rewrite disjoint_cons disjoint_nil andb_true_r /= map_cat mem_cat negb_orb in_cons in_nil orb_false_r /=.
    apply/andP. split.
    + rewrite -map_comp.
      clear - Dlr Se.
      induction p2 as [ | [[e2 E2] b2] p2 IH]; first by [].
      rewrite /= in_cons negb_orb {}IH andb_true_r {p2}.
      apply/eqP => H.
      move: E2. rewrite in_set => /andP[SE2 TE2].
      rewrite H in Se.
      destruct b2.
      * exact (disjointE Dlr Se SE2).
      * exact (disjointE Dlr Se TE2).
    + apply/eqP => H.
      refine (disjointE Dlr Se _). by rewrite H source_right_Sr.
  - assert (target (right_tens V) != utarget (e, b)).
    { rewrite right_e.
      apply/eqP => F.
      refine (disjointE Dvr _ Te). by rewrite F in_set. }
    destruct p2 as [ | e2 p2]; rewrite /= in_cons in_nil orb_false_r //.
    by rewrite map_cat last_cat.
  - destruct p2 as [ | [[e2 E2] b2] p2]; simpl.
    + by apply/eqP.
    + apply/eqP => ?. subst e2. by rewrite E2 in Er.
  - move: target_1 => /eqP.
    rewrite /= sub_val_eq /=.
    clear.
    case/lastP: p1 => [// | e1 p1].
    by rewrite !map_rcons !last_rcons.
  - rewrite disjoint_sym !map_cat !disjoint_cat /= !disjoint_cons !disjoint_nil !andb_true_r.
    repeat (apply/andP; split).
    + assert (endpoint (~~ b) e = upath_target (source (left_tens V)) [seq (sval e.1, e.2) | e <- p1]) as ->.
      { move: target_1 => /eqP. cbn. rewrite -last_map /= => /eqP-target_1.
        by rewrite -[in LHS]target_1 -!map_comp. }
      assert (simple_1' : simple_upath [seq (sval e.1, e.2) | e <- p1])
        by by rewrite -simple_upath_in_subgraph simple_1.
      apply/negP => t_in_s.
      assert (F := simple_upath_target_in_sources simple_1' t_in_s).
      contradict F. apply/eqP.
      destruct non_cyclic_1 as [p1_nil | non_cyclic_1]; first by (simpl in p1_nil; by subst p1).
      move: non_cyclic_1 => /eqP.
      rewrite -target_1 -source_1 /=. cbn.
      rewrite -last_map -head_map /= -!map_comp.
      by destruct p1.
    + rewrite -!map_comp.
      apply /disjointP => u /mapP[[[a A] c] /= _ u_eq_a] /mapP[[[a' A'] c'] /= _ u_eq_a'].
      rewrite u_eq_a' in u_eq_a. clear - u_eq_a A A' Dlr.
      move: A A'. rewrite !in_set => /andP[SA TA] /andP[SA' TA'].
      destruct c, c'.
      * apply (disjointE Dlr SA'). by rewrite u_eq_a.
      * apply (disjointE Dlr TA'). by rewrite u_eq_a.
      * apply (disjointE Dlr SA'). by rewrite u_eq_a.
      * apply (disjointE Dlr TA'). by rewrite u_eq_a.
    + rewrite -map_comp.
      apply/mapP. move=> [[[a A] c] /= _ a_eq].
      move: A. rewrite in_set => /andP[SA TA].
      destruct c.
      * apply (disjointE Dlr SA). by rewrite -a_eq source_right_Sr.
      * apply (disjointE Dlr TA). by rewrite -a_eq source_right_Sr.
  - rewrite /= map_cat last_cat /= right_e -map_comp.
    apply/mapP. move => [[[a A] c] /= _ a_eq].
    move: A. rewrite in_set => /andP[SA TA].
    destruct c.
    + refine (disjointE Dvl _ TA). by rewrite -a_eq in_set.
    + refine (disjointE Dvl _ SA). by rewrite -a_eq in_set.
  - destruct p1 as [ | e1 p1]; first by [].
    rewrite /= last_map /=.
    destruct (last e1 p1) as [[l L] ?] eqn:Hr.
    rewrite {}Hr /=.
    apply/eqP => ?. subst l. by rewrite L in El.
  - destruct p1.
    + move: target_1 => /eqP.
      by rewrite sub_val_eq.
    + move: source_1 => /eqP.
      by rewrite sub_val_eq eq_sym.
  - rewrite disjoint_cons disjoint_nil andb_true_r !map_cat !mem_cat
      !negb_orb !andb_true_r /= left_e -!map_comp.
    repeat (apply/andP; split).
    + apply/mapP. move=> [[[a A] c] /= _ a_eq].
      move: A. rewrite in_set => /andP[SA TA].
      destruct c.
      * refine (disjointE Dvl _ SA). by rewrite -a_eq in_set.
      * refine (disjointE Dvl _ TA). by rewrite -a_eq in_set.
    + apply/eqP => v_eq_se.
      refine (disjointE Dvl _ Se). by rewrite -v_eq_se in_set.
    + apply/mapP. move=> [[[a A] c] /= _ a_eq].
      move: A. rewrite in_set => /andP[SA TA].
      destruct c.
      * refine (disjointE Dvr _ SA). by rewrite -a_eq in_set.
      * refine (disjointE Dvr _ TA). by rewrite -a_eq in_set.
    + assert (Hr : v = target (right_tens V)) by by rewrite right_e.
      rewrite {1}Hr.
      apply/eqP. apply nesym, no_selfloop.
  - assert (source (left_tens V) != target (right_tens V)).
    { assert (Hr : v = (target (left_tens V))) by by rewrite left_e.
      rewrite right_e {2}Hr.
      apply/eqP. apply no_selfloop. }
    destruct p1 as [ | e1 p1]; simpl.
    + by rewrite map_cat last_cat in_cons in_nil orb_false_r /= eq_sym.
    + by rewrite map_cat last_cat in_cons in_nil orb_false_r /= eq_sym map_cat last_cat.
  - destruct p1 as [ | [[e1 E1] b1] p1]; simpl.
    + apply/eqP. by apply nesym.
    + apply/eqP => ?. subst e1.
      clear - E1 Dvl. contradict E1. apply /negP.
      rewrite in_set negb_andb left_e.
      apply/orP. right. apply/negP => F.
      refine (disjointE Dvl _ F). by rewrite in_set.
Qed.

Lemma splitting_iso_e_fwd_last_case (e : edge G) :
  e \notin edge_set Sl -> e \notin edge_set Sr -> e <> left_tens V -> e <> right_tens V ->
  ccl_tens V = e.
Proof.
  move=> El Er Eleft Eright.
  assert (Se : source e \in setT) by by rewrite in_set.
  assert (Te : target e \in setT) by by rewrite in_set.
  move: Te Se.
  rewrite -(cover_partition partition_terminal) /cover !bigcup_setU !bigcup_set1 !in_set.
  rewrite orbC => /orP[/eqP-Te _ | ].
  { transitivity (edge_of_concl vlabel_target_ccl); [ | symmetry]; by apply concl_eq. }
  rewrite orbC => /orP[/eqP-Te | ].
  { assert (EV : e \in edges_at_in v) by by rewrite !in_set Te.
    contradict EV. apply /negP.
    rewrite (right_set (or_introl V)) !in_set. splitb; by apply /eqP. }
  move=> Te Se. move: Se Te.
  rewrite orbC => /orP[/eqP-Se | ].
  { contradict Se. apply no_source_c, vlabel_target_ccl. }
  rewrite orbC => /orP[/eqP-Se _ | ].
  { symmetry. by apply ccl_eq. }
  move=> /orP[Se | Se] /orP[Te | Te]; exfalso.
  - contradict El. apply /negP/negPn. by rewrite in_set Se Te.
  - by apply (@no_crossing e true).
  - by apply (@no_crossing e false).
  - contradict Er. apply /negP/negPn. by rewrite in_set Se Te.
Qed.

Lemma out_Sl u b e :
  u \in Sl -> e \in edges_at_outin b u -> e \notin edge_set Sl -> e = left_tens V /\ ~~ b.
Proof.
  destruct partition_disjoint as [Dlr [Dvl [_ [Dcl _]]]].
  move=> U Ein E.
  revert Ein. rewrite !in_set => /eqP-?. subst u.
  enough (EV : e \in edges_at v).
  { revert EV. rewrite edges_at_eq => /orP[/eqP-EV | /eqP-EV].
    - exfalso.
      assert (e = ccl_tens V) by by apply ccl_eq.
      subst e. clear EV E.
      destruct b.
      + refine (disjointE Dcl _ U). by rewrite !in_set.
      + refine (disjointE Dvl _ U). by rewrite ccl_e !in_set.
    - destruct b.
      + exfalso. refine (disjointE Dvl _ U). by rewrite EV !in_set.
      + assert (EV' : e \in [set left_tens V; right_tens V]) by by rewrite -right_set in_set EV.
        revert EV'. rewrite {EV} !in_set; introb.
        exfalso. exact (disjointE Dlr U source_right_Sr). }
  apply /negPn/negP. rewrite edges_at_eq => /norP[SEV TEV].
  enough (F : ccl_tens V = e).
  { subst e. contradict SEV. apply /negP/negPn/eqP.
    by rewrite ccl_e. }
  apply splitting_iso_e_fwd_last_case.
  - assumption.
  - rewrite !in_set negb_andb.
    enough (U' : endpoint b e \notin Sr)
      by by destruct b; rewrite U' // orb_true_r.
    apply /negP => F.
    exact (disjointE Dlr U F).
  - move => ?. subst e. by rewrite left_e eq_refl in TEV.
  - move => ?. subst e. by rewrite right_e eq_refl in TEV.
Qed.
Lemma out_Sr u b e :
  u \in Sr -> e \in edges_at_outin b u -> e \notin edge_set Sr -> e = right_tens V /\ ~~b.
Proof.
  destruct partition_disjoint as [Dlr [_ [Dvr [_ [Dcr _]]]]].
  move=> U Ein E.
  revert Ein. rewrite !in_set => /eqP-?. subst u.
  enough (EV : e \in edges_at v).
  { revert EV. rewrite edges_at_eq => /orP[/eqP-EV | /eqP-EV].
    - exfalso.
      assert (e = ccl_tens V) by by apply ccl_eq.
      subst e. clear EV E.
      destruct b.
      + refine (disjointE Dcr _ U). by rewrite !in_set.
      + refine (disjointE Dvr _ U). by rewrite ccl_e !in_set.
    - destruct b.
      + exfalso. refine (disjointE Dvr _ U). by rewrite EV !in_set.
      + assert (EV' : e \in [set left_tens V; right_tens V]) by by rewrite -right_set in_set EV.
        revert EV'. rewrite {EV} !in_set; introb.
        exfalso. exact (disjointE Dlr source_left_Sl U). }
  apply /negPn/negP. rewrite edges_at_eq => /norP[SEV TEV].
  enough (F : ccl_tens V = e).
  { subst e. contradict SEV. apply /negP/negPn/eqP.
    by rewrite ccl_e. }
  apply splitting_iso_e_fwd_last_case.
  - rewrite !in_set negb_andb.
    enough (U' : endpoint b e \notin Sl)
      by by destruct b; rewrite U' // orb_true_r.
    apply /negP => F.
    exact (disjointE Dlr F U).
  - assumption.
  - move => ?. subst e. by rewrite left_e eq_refl in TEV.
  - move => ?. subst e. by rewrite right_e eq_refl in TEV.
Qed.

Lemma edge_to_Gl_inj b u : u \in Sl -> {in edges_at_outin b u &, injective edge_to_Gl}.
Proof.
  intros U e f Ein Fin.
  unfold edge_to_Gl.
  case: {-}_ /boolP => [E | E]; case: {-}_ /boolP => [F | F] //.
  - intro H. by inversion H.
  - intros _.
    transitivity (left_tens V); [ | symmetry].
    + by apply (out_Sl U Ein).
    + by apply (out_Sl U Fin).
Qed.
Lemma edge_to_Gr_inj b u : u \in Sr -> {in edges_at_outin b u &, injective edge_to_Gr}.
Proof.
  intros U e f Ein Fin.
  unfold edge_to_Gr.
  case: {-}_ /boolP => [E | E]; case: {-}_ /boolP => [F | F] //.
  - intro H. by inversion H.
  - intros _.
    transitivity (right_tens V); [ | symmetry].
    + by apply (out_Sr U Ein).
    + by apply (out_Sr U Fin).
Qed.

Lemma Gl_edges_at_outin b u U :
  edges_at_outin b (inl (Sub u U : induced Sl) : Gl) =
  [set edge_to_Gl e | e in edges_at_outin b u].
Proof.
  apply /setP => e. rewrite !in_set. symmetry.
  destruct e as [[[e Ein] | []] | ]; simpl.
  - cbn. rewrite !SubK.
    apply /imsetP. case: ifP => [E | /negP/negP-E].
    + exists e; first by rewrite !in_set.
      unfold edge_to_Gl. case: {-}_ /boolP => [E' | E']; first by cbnb.
      by rewrite Ein in E'.
    + move => [a Ain].
      unfold edge_to_Gl. case: {-}_ /boolP => [A | //].
      cbnb. intros ?. subst a.
      contradict Ain. apply /negP.
      by rewrite !in_set.
  - apply /imsetP. case: ifP => [E | /negP/negP-E].
    + destruct b; first by by [].
      revert E. cbnb => /eqP-?. subst u.
      exists (left_tens V); first by rewrite !in_set.
      unfold edge_to_Gl. case: {-}_ /boolP => [E' | //].
      exfalso. revert E'. rewrite in_set left_e => /andP[_ VF].
      destruct partition_disjoint as [_ [D _]].
      refine (disjointE D _ VF). by rewrite in_set.
    + move => [a Ain].
      unfold edge_to_Gl. case: {-}_ /boolP => [// | A] _.
      destruct (out_Sl U Ain A) as [? B].
      subst a. destruct b; try by by []. clear B.
      contradict E. apply /negP/negPn. cbnb.
      revert Ain. by rewrite in_set => ->.
Qed.
Lemma Gr_edges_at_outin b u U :
  edges_at_outin b (inl (Sub u U : induced Sr) : Gr) =
  [set edge_to_Gr e | e in edges_at_outin b u].
Proof.
  apply /setP => e. rewrite !in_set. symmetry.
  destruct e as [[[e Ein] | []] | ]; simpl.
  - cbn. rewrite !SubK.
    apply /imsetP. case: ifP => [E | /negP/negP-E].
    + exists e; first by rewrite !in_set.
      unfold edge_to_Gr. case: {-}_ /boolP => [E' | E']; first by cbnb.
      by rewrite Ein in E'.
    + move => [a Ain].
      unfold edge_to_Gr. case: {-}_ /boolP => [A | //].
      cbnb. intros ?. subst a.
      contradict Ain. apply /negP.
      by rewrite !in_set.
  - apply /imsetP. case: ifP => [E | /negP/negP-E].
    + destruct b; first by by [].
      revert E. cbnb => /eqP-?. subst u.
      exists (right_tens V); first by rewrite !in_set.
      unfold edge_to_Gr. case: {-}_ /boolP => [E' | //].
      exfalso. revert E'. rewrite in_set right_e => /andP[_ VF].
      destruct partition_disjoint as [_ [_ [D _]]].
      refine (disjointE D _ VF). by rewrite in_set.
    + move => [a Ain].
      unfold edge_to_Gr. case: {-}_ /boolP => [// | A] _.
      destruct (out_Sr U Ain A) as [? B].
      subst a. destruct b; try by by []. clear B.
      contradict E. apply /negP/negPn. cbnb.
      revert Ain. by rewrite in_set => ->.
Qed.

Lemma edge_to_Gl_flabel e u b : u \in Sl -> e \in edges_at_outin b u -> flabel (edge_to_Gl e) = flabel e.
Proof.
  intros U Ein.
  unfold edge_to_Gl. case: {-}_ /boolP => [// | E] /=.
  destruct (out_Sl U Ein E) as [? B]. subst e. by destruct b.
Qed.
Lemma edge_to_Gr_flabel e u b : u \in Sr -> e \in edges_at_outin b u -> flabel (edge_to_Gr e) = flabel e.
Proof.
  intros U Ein.
  unfold edge_to_Gr. case: {-}_ /boolP => [// | E] /=.
  destruct (out_Sr U Ein E) as [? B]. subst e. by destruct b.
Qed.

Lemma edge_to_Gl_llabel e u b : u \in Sl -> e \in edges_at_outin b u -> llabel (edge_to_Gl e) = llabel e.
Proof.
  intros U Ein.
  unfold edge_to_Gl. case: {-}_ /boolP => [// | E] /=.
  destruct (out_Sl U Ein E) as [? B]. subst e. destruct b; try by by []. clear B.
  by rewrite left_l.
Qed.

(* Main difference between Gl and Gr : we change llabel of right_tens V *)
Lemma edge_to_Gr_llabel e u b : u \in Sr -> e \in edges_at_outin b u ->
  e <> right_tens V -> llabel (edge_to_Gr e) = llabel e.
Proof.
  intros U Ein Er.
  unfold edge_to_Gr. case: {-}_ /boolP => [// | E] /=.
  contradict Er. by destruct (out_Sr U Ein E).
Qed.

Lemma Gl_p_deg : proper_degree Gl.
Proof.
  intros b u.
  destruct u as [[u U] | []]; simpl.
  - by rewrite -p_deg -(card_in_imset (edge_to_Gl_inj U)) Gl_edges_at_outin.
  - destruct b; simpl.
    + enough (Hr : edges_at_in (inr tt : Gl) = [set None]) by by rewrite Hr cards1.
      apply /setP => e. rewrite !in_set. by destruct e as [[[e E] | []] | ].
    + enough (Hr : edges_at_out (inr tt : Gl) = set0) by by rewrite Hr cards0.
      apply /setP => e. rewrite !in_set. by destruct e as [[[e E] | []] | ].
Qed.
Lemma Gr_p_deg : proper_degree Gr.
Proof.
  intros b u.
  destruct u as [[u U] | []]; simpl.
  - by rewrite -p_deg -(card_in_imset (edge_to_Gr_inj U)) Gr_edges_at_outin.
  - destruct b; simpl.
    + enough (Hr : edges_at_in (inr tt : Gr) = [set None]) by by rewrite Hr cards1.
      apply /setP => e. rewrite !in_set. by destruct e as [[[e E] | []] | ].
    + enough (Hr : edges_at_out (inr tt : Gr) = set0) by by rewrite Hr cards0.
      apply /setP => e. rewrite !in_set. by destruct e as [[[e E] | []] | ].
Qed.

Lemma Gl_p_ax_cut : proper_ax_cut Gl.
Proof.
  intros b [[u Uin] | ] U; simpl in *; last first.
  { by destruct b. }
  destruct (p_ax_cut U) as [el [er [El [Er LR]]]].
  exists (edge_to_Gl el), (edge_to_Gl er).
  rewrite Gl_edges_at_outin. repeat split.
  - by apply imset_f.
  - by apply imset_f.
  - by rewrite (edge_to_Gl_flabel Uin El) (edge_to_Gl_flabel Uin Er).
Qed.
Lemma Gr_p_ax_cut : proper_ax_cut Gr.
Proof.
  intros b [[u Uin] | ] U; simpl in *; last first.
  { by destruct b. }
  destruct (p_ax_cut U) as [el [er [El [Er LR]]]].
  exists (edge_to_Gr el), (edge_to_Gr er).
  rewrite Gr_edges_at_outin. repeat split.
  - by apply imset_f.
  - by apply imset_f.
  - by rewrite (edge_to_Gr_flabel Uin El) (edge_to_Gr_flabel Uin Er).
Qed.

Lemma Gl_p_tens_parr : proper_tens_parr Gl.
Proof.
  intros b [[u Uin] | ] U; simpl in *; last first.
  { by destruct b. }
  destruct (p_tens_parr U) as [el [er [ec [El [Ll [Er [Lr [Ec F]]]]]]]].
  exists (edge_to_Gl el), (edge_to_Gl er), (edge_to_Gl ec).
  rewrite !Gl_edges_at_outin. repeat split.
  - by apply imset_f.
  - by rewrite (edge_to_Gl_llabel Uin El).
  - by apply imset_f.
  - by rewrite (edge_to_Gl_llabel Uin Er).
  - by apply imset_f.
  - by rewrite (edge_to_Gl_flabel Uin El) (edge_to_Gl_flabel Uin Er) (edge_to_Gl_flabel Uin Ec).
Qed.
Lemma Gr_p_tens_parr : proper_tens_parr Gr.
Proof.
  intros b [[u Uin] | ] U; simpl in *; last first.
  { by destruct b. }
  destruct (p_tens_parr U) as [el [er [ec [El [Ll [Er [Lr [Ec F]]]]]]]].
  exists (edge_to_Gr el), (edge_to_Gr er), (edge_to_Gr ec).
  rewrite !Gr_edges_at_outin. repeat split.
  - by apply imset_f.
  - rewrite (edge_to_Gr_llabel Uin El) //.
    intros ?. subst el.
    destruct partition_disjoint as [_ [_ [Dvr _]]].
    refine (disjointE Dvr _ Uin).
    revert El. by rewrite !in_set right_e => /eqP-->.
  - by apply imset_f.
  - rewrite (edge_to_Gr_llabel Uin Er) //.
    intros ?. subst er.
    destruct partition_disjoint as [_ [_ [Dvr _]]].
    refine (disjointE Dvr _ Uin).
    revert Er. by rewrite !in_set right_e => /eqP-->.
  - by apply imset_f.
  - by rewrite (edge_to_Gr_flabel Uin El) (edge_to_Gr_flabel Uin Er) (edge_to_Gr_flabel Uin Ec).
Qed.

Lemma Gl_p_noleft : proper_noleft Gl.
Proof.
  move => [[[e E] | []] | ] //=.
  intro Ve. by assert (H := p_noleft Ve).
Qed.
Lemma Gr_p_noleft : proper_noleft Gr.
Proof.
  move => [[[e E] | []] | ] //=.
  intro Ve. by assert (H := p_noleft Ve).
Qed.

Lemma Gl_p_order : proper_order Gl_graph_data.
Proof.
  split.
  - move => [[[e E] | []] | ] //=.
    apply (iff_stepl (A := e \in order G)); [ | by apply iff_sym, p_order].
    rewrite in_cons /=.
    induction (order G) as [ | a l IH]; trivial.
    rewrite in_cons /= mem_cat.
    destruct (eq_comparable e a) as [? | AE].
    + subst a. rewrite eq_refl /=.
      case: {-}_ /boolP => [E' | E'].
      * rewrite in_cons. cbnb. by rewrite eq_refl.
      * by rewrite E in E'.
    + replace (e == a) with false by (symmetry; by apply /eqP).
      simpl. case: {-}_ /boolP => [E' | E'].
      * rewrite in_cons in_nil. cbnb.
        replace (e == a) with false by (symmetry; by apply /eqP).
        simpl. exact IH.
      * rewrite in_nil /=. exact IH.
  - simpl. splitb.
    + induction (order G); trivial. simpl.
      case: {-}_ /boolP => ?; rewrite mem_cat ?in_cons in_nil //=.
    + destruct (p_order G) as [_ U].
      revert U. induction (order G) as [ | e o IH]; trivial.
      rewrite /= cat_uniq => /andP[E O].
      rewrite (IH O) andb_true_r {IH O}.
      case: {-}_ /boolP => Ein /=; rewrite has_sym //= orb_false_r.
      induction o as [ | a o IH]; trivial.
      revert E. rewrite in_cons /= => /norP[EA E].
      rewrite mem_cat negb_orb IH // andb_true_r.
      case: {-}_ /boolP => ?; by rewrite ?in_cons in_nil ?orb_false_r.
Qed.
Lemma Gr_p_order : proper_order Gr_graph_data.
Proof.
  split.
  - move => [[[e E] | []] | ] //=.
    apply (iff_stepl (A := e \in order G)); [ | by apply iff_sym, p_order].
    rewrite in_cons /=.
    induction (order G) as [ | a l IH]; trivial.
    rewrite in_cons /= mem_cat.
    destruct (eq_comparable e a) as [? | AE].
    + subst a. rewrite eq_refl /=.
      case: {-}_ /boolP => [E' | E'].
      * rewrite in_cons. cbnb. by rewrite eq_refl.
      * by rewrite E in E'.
    + replace (e == a) with false by (symmetry; by apply /eqP).
      simpl. case: {-}_ /boolP => [E' | E'].
      * rewrite in_cons in_nil. cbnb.
        replace (e == a) with false by (symmetry; by apply /eqP).
        simpl. exact IH.
      * rewrite in_nil /=. exact IH.
  - simpl. splitb.
    + induction (order G); trivial. simpl.
      case: {-}_ /boolP => ?; rewrite mem_cat ?in_cons in_nil //=.
    + destruct (p_order G) as [_ U].
      revert U. induction (order G) as [ | e o IH]; trivial.
      rewrite /= cat_uniq => /andP[E O].
      rewrite (IH O) andb_true_r {IH O}.
      case: {-}_ /boolP => Ein /=; rewrite has_sym //= orb_false_r.
      induction o as [ | a o IH]; trivial.
      revert E. rewrite in_cons /= => /norP[EA E].
      rewrite mem_cat negb_orb IH // andb_true_r.
      case: {-}_ /boolP => ?; by rewrite ?in_cons in_nil ?orb_false_r.
Qed.

Definition Gl_ps : proof_structure := {|
  graph_data_of := Gl_graph_data;
  p_deg := Gl_p_deg;
  p_ax_cut := Gl_p_ax_cut;
  p_tens_parr := Gl_p_tens_parr;
  p_noleft := Gl_p_noleft;
  p_order := Gl_p_order;
  |}.
Definition Gr_ps : proof_structure := {|
  graph_data_of := Gr_graph_data;
  p_deg := Gr_p_deg;
  p_ax_cut := Gr_p_ax_cut;
  p_tens_parr := Gr_p_tens_parr;
  p_noleft := Gr_p_noleft;
  p_order := Gr_p_order;
  |}.

Lemma Gl_p_correct : mll_def.correct Gl.
Proof.
  destruct (correct_to_weak (p_correct G)).
  apply add_concl_correct. split.
  - by apply uacyclic_induced.
  - exact uconnected_Sl.
Qed.
Lemma Gr_p_correct : mll_def.correct Gr.
Proof.
  destruct (correct_to_weak (p_correct G)).
  apply add_concl_correct. split.
  - by apply uacyclic_induced.
  - exact uconnected_Sr.
Qed.

Definition Gl_pn : proof_net := {|
  ps_of := Gl_ps;
  p_correct := Gl_p_correct;
  |}.
Definition Gr_pn : proof_net := {|
  ps_of := Gr_ps;
  p_correct := Gr_p_correct;
  |}.

Lemma splitting_iso_v_fwd_helper1 u : inl (inl (inl u)) \in [set: add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None)]
  :\ inl (target (inl None : edge (union_ps Gl_ps Gr_ps))) :\ inl (target (inr None : edge (union_ps Gl_ps Gr_ps))).
Proof. by rewrite !in_set. Qed.
Lemma splitting_iso_v_fwd_helper2 u : inl (inr (inl u)) \in [set: add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None)]
  :\ inl (target (inl None : edge (union_ps Gl_ps Gr_ps))) :\ inl (target (inr None : edge (union_ps Gl_ps Gr_ps))).
Proof. by rewrite !in_set. Qed.
Lemma splitting_iso_v_fwd_helper3 : inr (inl tt) \in [set: add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None)]
  :\ inl (target (inl None : edge (union_ps Gl_ps Gr_ps))) :\ inl (target (inr None : edge (union_ps Gl_ps Gr_ps))).
Proof. by rewrite !in_set. Qed.
Lemma splitting_iso_v_fwd_helper4 : inr (inr tt) \in [set: add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None)]
  :\ inl (target (inl None : edge (union_ps Gl_ps Gr_ps))) :\ inl (target (inr None : edge (union_ps Gl_ps Gr_ps))).
Proof. by rewrite !in_set. Qed.
Definition splitting_iso_v_fwd (u : G) : add_node_ps_tens Gl_ps Gr_ps :=
  if @boolP (u \in Sl) is AltTrue Ul then
    Sub (inl (inl (inl (Sub u Ul : induced Sl)))) (splitting_iso_v_fwd_helper1 (Sub u Ul : induced Sl))
  else if @boolP (u \in Sr) is AltTrue Ur then
    Sub (inl (inr (inl (Sub u Ur : induced Sr)))) (splitting_iso_v_fwd_helper2 (Sub u Ur : induced Sr))
  else if u == v then
    Sub (inr (inl tt)) splitting_iso_v_fwd_helper3
  else (* u == target (ccl_tens V) *)
    Sub (inr (inr tt)) splitting_iso_v_fwd_helper4.
(* TODO giving the type induced X speed the compilation by a factor ~10 *)

Lemma splitting_iso_v_fwd_last_case (u : G) :
  u \notin Sl -> u \notin Sr -> u != v -> u == target (ccl_tens V).
Proof.
  intros Ul Ur UV.
  assert (U : u \in setT) by by rewrite in_set.
  revert U.
  rewrite -(cover_partition partition_terminal) /cover !bigcup_setU !bigcup_set1 !in_set.
  move => /orP[/orP[/orP[U | U] | U] | //].
  - by rewrite U in Ul.
  - by rewrite U in Ur.
  - by rewrite U in UV.
Qed.

Definition splitting_iso_v_bwd (u : add_node_ps_tens Gl_ps Gr_ps) : G :=
  match u with
  | exist (inl (inl (inl (exist u _)))) _ => u                   (* Vertex of Sl *)
  | exist (inl (inl (inr tt)))          _ => v                   (* Contradictory case: this is the left conclusion we add then remove *)
  | exist (inl (inr (inl (exist u _)))) _ => u                   (* Vertex of Sr *)
  | exist (inl (inr (inr tt)))          _ => v                   (* Contradictory case: this is the right conclusion we add then remove *)
  | exist (inr (inl tt))                _ => v                   (* Vertex replacing v *)
  | exist (inr (inr tt))                _ => target (ccl_tens V) (* Last concl added *)
  end.

Lemma splitting_iso_v_bijK : cancel splitting_iso_v_bwd splitting_iso_v_fwd.
Proof.
  destruct partition_disjoint as [Dlr [Dvl [Dvr [Dcl [Dcr _]]]]].
  intros [[[[[u Ul] | []] | [[u Ur] | []]] | [[] | []]] U]; rewrite /= /splitting_iso_v_fwd.
  - case: {-}_ /boolP => [Ul' | Ul']; first by cbnb.
    exfalso. clear -Ul Ul'. contradict Ul'. by apply /negP/negPn.
  - exfalso. contradict U. by rewrite !in_set.
  - case: {-}_ /boolP => [Ul' | Ul'].
    { exfalso. exact (disjointE Dlr Ul' Ur). }
    case: {-}_ /boolP => [Ur' | Ur']; first by cbnb.
    exfalso. clear -Ur Ur'. contradict Ur'. by apply /negP/negPn.
  - exfalso. contradict U. by rewrite !in_set.
  - case: {-}_ /boolP => [Ul' | Ul'].
    { exfalso. refine (disjointE Dvl _ Ul'). by rewrite in_set. }
    case: {-}_ /boolP => [Ur' | Ur']; last by (rewrite eq_refl; cbnb).
    exfalso. refine (disjointE Dvr _ Ur'). by rewrite in_set.
  - case: {-}_ /boolP => [Ul' | Ul'].
    { exfalso. refine (disjointE Dcl _ Ul'). by rewrite in_set. }
    case: {-}_ /boolP => [Ur' | Ur'].
    { exfalso. refine (disjointE Dcr _ Ur'). by rewrite in_set. }
    enough ((target (ccl_tens V) == v) = false) as -> by cbnb.
    apply /eqP. rewrite -{2}(ccl_e (or_introl V)). apply nesym, no_selfloop.
Qed.

Lemma splitting_iso_v_bijK' : cancel splitting_iso_v_fwd splitting_iso_v_bwd.
Proof.
  intro u.
  unfold splitting_iso_v_fwd.
  case: {-}_ /boolP => [// | Ul].
  case: {-}_ /boolP => [// | Ur].
  case: ifP => [/eqP-? // | /eqP/eqP-UV] /=.
  symmetry. apply /eqP. by apply splitting_iso_v_fwd_last_case.
Qed.

Definition splitting_iso_v := {|
  bijK:= splitting_iso_v_bijK;
  bijK':= splitting_iso_v_bijK';
  |}.

Definition splitting_iso_e_bwd (e : edge (add_node_ps_tens Gl_ps Gr_ps)) : edge G :=
  match e with
  | exist (Some (Some (inl (inl (Some (inl (exist e _))))))) _ => e                (* Edge of Sl *)
  | exist (Some (Some (inl (inl (Some (inr e))))))           _ => match e with end
  | exist (Some (Some (inl (inl None))))                     _ => ccl_tens V       (* Contradictory case: this is the left conclusion we add then remove *)
  | exist (Some (Some (inl (inr (Some (inl (exist e _))))))) _ => e                (* Edge of Sr *)
  | exist (Some (Some (inl (inr (Some (inr e))))))           _ => match e with end
  | exist (Some (Some (inl (inr None))))                     _ => ccl_tens V       (* Contradictory case: this is the right conclusion we add then remove *)
  | exist (Some (Some (inr (Some (inl e)))))                 _ => match e with end
  | exist (Some (Some (inr (Some (inr e)))))                 _ => match e with end
  | exist (Some (Some (inr None)))                           _ => ccl_tens V
  | exist (Some None)                                        _ => left_tens V
  | exist None                                               _ => right_tens V
  end.

Lemma splitting_iso_e_fwd_helper1 e : Some (Some (inl (inl (Some (inl e)))))
  \in edge_set ([set: add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None)]
  :\ inl (target (inl None : edge (union_ps Gl_ps Gr_ps))) :\ inl (target (inr None : edge (union_ps Gl_ps Gr_ps)))).
Proof. by rewrite !in_set. Qed.
Lemma splitting_iso_e_fwd_helper2 e : Some (Some (inl (inr (Some (inl e)))))
  \in edge_set ([set: add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None)]
  :\ inl (target (inl None : edge (union_ps Gl_ps Gr_ps))) :\ inl (target (inr None : edge (union_ps Gl_ps Gr_ps)))).
Proof. by rewrite !in_set. Qed.
Lemma splitting_iso_e_fwd_helper3 : Some None
  \in edge_set ([set: add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None)]
  :\ inl (target (inl None : edge (union_ps Gl_ps Gr_ps))) :\ inl (target (inr None : edge (union_ps Gl_ps Gr_ps)))).
Proof. by rewrite !in_set. Qed.
Lemma splitting_iso_e_fwd_helper4 : None
  \in edge_set ([set: add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None)]
  :\ inl (target (inl None : edge (union_ps Gl_ps Gr_ps))) :\ inl (target (inr None : edge (union_ps Gl_ps Gr_ps)))).
Proof. by rewrite !in_set. Qed.
Lemma splitting_iso_e_fwd_helper5 : Some (Some (inr None))
  \in edge_set ([set: add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None)]
  :\ inl (target (inl None : edge (union_ps Gl_ps Gr_ps))) :\ inl (target (inr None : edge (union_ps Gl_ps Gr_ps)))).
Proof. by rewrite !in_set. Qed.
Definition splitting_iso_e_fwd (e : edge G) : edge (add_node_ps_tens Gl_ps Gr_ps) :=
  if @boolP (e \in edge_set Sl) is AltTrue El then
    Sub (Some (Some (inl (inl (Some (inl (Sub e El : edge (induced Sl))))))))
    (splitting_iso_e_fwd_helper1 (Sub e El : edge (induced Sl)))
  else if @boolP (e \in edge_set Sr) is AltTrue Er then
    Sub (Some (Some (inl (inr (Some (inl (Sub e Er : edge (induced Sr))))))))
    (splitting_iso_e_fwd_helper2 (Sub e Er : edge (induced Sr)))
  else if e == left_tens V then
    Sub (Some None) splitting_iso_e_fwd_helper3
  else if e == right_tens V then
    Sub None splitting_iso_e_fwd_helper4
  else (* e == ccl_tens V *)
    Sub (Some (Some (inr None))) splitting_iso_e_fwd_helper5.

(* Coercion uedge_of_edge {Lv Le : Type} {G' : graph Lv Le} (e : edge G') : edge G' * bool :=
  forward e. *)
(* TODO replace upath_of_path? /!\ non uniform *)

Lemma splitting_iso_e_bijK : cancel splitting_iso_e_bwd splitting_iso_e_fwd.
Proof.
  destruct partition_disjoint as [Dlr [Dvl [Dvr [Dcl [Dcr _]]]]].
  intros [[[[[[[[e El] | []] | ] | [[[e Er] | []] | ]] | [[[] | []] | ]] | ] | ] E];
  rewrite /= /splitting_iso_e_fwd.
  - case: {-}_ /boolP => [El' | El']; first by cbnb.
    exfalso. clear -El El'. contradict El'. by apply /negP/negPn.
  - exfalso. contradict E. by rewrite !in_set.
  - case: {-}_ /boolP => [El' | El'].
    { exfalso. clear E.
      revert El' Er. rewrite !in_set => /andP[El' _] /andP[Er _].
      exact (disjointE Dlr El' Er). }
    case: {-}_ /boolP => [Er' | Er']; first by cbnb.
    exfalso. clear -Er Er'. contradict Er'. by apply /negP/negPn.
  - exfalso. contradict E. by rewrite !in_set.
  - case: {-}_ /boolP => [El' | El'].
    { exfalso. clear E.
      revert El'. rewrite !in_set ccl_e => /andP[El' _].
      refine (disjointE Dvl _ El'). by rewrite in_set. }
    case: {-}_ /boolP => [Er' | Er'].
    { exfalso. clear E.
      revert Er'. rewrite !in_set ccl_e => /andP[Er' _].
      refine (disjointE Dvr _ Er'). by rewrite in_set. }
    assert ((ccl_tens V == left_tens V) = false) as ->.
    { apply /eqP => Eq.
      assert (F := @no_selfloop _ _ (ccl_tens V)). contradict F.
      by rewrite ccl_e Eq left_e. }
    enough ((ccl_tens V == right_tens V) = false) as -> by cbnb.
    apply /eqP => Eq.
    assert (F := @no_selfloop _ _ (ccl_tens V)). contradict F.
    by rewrite ccl_e Eq right_e.
  - case: {-}_ /boolP => [El' | El'].
    { exfalso. clear E.
      revert El'. rewrite !in_set left_e => /andP[_ El'].
      refine (disjointE Dvl _ El'). by rewrite in_set. }
    case: {-}_ /boolP => [Er' | Er'].
    { exfalso. clear E.
      revert Er'. rewrite !in_set left_e => /andP[_ Er'].
      refine (disjointE Dvr _ Er'). by rewrite in_set. }
    rewrite eq_refl. cbnb.
  - case: {-}_ /boolP => [El' | El'].
    { exfalso. clear E.
      revert El'. rewrite !in_set right_e => /andP[_ El'].
      refine (disjointE Dvl _ El'). by rewrite in_set. }
    case: {-}_ /boolP => [Er' | Er'].
    { exfalso. clear E.
      revert Er'. rewrite !in_set right_e => /andP[_ Er'].
      refine (disjointE Dvr _ Er'). by rewrite in_set. }
    assert ((right_tens V == left_tens V) = false) as ->.
    { apply /eqP. apply nesym, left_neq_right. }
    rewrite eq_refl. cbnb.
Qed. (* TODO Too long *)

Lemma splitting_iso_e_bijK' : cancel splitting_iso_e_fwd splitting_iso_e_bwd.
Proof.
  intro e.
  unfold splitting_iso_e_fwd.
  case: {-}_ /boolP => [// | El].
  case: {-}_ /boolP => [// | Er].
  case_if.
  by apply splitting_iso_e_fwd_last_case.
Qed.

Definition splitting_iso_e := {|
  bijK:= splitting_iso_e_bijK;
  bijK':= splitting_iso_e_bijK';
  |}.

Lemma splitting_iso_ihom : is_ihom splitting_iso_v splitting_iso_e pred0.
Proof.
  split.
  - intros [[[[[[[[e El] | []] | ] | [[[e Er] | []] | ]] | [[[] | []] | ]] | ] | ] E] [];
    try by []; rewrite /= ?left_e ?right_e ?ccl_e //.
    all: contradict E; by rewrite !in_set.
  - intros [[[[[u Ul] | []] | [[u Ur] | []]] | [[] | []]] U]; try by [].
    + exfalso. contradict U. apply /negP.
      by rewrite !in_set.
    + exfalso. contradict U. apply /negP.
      by rewrite !in_set.
    + simpl. clear U. apply vlabel_target_ccl.
  - intros [[[[[[[[e El] | []] | ] | [[[e Er] | []] | ]] | [[[] | []] | ]] | ] | ] E];
    try by []; simpl.
    + exfalso. contradict E. by rewrite !in_set.
    + exfalso. contradict E. by rewrite !in_set.
    + rewrite elabel_eq.
      destruct (p_tens_parr_bis G) as [VE _]. revert VE => /(_ _ V)->.
      enough (llabel (ccl_tens V)) as -> by by [].
      apply p_noleft. clear E. rewrite vlabel_target_ccl. auto.
    + by rewrite elabel_eq left_l.
    + rewrite elabel_eq.
      enough (llabel (right_tens V) = false) as -> by by [].
      apply /negP/negP. apply right_l.
Qed.

Definition splitting_iso := {| iso_ihom := splitting_iso_ihom |}.

Lemma splitting_terminal_tens_is_sequentializing : sequentializing v.
Proof.
  rewrite /sequentializing V. exists (Gl_pn, Gr_pn).
  symmetry. exact splitting_iso.
Qed.

End Splitting_is_sequentializing.

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

(* TODO define generally and use this : + warning *)(*
Coercion supath_to_Supath {s t : G} {p : upath} : supath switching s t p -> Supath switching s t :=
  (fun S => {| upvalK := S |}). *)

(* TODO use tens case to conclude on cut ? is it enough to just rework the proof above, mainly replacing
vlabel v = ⊗ with vlabel v = ⊗ \/ vlabel v = cut? do a subst a cut by a tens and prove respect correctness? *)

End Splitting_tens.

End Atoms.
