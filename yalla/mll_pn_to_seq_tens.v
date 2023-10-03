(* Sequentialisation - A terminal splitting ⊗ is sequentializing *)

From Coq Require Import Bool.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export mll_prelim graph_more upath supath mll_def mll_basic mll_correct mll_seq_to_pn
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


Section Splitting_tens.
Context {G : proof_net} {v : G} (vlabel_v : vlabel v = ⊗)
  (splitting_v : splitting bridge v) (terminal_v : terminal v).

(* Edges incident to v *)
Local Notation left_v := (left_tens vlabel_v).
Local Notation right_v := (right_tens vlabel_v).
Local Notation ccl_v := (ccl_tens vlabel_v).

(* Conclusion vertex below v *)
Local Notation concl_v := (target ccl_v).

Lemma vlabel_concl_v :
  vlabel concl_v = c.
Proof. apply (terminal_source terminal_v), ccl_e. Qed.

(* The vertices making the subgraph sent to the left of v are those
   of the connected component containing left of v when removing v. *)
Definition Sl : {set G} := [set u | [exists p : Simple_upath G,
  (upath_source v (val p) == v) && (upath_target v (val p) == u) &&
  (head (forward left_v) (val p) == backward left_v)]].

(* The vertices making the subgraph sent to the right of v are those
   not sent with left of v, including eventual vertices not in the
   connected component of v. *)
Definition Sr : {set G} := setT :\: Sl :\ v :\ concl_v.

(* We begin by proving properties of these sets:
   Sl contains the source of left_v,
   Sr contains the source of right_v and
   Sl, Sr, v, concl_v are a partition of the vertices. *)

Lemma source_left_Sl : source left_v \in Sl.
Proof.
  rewrite in_set.
  apply/existsP. exists (Sub _ (simple_upath_edge (backward left_v))).
  by rewrite /= left_e !eq_refl.
Qed.

Lemma source_right_Sr : source right_v \in Sr.
Proof.
  rewrite !in_set !in_set1 andb_true_r.
  assert (source_r_neq_v : source right_v != v).
  { apply/eqP.
    rewrite -{2}(right_e (or_introl vlabel_v)).
    apply no_selfloop. }
  assert (source_l_neq_v : source left_v != v).
  { apply/eqP.
    rewrite -{2}(left_e (or_introl vlabel_v)).
    apply no_selfloop. }
  assert (left_right : left_v != right_v).
  { apply/eqP. apply left_neq_right. }
  rewrite source_r_neq_v /=.
  apply/andP; split.
  { apply/eqP. apply no_source_c, vlabel_concl_v. }
  apply/existsPn. move=> [[ | [e b] p] simple_p] /=.
  { cbn. by rewrite !andb_false_r. }
  rewrite !negb_andb.
  case/boolP: (endpoint (~~ b) e == v) => //= source_e.
  case/boolP: (last (endpoint b e) [seq utarget e | e <- p] == source (right_v))
    => //= target_p.
  case/boolP: (e == left_tens vlabel_v) => //= /eqP-?. subst e.
  destruct b; first by []. clear source_e.
  enough (simple_pe : simple_upath (rcons (backward (left_v) :: p) (forward (right_v)))).
  { move: splitting_v => /forallP/(_ (Sub _ simple_pe)) /=.
    by rewrite /bridge left_e map_rcons !last_rcons right_e eq_refl vlabel_v. }
  rewrite simple_upath_rcons simple_p /= left_e right_e (eqP target_p) eq_refl in_cons negb_orb
    !(eq_sym v) source_r_neq_v source_l_neq_v !andb_true_r /=.
  apply/andP; split.
  - destruct p as [ | p e _] using last_ind.
    { by rewrite eq_sym (negPf left_right). }
    move: simple_p target_p.
    rewrite simple_upath_cons simple_upath_rcons !map_rcons !last_rcons in_rcons negb_orb left_e.
    move=> /andP[/andP[_ /andP[source_e _]] _] target_e.
    destruct e as [e b].
    apply/eqP => /= ?. subst e.
    move: target_e source_e.
    destruct b; rewrite /= right_e ?eq_refl //.
    by move=> ->.
  - move: simple_p. rewrite simple_upath_cons /= left_e.
    move=> /andP[/andP[/andP[/andP[simple_p _] _] v_notin_sources_p] _].
    apply/negP => v_in_targets_p.
    assert (F : v \in upath_target v p :: [seq usource _e | _e <- p])
      by by rewrite (mem_usource_utarget_uwalk (uwalk_of_simple_upath simple_p v))
      in_cons v_in_targets_p orb_true_r.
    move: F. rewrite in_cons (negPf v_notin_sources_p) orb_false_r /=.
    rewrite (@last_eq _ _ (source (left_tens vlabel_v))); last by destruct p.
    by rewrite (eqP target_p) eq_sym (negPf source_r_neq_v).
Qed.

Lemma disjoint_Sl_Sr : [disjoint Sl & Sr].
Proof.
  apply/disjointP => u.
  rewrite !in_set andb_true_r => ->. by rewrite !andb_false_r.
Qed.

Lemma disjoint_v_Sl : [disjoint [set v] & Sl].
Proof.
  apply/disjointP => u.
  rewrite in_set in_set1 => /eqP-? /existsP[p /andP[/andP[source_p target_p] head_p]]. subst u.
  move: splitting_v => /forallP/(_ p)/implyP/(_ source_p)/implyP/(_ target_p).
  clear source_p.
  destruct p as [[ | e p] simple_p].
  { contradict head_p. apply/negP. cbn. by rewrite andb_false_r. }
  move: head_p => /= /eqP-?. subst e.
  by rewrite /bridge left_e vlabel_v andb_false_r.
Qed.

Lemma disjoint_v_Sr : [disjoint [set v] & Sr].
Proof.
  apply/disjointP => u.
  rewrite !in_set in_set1 => ->. by rewrite andb_false_r.
Qed.

Lemma disjoint_concl_v_Sl : [disjoint [set concl_v] & Sl].
Proof.
  apply/disjointP => u.
  rewrite !in_set in_set1 => /eqP-? /existsP[p /andP[/andP[_ target_p] head_p]]. subst u.
  destruct p as [[ | e p] simple_p].
  { contradict head_p. apply/negP. cbn. by rewrite andb_false_r. }
  move: head_p => /= /eqP-?. subst e.
  destruct p as [ | p [e b] _] using last_ind.
  - move: target_p => /= /eqP-target_p.
    contradict target_p.
    apply no_source_c, vlabel_concl_v.
  - move: target_p. rewrite /= map_rcons last_rcons /= => /eqP-target_p.
    destruct b; last first.
    { contradict target_p.
      apply no_source_c, vlabel_concl_v. }
    assert (H := one_target_c vlabel_concl_v target_p). subst e. clear target_p.
    apply uniq_usource_simple_upath in simple_p.
    contradict simple_p. apply/negP.
    by rewrite /= map_rcons rcons_uniq in_rcons left_e ccl_e eq_refl.
Qed.

Lemma disjoint_concl_v_Sr : [disjoint [set concl_v] & Sr].
Proof.
  apply/disjointP => u.
  by rewrite !in_set in_set1 => ->.
Qed.

Lemma cover_vertices :
  [set: G] = v |: (concl_v |: Sl :|: Sr).
Proof.
  rewrite /Sr !setDDl -[in LHS](setID [set: G] (Sl :|: [set v; concl_v])) setTI !setUA. f_equal.
  rewrite [in RHS]setUAC. f_equal.
  by rewrite setUC.
Qed.

Lemma no_crossing (e : edge G * bool) :
  usource e \in Sl -> utarget e \in Sr -> False.
Proof.
  rewrite !in_set !in_set1 /= andb_true_r.
  move=> /existsP[[p simple_p] /= /andP[/andP[source_p target_p] head_p]].
  move=> /andP[_ /andP[be_neq_v /existsPn-H]].
  enough (simple_p' : simple_upath (rcons p e)).
  { move: H => /(_ (Sub _ simple_p')).
    rewrite /= !map_rcons !head_rcons last_rcons /= eq_refl.
    destruct p as [ | a p].
    - move: head_p. cbn. by rewrite andb_false_r.
    - simpl in *. by rewrite source_p head_p. }
  rewrite simple_upath_rcons simple_p /=.
  destruct p as [ | a p]; first by rewrite /= eq_refl.
  simpl in *.
  move: head_p => /eqP-?. subst a. clear source_p.
  rewrite (eqP target_p) eq_refl andb_true_r in_cons /= left_e negb_orb.
  destruct e as [e b].
  repeat (apply/andP; split).
  - destruct p as [ | p [ae ab] _] using last_ind.
    + simpl in *.
      apply/eqP => ?. subst e.
      destruct b.
      * contradict be_neq_v. apply/negP/negPn/eqP.
        by rewrite left_e.
      * contradict target_p. apply/negP/eqP.
        apply no_selfloop.
    + rewrite last_rcons /=.
      apply/eqP => ?. subst ae.
      move: target_p. rewrite map_rcons last_rcons /= => /eqP-target_p.
      assert (ab = ~~ b).
      { destruct ab, b; try by [].
        - contradict target_p. apply nesym, no_selfloop.
        - contradict target_p. apply no_selfloop. }
      subst ab. clear target_p.
      move: simple_p. rewrite -rcons_cons simple_upath_rcons /= negb_involutive.
      move=> /andP[/andP[/andP[/andP[simple_p _] last_p_eq] _] _].
      move: H => /(_ (Sub _ simple_p)) /=.
      by rewrite left_e -(eqP last_p_eq) !eq_refl.
  - apply/eqP => be_eq.
    move: H => /(_ (Sub _ (simple_upath_edge (backward left_v)))).
    by rewrite /= left_e be_eq !eq_refl.
  - apply/mapP. move=> [a a_in_p be_eq].
    move: a_in_p. rewrite in_elt_sub => /existsP[n /eqP-p_eq].
    rewrite p_eq -cat_rcons -cat_cons in simple_p.
    apply simple_upath_prefix in simple_p.
    move: H => /(_ (Sub _ simple_p)) /=.
    by rewrite left_e map_rcons last_rcons be_eq !eq_refl.
  - apply/eqP => nbe_eq_v.
    move: splitting_v => /forallP/(_ (Sub _ simple_p)).
    by rewrite /bridge /= left_e (eqP target_p) -nbe_eq_v eq_refl vlabel_v andb_false_r.
Qed.

Lemma splitting_iso_e_fwd_last_case (e : edge G) :
  e \notin edge_set Sl -> e \notin edge_set Sr -> e <> left_v -> e <> right_v ->
  ccl_v = e.
Proof.
  move=> El Er Eleft Eright.
  assert (Se : source e \in setT) by by rewrite in_set.
  assert (Te : target e \in setT) by by rewrite in_set.
  move: Te Se.
  rewrite cover_vertices 3!in_set !in_set1 -!orbA.
  move=> /orP[/eqP-Te _ | ].
  { contradict Eright. by apply right_eq2. }
  move=> /orP[/eqP-Te _ | Te].
  { symmetry. exact: (one_target_c vlabel_concl_v Te). }
  rewrite 3!in_set !in_set1 -!orbA.
  move=> /orP[/eqP-Se | ].
  { symmetry. by apply ccl_eq. }
  move=> /orP[/eqP-Se | Se].
  { contradict Se. apply no_source_c, vlabel_concl_v. }
  exfalso.
  move: Te Se => /orP[Te | Te] /orP[Se | Se].
  - contradict El. apply/negP/negPn. by rewrite in_set Se Te.
  - by apply (@no_crossing (backward e)).
  - by apply (@no_crossing (forward e)).
  - contradict Er. apply/negP/negPn. by rewrite in_set Se Te.
Qed.

Lemma out_Sl u b e :
  u \in Sl -> e \in edges_at_outin b u -> e \notin edge_set Sl -> e = left_v /\ ~~ b.
Proof.
  move=> U Ein E.
  move: Ein. rewrite !in_set => /eqP-?. subst u.
  enough (EV : e \in edges_at v).
  { move: EV. rewrite edges_at_eq => /orP[/eqP-EV | /eqP-EV].
    - exfalso.
      assert (e = ccl_v) by by apply ccl_eq. subst e. clear EV E.
      destruct b.
      + refine (disjointE disjoint_concl_v_Sl _ U). by rewrite in_set1.
      + refine (disjointE disjoint_v_Sl _ U). by rewrite ccl_e in_set1.
    - destruct b.
      + exfalso. refine (disjointE disjoint_v_Sl _ U). by rewrite EV in_set1.
      + assert (EV' : e \in [set left_v; right_v]) by by rewrite -right_set in_set EV.
        move: EV'. rewrite {EV} !in_set !in_set1 => /orP[/eqP--> // | /eqP-?]. subst e.
        exfalso. exact (disjointE disjoint_Sl_Sr U source_right_Sr). }
  apply/negPn/negP. rewrite edges_at_eq => /norP[SEV TEV].
  enough (ccl_v = e).
  { subst e. contradict SEV. apply/negP/negPn/eqP.
    by rewrite ccl_e. }
  apply splitting_iso_e_fwd_last_case; trivial.
  - rewrite in_set negb_andb.
    case/boolP: (endpoint b e \notin Sr).
    + destruct b => -> //. by rewrite orb_true_r.
    + move=> /negPn-F.
      exfalso. exact (disjointE disjoint_Sl_Sr U F).
  - move=> ?. subst e. by rewrite left_e eq_refl in TEV.
  - move=> ?. subst e. by rewrite right_e eq_refl in TEV.
Qed.
Lemma out_Sr u b e :
  u \in Sr -> e \in edges_at_outin b u -> e \notin edge_set Sr -> e = right_v /\ ~~b.
Proof.
  move=> U Ein E.
  move: Ein. rewrite !in_set => /eqP-?. subst u.
  enough (EV : e \in edges_at v).
  { move: EV. rewrite edges_at_eq => /orP[/eqP-EV | /eqP-EV].
    - exfalso.
      assert (e = ccl_v) by by apply ccl_eq. subst e. clear EV E.
      destruct b.
      + refine (disjointE disjoint_concl_v_Sr _ U). by rewrite in_set1.
      + refine (disjointE disjoint_v_Sr _ U). by rewrite ccl_e in_set1.
    - destruct b.
      + exfalso. refine (disjointE disjoint_v_Sr _ U). by rewrite EV in_set1.
      + assert (EV' : e \in [set left_v; right_v]) by by rewrite -right_set in_set EV.
        move: EV'. rewrite {EV} !in_set !in_set1 => /orP[/eqP-? | /eqP--> //]. subst e.
        exfalso. exact (disjointE disjoint_Sl_Sr source_left_Sl U). }
  apply/negPn/negP. rewrite edges_at_eq => /norP[SEV TEV].
  enough (ccl_v = e).
  { subst e. contradict SEV. apply/negP/negPn/eqP.
    by rewrite ccl_e. }
  apply splitting_iso_e_fwd_last_case; trivial.
  - rewrite in_set negb_andb.
    case/boolP: (endpoint b e \notin Sl).
    + destruct b => -> //. by rewrite orb_true_r.
    + move=> /negPn-F.
      exfalso. exact (disjointE disjoint_Sl_Sr F U).
  - move=> ?. subst e. by rewrite left_e eq_refl in TEV.
  - move=> ?. subst e. by rewrite right_e eq_refl in TEV.
Qed.

(* We now prove that v is sequentializing, using these properties. *)

(* Our two connected components, with a conclusion replacing v *)
Definition Gl : base_graph := @add_concl_graph _ (induced Sl)
  (Sub (source left_v) source_left_Sl) c (flabel left_v).
Definition Gr : base_graph := @add_concl_graph _ (induced Sr)
  (Sub (source right_v) source_right_Sr) c (flabel right_v).
(* TODO : in all this part we do things in double, try to merge them when possible:
define Glr b = if b then Gl else Gr, and prove this is a proof structure *)

(* Function sending a list of edges of G to a list of edges of Gl, forgetting those in Gr *)
Fixpoint order_to_Gl (l : seq (edge G)) : seq (edge Gl) :=
  match l with
  | [::] => [::]
  | e :: l' => (if @boolP (e \in edge_set Sl) is AltTrue E then [:: Some (inl (Sub e E))] else [::]) ++ order_to_Gl l'
  end.
(* Function sending a list of edges of G to a list of edges of Gr, forgetting those in Gl *)
Fixpoint order_to_Gr (l : seq (edge G)) : seq (edge Gr) :=
  match l with
  | [::] => [::]
  | e :: l' => (if @boolP (e \in edge_set Sr) is AltTrue E then [:: Some (inl (Sub e E))] else [::]) ++ order_to_Gr l'
  end.

Definition Gl_graph_data : graph_data := {|
  graph_of := Gl;
  order := None :: order_to_Gl (order G);
  |}.
Definition Gr_graph_data : graph_data := {|
  graph_of := Gr;
  order := None :: order_to_Gr (order G);
  |}.

(* TODO would be good to have G iso add_tens H1 H2 with G proof net implies
H1 and H2 proof nets, so that we do not have to prove it here *)
(* We first show that Gl and Gr are proof structures. *)

Definition edge_to_Gl (e : edge G) : edge Gl :=
  if @boolP (e \in edge_set Sl) is AltTrue E then Some (inl (Sub e E)) else None.
Definition edge_to_Gr (e : edge G) : edge Gr :=
  if @boolP (e \in edge_set Sr) is AltTrue E then Some (inl (Sub e E)) else None.

Lemma edge_to_Gl_inj b u : u \in Sl -> {in edges_at_outin b u &, injective edge_to_Gl}.
Proof.
  move=> U e f Ein Fin.
  rewrite /edge_to_Gl. case: {-}_ /boolP; case: {-}_ /boolP => F E //.
  - move=> H. by inversion H.
  - move=> _.
    by destruct (out_Sl U Ein E) as [-> _], (out_Sl U Fin F) as [-> _].
Qed.
Lemma edge_to_Gr_inj b u : u \in Sr -> {in edges_at_outin b u &, injective edge_to_Gr}.
Proof.
  move=> U e f Ein Fin.
  rewrite /edge_to_Gr. case: {-}_ /boolP; case: {-}_ /boolP => F E //.
  - move=> H. by inversion H.
  - move=> _.
    by destruct (out_Sr U Ein E) as [-> _], (out_Sr U Fin F) as [-> _].
Qed.

Lemma Gl_edges_at_outin b u U :
  edges_at_outin b (inl (Sub u U : induced Sl) : Gl) =
  [set edge_to_Gl e | e in edges_at_outin b u].
Proof.
  apply/setP => e. rewrite in_set. symmetry.
  destruct e as [[[e Ein] | []] | ]; simpl.
  - cbn. simpl.
    apply/imsetP. case: ifP => [E | /negP/negP-E].
    + exists e; first by rewrite !in_set.
      rewrite /edge_to_Gl. case: {-}_ /boolP => E'; first by cbnb.
      by rewrite Ein in E'.
    + move=> [a Ain].
      rewrite /edge_to_Gl. case: {-}_ /boolP => [A | //].
      move=> a_eq. inversion a_eq. clear a_eq. subst a.
      contradict Ain. apply/negP.
      by rewrite !in_set.
  - apply/imsetP. case: ifP => [E | /negP/negP-E].
    + destruct b; first by [].
      move: E => /eqP-E. inversion E. clear E. subst u.
      exists (left_v); first by rewrite !in_set.
      rewrite /edge_to_Gl. case: {-}_ /boolP => [E' | //].
      exfalso. move: E'. rewrite in_set left_e => /andP[_ VF].
      refine (disjointE disjoint_v_Sl _ VF). by rewrite in_set1.
    + move=> [a Ain].
      rewrite /edge_to_Gl. case: {-}_ /boolP => [// | A] _.
      elim: (out_Sl U Ain A) => ? /negPf-?. subst a b.
      contradict E. apply/negP/negPn. cbnb.
      move: Ain. by rewrite in_set => ->.
Qed.
Lemma Gr_edges_at_outin b u U :
  edges_at_outin b (inl (Sub u U : induced Sr) : Gr) =
  [set edge_to_Gr e | e in edges_at_outin b u].
Proof.
  apply/setP => e. rewrite !in_set. symmetry.
  destruct e as [[[e Ein] | []] | ]; simpl.
  - cbn. simpl.
    apply/imsetP. case: ifP => [E | /negP/negP-E].
    + exists e; first by rewrite !in_set.
      rewrite /edge_to_Gr. case: {-}_ /boolP => E'; first by cbnb.
      by rewrite Ein in E'.
    + move=> [a Ain].
      rewrite /edge_to_Gr. case: {-}_ /boolP => [A | //].
      move=> a_eq. inversion a_eq. clear a_eq. subst a.
      contradict Ain. apply/negP.
      by rewrite !in_set.
  - apply/imsetP. case: ifP => [E | /negP/negP-E].
    + destruct b; first by [].
      move: E => /eqP-E. inversion E. clear E. subst u.
      exists (right_v); first by rewrite !in_set.
      rewrite /edge_to_Gr. case: {-}_ /boolP => [E' | //].
      exfalso. move: E'. rewrite in_set right_e => /andP[_ VF].
      refine (disjointE disjoint_v_Sr _ VF). by rewrite in_set1.
    + move=> [a Ain].
      rewrite /edge_to_Gr. case: {-}_ /boolP => [// | A] _.
      elim: (out_Sr U Ain A) => ? /negPf-?. subst a b.
      contradict E. apply/negP/negPn. cbnb.
      move: Ain. by rewrite in_set => ->.
Qed.

Lemma edge_to_Gl_flabel e u b :
  u \in Sl -> e \in edges_at_outin b u -> flabel (edge_to_Gl e) = flabel e.
Proof.
  move=> U Ein.
  rewrite /edge_to_Gl. case: {-}_ /boolP => [// | E] /=.
  elim: (out_Sl U Ein E) => ? _. by subst e.
Qed.
Lemma edge_to_Gr_flabel e u b :
  u \in Sr -> e \in edges_at_outin b u -> flabel (edge_to_Gr e) = flabel e.
Proof.
  move=> U Ein.
  rewrite /edge_to_Gr. case: {-}_ /boolP => [// | E] /=.
  elim: (out_Sr U Ein E) => ? _. by subst e.
Qed.

Lemma edge_to_Gl_llabel e u b :
  u \in Sl -> e \in edges_at_outin b u -> llabel (edge_to_Gl e) = llabel e.
Proof.
  move=> U Ein.
  rewrite /edge_to_Gl. case: {-}_ /boolP => [// | E] /=.
  elim: (out_Sl U Ein E) => ? /negPf-?. subst e b.
  by rewrite left_l.
Qed.
(* Difference between Gl and Gr : we change llabel of right_v *)
Lemma edge_to_Gr_llabel e u b :
  u \in Sr -> e \in edges_at_outin b u ->
  e <> right_v -> llabel (edge_to_Gr e) = llabel e.
Proof.
  move=> U Ein Er.
  rewrite /edge_to_Gr. case: {-}_ /boolP => [// | E] /=.
  contradict Er. by destruct (out_Sr U Ein E) as [? _].
Qed.

Lemma Gl_p_deg : proper_degree Gl.
Proof.
  move=> b [[u U] | []] /=.
  - by rewrite -p_deg -(card_in_imset (edge_to_Gl_inj U)) Gl_edges_at_outin.
  - destruct b; simpl.
    + enough (Hr : edges_at_in (inr tt : Gl) = [set None]) by by rewrite Hr cards1.
      apply/setP => e. rewrite !in_set in_set1. by destruct e as [[[e E] | []] | ].
    + enough (Hr : edges_at_out (inr tt : Gl) = set0) by by rewrite Hr cards0.
      apply/setP => e. rewrite !in_set. by destruct e as [[[e E] | []] | ].
Qed.
Lemma Gr_p_deg : proper_degree Gr.
Proof.
  move=> b [[u U] | []] /=.
  - by rewrite -p_deg -(card_in_imset (edge_to_Gr_inj U)) Gr_edges_at_outin.
  - destruct b; simpl.
    + enough (Hr : edges_at_in (inr tt : Gr) = [set None]) by by rewrite Hr cards1.
      apply/setP => e. rewrite !in_set in_set1. by destruct e as [[[e E] | []] | ].
    + enough (Hr : edges_at_out (inr tt : Gr) = set0) by by rewrite Hr cards0.
      apply/setP => e. rewrite !in_set. by destruct e as [[[e E] | []] | ].
Qed.

Lemma Gl_p_ax_cut : proper_ax_cut Gl.
Proof.
  move=> b [[u Uin] | ] /= U; last by destruct b.
  destruct (p_ax_cut U) as [el [er [El [Er LR]]]].
  exists (edge_to_Gl el), (edge_to_Gl er).
  by rewrite Gl_edges_at_outin (edge_to_Gl_flabel Uin El) (edge_to_Gl_flabel Uin Er) LR !imset_f.
Qed.
Lemma Gr_p_ax_cut : proper_ax_cut Gr.
Proof.
  move=> b [[u Uin] | ] /= U; last by destruct b.
  destruct (p_ax_cut U) as [el [er [El [Er LR]]]].
  exists (edge_to_Gr el), (edge_to_Gr er).
  by rewrite Gr_edges_at_outin (edge_to_Gr_flabel Uin El) (edge_to_Gr_flabel Uin Er) LR !imset_f.
Qed.

Lemma Gl_p_tens_parr : proper_tens_parr Gl.
Proof.
  move=> b [[u Uin] | ] /= U; last by destruct b.
  destruct (p_tens_parr U) as [el [er [ec [El [Ll [Er [Lr [Ec F]]]]]]]].
  exists (edge_to_Gl el), (edge_to_Gl er), (edge_to_Gl ec).
  by rewrite !Gl_edges_at_outin (edge_to_Gl_llabel Uin El) (edge_to_Gl_llabel Uin Er)
    (edge_to_Gl_flabel Uin El) (edge_to_Gl_flabel Uin Er) (edge_to_Gl_flabel Uin Ec) !imset_f.
Qed.
Lemma Gr_p_tens_parr : proper_tens_parr Gr.
Proof.
  move=> b [[u Uin] | ] /= U; last by destruct b.
  destruct (p_tens_parr U) as [el [er [ec [El [Ll [Er [Lr [Ec F]]]]]]]].
  exists (edge_to_Gr el), (edge_to_Gr er), (edge_to_Gr ec).
  rewrite !Gr_edges_at_outin (edge_to_Gr_flabel Uin El) (edge_to_Gr_flabel Uin Er) (edge_to_Gr_flabel Uin Ec)
    !imset_f //.
  repeat split; trivial.
  - rewrite (edge_to_Gr_llabel Uin El) //.
    move=> ?. subst el.
    refine (disjointE disjoint_v_Sr _ Uin).
    move: El. by rewrite !in_set in_set1 right_e => /eqP-->.
  - rewrite (edge_to_Gr_llabel Uin Er) //.
    move=> ?. subst er.
    refine (disjointE disjoint_v_Sr _ Uin).
    move: Er. by rewrite !in_set in_set1 right_e => /eqP-->.
Qed.

Lemma Gl_p_noleft : proper_noleft Gl.
Proof. move=> [[[e E] | []] | ] //= Ve. apply (p_noleft Ve). Qed.
Lemma Gr_p_noleft : proper_noleft Gr.
Proof. move=> [[[e E] | []] | ] //= Ve. apply (p_noleft Ve). Qed.

Lemma Gl_p_order_full : proper_order_full Gl_graph_data.
Proof.
  move=> [[[e E] | []] | ] //=.
  apply (iff_stepl (A := e \in order G)); [ | by apply iff_sym, p_order_full].
  rewrite in_cons /=.
  induction (order G) as [ | a l IH]; first by [].
  rewrite in_cons /= mem_cat.
  case/boolP: (e == a) => /= [/eqP-? | AE].
  - subst a.
    case: {-}_ /boolP => E'.
    + rewrite in_cons. cbnb. by rewrite eq_refl.
    + by rewrite E in E'.
  - case: {-}_ /boolP => E'.
    + rewrite in_cons in_nil. cbnb. rewrite (negPf AE) /=. exact IH.
    + rewrite in_nil /=. exact IH.
Qed.
Lemma Gr_p_order_full : proper_order_full Gr_graph_data.
Proof.
  move=> [[[e E] | []] | ] //=.
  apply (iff_stepl (A := e \in order G)); [ | by apply iff_sym, p_order_full].
  rewrite in_cons /=.
  induction (order G) as [ | a l IH]; first by [].
  rewrite in_cons /= mem_cat.
  case/boolP: (e == a) => /= [/eqP-? | AE].
  - subst a.
    case: {-}_ /boolP => E'.
    + rewrite in_cons. cbnb. by rewrite eq_refl.
    + by rewrite E in E'.
  - case: {-}_ /boolP => E'.
    + rewrite in_cons in_nil. cbnb. rewrite (negPf AE) /=. exact IH.
    + rewrite in_nil /=. exact IH.
Qed.

Lemma Gl_p_order_uniq : proper_order_uniq Gl_graph_data.
Proof.
  rewrite /proper_order_uniq /=. apply/andP. split.
  - induction (order G) => //=.
    by case: {-}_ /boolP => ?; rewrite mem_cat ?in_cons in_nil.
  - have := p_order_uniq G.
    rewrite /proper_order_uniq.
    induction (order G) as [ | e o IH]; first by [].
    rewrite /= cat_uniq => /andP[E O].
    rewrite (IH O) andb_true_r {IH O}.
    case: {-}_ /boolP => Ein /=; rewrite has_sym //= orb_false_r.
    induction o as [ | a o IH]; first by [].
    move: E. rewrite in_cons /= => /norP[EA E].
    rewrite mem_cat negb_orb {}IH // andb_true_r.
    case: {-}_ /boolP => ?; by rewrite ?in_cons in_nil ?orb_false_r.
Qed.
Lemma Gr_p_order_uniq : proper_order_uniq Gr_graph_data.
Proof.
  rewrite /proper_order_uniq /=. apply/andP. split.
  - induction (order G) => //=.
    by case: {-}_ /boolP => ?; rewrite mem_cat ?in_cons in_nil.
  - have := p_order_uniq G.
    rewrite /proper_order_uniq.
    induction (order G) as [ | e o IH]; first by [].
    rewrite /= cat_uniq => /andP[E O].
    rewrite (IH O) andb_true_r {IH O}.
    case: {-}_ /boolP => Ein /=; rewrite has_sym //= orb_false_r.
    induction o as [ | a o IH]; first by [].
    move: E. rewrite in_cons /= => /norP[EA E].
    rewrite mem_cat negb_orb {}IH // andb_true_r.
    case: {-}_ /boolP => ?; by rewrite ?in_cons in_nil ?orb_false_r.
Qed.

Definition Gl_ps : proof_structure := {|
  graph_data_of := Gl_graph_data;
  p_deg := Gl_p_deg;
  p_ax_cut := Gl_p_ax_cut;
  p_tens_parr := Gl_p_tens_parr;
  p_noleft := Gl_p_noleft;
  p_order_full := Gl_p_order_full;
  p_order_uniq := Gl_p_order_uniq;
  |}.
Definition Gr_ps : proof_structure := {|
  graph_data_of := Gr_graph_data;
  p_deg := Gr_p_deg;
  p_ax_cut := Gr_p_ax_cut;
  p_tens_parr := Gr_p_tens_parr;
  p_noleft := Gr_p_noleft;
  p_order_full := Gr_p_order_full;
  p_order_uniq := Gr_p_order_uniq;
  |}.

(* We now prove there is the wished isomorphism. *)

Definition splitting_iso_v_fwd_1 (u : G) : add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None) :=
  if @boolP (u \in Sl) is AltTrue Ul then
    inl (inl (inl (Sub u Ul : induced Sl)))
  else if @boolP (u \in Sr) is AltTrue Ur then
    inl (inr (inl (Sub u Ur : induced Sr)))
  else if u == v then
    inr (inl tt)
  else (* u == concl_v *)
    inr (inr tt).

Lemma splitting_iso_v_fwd_helper (u : G) :
  splitting_iso_v_fwd_1 u \in [set: add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None)]
  :\ inl (target (inl None : edge (union_ps Gl_ps Gr_ps))) :\ inl (target (inr None : edge (union_ps Gl_ps Gr_ps))).
Proof.
  rewrite !in_set !in_set1 /= /splitting_iso_v_fwd_1.
  case: {-}_ /boolP => [// | _]. case: {-}_ /boolP => [// | _]. by case: ifP.
Qed.

Definition splitting_iso_v_fwd (u : G) : add_node_ps_tens Gl_ps Gr_ps :=
  Sub (splitting_iso_v_fwd_1 u) (splitting_iso_v_fwd_helper u).

Lemma splitting_iso_v_fwd_last_case (u : G) :
  u \notin Sl -> u \notin Sr -> u != v -> u == concl_v.
Proof.
  move=> Ul Ur UV.
  assert (U : u \in setT) by by rewrite in_set.
  move: U. by rewrite cover_vertices 3!in_set !in_set1 (negPf Ul) (negPf Ur) (negPf UV) !orb_false_r.
Qed.

Definition splitting_iso_v_bwd (u : add_node_ps_tens Gl_ps Gr_ps) : G :=
  match val u with
  | inl (inl (inl (exist u _))) => u       (* Vertex of Sl *)
  | inl (inl (inr tt))          => v       (* Contradictory case: this is the left conclusion we add then remove *)
  | inl (inr (inl (exist u _))) => u       (* Vertex of Sr *)
  | inl (inr (inr tt))          => v       (* Contradictory case: this is the right conclusion we add then remove *)
  | inr (inl tt)                => v       (* Vertex replacing v *)
  | inr (inr tt)                => concl_v (* Last concl added *)
  end.

Lemma splitting_iso_v_bijK : cancel splitting_iso_v_bwd splitting_iso_v_fwd.
Proof.
  move=> [u U].
  apply val_inj.
  rewrite /splitting_iso_v_fwd /splitting_iso_v_bwd !SubK.
  rewrite !in_set !in_set1 /= in U.
  move: U => /andP[? /andP[? _]].
  destruct u as [[[[u Ul] | []] | [[u Ur] | []]] | [[] | []]];
  rewrite // /splitting_iso_v_fwd_1.
  - case: {-}_ /boolP => [? | Ul']; first by cbnb.
    exfalso. clear - Ul Ul'. by rewrite Ul in Ul'.
  - case: {-}_ /boolP => [Ul' | ?].
    { exfalso. exact (disjointE disjoint_Sl_Sr Ul' Ur). }
    case: {-}_ /boolP => [? | Ur']; first by cbnb.
    exfalso. clear - Ur Ur'. by rewrite Ur in Ur'.
  - case: {-}_ /boolP => [Ul' | ?].
    { exfalso. refine (disjointE disjoint_v_Sl _ Ul'). by rewrite in_set1. }
    case: {-}_ /boolP => [Ur' | ?]; last by (rewrite eq_refl; cbnb).
    exfalso. refine (disjointE disjoint_v_Sr _ Ur'). by rewrite in_set1.
  - case: {-}_ /boolP => [Ul' | ?].
    { exfalso. refine (disjointE disjoint_concl_v_Sl _ Ul'). by rewrite in_set1. }
    case: {-}_ /boolP => [Ur' | ?].
    { exfalso. refine (disjointE disjoint_concl_v_Sr _ Ur'). by rewrite in_set1. }
    case: ifP => [/eqP-F | //].
    contradict F. rewrite -{2}(ccl_e (or_introl vlabel_v)). apply nesym, no_selfloop.
Qed.

Lemma splitting_iso_v_bijK' : cancel splitting_iso_v_fwd splitting_iso_v_bwd.
Proof.
  move=> u.
  rewrite /splitting_iso_v_fwd /splitting_iso_v_bwd SubK /splitting_iso_v_fwd_1.
  case: {-}_ /boolP => [// | Ul]. case: {-}_ /boolP => [// | Ur].
  case: ifP => [/eqP--> // | /eqP/eqP-UV] /=.
  symmetry. apply/eqP. by apply splitting_iso_v_fwd_last_case.
Qed.

Definition splitting_iso_v := {|
  bijK:= splitting_iso_v_bijK;
  bijK':= splitting_iso_v_bijK';
  |}.

Definition splitting_iso_e_bwd (e : edge (add_node_ps_tens Gl_ps Gr_ps)) : edge G :=
  match val e with
  | Some (Some (inl (inl (Some (inl (exist e _))))))  => e                (* Edge of Sl *)
  | Some (Some (inl (inl (Some (inr e)))))            => match e with end
  | Some (Some (inl (inl None)))                      => ccl_v            (* Contradictory case: this is the left conclusion we add then remove *)
  | Some (Some (inl (inr (Some (inl (exist e _))))))  => e                (* Edge of Sr *)
  | Some (Some (inl (inr (Some (inr e)))))            => match e with end
  | Some (Some (inl (inr None)))                      => ccl_v            (* Contradictory case: this is the right conclusion we add then remove *)
  | Some (Some (inr (Some (inl e))))                  => match e with end
  | Some (Some (inr (Some (inr e))))                  => match e with end
  | Some (Some (inr None))                            => ccl_v
  | Some None                                         => left_v
  | None                                              => right_v
  end.

Definition splitting_iso_e_fwd_1 (e : edge G) : edge (add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None)) :=
  if @boolP (e \in edge_set Sl) is AltTrue El then
    Some (Some (inl (inl (Some (inl (Sub e El : edge (induced Sl)))) : edge (union_ps Gl_ps Gr_ps))))
  else if @boolP (e \in edge_set Sr) is AltTrue Er then
    Some (Some (inl (inr (Some (inl (Sub e Er : edge (induced Sr)))) : edge (union_ps Gl_ps Gr_ps))))
  else if e == left_v then
    Some None
  else if e == right_v then
    None
  else (* e == ccl_v *)
    Some (Some (inr None)).

Lemma splitting_iso_e_fwd_helper (e : edge G) :
  splitting_iso_e_fwd_1 e \in edge_set ([set: add_node_graph_1 tens_t (inl None : edge (union_ps Gl_ps Gr_ps)) (inr None)]
  :\ inl (target (inl None : edge (union_ps Gl_ps Gr_ps))) :\ inl (target (inr None : edge (union_ps Gl_ps Gr_ps)))).
Proof.
  rewrite !in_set !in_set1 /= /splitting_iso_e_fwd_1.
  case: {-}_ /boolP => [// | _]. case: {-}_ /boolP => [// | _]. by case: ifP; [ | case: ifP].
Qed.

Definition splitting_iso_e_fwd (e : edge G) : edge (add_node_ps_tens Gl_ps Gr_ps) :=
  Sub (splitting_iso_e_fwd_1 e) (splitting_iso_e_fwd_helper e).

Lemma splitting_iso_e_bijK : cancel splitting_iso_e_bwd splitting_iso_e_fwd.
Proof.
  move=> [e E].
  apply val_inj.
  rewrite /splitting_iso_e_fwd /splitting_iso_e_bwd !SubK.
  rewrite !in_set !in_set1 in E.
  move: E => /andP[/andP[? /andP[? _]] /andP[? /andP[? _]]].
  destruct e as [[[[[[[e El] | []] | ] | [[[e Er] | []] | ]] | [[[] | []] | ]] | ] | ];
  rewrite // /splitting_iso_e_fwd_1.
  - case: {-}_ /boolP => [? | El']; first by cbnb.
    exfalso. clear - El El'. by rewrite El in El'.
  - case: {-}_ /boolP => [El' | ?].
    { exfalso. clear - El' Er.
      move: El'. rewrite in_set => /andP[El' _].
      move: Er. rewrite in_set => /andP[Er _].
      exact (disjointE disjoint_Sl_Sr El' Er). }
    case: {-}_ /boolP => [? | Er']; first by cbnb.
    exfalso. clear - Er Er'. by rewrite Er in Er'.
  - case: {-}_ /boolP => [El' | ?].
    { exfalso.
      move: El'. rewrite in_set ccl_e => /andP[El' _].
      refine (disjointE disjoint_v_Sl _ El'). by rewrite in_set1. }
    case: {-}_ /boolP => [Er' | ?].
    { exfalso.
      move: Er'. rewrite in_set ccl_e => /andP[Er' _].
      refine (disjointE disjoint_v_Sr _ Er'). by rewrite in_set1. }
    repeat (case: ifP); last by done.
    + move=> /eqP-Eq.
      assert (F := @no_selfloop _ _ (ccl_v)). contradict F.
      by rewrite ccl_e Eq left_e.
    + move=> /eqP-Eq.
      assert (F := @no_selfloop _ _ (ccl_v)). contradict F.
      by rewrite ccl_e Eq right_e.
  - case: {-}_ /boolP => [El' | _].
    { exfalso.
      move: El'. rewrite in_set left_e => /andP[_ El'].
      refine (disjointE disjoint_v_Sl _ El'). by rewrite in_set1. }
    case: {-}_ /boolP => [Er' | _].
    { exfalso.
      move: Er'. rewrite in_set left_e => /andP[_ Er'].
      refine (disjointE disjoint_v_Sr _ Er'). by rewrite in_set1. }
    by rewrite eq_refl.
  - case: {-}_ /boolP => [El' | _].
    { exfalso.
      move: El'. rewrite in_set right_e => /andP[_ El'].
      refine (disjointE disjoint_v_Sl _ El'). by rewrite in_set1. }
    case: {-}_ /boolP => [Er' | _].
    { exfalso.
      move: Er'. rewrite in_set right_e => /andP[_ Er'].
      refine (disjointE disjoint_v_Sr _ Er'). by rewrite in_set1. }
    case: ifP; last by rewrite eq_refl.
    move=> /eqP-F. contradict F.
    apply nesym, left_neq_right.
Qed.

Lemma splitting_iso_e_bijK' : cancel splitting_iso_e_fwd splitting_iso_e_bwd.
Proof.
  move=> e.
  rewrite /splitting_iso_e_fwd /splitting_iso_e_bwd SubK /splitting_iso_e_fwd_1.
  case: {-}_ /boolP => [// | ?].
  case: {-}_ /boolP => [// | ?].
  case: ifP => [/eqP--> // | /eqP-?].
  case: ifP => [/eqP--> // | /eqP-?].
  by apply splitting_iso_e_fwd_last_case.
Qed.

Definition splitting_iso_e := {|
  bijK:= splitting_iso_e_bijK;
  bijK':= splitting_iso_e_bijK';
  |}.

Lemma splitting_iso_ihom : is_ihom splitting_iso_v splitting_iso_e pred0.
Proof.
  split.
  - move=> [e E] b.
    rewrite /splitting_iso_e /splitting_iso_e_bwd /splitting_iso_v /splitting_iso_v_bwd /=.
    rewrite !in_set !in_set1 in E.
    move: E => /andP[/andP[? /andP[? _]] /andP[? /andP[? _]]].
    by destruct e as [[[[[[[e El] | []] | ] | [[[e Er] | []] | ]] | [[[] | []] | ]] | ] | ];
      try by []; destruct b; rewrite //= ?left_e ?right_e ?ccl_e.
  - move=> [u U].
    rewrite /splitting_iso_v /splitting_iso_v_bwd /=.
    rewrite !in_set !in_set1 /= in U.
    move: U => /andP[? /andP[? _]].
    destruct u as [[[[u Ul] | []] | [[u Ur] | []]] | [[] | []]]; try by [].
    apply vlabel_concl_v.
  - move=> [e E].
    rewrite /splitting_iso_e /splitting_iso_e_bwd /=.
    rewrite !in_set !in_set1 in E.
    move: E => /andP[/andP[? /andP[? _]] /andP[? /andP[? _]]].
    destruct e as [[[[[[[e El] | []] | ] | [[[e Er] | []] | ]] | [[[] | []] | ]] | ] | ];
      try by [].
    + rewrite elabel_eq (p_tens_bis vlabel_v).
      enough (llabel (ccl_v)) as -> by by [].
      apply p_noleft. rewrite vlabel_concl_v. auto.
    + by rewrite elabel_eq left_l.
    + rewrite elabel_eq.
      enough (llabel (right_v) = false) as -> by by [].
      apply/negP/negP. apply right_l.
Qed.

Definition splitting_iso := {| iso_ihom := splitting_iso_ihom |}.

(* TODO use connectivity of the original graph to prove connectivity
of the new ones ; transform in acyc <-> acyc then equality of nb_connex *)
Lemma Gl_p_correct : mll_def.correct Gl.
Proof.
  eapply (add_node_tens_correct' _ (iso_correct splitting_iso (p_correct G))). Unshelve.
  by exists None, (order_to_Gl (order G)), None, (order_to_Gr (order G)).
(*   destruct (correct_to_weak (p_correct G)).
  apply add_concl_correct. split.
  - by apply uacyclic_induced.
  - exact uconnected_Sl. *)
Qed.
Lemma Gr_p_correct : mll_def.correct Gr.
Proof.
  eapply (add_node_tens_correct' _ (iso_correct splitting_iso (p_correct G))). Unshelve.
  by exists None, (order_to_Gl (order G)), None, (order_to_Gr (order G)).
(*   destruct (correct_to_weak (p_correct G)).
  apply add_concl_correct. split.
  - by apply uacyclic_induced.
  - exact uconnected_Sr. *)
Qed.

Definition Gl_pn : proof_net := {|
  ps_of := Gl_ps;
  p_correct := Gl_p_correct;
  |}.
Definition Gr_pn : proof_net := {|
  ps_of := Gr_ps;
  p_correct := Gr_p_correct;
  |}.

Lemma splitting_terminal_tens_is_sequentializing : sequentializing v.
Proof.
  rewrite /sequentializing vlabel_v. exists (Gl_pn, Gr_pn).
  symmetry. exact splitting_iso.
Qed.

End Splitting_tens.

(* TODO use tens case to conclude on cut ?
is it enough to just rework the proof above, mainly replacing
vlabel v = ⊗ with vlabel v = ⊗ \/ vlabel v = cut? *)

(* Coercion uedge_of_edge {Lv Le : Type} {G' : graph Lv Le} (e : edge G') : edge G' * bool :=
  forward e. *)
(* TODO replace upath_of_path? /!\ non uniform *)

End Atoms.
