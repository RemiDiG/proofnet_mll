(* Sequentialisation *)
(* From a Proof Net, return a LL proof of the same sequent *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export graph_more mll_prelim mll_def mll_basic mll_seq_to_pn.

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

Lemma supath_cons {Lv Le : Type} {G : graph Lv Le}
  {I : finType} (f : edge G -> option I) (s t : G) e (p : upath) :
  supath f s t (e :: p) =
  (supath f (utarget e) t p && (usource e == s) &&
  (f e.1 \notin [seq f a.1 | a <- p]) && (None != f e.1)).
Proof.
  rewrite /supath /= in_cons negb_orb.
  destruct (usource e == s); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (uwalk (utarget e) t p); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (uniq [seq f a.1 | a <- p]); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (None \notin [seq f a.1 | a <- p]) eqn:Hr; rewrite !Hr ?andb_false_r ?andb_true_r //=.
Qed. (* TODO in graph_more, and use it everywhere *)

Lemma supath_rcons {Lv Le : Type} {G : graph Lv Le}
  {I : finType} (f : edge G -> option I) (s t : G) e (p : upath) :
  supath f s t (rcons p e) =
  (supath f s (usource e) p && (utarget e == t) &&
  (f e.1 \notin [seq f a.1 | a <- p]) && (None != f e.1)).
Proof.
  rewrite /supath /= map_rcons in_rcons rcons_uniq negb_orb uwalk_rcons.
  destruct (utarget e == t); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (uwalk s (usource e) p); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (uniq [seq f a.1 | a <- p]); rewrite ?andb_false_r ?andb_true_r //=.
  destruct (None \notin [seq f a.1 | a <- p]) eqn:Hr; rewrite !Hr ?andb_false_r ?andb_true_r //=.
Qed. (* TODO in graph_more, and use it everywhere *)

Lemma supath_of_nil {Lv Le : Type} {G : graph Lv Le} {I : finType} (f : edge G -> option I)
  (s t : G) :
  supath f s t [::] -> s = t.
Proof. by rewrite /supath /= => /andP[/andP[/eqP--> _] _]. Qed. (* TODO in graph_more, and use it everywhere *)

Definition iso_to_isod (F G : proof_structure) (h : F ≃ G) :
  F ≃d perm_graph_data G (sequent_iso_perm h).
Proof. eexists; simpl. apply perm_of_sequent_iso_perm. Defined.

Lemma supath_from_induced {Lv Le : Type} {G : graph Lv Le} (S : {set G})
  {I J : finType} (f : edge G -> option I) (f' : edge (induced S) -> option J)
  s t (q : Supath f' s t) :
  (forall e (E : e \in edge_set S), None <> f' (Sub e E) -> None <> f e) ->
  (forall e a (E : e \in edge_set S) (A : a \in edge_set S),
    f e = f a -> f' (Sub e E) = f' (Sub a A)) ->
  supath f (val s) (val t) [seq (val a.1, a.2) | a <- upval q].
Proof.
  intros F0 F1.
  destruct q as [q Q]. revert s t Q.
  induction q as [ | ([a A], b) q IH] => /= s t Q.
  { apply (@supath_of_nil _ _ _ _ f') in Q. subst. apply supath_nilK. }
  rewrite supath_cons /= in Q. revert Q => /andP[/andP[/andP[Q /eqP-?] U] /eqP-N]. subst s. simpl.
  revert IH => /(_ _ _ Q)-IH. rewrite supath_cons IH. splitb.
  - clear - F1 U.
    apply /mapP. move => [c' /mapP[c Cin ?] Fc]. subst c'. simpl in Fc.
    contradict U. apply /negP/negPn/mapP.
    exists c; trivial. simpl.
    destruct c as [[? ?] ?]. by apply F1.
  - clear - F0 N.
    apply /eqP. apply (F0 _ _ N).
Qed.

Lemma induced_upath_inside {Lv Le : Type} {G : graph Lv Le} (S : {set G}) (q : @upath _ _ (induced S)) e :
  e \in [seq (val a.1, a.2) | a <- q] -> e.1 \in edge_set S.
Proof. move => /mapP[[[e' Ein] ?] ? ?]. by subst e. Qed.

Lemma supath_from_induced_switching (G : base_graph) (S : {set G}) s t (p : Supath (@switching _ (induced S)) s t) :
  supath (@switching _ G) (val s) (val t) [seq (val a.1, a.2) | a <- upval p].
Proof.
  apply (@supath_from_induced _ _ _ _ _ _ switching _ _ _ p).
  - intros ? ? _. case_if.
  - move => ? ? ? ? /eqP-F. apply /eqP. revert F. rewrite /switching /=. case_if.
Qed.

Lemma uacyclic_induced (G : base_graph) (S : {set G}) :
  uacyclic (@switching _ G) -> uacyclic (@switching _ (induced S)).
Proof.
  intros U ? p.
  specialize (U _ {| upvalK := supath_from_induced_switching p |}).
  destruct p as [p ?]. cbnb. by destruct p.
Qed.

Lemma supath_from_induced_switching_left (G : base_graph) (S : {set G}) s t
  (p : Supath (@switching_left _ (induced S)) s t) :
  supath (@switching_left _ G) (val s) (val t) [seq (val a.1, a.2) | a <- upval p].
Proof.
  apply supath_from_induced.
  - intros ? ?. unfold switching_left. case_if.
  - move => ? ? ? ? /eqP. unfold switching_left. case_if; cbnb.
Qed.

Lemma switching_left_induced_None_to (G : base_graph) (S : {set G}) e (E : e \in edge_set S) :
  None <> @switching_left _ G e -> None <> @switching_left _ (induced S) (Sub e E).
Proof. unfold switching_left. case_if. Qed.

Lemma switching_left_induced_eq_to (G : base_graph) (S : {set G}) e a (E : e \in edge_set S)
  (A : a \in edge_set S) :
  @switching_left _ (induced S) (Sub e E) = @switching_left _ (induced S) (Sub a A) ->
  switching_left e = switching_left a.
Proof. move => /eqP. unfold switching_left. case_if; simpl in *; by subst. Qed.

(* sequentialisation : fonction reliant regles à noeuds => nb cut + quels tens lies à des cut *)
(* seuentialisation sans coupure puis avec (+ de cas ou en remplacant par des tens) *)



Definition splitting (G : proof_net) (v : G) : Type :=
  match vlabel v with
  | ax => {A & G ≃ ax_pn A}
  | ⊗ => {'(G0, G1) : proof_net * proof_net & G ≃ add_node_ps_tens G0 G1}
  | ⅋ => {G0 : proof_net & G ≃ add_node_ps_parr G0}
  | cut => {'(G0, G1) : proof_net * proof_net & G ≃ add_node_ps_cut G0 G1}
  | c => void (* a conclusion node is never splitting *)
  end.

(* BEGIN TOO LONG
(** Base graph for removing a node *) (* TODO faire comme add_node des cas selon vlabel_v pour factoriser ? *)
(* Remove the node and its eventual conclusion *)
Definition rem_node_graph_1 {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :=
  induced (setT :\ v :\ target (ccl H)).

Lemma rem_node_sources_stay {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  source (left H) \in setT :\ v :\ target (ccl H) /\
  source (right H) \in setT :\ v :\ target (ccl H).
Proof.
  assert (C := @ps_acyclic _ G).
  rewrite !in_set. splitb; apply /eqP => F.
  - set p := left H :: ccl H :: nil.
    assert (P : walk (source (left H)) (source (left H)) p).
    { rewrite /= F ccl_e left_e. splitb. }
    specialize (C _ _ P).
    by contradict C.
  - assert (Eq : left H = ccl H) by by apply ccl_eq.
    assert (FF : source (left H) = target (left H)) by by rewrite left_e Eq ccl_e.
    contradict FF. apply no_selfloop.
  - set p := right H :: ccl H :: nil.
    assert (P : walk (source (right H)) (source (right H)) p).
    { rewrite /= F ccl_e right_e. splitb. }
    specialize (C _ _ P).
    by contradict C.
  - assert (Eq : right H = ccl H) by by apply ccl_eq.
    assert (FF : source (right H) = target (right H)) by by rewrite right_e Eq ccl_e.
    contradict FF. apply no_selfloop.
Qed.

(* Add two new conclusions *)
Definition rem_node_graph {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :=
  @add_concl_graph _
  (@add_concl_graph _ (rem_node_graph_1 H) (Sub (source (right H)) (proj2 (rem_node_sources_stay H))) c (flabel (right H)))
  (inl (Sub (source (left H)) (proj1 (rem_node_sources_stay H)))) c (flabel (left H)).
(* TODO faire pareil dans d'autres cas pour se passer de lemmas inutiles *)

Definition rem_node_transport {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
    edge G -> edge (rem_node_graph H) :=
    fun e => if @boolP _ is AltTrue p then Some (inl (Some (inl (Sub e p : edge (rem_node_graph_1 H)))))
    else if e == left H then None else Some (inl None).

Definition rem_node_order {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :=
  None :: (Some (inl None)) :: [seq rem_node_transport H x | x <- [seq x <- order G | x != ccl H]].

Definition rem_node_graph_data {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) := {|
  graph_of := rem_node_graph H;
  order := rem_node_order _;
  |}.

Lemma rem_node_removed {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  terminal v ->
  edge_set ([set: G] :\ v :\ target (ccl H)) = setT :\ left H :\ right H :\ ccl H.
Proof.
  rewrite terminal_tens_parr => /eqP-C.
  apply /setP => a.
  rewrite !in_set.
  destruct (eq_comparable a (ccl H)) as [? | Hc];
  [ | destruct (eq_comparable a (right H)) as [? | Hr]];
  [ | | destruct (eq_comparable a (left H))];
  try by (subst a; rewrite ?left_e ?right_e !eq_refl ?andb_false_r).
  assert (a != ccl H /\ a != right H /\ a != left H) as [-> [-> ->]]
    by by splitb; apply /eqP.
  splitb; apply /eqP.
  - by apply no_source_c.
  - intros ?. contradict Hc. by apply ccl_eq.
  - intros Ht. contradict Hc. by apply one_target_c.
  - intros ?. contradict Hr. by apply right_eq2.
Qed.

Definition rem_node_transport' {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  edge (rem_node_graph H) -> edge G :=
  fun e => match e with
  | Some (inl (Some (inl (exist a _)))) => a
  | Some (inl (Some (inr a))) => match a with end
  | Some (inl None) => right H
  | Some (inr a) => match a with end
  | None => left H
  end.

Lemma rem_node_transport'_inj {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  terminal v -> injective (@rem_node_transport' _ _ H).
Proof.
  move => T [[[[[e E] | []] | ]| []] | ] [[[[[a A] | []] | ]| []] | ];
  cbnb; introb; cbnb.
  all: try by (contradict E || contradict A); apply /negP; rewrite rem_node_removed // !in_set; caseb.
  - enough (right H <> left H) by by [].
    apply nesym, left_neq_right.
  - enough (left H <> right H) by by [].
    apply left_neq_right.
Qed.

(* pour ces 3 là : ça serait bien un lemme reliant les edges_at de G à ceux de rem_node *)
Lemma rem_node_transport_edges {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  terminal v ->
  forall u Hu b, edges_at_outin b u =
    [set rem_node_transport' a | a in edges_at_outin b (inl (inl (Sub u Hu)) : rem_node_graph H)].
Proof.
  move => T u Hu b. apply /setP => e.
  rewrite in_set.
  symmetry. destruct (eq_comparable u (endpoint b e)) as [? | Hc]; [subst u | ].
  - rewrite eq_refl.
    apply /imsetP.
    exists (rem_node_transport H e).
    + (* lemma *)
      rewrite in_set /rem_node_transport.
      case: {-}_ /boolP => In; cbnb; case_if; destruct b; cbnb.
      * contradict Hu; apply /negP. rewrite !in_set left_e. caseb.
      * (* lemma *)
        revert In. rewrite rem_node_removed // !in_set. introb.
        all: contradict Hu; apply /negP; rewrite !in_set ?left_e ?right_e; caseb.
      * revert In. rewrite rem_node_removed // !in_set. introb.
        contradict Hu; apply /negP.
        rewrite ccl_e !in_set. caseb.
    + (* lemma *)
      unfold rem_node_transport, rem_node_transport'.
      case: {-}_ /boolP => In; cbnb.
      case_if.
      revert In. rewrite rem_node_removed // !in_set. introb.
      (* lemma *)
      contradict Hu; apply /negP.
      rewrite !in_set.
      destruct b; rewrite ?ccl_e; caseb.
  - assert (endpoint b e == u = false) as -> by by apply /eqP; apply nesym.
    apply /imsetP; move => [[[[[[a A] | []] | ] | []] | ] Ain /= ?]; subst e.
    all: contradict Ain; apply /negP.
    all: rewrite !in_set eq_sym; destruct b; cbnb; by apply /eqP.
Qed.

Lemma rem_node_p_deg {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  terminal v -> proper_degree (rem_node_graph H).
Proof.
  intros T b [[[u U] | []] | []]; simpl.
  - rewrite -p_deg (rem_node_transport_edges T) card_imset //; by apply rem_node_transport'_inj.
  - (* lemma *)
    assert (edges_at_out (inl (inr tt) : rem_node_graph H) = set0).
    { apply /setP => e; rewrite !in_set. by destruct e as [[[[[? ?] | []] | ] | []] | ]. }
    assert (edges_at_in (inl (inr tt) : rem_node_graph H) = [set Some (inl None)]).
    { apply /setP => e; rewrite !in_set. by destruct e as [[[[[? ?] | []] | ] | []] | ]. }
    destruct b; by rewrite ?_H0 ?_H ?cards1 ?cards0.
  - (* lemma *)
    assert (edges_at_out (inr tt : rem_node_graph H) = set0).
    { apply /setP => e; rewrite !in_set [in RHS]in_set. by destruct e as [[[[[? ?] | []] | ] | []] | ]. }
    assert (edges_at_in (inr tt : rem_node_graph H) = [set None]).
    { apply /setP => e; rewrite !in_set [in RHS]in_set. by destruct e as [[[[[? ?] | []] | ] | []] | ]. }
    destruct b; by rewrite ?_H0 ?_H ?cards1 ?cards0.
Qed.

Lemma rem_node_p_ax_cut {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  terminal v -> proper_ax_cut (rem_node_graph H).
Proof.
  move => T b [[[u U] | []] | []] /= Hu; try by destruct b.
  destruct (p_ax_cut Hu) as [el [er [Lin [Rin LR]]]].
  revert Lin Rin.
  exists (rem_node_transport H el), (rem_node_transport H er).
Admitted.
Lemma rem_node_p_tens_parr {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  terminal v -> proper_tens_parr (rem_node_graph H).
Proof.
  intros V b [[[u U] | []] | []] Ur.
  2,3: contradict Ur; by destruct b.
Admitted.

Lemma rem_node_p_noleft {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  proper_noleft (rem_node_graph H).
Proof. move => [[[[[e E] | []] | ]| []] | ] //=. by apply p_noleft. Qed.

Lemma rem_node_p_order {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  terminal v -> proper_order (rem_node_graph_data H).
Proof.
  intro T.
  assert (C : vlabel (target (ccl H)) = c) by by apply /eqP; rewrite -terminal_tens_parr.
  split.
  - rewrite /= /rem_node_order.
    move => [[[[[e E] | []] | ] | []] | ] //=.
    rewrite !in_cons /=.
    assert (Hr : Some (inl (Some (inl (Sub e E : edge (rem_node_graph_1 H))))) = rem_node_transport H e).
    { rewrite /rem_node_transport.
      case: {-}_ /boolP => [In | /negP-In //].
      cbnb. }
    rewrite Hr {Hr}.
    split => O.
    + apply map_f.
      rewrite mem_filter. splitb.
      * revert E. rewrite !in_set. introb.
        apply /eqP => ?. by subst e.
      * by apply p_order.
    + revert O => /mapP[a A Ha].
      assert (a = e).
      { revert Ha. unfold rem_node_transport. case: {-}_ /boolP => [In | /negP-? //].
        case: {-}_ /boolP => [In' | /negP-? //]; last by case_if.
        move => /eqP. by cbnb => /eqP-->. }
      subst a.
      revert A. rewrite mem_filter. introb.
      by apply p_order.
  - rewrite /= in_cons /=. splitb.
    + apply /mapP; move => [a A] /eqP.
      rewrite /rem_node_transport.
      case: {-}_ /boolP => ?; case_if.
      revert A. rewrite mem_filter => /andP[_ A].
      apply p_order in A.
      contradict A.
      rewrite left_e. by destruct H as [H | H]; rewrite H.
    + apply /mapP; move => [a A] /eqP.
      rewrite /rem_node_transport.
      case: {-}_ /boolP => Ain; case_if.
      revert A. rewrite mem_filter => /andP[/eqP-A0 A].
      revert Ain. rewrite rem_node_removed // !in_set. introb.
      apply p_order in A.
      contradict A.
      rewrite right_e. by destruct H as [H | H]; rewrite H.
    + rewrite map_inj_in_uniq.
      { apply filter_uniq, p_order. }
      intros a b.
      rewrite !mem_filter => /andP[_ A] /andP[_ B].
      rewrite /rem_node_transport.
      case: {-}_ /boolP => Ain;
      case: {-}_ /boolP => Bin => /eqP; case_if.
      enough (L : forall e, e \notin edge_set (setT :\ v :\ target (ccl H)) -> e \in order G ->
        e = ccl H).
      { transitivity (ccl H); [ | symmetry]; by apply L. }
      clear -C.
      intros a Ain A.
      apply p_order in A.
      revert Ain. rewrite !in_set => /nandP[/nandP[/negPn/eqP-Ain | /nandP[/negPn/eqP-Ain | //]] |
                                            /nandP[/negPn/eqP-Ain | /nandP[/negPn/eqP-Ain | //]]].
      * contradict Ain. by apply no_source_c.
      * by apply ccl_eq.
      * by apply one_target_c.
      * subst v. contradict A.
        destruct H as [H | H]; by rewrite H.
Qed.

Definition rem_node_ps {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋)
  (V : terminal v) := {|
  graph_data_of := rem_node_graph_data H;
  p_deg := @rem_node_p_deg _ _ _ V;
  p_ax_cut := @rem_node_p_ax_cut _ _ _ V;
  p_tens_parr := @rem_node_p_tens_parr _ _ _ V;
  p_noleft := @rem_node_p_noleft _ _ _;
  p_order := rem_node_p_order _ V;
  |}.

Definition rem_parr_ps {G : proof_net} {v : G} (H : vlabel v = ⅋)
  (V : terminal v) := rem_node_ps (or_intror H) V.

Lemma rem_parr_v_bij_helper {G : proof_net} {v : G} (H : vlabel v = ⅋)
  (V : terminal v) (u : induced ([set: G] :\ v :\ target (ccl_parr H))) :
  inl (inl (inl u))
  \in [set: add_node_graph_1 parr_t (None : edge (rem_parr_ps H V)) (Some (inl None))] :\
    inl (target (None : edge (rem_parr_ps H V))) :\
    inl (target (Some (inl None) : edge (rem_parr_ps H V))).
Proof. rewrite /= !in_set. splitb. Qed.

Definition test_help0_parr {G : proof_net} {v : G} (H : vlabel v = ⅋) (V : terminal v) :
  inr (inr tt) \in [set: add_node_graph_1 parr_t (None : edge (rem_parr_ps H V)) (Some (inl None))]
  :\ inl (target (None : edge (rem_parr_ps H V))) :\ inl (target (Some (inl None) : edge (rem_parr_ps H V))).
Proof. rewrite /= !in_set. splitb. Qed.
Definition test_help1_parr {G : proof_net} {v : G} (H : vlabel v = ⅋) (V : terminal v) :
  inr (inl tt) \in [set: add_node_graph_1 tens_t (None : edge (rem_parr_ps H V)) (Some (inl None))]
  :\ inl (target (None : edge (rem_parr_ps H V))) :\ inl (target (Some (inl None) : edge (rem_parr_ps H V))).
Proof. rewrite /= !in_set. splitb. Qed.
Lemma test_help2 {G : proof_net} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) u :
  u \notin [set: G] :\ v :\ target (ccl H) -> (u == target (ccl H)) + (u == v).
Proof.
rewrite !in_set andb_true_r => /nandP/orP U.
elim: (orb_sum U) => /negPn/eqP-->; caseb.
Qed.

Unset Mangle Names.

Lemma rem_parr_v_bij_bwd_helper0 {G : proof_net} {v : G} (H : vlabel v = ⅋) (V : terminal v) :
 (inl (inl (inr tt))
      \in [set: add_node_graph_1 parr_t (None : edge (rem_parr_ps H V)) (Some (inl None))]
          :\ inl (target (None : edge (rem_parr_ps H V))) :\ inl (target (Some (inl None) : edge (rem_parr_ps H V)))) -> False.
Proof. rewrite !in_set. caseb. Qed.
Lemma rem_parr_v_bij_bwd_helper1 {G : proof_net} {v : G} (H : vlabel v = ⅋) (V : terminal v) :
 (inl (inr tt)
      \in [set: add_node_graph_1 parr_t (None : edge (rem_parr_ps H V)) (Some (inl None))]
          :\ inl (target (None : edge (rem_parr_ps H V))) :\ inl (target (Some (inl None) : edge (rem_parr_ps H V)))) -> False.
Proof. rewrite /= !in_set. caseb. Qed.

Definition rem_parr_v_bij_bwd {G : proof_net} {v : G} (H : vlabel v = ⅋) (V : terminal v) :
  add_node_graph parr_t (None : edge (rem_parr_ps H V)) (Some (inl None)) -> G.
Proof.
intros [[[[[u ?] | []] | []] | [[] | []]] U].
- exact u.
- exfalso. exact (rem_parr_v_bij_bwd_helper0 U).
- exfalso. exact (rem_parr_v_bij_bwd_helper1 U).
- exact v.
- exact (target (ccl_parr H)).
Defined.
Definition rem_parr_v_bij_bwd2 {G : proof_net} {v : G} (H : vlabel v = ⅋) (V : terminal v) :
  add_node_graph parr_t (None : edge (rem_parr_ps H V)) (Some (inl None)) -> G :=
  fun u => match u with
  | exist (inl (inl (inl (exist u _)))) _ => u
  | exist (inl (inl (inr tt)))          U => False_rect G (rem_parr_v_bij_bwd_helper0 U)
  | exist (inl (inr tt))                U => False_rect G (rem_parr_v_bij_bwd_helper1 U)
  | exist (inr (inl tt))                _ => v
  | exist (inr (inr tt))                _ => target (ccl_parr H)
  end. (* Defining this in proof mode yield *)
Definition rem_parr_v_bij_bwd3 {G : proof_net} {v : G} (H : vlabel v = ⅋) (V : terminal v) :
  add_node_graph parr_t (None : edge (rem_parr_ps H V)) (Some (inl None)) -> G :=
  fun u => match val u with
  | inl (inl (inl a)) => val a
  | inr (inr tt)      => target (ccl_parr H)
  | _                 => v (* case inr (inl tt), other cases are absurd *)
  end.
Time Print rem_parr_v_bij_bwd. (* Finished transaction in 13.123 secs (13.041u,0.011s) (successful) *)
Time Print rem_parr_v_bij_bwd2. (* Finished transaction in 5.552 secs (5.511u,0.012s) (successful) *)
Time Print rem_parr_v_bij_bwd3. (* Finished transaction in 1.461 secs (1.455u,0.s) (successful) *)

Definition rem_parr_v_bij_fwd {G : proof_net} {v : G} (H : vlabel v = ⅋) (V : terminal v) :
  G -> add_node_graph parr_t (None : edge (rem_parr_ps H V)) (Some (inl None)).
Proof.
  intro u.
  destruct (@boolP (u \in [set: G] :\ v :\ target (ccl_parr H))) as [U | U].
  - exact (Sub (inl (inl (inl (Sub u U))) : add_node_graph_1 parr_t
    (None : edge (rem_node_graph (or_intror H))) (Some (inl None))) (rem_parr_v_bij_helper V (Sub u U))).
  - elim: (test_help2 U) => U'.
    + exact (Sub (inr (inr tt)) (test_help0_parr H V)).
    + exact (Sub (inr (inl tt)) (test_help1_parr H V)).
Defined.
Time Print rem_parr_v_bij_fwd. (* Finished transaction in 5.98 secs (5.934u,0.003s) (successful) *)


Lemma rem_parr_e_bij_helper {G : proof_net} {v : G} (H : vlabel v = ⅋)
  (V : terminal v) (e : edge (induced ([set: G] :\ v :\ target (ccl_parr H)))) :
  Some (Some (inl (Some (inl (Some (inl e))))))
  \in edge_set ([set: add_node_graph_1 parr_t (None : edge (rem_parr_ps H V)) (Some (inl None))]
  :\ inl (target (None : edge (rem_parr_ps H V))) :\ inl (target (Some (inl None) : edge (rem_parr_ps H V)))).
Proof. rewrite /= !in_set. splitb. Qed.

Lemma rem_parr_e_bij_helper2 {G : proof_net} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) (V : terminal v) e :
  e \notin edge_set ([set: G] :\ v :\ target (ccl H)) ->
  (e == left H) + (e == right H) + (e == ccl H).
Proof.
  assert (C : vlabel (target (ccl H)) = c) by by apply /eqP; rewrite -terminal_tens_parr.
  rewrite !in_set !andb_true_r => /nandP/orP E.
  elim: (orb_sum E); clear E.
  - move => /nandP/orP E.
    elim: (orb_sum E) => {E} /negPn/eqP-E.
    + contradict E.
      by apply no_source_c.
    + enough (E' : e = ccl H) by (subst e; caseb).
      by apply ccl_eq.
  - move => /nandP/orP E.
    elim: (orb_sum E) => {E} /negPn/eqP-E.
    + enough (E' : e = ccl H) by (subst e; caseb).
      by apply one_target_c.
    + destruct (llabel e) eqn:L.
      * enough (E' : e = left H) by (subst e; caseb).
        by apply left_eq.
      * revert L => /negP-L.
        enough (E' : e = right H) by (subst e; caseb).
        by apply right_eq.
Qed.

Lemma rem_parr_e_bij_helper3 {G : proof_net} {v : G} (H : vlabel v = ⅋) (V : terminal v) :
  let S := [set: add_node_graph_1 parr_t (None : edge (rem_parr_ps H V)) (Some (inl None))]
  :\ inl (target (None : edge (rem_parr_ps H V))) :\ inl (target (Some (inl None) : edge (rem_parr_ps H V))) in
  None \in edge_set S /\ Some None \in edge_set S.
Proof. eapply add_node_new_edges_at_in. by rewrite /= /rem_node_order. Qed.

Lemma rem_parr_e_bij_helper4 {G : proof_net} {v : G} (H : vlabel v = ⅋) (V : terminal v) :
  let S := [set: add_node_graph_1 parr_t (None : edge (rem_parr_ps H V)) (Some (inl None))]
  :\ inl (target (None : edge (rem_parr_ps H V))) :\ inl (target (Some (inl None) : edge (rem_parr_ps H V))) in
  Some (Some (inr None)) \in edge_set S.
Proof. rewrite /= !in_set. splitb. Qed.

Definition rem_parr_e_bij_fwd {G : proof_net} {v : G} (H : vlabel v = ⅋) (V : terminal v) :
  edge G -> edge (add_node_graph parr_t (None : edge (rem_parr_ps H V)) (Some (inl None))).
Proof.
  intro e.
  destruct (@boolP (e \in edge_set ([set: G] :\ v :\ target (ccl_parr H)))) as [E | E].
  - exact (Sub (Some (Some (inl (Some (inl (Some (inl (Sub e E))))))) :
    edge (add_node_graph_1 parr_t (None : edge (rem_parr_ps H V)) (Some (inl None))))
    (rem_parr_e_bij_helper V (Sub e E))).
  - elim: (rem_parr_e_bij_helper2 V E) => E'; [elim: E' => E'' | ].
    + exact (Sub (Some None) (proj2 (rem_parr_e_bij_helper3 _ _))).
    + exact (Sub None (proj1 (rem_parr_e_bij_helper3 _ _))).
    + exact (Sub (Some (Some (inr None))) (rem_parr_e_bij_helper4 _ _)).
Defined.

Definition rem_parr_e_bij_bwd {G : proof_net} {v : G} (H : vlabel v = ⅋) (V : terminal v) :
  edge (add_node_graph parr_t (None : edge (rem_parr_ps H V)) (Some (inl None))) -> edge G :=
  fun e => match val e with
  | Some (Some (inl (Some (inl (Some (inl a)))))) => val a
  | Some None => left_parr H
  | None => right_parr H
  | _ => ccl_parr H (* case Some (Some (inr None)) *)
  end.

(*
Lemma rem_parr_iso {G : proof_net} {v : G} (H : vlabel v = ⅋)
  (V : terminal v) :
  G ≃ add_node_graph parr_t (None : edge (rem_parr_ps H V)) (Some (inl None)).
Proof.
  assert (C : vlabel (target (ccl_parr H)) = c) by by apply /eqP; rewrite -terminal_tens_parr.
  assert (v_bijK : cancel (rem_parr_v_bij_fwd H V) (@rem_parr_v_bij_bwd3 _ _ H V)).
  { intro u. unfold rem_parr_v_bij_fwd, rem_parr_v_bij_bwd3.
    case: {-}_ /boolP => U //. by elim: (test_help2 U) => /eqP-? /=. }
  assert (v_bijK' : cancel (@rem_parr_v_bij_bwd3 _ _ H V) (rem_parr_v_bij_fwd H V)).
  { unfold rem_parr_v_bij_fwd, rem_parr_v_bij_bwd3.
    intros [[[[[u Uin] | []] | []] | [[] | []]] U]; simpl.
    - case: {-}_ /boolP => U'.
      + cbnb.
      + exfalso; clear U; contradict Uin; apply /negP.
        rewrite !in_set.
        elim: (test_help2 U') => /eqP-? /=; subst u; caseb.
    - contradict U. rewrite !in_set. caseb.
    - contradict U. rewrite /= !in_set. caseb.
    - case: {-}_ /boolP => U'.
      + contradict U'; apply /negP. rewrite !in_set. caseb.
      + elim: (test_help2 U') => /eqP-U'' /=; cbnb.
        contradict C.
        by rewrite -U'' H.
    - case: {-}_ /boolP => U'.
      + contradict U'; apply /negP. rewrite !in_set. caseb.
      + elim: (test_help2 U') => /eqP-U'' /=; cbnb.
        contradict C.
        by rewrite U'' H. }
  set iso_v := {|
    bij_fwd := _;
    bij_bwd:= _;
    bijK:= v_bijK;
    bijK':= v_bijK';
    |}.
  assert (e_bijK : cancel (rem_parr_e_bij_fwd H V) (@rem_parr_e_bij_bwd _ _ H V)).
  { intro e. unfold rem_parr_e_bij_fwd, rem_parr_e_bij_bwd.
    case: {-}_ /boolP => E //. elim: (rem_parr_e_bij_helper2 V E) => [E' | /= /eqP--> //].
    elim: E' => /= /eqP--> //. }
  assert (e_bijK' : cancel (@rem_parr_e_bij_bwd _ _ H V) (rem_parr_e_bij_fwd H V)).
  { unfold rem_parr_e_bij_fwd, rem_parr_e_bij_bwd.
    intros [[[[[[[[[e Ein] | []] | ] | []] | ] | [[[] | []] | ]] | ] | ] E]; simpl.
    - case: {-}_ /boolP => E'.
      + cbnb.
      + exfalso; clear E; by contradict Ein; apply /negP.
    - contradict E. by rewrite /= !in_set.
    - contradict E. by rewrite /= !in_set.
    - case: {-}_ /boolP => E'.
      + contradict E'; apply /negP. rewrite /= !in_set. caseb.
      + elim: (rem_parr_e_bij_helper2 V E'); [move => E''; elim: E'' | ];
        move => /= /eqP-E'''; cbnb.
        * contradict C.
          by rewrite E''' left_e H.
        * contradict C.
          by rewrite E''' right_e H.
    - case: {-}_ /boolP => E'.
      + contradict E'; apply /negP. rewrite /= !in_set left_e. caseb.
      + elim: (rem_parr_e_bij_helper2 V E'); [move => E''; elim: E'' | ];
        move => /= /eqP-E'''; cbnb.
        * assert (L : llabel (left_parr H)) by by apply left_l.
          contradict L; apply /negP.
          rewrite E'''. apply right_l.
        * contradict C.
          by rewrite /ccl_parr -E''' left_e H.
    - case: {-}_ /boolP => E'.
      + contradict E'; apply /negP. rewrite /= !in_set right_e. caseb.
      + elim: (rem_parr_e_bij_helper2 V E'); [move => E''; elim: E'' | ];
        move => /= /eqP-E'''; cbnb.
        * assert (L : llabel (left_parr H)) by by apply left_l.
          contradict L; apply /negP.
          rewrite /left_parr -E'''. apply right_l.
        * contradict C.
          by rewrite /ccl_parr -E''' right_e H. }
  set iso_e := {|
    bij_fwd := _;
    bij_bwd:= _;
    bijK:= e_bijK;
    bijK':= e_bijK';
    |}.
  assert (iso_ihom : is_ihom iso_v iso_e pred0).
  { split.
    - intros a []; elim: (orb_sum (Ca a)) => /eqP-?; subst a; simpl.
      all: unfold e_bij_fwd, v_bij_fwd; case_if.
      enough (source e' <> target e) by by [].
      rewrite E'. by apply nesym.
    - intros u; destruct (Cu u) as [? | [? | ?]]; subst u; simpl.
      all: unfold v_bij_fwd; case_if.
    - intros a; elim: (orb_sum (Ca a)) => /eqP-?; subst a; simpl.
      all: unfold e_bij_fwd; case_if.
      + destruct (elabel e) as [Fe Le] eqn:LL.
        apply /eqP. revert LL => /eqP. cbn => /andP[? /eqP-L]. splitb.
        rewrite -L. apply p_noleft. caseb.
      + destruct (elabel e') as [Fe Le] eqn:LL.
        apply /eqP. revert LL => /eqP. cbn => /andP[/eqP-F' /eqP-L]. subst Fe Le. splitb.
        * rewrite F bidual. cbnb.
        * apply p_noleft. caseb. }
  exact ({| iso_v := _; iso_e := _; iso_d := _; iso_ihom := iso_ihom |}).
  
(* heavy ... *)
Admitted.
(* waiting ! *)

******************************************************************************************************)
(* TODO idée pour résoudre ce problème de temps: définir rem_node en changeant les sommets et arêtes,
sans les retirer ; mais ça serait moche *)


(*
Definition rem_cut_graph_1 {G : proof_structure} {v : G} (H : vlabel v = cut) :=
  induced (setT :\ v).

(* Add two new conclusions *)
Lemma rem_cut_graph_helper {G : proof_structure} {v : G} (H : vlabel v = cut) :
  {'(e, f) & edges_at_in v = [set e; f] /\ e <> f /\ source e \in [set: G] :\ v /\ source f \in [set: G] :\ v}.
Proof.
  assert (C : exists e, [exists f, (e != f) && (edges_at_in v == [set e; f])]).
  { assert (C := pre_proper_cut H).
    revert C => /eqP/cards2P[e [f [? ?]]].
    exists e. apply /existsP. exists f. apply /andP. split; trivial. by apply /eqP. }
  revert C => /sigW[e] /existsP/sigW[f /andP[/eqP-? /eqP-In]].
  exists (e, f). splitb; trivial; [set a := e | set a := f].
  all: rewrite !in_set andb_true_r; apply /eqP.
  all: enough (v = target a) as -> by apply no_selfloop.
  all: enough (A : a \in edges_at_in v) by by revert A; rewrite in_set => /eqP-->.
  all: rewrite In !in_set; caseb.
Qed.

Definition rem_cut_graph {G : proof_structure} {v : G} (H : vlabel v = cut) : base_graph.
Proof.
  destruct (rem_cut_graph_helper H) as [[e f] [_ [_ [E F]]]].
  exact(@add_concl_graph _
    (@add_concl_graph _ (rem_cut_graph_1 H) (Sub (source e) E) c (flabel e))
      (inl (Sub (source f) F)) c (flabel f)).
Defined.

Definition splitting_cc (G : proof_net) (v : G) : bool :=
  match vlabel v as V return vlabel v = V -> bool with
  | ax => fun _ => terminal v
  | ⊗ => fun H => uconnected_nb (@switching_left _ (rem_node_graph (or_introl H))) == 2
  | ⅋ => fun H => uconnected_nb (@switching_left _ (rem_node_graph (or_intror H))) == 1
  | cut => fun H => uconnected_nb (@switching_left _ (rem_cut_graph H)) == 2
  | c => fun _ => false
  end Logic.eq_refl.

(* puis définir les graphes avec induced_sub S pour S dans 
equivalence_partition (is_uconnected f) [set: G] et là ça devient galère,
faire des vues pour se retrouver avec des il existe equi = [S S'] (il existe sur
set de finset, donc ok je pense) puis définir les Gi à partir de là,
montrer qu'ils sont uconnected_nb = 1, puis finalement que
G iso à add_node Gi *)*)

END TOO LONG *)

Lemma terminal_ax_is_splitting_step0 (G : proof_net) (v : G) :
  vlabel v = ax -> terminal v ->
  {'(e, e') & flabel e = flabel e'^ & source e = v /\ source e' = v /\ vlabel (target e) = c /\
  vlabel (target e') = c}.
Proof.
  intros V T.
  destruct (p_ax_type V) as [[e e'] [E [E' F]]]. subst v.
  exists (e, e'); splitb.
  all: by apply (terminal_source T).
Qed.

Lemma terminal_ax_is_splitting_step1 (G : proof_net) (v : G) :
  vlabel v = ax ->
  forall e e', flabel e = flabel e'^ -> source e = v -> source e' = v -> vlabel (target e) = c ->
  vlabel (target e') = c ->
  forall u, u = source e \/ u = target e \/ u = target e'.
Proof.
  intros V e e' F E E' Te Te' u. subst v.
  assert (C : correct G) by apply p_correct.
  apply correct_to_weak in C.
  destruct C as [_ C]. elim: (C (source e) u) => [[p /andP[/andP[W U] N]] _].
  destruct p as [ | (a, b) p]; first by (revert W => /= /eqP-->; caseb).
  revert W => /= /andP[/eqP-Hf W].
  destruct b; last by (contradict Hf; by apply no_target_ax).
  enough (A : a = e \/ a = e').
  { destruct A; [set ae := e | set ae := e']; subst a.
    all: destruct p as [ | (a, b) p]; first by (revert W => /= /eqP-->; caseb).
    all: revert W => /= /andP[/eqP-Hf2 _].
    all: destruct b; first by (contradict Hf2; by apply no_source_c).
    all: assert (a = ae) by (by apply one_target_c); subst a.
    all: contradict U; apply /negP.
    all: rewrite /= in_cons; caseb. }
  assert (C2 : #|edges_at_out (source e)| == 2) by by apply /eqP; rewrite p_deg_out V.
  revert C2 => /cards2P [f [f' [/eqP-Fneq FF]]].
  assert (a \in edges_at_out (source e) /\ e \in edges_at_out (source e) /\
    e' \in edges_at_out (source e)) as [Ina [Ine Ine']]
    by by splitb; rewrite !in_set; apply /eqP.
  revert Ina Ine Ine'. rewrite !FF !in_set. introb; subst; caseb.
  all: contradict F; apply nesym, no_selfdual.
Qed.

Lemma terminal_ax_is_splitting_step2 (G : proof_net) (v : G) :
  vlabel v = ax ->
  forall e e', flabel e = flabel e'^ -> source e = v -> source e' = v -> vlabel (target e) = c ->
  vlabel (target e') = c ->
  forall a, (a == e) || (a == e').
Proof.
  intros V e e' F E E' Te Te' a. subst v.
  assert (Cu : forall u, u = source e \/ u = target e \/ u = target e')
    by by apply (terminal_ax_is_splitting_step1 V).
  destruct (Cu (target a)) as [A | [A | A]].
  - contradict A. by apply no_target_ax.
  - apply /orP; left; apply /eqP. by apply one_target_c.
  - apply /orP; right; apply /eqP. by apply one_target_c.
Qed.

Lemma terminal_ax_is_splitting_step3 (G : proof_net) (v : G) :
  vlabel v = ax ->
  forall e e', flabel e = flabel e'^ -> source e = v -> source e' = v -> vlabel (target e) = c ->
  vlabel (target e') = c ->
  target e' <> source e /\ target e <> source e /\ e' <> e /\ target e' <> target e.
Proof.
  intros V e e' F E E' Te Te'. subst v.
  assert (En : e' <> e).
  { intros ?. subst e'.
    contradict F. apply nesym, no_selfdual. }
  splitb.
  - rewrite -E'. apply nesym, no_selfloop.
  - by apply nesym, no_selfloop.
  - intros ?. contradict En. by by apply one_target_c.
Qed.

Lemma terminal_ax_is_splitting_step4 (G : proof_net) (v : G) :
  vlabel v = ax ->
  forall e e', flabel e = flabel e'^ -> source e = v -> source e' = v -> vlabel (target e) = c ->
  vlabel (target e') = c -> (forall u, u = source e \/ u = target e \/ u = target e') ->
  (forall a, (a == e) || (a == e')) -> target e' <> source e -> target e <> source e ->
  e' <> e -> target e' <> target e ->
  G ≃ ax_graph_data (flabel e).
Proof.
  intros V e e' F E E' Te Te' Cu Ca T'S TS En T'T. subst v.
  set v_bij_fwd : G -> ax_graph (flabel e) := fun u =>
    if u == source e then ord0
    else if u == target e then ord2
    else ord1.
  set v_bij_bwd : ax_graph (flabel e) -> G := fun u => let (n, _) := u in match n with
    | 0 => source e
    | 1 => target e'
    | _ => target e
    end.
  assert (v_bijK : cancel v_bij_fwd v_bij_bwd).
  { intro u. unfold v_bij_bwd, v_bij_fwd. case_if. by destruct (Cu u) as [? | [? | ?]]. }
  assert (v_bijK' : cancel v_bij_bwd v_bij_fwd).
  { intro u. unfold v_bij_bwd, v_bij_fwd. destruct_I u; case_if; cbnb. }
  set iso_v := {|
    bij_fwd := _;
    bij_bwd:= _;
    bijK:= v_bijK;
    bijK':= v_bijK';
    |}.
  set e_bij_fwd : edge G -> edge (ax_graph (flabel e)) := fun a =>
    if a == e then ord1
    else ord0.
  set e_bij_bwd : edge (ax_graph (flabel e)) -> edge G := fun u => let (n, _) := u in match n with
    | 0 => e'
    | _ => e
    end.
  assert (e_bijK : cancel e_bij_fwd e_bij_bwd).
  { intro a. unfold e_bij_bwd, e_bij_fwd. case_if.
    by elim: (orb_sum (Ca a)) => /eqP-?. }
  assert (e_bijK' : cancel e_bij_bwd e_bij_fwd).
  { intro a. unfold e_bij_bwd, e_bij_fwd. destruct_I a; case_if; cbnb. }
  set iso_e := {|
    bij_fwd := _;
    bij_bwd:= _;
    bijK:= e_bijK;
    bijK':= e_bijK';
    |}.
  assert (iso_ihom : is_ihom iso_v iso_e pred0).
  { split.
    - intros a []; elim: (orb_sum (Ca a)) => /eqP-?; subst a; simpl.
      all: unfold e_bij_fwd, v_bij_fwd; case_if.
      enough (source e' <> target e) by by [].
      rewrite E'. by apply nesym.
    - intros u; destruct (Cu u) as [? | [? | ?]]; subst u; simpl.
      all: unfold v_bij_fwd; case_if.
    - intros a; elim: (orb_sum (Ca a)) => /eqP-?; subst a; simpl.
      all: unfold e_bij_fwd; case_if.
      + destruct (elabel e) as [Fe Le] eqn:LL.
        apply /eqP. revert LL => /eqP. cbn => /andP[? /eqP-L]. splitb.
        rewrite -L. apply p_noleft. caseb.
      + destruct (elabel e') as [Fe Le] eqn:LL.
        apply /eqP. revert LL => /eqP. cbn => /andP[/eqP-F' /eqP-L]. subst Fe Le. splitb.
        * rewrite F bidual. cbnb.
        * apply p_noleft. caseb. }
  exact ({| iso_v := _; iso_e := _; iso_d := _; iso_ihom := iso_ihom |}).
Qed.

Lemma terminal_ax_is_splitting (G : proof_net) (v : G) :
  vlabel v = ax -> terminal v -> splitting v.
Proof.
  intros V T.
  destruct (terminal_ax_is_splitting_step0 V T) as [[e e'] F [E [E' [Te Te']]]].
  subst v. clear T.
  assert (Cu : forall u, u = source e \/ u = target e \/ u = target e')
    by by apply (terminal_ax_is_splitting_step1 V).
  assert (Ca : forall a, (a == e) || (a == e'))
    by by apply (terminal_ax_is_splitting_step2 V).
  assert (target e' <> source e /\ target e <> source e /\ e' <> e /\ target e' <> target e)
    as [T'S [TS [En T'T]]] by by apply (terminal_ax_is_splitting_step3 V).
  rewrite /splitting V.
  exists (flabel e).
  by apply (@terminal_ax_is_splitting_step4 _ _ V _ e').
Qed.


(* BEGIN NEW TRY *)

Lemma terminal_parr_is_splitting (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal v -> splitting v.
Proof.
  intros V T.
  rewrite /splitting V.
Abort. (* TODO *)

Lemma supath_to_induced {Lv Le : Type} {G : graph Lv Le} (S : {set G})
  {I J : finType} (f : edge G -> option I) (f' : edge (induced S) -> option J)
  s t (p : Supath f s t) :
  (forall e (E : e \in edge_set S), None <> f e -> None <> f' (Sub e E)) ->
  (forall e a (E : e \in edge_set S) (A : a \in edge_set S),
    f' (Sub e E) = f' (Sub a A) -> f e = f a) ->
  (forall e, e \in upval p -> e.1 \in edge_set S) ->
  forall (Sin : s \in S) (Tin : t \in S),
  {q : Supath f' (Sub s Sin) (Sub t Tin) & upval p = [seq (val a.1, a.2) | a <- upval q]}.
Proof. (* in fact can even deduce Sin and Tin, provided p not empty *)
  intros F0 F1 Hp Sin Tin.
  destruct p as [p P].
  simpl in *.
  revert s Sin P. induction p as [ | e p IHp] => s Sin.
  { rewrite /supath /=. introb.
    assert (Sin = Tin) by apply eq_irrelevance. subst.
    by exists (supath_nil _ _). }
  rewrite /supath /= in_cons => /andP[/andP[/andP[/eqP-? PW] /andP[Pu PU]] /norP[/eqP-Pn PN]].
  subst s.
  assert (P : supath f (utarget e) t p) by splitb.
  assert (E : e.1 \in edge_set S).
  { apply Hp. rewrite in_cons. caseb. }
  assert (Hp' : forall e, e \in p -> e.1 \in edge_set S).
  { intros. apply Hp. rewrite in_cons. caseb. }
  assert (T : utarget e \in S).
  { revert E. rewrite in_set. destruct e as [? []]; introb. }
  revert IHp => /(_ Hp' _ T P) {Hp Hp' P} [[q Q] ?]. subst p.
  enough (Q' : supath (f' : edge (induced _) -> _) (Sub (usource e) Sin) (Sub t Tin)
    ((Sub e.1 E : edge (induced S), e.2) :: q)).
  { exists {| upvalK := Q' |}. by destruct e. }
  assert (E' : supath (f' : edge (induced _) -> _) (Sub (usource e) Sin) (Sub (utarget e) T) [:: (Sub e.1 E, e.2)]). (* TODO lemma for edge supath? *)
  { rewrite /supath /= in_cons in_nil orb_false_r. splitb; try by cbnb.
    apply /eqP. clear - F0 Pn. by apply F0. }
  rewrite -cat1s.
  apply (@supath_catK _ _ _ _ _ _ _ _ {| upvalK := E' |} {| upvalK := Q |}).
  rewrite /upath_disjoint disjoint_has /= orb_false_r.
  clear - F1 Pu.
  apply /mapP. move => [[[z Z] zb] Zin Zeq].
  contradict Pu. apply /negP/negPn/mapP.
  exists (z, zb); last by apply (F1 _ _ _ _ Zeq).
  simpl. revert Zin. generalize q. clear. intro l.
  induction l as [ | [? ?] ? H]; trivial.
  rewrite !in_cons. cbn.
  move => /orP[-> // | ?].
  apply /orP. right. by apply H.
Qed.

Lemma mem_pblock2 {T : finType} {rT : eqType} {f : T -> rT} {S : {set T}} {x y : T} :
  y \in pblock (preim_partition f S) x -> y \in S.
Proof.
  intro Y.
  assert (Spart := preim_partitionP f S).
  by rewrite -(cover_partition Spart) -mem_pblock (same_pblock (partition_trivIset Spart) Y).
Qed.

Lemma equivalence_rel_preim {T : finType} {rT : eqType} {f : T -> rT} {S : {set T}} :
  {in S & &, equivalence_rel (fun x y : T => f x == f y)}.
Proof. split; try done. by move => /eqP-->. Qed.

Lemma preim_partition_im_eq {T : finType} {rT : eqType} (f : T -> rT) (S : {set T}) (P : {set T}) :
  P \in preim_partition f S -> forall x y, x \in P -> y \in S -> f y = f x -> y \in P.
Proof.
  intros Pin x y Px Sy YX.
  assert (Spart := preim_partitionP f S).
  assert (P = pblock (preim_partition f S) x).
  { symmetry; apply def_pblock; trivial. apply (partition_trivIset Spart). }
  subst P.
  rewrite pblock_equivalence_partition //.
  - by apply /eqP.
  - exact equivalence_rel_preim.
  - exact (mem_pblock2 Px).
Qed.

Lemma preim_partition_in_eq {T : finType} {rT : eqType} (f : T -> rT) (S : {set T}) (P : {set T}) :
  P \in preim_partition f S -> forall x y, x \in P -> y \in P -> f x = f y.
Proof.
  intros Pin x y X Y.
  assert (Spart := preim_partitionP f S).
  assert (P = pblock (preim_partition f S) x).
  { symmetry; apply def_pblock; trivial. apply (partition_trivIset Spart). }
  subst P.
  assert (Y2 := Y). rewrite pblock_equivalence_partition in Y2.
  - by apply /eqP.
  - exact equivalence_rel_preim.
  - exact (mem_pblock2 X).
  - exact (mem_pblock2 Y).
Qed.

Lemma preim_partition_pblock_eq {T : finType} {rT : eqType} (f : T -> rT) (S : {set T}) x y :
  x \in S -> y \in S ->
  (pblock (preim_partition f S) x == pblock (preim_partition f S) y) = (f x == f y).
Proof.
  assert (Spart := preim_partitionP f S).
  revert Spart => /andP[/eqP-Cov /andP[Triv Zero]].
  intros X Y.
  rewrite eq_pblock //; last by rewrite Cov.
  destruct (eq_comparable (f x) (f y)) as [F | F].
  - rewrite F eq_refl.
    symmetry in F.
    eapply (preim_partition_im_eq _ _ Y F). Unshelve.
    + apply pblock_mem. by rewrite Cov.
    + by rewrite mem_pblock Cov.
  - transitivity false; last by (symmetry; apply /eqP).
    apply /negP => Y'.
    contradict F.
    eapply (@preim_partition_in_eq _ _ _ S _ _ _ _ _ Y'). Unshelve.
    + apply pblock_mem. by rewrite Cov.
    + by rewrite mem_pblock Cov.
Qed.

(* More general than preim_partition_eq *)
Lemma equivalence_partition_eq {T : finType} (r : rel T) (S : {set T}) :
  {in S & &, equivalence_rel r} ->
  equivalence_partition r S = [set (pblock (equivalence_partition r S) x) | x in S].
Proof.
  intro R.
  assert (Spart := equivalence_partitionP R).
  revert Spart => /andP[/eqP-Cov /andP[Triv Zero]].
  apply /setP => P.
  symmetry. destruct (P \in equivalence_partition r S) eqn:Pin.
  - assert {x | x \in P} as [x X].
    { destruct (set_0Vmem P); trivial.
      exfalso. subst P.
      contradict Zero. by apply /negP/negPn. }
    assert (Peq := def_pblock Triv Pin X). subst P.
    apply imset_f.
    by rewrite mem_pblock Cov in X.
  - apply /imsetP. move => [x X Peq]. subst P.
    revert Pin => /negP/negP => Pin.
    contradict Pin. apply /negP/negPn.
    apply pblock_mem. by rewrite Cov.
Qed.

Lemma preim_partition_eq {T : finType} {rT : eqType} (f : T -> rT) (S : {set T}) :
  preim_partition f S = [set (pblock (preim_partition f S) x) | x in S].
Proof. apply equivalence_partition_eq, equivalence_rel_preim. Qed.

Lemma inside_utree_part {Lv Le : Type} {G : graph Lv Le} (S : {set G})
  {I : finType} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v : G) :
  S \in (preim_partition (utree_part F T v) [set: G]) ->
  forall a p (x : G) (X : x \in S),
  supath f v x (a :: p) ->
  forall e, e \in p -> e.1 \in edge_set S.
Proof.
  intros Sin a p.
  induction p as [ | p ep IH] using last_ind; first by by [].
  intros x X P e E.
  rewrite -rcons_cons in P.
  assert (P' := P).
  rewrite supath_rcons in P. revert P => /andP[/andP[/andP[P /eqP-?] ?] ?]. subst x.
  enough (TepS : usource ep \in S).
  { specialize (IH _ TepS P).
    revert E. rewrite in_rcons => /orP[/eqP-? | ]; last by apply IH.
    subst e. rewrite /= in_set.
    destruct ep as [? []]; splitb. }
  clear IH E e.
  apply (preim_partition_im_eq Sin X); trivial.
  clear Sin X S.
  unfold utree_part.
  destruct (utree_unique_path F T v (usource ep)) as [[ps Ps] Us].
  assert (ps = a :: p).
  { specialize (Us {| upvalK := P |}). by inversion Us. }
  subst ps. clear Us Ps .
  destruct (utree_unique_path F T v (utarget ep)) as [[pt Pt] Ut].
  assert (pt = rcons (a :: p) ep).
  { specialize (Ut {| upvalK := P' |}). by inversion Ut. }
  subst pt. clear Ut Pt P'.
  reflexivity.
Qed.

Lemma uconnected_utree_part_in {Lv Le : Type} {G : graph Lv Le} (S : {set G})
  {I : finType} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v : G) :
  S \in (preim_partition (utree_part F T v) [set: G]) ->
  forall x y, x \in S -> y \in S ->
  forall e, e \in upval (projT1 (utree_unique_path F T x y)) -> e.1 \in edge_set S.
(* Sketch of the proof :
   We have a path from v to x and one from v to y.
   Their concatenation, after reversing the first path and simplification,
   yields the unique path from x to y.
   This is a subpath of the previous two paths, without their
   first edges (the one involving v).
   These subpaths are included in S by Lemma inside_utree_part. *)
Proof.
  intros Sin x y X Y.
  destruct (utree_unique_path F T x y) as [P Pu]. simpl.
  assert (XY := preim_partition_in_eq Sin X Y).
  unfold utree_part in XY.
  destruct (utree_unique_path F T v x) as [[px Px] _].
  destruct (utree_unique_path F T v y) as [[py Py] _].
  destruct px as [ | (ex, box) px], py as [ | (ey, boy) py]; try by [].
  { apply supath_of_nil in Px, Py. subst x y.
    specialize (Pu (supath_nil _ v)). by subst P. }
  inversion XY. subst ey. clear XY.
  assert (PxS := inside_utree_part Sin X Px).
  assert (PyS := inside_utree_part Sin Y Py).
  rewrite !supath_cons in Px, Py.
  revert Px => /andP[/andP[/andP[Px /eqP-Usex] _] /eqP-FexN]. simpl in FexN.
  revert Py => /andP[/andP[/andP[Py /eqP-Usey] _] _].
  assert (box = boy).
  { clear P Pu px Px PxS py Py PyS x X y Y Sin F.
    destruct T as [A _].
    destruct (eq_comparable box boy) as [ | B]; trivial.
    apply nesym in FexN. assert (F := uacyclic_loop A FexN). contradict F.
    subst v. by destruct box, boy. }
  subst boy. clear Usey Usex FexN.
  apply supath_revK in Px. revert Px => /andP[/andP[Wx _] Nx].
  revert Py => /andP[/andP[Wy _] Ny].
  assert (Nxy : None \notin [seq f _e.1 | _e <- upath_rev px ++ py]).
  { by rewrite map_cat mem_cat negb_orb Nx Ny. }
  destruct (uconnected_simpl F (uwalk_cat Wx Wy) Nxy) as [Pxy Exy].
  specialize (Pu Pxy). subst Pxy.
  clear Nx Ny Nxy Wx Wy ex box X Y Sin T F.
  intros (e, b) E.
  revert Exy => /(_ _ E) {E}. rewrite mem_cat upath_rev_in => /orP[E | E].
  - exact (PxS _ E).
  - exact (PyS _ E).
Qed.

(* The patition of a tree yields connected components *)
Lemma uconnected_utree_part {Lv Le : Type} {G : graph Lv Le} (S : {set G})
  {I J : finType} (f : edge G -> option I) (f' : edge (induced S) -> option J)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v : G) :
  (forall e (E : e \in edge_set S), None <> f e -> None <> f' (Sub e E : edge (induced S))) ->
  (forall e a (E : e \in edge_set S) (A : a \in edge_set S),
    f' (Sub e E) = f' (Sub a A) -> f e = f a) ->
  S \in (preim_partition (utree_part F T v) [set: G]) -> uconnected f'.
Proof.
  intros F0 F1 Sin [x X] [y Y].
  destruct (supath_to_induced F0 F1 (uconnected_utree_part_in Sin X Y) X Y) as [Q _].
  by exists Q.
Qed.
(* TODO voir ce qui tient avec cette définition de f', plus générale *)

Lemma utree_part_None {Lv Le : Type} {G : graph Lv Le} {I : finType} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v x : G) :
  utree_part F T v x = None -> x = v.
Proof.
  unfold utree_part.
  destruct (utree_unique_path F T v x) as [[[ | (e, b) p] P] _]; last by [].
  revert P. rewrite /supath /=. introb.
Qed.

Lemma utree_part_v_v {Lv Le : Type} {G : graph Lv Le} {I : finType} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v : G) :
  utree_part F T v v = None.
Proof.
  unfold utree_part. destruct (utree_unique_path F T v v) as [P Pu].
  specialize (Pu (supath_nil _ v)). by subst P.
Qed.

Lemma utree_part_v {Lv Le : Type} {G : graph Lv Le} {I : finType} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v : G) :
  pblock (preim_partition (utree_part F T v) [set: G]) v = [set v].
Proof.
  assert (Spart := preim_partitionP (utree_part F T v) [set: G]).
  revert Spart => /andP[/eqP-Cov /andP[Triv _]].
  apply /setP => y.
  rewrite in_set -eq_pblock // ?Cov // preim_partition_pblock_eq //.
  destruct (eq_comparable y v) as [? | Y].
  { subst y. by rewrite !eq_refl. }
  transitivity false; last by (symmetry; apply /eqP).
  rewrite utree_part_v_v.
  destruct (utree_part F T v y) eqn:H; first by [].
  contradict Y. by apply (utree_part_None H).
Qed.

Lemma utree_switching_left (G : proof_net) :
  utree (@switching_left _ G).
Proof. split; [apply uacyclic_swithching_left, G | apply uconnected_from_nb1, G]. Qed.

Lemma partition_terminal_ccl (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  terminal v ->
  forall x, utree_part (@switching_left_sinj _ G) (utree_switching_left G) v x = Some (ccl_tens V) ->
  pblock (preim_partition (utree_part (@switching_left_sinj _ G) (utree_switching_left G) v) [set: G]) x
    = [set target (ccl_tens V)].
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  rewrite (terminal_tens_parr (or_introl V)) => /eqP-C.
  intros x X. apply /setP => y.
  assert (Spart := preim_partitionP (utree_part F T v) [set: G]).
  revert Spart => /andP[/eqP-Cov /andP[Triv _]].
  rewrite in_set -eq_pblock // ?Cov {Cov Triv} // preim_partition_pblock_eq // X {X}.
  destruct (eq_comparable y (target (ccl_tens V))) as [? | Y].
  - subst y. rewrite eq_refl. apply /eqP.
    unfold utree_part. destruct (utree_unique_path F T v (target (ccl_tens V))) as [P Pu].
    assert (S : supath switching_left v (target (ccl_tens V)) [:: forward (ccl_tens V)]).
    { rewrite /supath /= in_cons negb_orb ccl_e. splitb.
      by rewrite /switching_left C. }
    specialize (Pu {| upvalK := S |}). by subst P.
  - transitivity false; last by (symmetry; apply /eqP).
    apply /eqP.
    unfold utree_part. destruct (utree_unique_path F T v y) as [[p P] _].
    destruct p as [ | (e1, b1) p]; first by []. cbnb.
    destruct (eq_comparable e1 (ccl_tens V)); last by apply nesym.
    subst e1. exfalso.
    rewrite supath_cons in P. revert P => /andP[/andP[/andP[P1 /eqP-Vb1] U1] /eqP-N1].
    assert (b1 = true).
    { destruct b1; trivial. exfalso. destruct T as [A _].
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

Lemma partition_terminal_utree_part (G : proof_net) (v : G) (V : vlabel v = ⊗) (x : G) :
  utree_part (@switching_left_sinj _ G) (utree_switching_left G) v x
    \in [set None; Some (left_tens V); Some (right_tens V); Some (ccl_tens V)].
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  unfold utree_part. destruct (utree_unique_path F T v x) as [[[ | e p] P] _].
  { by rewrite !in_set. }
  rewrite supath_cons in P. revert P => /andP[/andP[/andP[_ /eqP-EV] _] _].
  destruct e as (e, []); simpl in EV.
  - assert (E := ccl_eq (or_introl V) EV). subst e.
    rewrite !in_set. caseb.
  - enough (E : e \in [set left_tens V; right_tens V]).
    { revert E. rewrite !in_set => /orP[/eqP--> | /eqP-->]; caseb. }
    by rewrite -right_set in_set EV.
Qed.

Lemma partition_terminal_utree_part_ccl (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  terminal v ->
  utree_part (@switching_left_sinj _ G) (utree_switching_left G) v (target (ccl_tens V))
    = Some (ccl_tens V).
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  rewrite (terminal_tens_parr (or_introl V)) => /eqP-C.
  unfold utree_part. destruct (utree_unique_path F T v (target (ccl_tens V))) as [P Pu].
  assert (S : supath switching_left v (target (ccl_tens V)) [:: forward (ccl_tens V)]).
  { rewrite /supath /= in_cons negb_orb ccl_e /switching_left C. splitb. }
  specialize (Pu {| upvalK := S |}). by subst P.
Qed.

Lemma partition_terminal_utree_part_left (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  utree_part (@switching_left_sinj _ G) (utree_switching_left G) v (source (left_tens V))
    = Some (left_tens V).
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  unfold utree_part. destruct (utree_unique_path F T v (source (left_tens V))) as [P Pu].
  assert (S : supath switching_left v (source (left_tens V)) [:: backward (left_tens V)]).
  { rewrite /supath /= in_cons negb_orb left_e /switching_left left_e V. splitb. }
  specialize (Pu {| upvalK := S |}). by subst P. (* TODO tout simplifier comme ça ! *)
Qed.

Lemma partition_terminal_utree_part_right (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  utree_part (@switching_left_sinj _ G) (utree_switching_left G) v (source (right_tens V))
    = Some (right_tens V).
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  unfold utree_part. destruct (utree_unique_path F T v (source (right_tens V))) as [P Pu].
  assert (S : supath switching_left v (source (right_tens V)) [:: backward (right_tens V)]).
  { rewrite /supath /= in_cons negb_orb right_e /switching_left right_e V. splitb. }
  specialize (Pu {| upvalK := S |}). by subst P.
Qed.

Lemma partition_terminal_eq (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  terminal v ->
  preim_partition (utree_part (@switching_left_sinj _ G) (utree_switching_left G) v) [set: G] =
  [set pblock (preim_partition (utree_part (@switching_left_sinj _ G) (utree_switching_left G) v) [set: G])
         (source (left_tens V));
       pblock (preim_partition (utree_part (@switching_left_sinj _ G) (utree_switching_left G) v) [set: G])
         (source (right_tens V));
       [set v]; [set target (ccl_tens V)]].
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
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
Lemma partition_terminal (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  terminal v ->
  {'(Sl, Sr) : {set G} * {set G} & partition [set Sl; Sr; [set v]; [set target (ccl_tens V)]] [set: G] /\
    uconnected (@switching_left _ (induced Sl)) /\ uconnected (@switching_left _ (induced Sr)) /\
    source (left_tens V) \in Sl /\ source (right_tens V) \in Sr}.
Proof.
  set T := utree_switching_left G. set F := @switching_left_sinj _ G.
  intro VT.
  assert (Spart := preim_partitionP (utree_part F T v) [set: G]).
  revert Spart => /andP[/eqP-Cov _].
  exists (pblock (preim_partition (utree_part F T v) [set: G]) (source (left_tens V)),
          pblock (preim_partition (utree_part F T v) [set: G]) (source (right_tens V))).
  split; [ | split; [ | split; [ | split]]]; trivial.
  - rewrite -(partition_terminal_eq V VT). apply tree_partition.
  - apply (@uconnected_utree_part _ _ _ _ _ _ _ _ F T v
      (@switching_left_induced_None_to _ _) (@switching_left_induced_eq_to _ _)).
    rewrite {2}(partition_terminal_eq V VT) !in_set. caseb.
  - apply (@uconnected_utree_part _ _ _ _ _ _ _ _ F T v
      (@switching_left_induced_None_to _ _) (@switching_left_induced_eq_to _ _)).
    rewrite {2}(partition_terminal_eq V VT) !in_set. caseb.
  - by rewrite mem_pblock Cov.
  - by rewrite mem_pblock Cov.
Qed.

(* We can do a case study on this, but not on splitting : Type *)
Definition splitting_tens_prop (G : proof_net) (v : G) (V : vlabel v = ⊗) (T : terminal v) :=
  let (SS, _) := (partition_terminal V T) in let (Sl, Sr) := SS in
  forall (p : G) (P : vlabel p = ⅋), (p \in Sl -> source (right_parr P) \in Sl)
                                  /\ (p \in Sr -> source (right_parr P) \in Sr).


Definition splitting_tens_bool (G : proof_net) (v : G) (V : vlabel v = ⊗) (T : terminal v) :=
  let (SS, _) := (partition_terminal V T) in let (Sl, Sr) := SS in
  [forall p : G, if @boolP (vlabel p == ⅋) is AltTrue P then ((p \in Sl) ==> (source (right_parr (eqP P)) \in Sl))
                                  && ((p \in Sr) ==> (source (right_parr (eqP P)) \in Sr)) else true].

Lemma splitting_tensP (G : proof_net) (v : G) (V : vlabel v = ⊗) (T : terminal v) :
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

Lemma splitting_tens_prop_is_splitting (G : proof_net) (v : G) (V : vlabel v = ⊗) (T : terminal v) :
  splitting_tens_prop V T -> splitting v.
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
And of course, this will be divided acroos plenty of lemmas. *)
(* Admitted for now, to check that this is a good notion of splitting,
before doing this no-fun proof *)
Admitted.

Lemma splitting_tens_is_splitting_prop (G : proof_net) (v : G) (V : vlabel v = ⊗) :
  splitting v -> {T : terminal v | splitting_tens_prop V T}.
Proof.
(* same as the proof above, but normally in a esaier way (well, we still have an iso to
manipulate); by contradiction ? *)
Admitted.

(* A tensor is non splitting because there is some ⅋ with its right edge in the other part
  of the partition *)
Lemma non_splitting_tens (G : proof_net) (v : G) (V : vlabel v = ⊗) (T : terminal v) :
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

(* TODO dans prelim *)
Lemma disjoint_rcons (T : finType) (x : T) (s : seq T) (B : {pred T}) :
  [disjoint (rcons s x) & B] = (x \notin B) && [disjoint s & B].
Proof. by rewrite -cats1 disjoint_cat disjoint_cons disjoint0 andb_true_r andb_comm. Qed.

Lemma correctness_parr (G : proof_net) (v : G) (V : vlabel v = ⊗) (T : terminal v)
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

Lemma case_todo_properly (G : proof_net) : {v : G & splitting v} + forall (v : G), (splitting v -> False).
Proof.
Admitted.

(* And then, descending path, followed by critical path *)


(* END NEW TRY *)

(* OLD TRY
Lemma terminal_parr_is_splitting_cc (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal v -> splitting_cc v.
Proof.
  intros V T.
  unfold splitting_cc. generalize (erefl (vlabel v)). rewrite {2 3}V => V'.
  assert (V = V') by apply eq_irrelevance. subst V'.
  enough (C : correct (rem_node_graph (or_intror V))) by by apply /eqP; destruct C.
  unfold rem_node_graph.
  destruct (rem_node_sources_stay (or_intror V)) as [e f].
  apply add_concl_correct, correct_to_weak, add_concl_correct. split.
  { apply uacyclic_induced, p_correct. }
  intros [x X] [y Y].
  destruct (correct_to_weak (p_correct G)) as [_ C].
  revert C => /(_ x y)/sigW[[p P] _].
  enough ({q : Supath switching_left (Sub x X : rem_node_graph_1 (or_intror V)) (Sub y Y) &
    p = [seq (val a.1, a.2) | a <- upval q]}) as [q _] by by exists q.
  revert x X P. induction p as [ | a p IH] => x X; rewrite /supath /=.
  { introb. replace Y with X by apply eq_irrelevance. by exists (supath_nil _ _). }
  rewrite in_cons => /andP[/andP[/andP[/eqP-? W] /andP[u U]] /norP[n N]]; subst x.
  destruct (utarget a \in [set: G] :\ v :\ target (ccl_parr V)) eqn:A.
  - destruct (IH _ A) as [q Hq].
    { splitb. }
    assert (Ain : a.1 \in edge_set ([set: G] :\ v :\ target (ccl_parr V))).
    { rewrite in_set. destruct a as [a []]; splitb. }
    assert (PA : supath switching_left (Sub (usource a) X : rem_node_graph_1 (or_intror V))
      (Sub (utarget a) A) [:: (Sub a.1 Ain, a.2)]).
    { rewrite /supath /= in_cons orb_false_r. splitb; try by cbnb.
      revert n. rewrite /switching_left /=. case_if. }
    enough (D : upath_disjoint switching_left {| upvalK := PA |} q).
    { exists (supath_cat D). cbn. rewrite Hq. f_equal. simpl. by destruct a. }
    rewrite /= /upath_disjoint disjoint_has /= orb_false_r.
    revert u. subst p.
    destruct q as [q Q]. rewrite -map_comp /=. clear.
    induction q as [ | c q IH]; trivial.
    rewrite /= !in_cons => /norP[k K]. apply /norP. rewrite IH //. splitb.
    revert k. rewrite /switching_left /=. case_if.
  - clear IH.
    assert (Vc : vlabel (target (ccl_parr V)) = c).
    { revert T. clear. rewrite (terminal_tens_parr (or_intror V)). apply /eqP. }
    assert (Ca : a = forward (left_parr V)).
    { clear - X A n Vc.
      revert A. rewrite !in_set andb_true_r => /nandP[/negPn/eqP-A | /negPn/eqP-A].
      - exfalso.
        destruct a as [a []].
        + assert (a = ccl_parr V) by by apply one_target_c.
          subst a.
          contradict X; apply /negP.
          rewrite !in_set /= ccl_e. caseb.
        + contradict A. simpl.
          by apply no_source_c.
      - destruct a as [a []].
        + simpl in A. f_equal.
          revert n. rewrite /switching_left /= A V /=. case_if.
          by apply left_eq.
        + assert (a = ccl_parr V) by by apply ccl_eq.
          subst a.
          contradict X; apply /negP.
          rewrite !in_set /=. caseb. }
    subst a.
    assert (Cp : p = [::] \/ p = [:: forward (ccl_parr V)]).
    { destruct p as [ | s p]; auto. right.
      assert (s = forward (ccl_parr V)).
      { revert W => /= /andP[/eqP-S W].
        rewrite left_e in S.
        destruct s as [s []]; simpl in *.
        - apply /eqP. cbn. rewrite andb_true_r. apply /eqP.
          by apply ccl_eq.
        - revert u N. rewrite !in_cons => /norP[S1 _] /norP[S2 _]. revert S1 S2.
          rewrite /switching_left left_e left_l S V /=.
          case_if.
          enough (left_parr V = s) by by [].
          symmetry. by apply left_eq. }
      subst s.
      destruct p as [ | r p]; trivial.
      exfalso. revert U W. clear - Vc.
      rewrite /= !in_cons => /andP[/norP[U _] _] /andP[_ /andP[/eqP-W _]].
      assert (r = backward (ccl_parr V)).
      { clear - W Vc.
        destruct r as [r []].
        - revert W. cbnb => W. contradict W.
          by apply no_source_c.
        - revert W. cbnb => W.
          apply /eqP. cbn. splitb. apply /eqP.
          by apply one_target_c. }
      subst r.
      contradict U. by apply /negP/negPn/eqP. }
    contradict Y. apply /negP. clear -Cp W.
    rewrite !in_set.
    revert W. destruct Cp; subst p; simpl.
    + move => /eqP-?; subst y. rewrite left_e. caseb.
    + move => /andP[_ /eqP-?]. subst y. caseb.
Qed.

Lemma splitting_cc_parr_is_splitting (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal v -> splitting_cc v -> splitting v.
Proof.
  intros V T.
  unfold splitting_cc. generalize (erefl (vlabel v)). rewrite {2 3}V => V' S.
  assert (V = V') by apply eq_irrelevance. subst V'.
  rewrite /splitting V.
  assert (C : correct (rem_node_graph (or_intror V))).
  { split; [ | by apply /eqP].
    apply union_edge_uacyclic; last by apply unit_graph_uacyclic.
    apply union_edge_uacyclic; last by apply unit_graph_uacyclic.
    apply uacyclic_induced, p_correct. }
  exists {| ps_of := rem_node_ps (or_intror V) T ; p_correct := C |}.
Abort.
(*
  assert (h := rem_node_iso (or_intror V) T).
  rewrite {1}V in h.
  apply h.
Qed.
*)

(* tenseur scindant ici, avec cut ... TODO traiter cut comme des tens ? *)


Lemma splitting_cc_is_splitting (G : proof_net) (v : G) :
  splitting_cc v -> splitting v.
Proof.
Admitted.

Lemma terminal_parr_is_splitting (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal v -> splitting v.
Proof. intros. by apply splitting_cc_is_splitting, terminal_parr_is_splitting_cc. Qed.
*)

Lemma has_splitting (G : proof_net) :
  {v : G & splitting v}.
Proof.
(* utiliser has_terminal, se ramener au cas où il n'y a que des cut / tens term
puis tenseur scindant *)
Admitted.

(* TODO admettre lemme tenseur scindant puis sequantialisation directement *)
(* ax : pas iso a G mais ps p iso à ax exp G *)
(* TODO ne séquentializer que des réseaux atomiques ! *)
Definition sequentialize (G : proof_net) : { p : ll (sequent G) & ps p ≃d G }.
Proof.
  revert G.
  enough (Hm : forall n (G : proof_net), #|edge G| = n -> { p : ll (sequent G) & ps p ≃d G })
    by by intro G; apply (Hm #|edge G|).
  intro n; induction n as [n IH] using lt_wf_rect; intros G ?; subst n.
  destruct (has_splitting G) as [v V].
  unfold splitting in V. destruct (vlabel v); try by [].
  - destruct V as [A h].
    set pi := ax_exp A : ⊢ sequent (ax_graph_data A).
    exists (ex_r pi (sequent_iso_perm h)). simpl. unfold pi.
    unfold ax_exp.
    assert({x | A = var x}) as [? ?]. { admit. } (* easy case where A is an atomic axiom *)
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
  destruct (has_splitting G) as [v V].
  unfold splitting in V. destruct (vlabel v); try by [].
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

(** ** Sequentialization *)
(* many things to do: spliting tens / cut, blocking parr, always a
  terminal parr or a splitting *)
(* function to turn a ps into a sequential proof *)
(* TOTHINK utiliser seulement connexité left possible (ie pas besoin de demontrer que
un graphe de correc correct ac notre def) ? to check, parr bloquant *)



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
(* TODO Lemma : nb cut ps (pi) = nb cut pi, idem other rules, et dans le sens sequentialisation aussi *)
End Atoms.
