(* Unit-free MLL following Yalla schemas *)
(* Basic results on proof nets *)

From Coq Require Import Bool Wellfounded.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.
From HB Require Import structures.

From Yalla Require Export mll_prelim graph_more upath supath graph_uconnected_nb mgraph_dag mll_def.

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
Notation sequent := (@sequent atom).
Notation base_graph := (graph (flat rule) (flat (formula * bool))).
Notation graph_data := (@graph_data atom).
Notation proof_structure := (@proof_structure atom).
Notation proof_net := (@proof_net atom).
Notation switching := (@switching atom).
Notation switching_left := (@switching_left atom).

(** No selfloop in a proof_structure *)
Lemma no_selfloop (G : proof_structure) (e : edge G) : source e <> target e.
Proof.
  intro H.
  assert (W := walk_edge e). rewrite H in W.
  now assert (F := ps_acyclic W).
Qed.



(** * Properties on switching & switching_left *)
Lemma switching_eq (G : base_graph) (a b : edge G) :
  switching a = switching b -> target a = target b.
Proof.
  unfold switching => /eqP; cbn => /eqP.
  case: ifP; case: ifP; by move => // _ _ /eqP; cbn => /eqP ->.
Qed.

Lemma switching_None (G : base_graph) (p : @upath _ _ G) :
  None \notin [seq switching e.1 | e <- p].
Proof. by induction p. Qed.

Lemma switching_left_sinj {G : base_graph} :
  {in ~: (@switching_left G) @^-1 None &, injective switching_left}.
Proof.
  move => a b; rewrite !in_set => A B /eqP; revert A B.
  unfold switching_left; case_if.
Qed.

Lemma swithching_to_left_eq {G : proof_structure} (a b : edge G) :
  switching_left a <> None -> switching_left b <> None ->
  switching a = switching b -> switching_left a = switching_left b.
Proof.
  move => A B S.
  assert (T := switching_eq S).
  apply /eqP; revert S A B => /eqP.
  rewrite /switching/switching_left T; cbn.
  case_if; apply /eqP.
  assert (Bl : vlabel (target b) = ⅋) by assumption.
  transitivity (left_parr Bl); [ | symmetry];
  by apply left_eq.
Qed.

Lemma supath_switching_from_leftK {G : proof_structure} (u v : G) p :
  supath switching_left u v p ->
  supath switching u v p.
Proof.
  move => /andP[/andP[? U] N].
  splitb; last by apply switching_None.
  destruct p as [ | e p]; trivial.
  apply /(uniqP (Some (inl (e.1)))) => a f A F.
  revert U => /(uniqP (Some e.1)) /(_ a f).
  rewrite_all size_map; rewrite !(nth_map e) // => /(_ A F) U Heq.
  apply U, swithching_to_left_eq; trivial.
  - intro Hc.
    contradict N; apply /negP/negPn/mapP.
    exists (nth e (e :: p) a); try by [].
    by apply mem_nth.
  - intro Hc.
    contradict N; apply /negP/negPn/mapP.
    exists (nth e (e :: p) f); try by [].
    by apply mem_nth.
Qed.

Definition supath_switching_from_left {G : proof_structure} (s t : G) (p : Supath switching_left s t) :
  Supath _ _ _ :=
  (Sub _ (supath_switching_from_leftK (valP p))).

Lemma uacyclic_swithching_left {G : proof_structure} :
  uacyclic (@switching G) -> uacyclic (@switching_left G).
Proof.
  move => A u [p P].
  specialize (A _ (supath_switching_from_left (Sub p P))).
  apply val_inj.
  by destruct p.
Qed.

Lemma switching_left_edges_None (G : base_graph) :
  (@switching_left G) @^-1 None = [set e | (vlabel (target e) == ⅋) && (~~llabel e)].
Proof.
  apply /setP => e.
  rewrite !in_set; symmetry.
  destruct (switching_left e \in pred1 None) eqn:E.
  all: revert E => /eqP.
  all: unfold switching_left; case_if.
Qed.

Lemma switching_left_edges_None_nb (G : proof_structure) :
  #|[set e : edge G | (vlabel (target e) == ⅋) && (~~llabel e)]| = #|[set v : G | vlabel v == ⅋]|.
Proof.
  rewrite -!card_set_subset.
  assert (Hf : forall E : {e : edge G | (vlabel (target e) == ⅋) && (~~llabel e)},
    (vlabel (target (val E)) == ⅋)).
  { by intros [e E]; cbn; revert E => /andP[E _]. }
  set f : {e : edge G | (vlabel (target e) == ⅋) && (~~llabel e)} ->
    {v | vlabel v == ⅋} :=
    fun e => Sub (target (val e)) (Hf e).
  assert (Hg : forall E : {v : G | vlabel v == ⅋},
    (vlabel (target (right_parr (eqP (valP E)))) == ⅋) && (~~llabel (right_parr (eqP (valP E))))).
  { intros [e E]; splitb.
    - by rewrite right_e.
    - apply right_l. }
  set g : {v | vlabel v == ⅋} ->
    {e : edge G | (vlabel (target e) == ⅋) && (~~llabel e)} :=
    fun V => Sub (right_parr (eqP (valP V))) (Hg V).
  apply (bij_card_eq (f := f)), (Bijective (g := g)).
  - move => [e E].
    rewrite /f/g; cbnb.
    symmetry; apply right_eq; simpl.
    by revert E => /andP[_ /negP-?].
  - move => [v V].
    rewrite /f/g; cbnb.
    apply right_e.
Qed.

Lemma switching_left_edges_nb (G : proof_structure) :
  #|[set v : G | vlabel v == ⅋]| + #|~: (@switching_left G) @^-1 None| = #|edge G|.
Proof. by rewrite -switching_left_edges_None_nb -switching_left_edges_None cardsC. Qed.

Lemma switching_left_uconnected_nb {G : proof_structure} :
  uacyclic (@switching G) ->
  uconnected_nb (@switching_left G) + #|edge G| = #|G| + #|[set v : G | vlabel v == ⅋]|.
Proof.
  move => *.
  rewrite -switching_left_edges_nb.
  transitivity (uconnected_nb (@switching_left G) +
    #|~: (@switching_left G) @^-1 None| + #|[set v : G | vlabel v == ⅋]|); [lia | ].
  rewrite uacyclic_uconnected_nb //.
  - apply switching_left_sinj.
  - by apply uacyclic_swithching_left.
Qed.

Lemma correct_from_weak (G : base_graph) :
  #|G| <> 0 -> correct_weak G -> correct G.
Proof. intros ? [? ?]. split; trivial. by apply uconnected_to_nb1. Qed.

Lemma correct_to_weak (G : base_graph) :
  correct G -> correct_weak G.
Proof. intros [? ?]. split; trivial. by apply uconnected_from_nb1. Qed.

Lemma correct_not_empty (G : base_graph) :
  correct G -> #|G| <> 0.
Proof. intros [_ C]. by apply (nb1_not_empty C). Qed.

Lemma exists_node (G : proof_net) : {v : G & vlabel v <> c}.
Proof.
  assert (N := correct_not_empty (p_correct G)).
  revert N => /eqP. rewrite -cardsT cards_eq0 => /set0Pn/sigW[v _].
  destruct (vlabel v) eqn:V;
  try by (exists v; rewrite V).
  exists (source (edge_of_concl V)).
  intros U.
  assert (F : source (edge_of_concl V) = source (edge_of_concl V)) by trivial.
  contradict F. by apply no_source_c.
Qed.

Lemma card_edges_at_vertex {G : proof_structure} (v : G) :
  #|edges_at v| = match vlabel v with
  | ax | cut => 2
  | ⊗  | ⅋   => 3
  | c        => 1
  end.
Proof.
  rewrite (card_edges_at_at_outin (v : dam_of_ps G)) !p_deg.
  destruct (vlabel v); simpl; lia.
Qed.

Lemma exists_edge (G : proof_net) : edge G.
Proof.
  destruct (exists_node G) as [v _].
  assert (E : 0 < #|edges_at v|).
  { rewrite card_edges_at_vertex. destruct (vlabel v); lia. }
  by revert E => /card_gt0P/sigW[? _].
Qed.

Lemma supath_from_induced_switching (G : base_graph) (S : {set G}) s t (p : Supath (@switching (induced S)) s t) :
  supath (@switching G) (val s) (val t) [seq (val a.1, a.2) | a <- val p].
Proof.
  apply supath_from_induced.
  - intros ? ? _. case_if.
  - move => ? ? ? ? /eqP-F. apply /eqP. revert F. unfold switching. case_if.
Qed.

Lemma uacyclic_induced (G : base_graph) (S : {set G}) :
  uacyclic (@switching G) -> uacyclic (@switching (induced S)).
Proof.
  intros U v [p P].
  specialize (U _ (Sub _ (supath_from_induced_switching (Sub p P)))).
  apply val_inj. by destruct p.
Qed.

Lemma supath_from_induced_switching_left (G : base_graph) (S : {set G}) s t
  (p : Supath (@switching_left (induced S)) s t) :
  supath (@switching_left G) (val s) (val t) [seq (val a.1, a.2) | a <- val p].
Proof.
  apply supath_from_induced.
  - move => ? ?. unfold switching_left. case_if.
  - move => ? ? ? ? /eqP. unfold switching_left. case_if; cbnb.
Qed.

Lemma switching_left_induced_None_to (G : base_graph) (S : {set G}) e (E : e \in edge_set S) :
  None <> @switching_left G e -> None <> @switching_left (induced S) (Sub e E).
Proof. unfold switching_left. case_if. Qed.

Lemma switching_left_induced_eq_to (G : base_graph) (S : {set G}) e a (E : e \in edge_set S)
  (A : a \in edge_set S) :
  @switching_left (induced S) (Sub e E) = @switching_left (induced S) (Sub a A) ->
  switching_left e = switching_left a.
Proof. move => /eqP. unfold switching_left. case_if; simpl in *; by subst. Qed.



(** * Isomorphism for each strata *)
(** Correction is preserved by isomorphism on base graphs *)
Definition switching_map (F G : base_graph) (h : F ≃ G) :=
  fun e => match e with
  | Some (inl a) => Some (inl (h.e a))
  | Some (inr a) => Some (inr (h a))
  | None => None
 end.

Lemma iso_switching (F G : base_graph) (h : F ≃ G) e :
  switching (h.e e) = switching_map h (switching e).
Proof.
  cbnb. rewrite !endpoint_iso iso_noflip vlabel_iso; cbn.
  by destruct (vlabel (target e)) eqn:Hl; rewrite Hl; case_if.
Qed.

Lemma iso_switching_left (F G : base_graph) (h : F ≃ G) e :
  switching_left (h.e e) = option_map h.e (switching_left e).
Proof.
  rewrite /switching_left/switching_left endpoint_iso iso_noflip vlabel_iso llabel_iso.
  case_if.
Qed.


Lemma iso_path_switchingK (F G : base_graph) (h : F ≃ G) p s t :
  supath switching s t p -> supath switching (h s) (h t) (iso_path h p).
Proof.
  move => /andP[/andP[W U] N]. splitb.
  - apply iso_walk; trivial. apply iso_noflip.
  - rewrite -map_comp /comp; cbn.
    assert (map _ p = [seq switching_map h (switching x.1) | x <- p]) as ->
      by (apply eq_map; move => *; by rewrite iso_switching).
    rewrite /switching map_comp map_inj_uniq // in U.
    rewrite (map_comp (fun e => match e with | inl _1 => _ | inr _1 => _ end) _ _) map_inj_uniq //.
    move => [a | a] [b | b] /eqP; cbn => // /eqP-Eq; cbnb.
    all: by revert Eq; apply bij_injective.
  - apply switching_None.
Qed.

Definition iso_path_switching (F G : base_graph) (h : F ≃ G) (s t : F) :
  Supath switching s t -> Supath switching (h s) (h t) :=
  fun p => Sub _ (iso_path_switchingK h (valP p)).

Lemma iso_path_switching_inj (F G : base_graph) (h : F ≃ G) s t :
  injective (@iso_path_switching _ _ h s t).
Proof.
  move => [p P] [q Q] Heq.
  apply val_inj. simpl.
  inversion Heq as [[Heq']]. clear Heq.
  move: Heq'. apply inj_map => [[e b] [f c]] /= Heq.
  inversion Heq as [[Heq0 Heq1]]. clear Heq.
  apply bij_injective in Heq0. by subst f c.
Qed.

Lemma iso_path_nil (F G : base_graph) (h : F ≃ G) (s : F) :
  iso_path_switching h (supath_nil switching s) = supath_nil switching (h s).
Proof. by apply val_inj. Qed.

Lemma iso_path_switching_leftK (F G : base_graph) (h : F ≃ G) p s t :
  supath switching_left s t p -> supath switching_left (h s) (h t) (iso_path h p).
Proof.
  move => /andP[/andP[W U] N].
  splitb.
  - apply iso_walk; trivial. apply iso_noflip.
  - rewrite -map_comp /comp; cbn.
    enough ([seq switching_left (h.e x.1) | x <- p] = [seq Some (h.e x.1) | x <- p] /\
      [seq switching_left e.1 | e <- p] = [seq Some x.1 | x <- p]) as [Hr' Hr].
    { rewrite Hr map_comp map_inj_uniq // in U.
      by rewrite Hr' map_comp map_inj_uniq // map_comp map_inj_uniq. }
    split; apply eq_in_map; intros (e, b) E.
    all: rewrite ?iso_switching_left /switching_left.
    all: case_if.
    all: contradict N; apply /negP/negPn.
    all: enough (Hn : None = switching_left (e, b).1) by
      (rewrite Hn; by apply (map_f (fun a => switching_left a.1))).
    all: rewrite /switching_left /=.
    all: replace (vlabel (target e) == ⅋) with true by by (symmetry; apply/eqP).
    all: by replace (~~llabel e) with true.
  - rewrite -map_comp /comp; cbn.
    apply /(nthP None); move => [n Hc] Hf.
    rewrite size_map in Hc.
    enough (nth None [seq switching_left x.1 | x <- p] n = None).
    { contradict N; apply /negP/negPn/(nthP None). rewrite size_map. by exists n. }
    revert Hf.
    destruct p as [ | (e, b) p]; try by [].
    rewrite !(nth_map (e, b) None) // iso_switching_left.
    unfold switching_left; case_if.
Qed.

Definition iso_path_switching_left (F G : base_graph) (h : F ≃ G) (s t : F) :
  Supath switching_left s t -> Supath switching_left (h s) (h t) :=
  fun p => Sub _ (iso_path_switching_leftK h (valP p)).

Lemma iso_uacyclic (F G : base_graph) :
  F ≃ G -> uacyclic switching (G := G) -> uacyclic switching (G := F).
Proof.
  intros h A ? ?.
  apply (@iso_path_switching_inj _ _ h).
  rewrite iso_path_nil.
  apply A.
Qed.

Lemma iso_uconnected (F G : base_graph) :
  F ≃ G -> uconnected switching_left (G := G) -> uconnected switching_left (G := F).
Proof.
  intros h C u v. destruct (C (h u) (h v)) as [p _].
  set h' := iso_sym h.
  rewrite -(bijK' h' u) -(bijK' h' v).
  by exists (iso_path_switching_left h' p).
Qed.

(*
Lemma iso_uconnectednb (F G : base_graph) :
  F ≃ G -> uconnected_nb switching_left (G := G) = uconnected_nb switching_left (G := F).
Proof.
Abort. (* TODO if useful, but it is stronger than what we need *)*)

Lemma iso_correct_weak (F G : base_graph) : F ≃ G -> correct_weak G -> correct_weak F.
Proof.
  intros h [? ?]; split.
  - by apply (iso_uacyclic h).
  - by apply (iso_uconnected h).
Qed.

Lemma iso_correct (F G : base_graph) : F ≃ G -> correct G -> correct F.
Proof.
  intros h C.
  apply correct_from_weak.
  - rewrite (card_iso h). by apply correct_not_empty.
  - by apply (iso_correct_weak h), correct_to_weak.
Qed.


(** * Isomorphism on graph data preserves being a proof structure *)

(* Equivalence relation *)
Definition iso_data_id (G : graph_data) : G ≃d G.
Proof. exists (iso_id (G:=G)). symmetry; apply map_id. Defined.

Definition iso_data_sym (F G : graph_data) : F ≃d G -> G ≃d F.
Proof.
  move => f.
  exists (iso_sym f).
  rewrite -(map_id (order F)) (order_iso f) -map_comp /=.
  apply eq_map => v /=.
  symmetry; apply bijK.
Defined.

Definition iso_data_comp (F G H : graph_data) : F ≃d G -> G ≃d H -> F ≃d H.
Proof.
  move => f g.
  exists (iso_comp f g).
  by rewrite (order_iso g) (order_iso f) -map_comp.
Defined.

Global Instance iso_data_Equivalence: CEquivalence (@iso_data atom).
Proof. constructor; [exact @iso_data_id | exact @iso_data_sym | exact @iso_data_comp]. Defined.

Lemma sequent_iso_data F G : F ≃d G -> sequent F = sequent G.
Proof.
  intros [h O].
  rewrite /sequent O -map_comp.
  apply eq_map => e /=.
  by rewrite flabel_iso.
Qed.

(* Properties making a graph a proof structure are transported *)
Lemma p_deg_iso (F G : base_graph) : F ≃ G -> proper_degree G -> proper_degree F.
Proof.
  intros h H b v.
  specialize (H b (h v)).
  rewrite ->vlabel_iso in H.
  rewrite -H edges_at_outin_iso ?card_imset //.
  apply iso_noflip.
Qed.

Lemma p_ax_cut_iso (F G : base_graph) : F ≃ G -> proper_ax_cut G -> proper_ax_cut F.
Proof.
  move => h H b v Hl.
  rewrite <-(vlabel_iso h v) in Hl.
  revert H => /(_ b _ Hl) [el [er H]].
  exists (h.e^-1 el), (h.e^-1 er).
  rewrite -(bijK h v) (@edges_at_outin_iso _ _ _ _ (iso_sym h)) ?(bij_imset_f (iso_sym h).e)
    ?(flabel_iso (iso_sym h)) //.
  apply iso_noflip.
Qed.

Lemma p_tens_parr_iso (F G : base_graph) : F ≃ G -> proper_tens_parr G -> proper_tens_parr F.
Proof.
  move => h H b /= v Hl.
  rewrite <-(vlabel_iso h v) in Hl.
  revert H => /(_ b _ Hl) [el [er [ec H]]].
  exists (h.e^-1 el), (h.e^-1 er), (h.e^-1 ec).
  rewrite -(bijK h v) !(@edges_at_outin_iso _ _ _ _ (iso_sym h)) ?(bij_imset_f (iso_sym h).e)
    ?(flabel_iso (iso_sym h)) ?(llabel_iso (iso_sym h)) //.
  all: apply iso_noflip.
Qed.

Lemma p_noleft_iso (F G : base_graph) : F ≃ G -> proper_noleft G -> proper_noleft F.
Proof.
  intros h H e Hl.
  assert (Hl' : vlabel (target (h.e e)) = ax \/ vlabel (target (h.e e)) = cut \/
    vlabel (target (h.e e)) = c) by by rewrite endpoint_iso iso_noflip vlabel_iso.
  specialize (H (h.e e) Hl').
  by rewrite llabel_iso in H.
Qed.

Lemma p_order_iso (F G : graph_data) : F ≃d G -> proper_order G -> proper_order F.
Proof.
  intros h [In U].
  split.
  - intro e.
    specialize (In (h.e e)). rewrite ->endpoint_iso, ->vlabel_iso, iso_noflip in In. simpl in In.
    symmetry; symmetry in In. apply (@iff_stepl _ _ _ In).
    by rewrite (order_iso h) mem_map.
  - by rewrite (order_iso h) map_inj_uniq in U.
Qed.

Lemma order_iso_weak (F G : proof_structure) (h : F ≃ G) e :
  e \in order F <-> h.e e \in order G.
Proof.
  destruct (p_order F) as [? _].
  destruct (p_order G) as [? _].
  transitivity (vlabel (target e) = c); [by symmetry | ].
  by replace (vlabel (target e)) with (vlabel (target (h.e e)))
    by by rewrite endpoint_iso iso_noflip vlabel_iso.
Qed.

Definition order_iso_perm (F G : proof_structure) (h : F ≃ G) :
  Permutation_Type (order G) [seq h.e e | e <- order F].
Proof.
  destruct (p_order F) as [_ ?], (p_order G) as [_ ?].
  by apply Permutation_Type_bij_uniq, order_iso_weak.
Defined.

Lemma sequent_iso_weak (F G : proof_structure) (h : F ≃ G) :
  sequent F = [seq flabel e | e <- [seq h.e e | e <- order F]].
Proof. rewrite /sequent -map_comp. apply eq_map => ? /=. by rewrite flabel_iso. Qed.

Definition sequent_iso_perm (F G : proof_structure) : F ≃ G ->
  Permutation_Type (sequent G) (sequent F).
Proof.
  intro h.
  rewrite (sequent_iso_weak h).
  exact (Permutation_Type_map_def _ (order_iso_perm h)).
Defined.

Lemma perm_of_sequent_iso_perm (F G : proof_structure) (h : F ≃ G) :
  perm_of (sequent_iso_perm h) (order G) = [seq h.e e | e <- order F].
Proof.
  by rewrite -(perm_of_consistent (order_iso_perm _)) perm_of_rew_r
    perm_of_Permutation_Type_map.
Qed.
(* TODO lemma iso_to_isod ici ? Necessite d'y mettre perm_graph aussi *)
(* TODO si besoin de proprietes comme left (h ) = h left, les mettre ici *)



(** * Some unused results, to generalize if useful *)(*
Lemma rset_bij {F G : base_graph} (h : F ≃ G) :
  [set h v | v : F & vlabel v == c] = [set v | vlabel v == c].
Proof. apply setP => v. by rewrite -[in LHS](bijK' h v) bij_imset_f !in_set (vlabel_iso (iso_sym h)). Qed.

Lemma rset_bij_in {F G : base_graph} (h : F ≃ G)
  (v : sig_finType (pred_of_set (~: [set v : F | vlabel v == c]))) :
  h (val v) \in ~: [set v : G | vlabel v == c].
Proof. destruct v. by rewrite -(rset_bij h) bij_imsetC bij_imset_f. Qed.
*)


(** * Useful results for sequentialization *)
Lemma has_ax (G : proof_net) : { v : G & vlabel v = ax }.
Proof.
  enough (E : { v : G & vlabel v == ax }).
  { destruct E as [v V]. revert V => /eqP-V. by exists v. }
  apply /sigW.
  apply (well_founded_ind (R := @is_connected_strict_rev _ _ G)).
  { apply (@well_founded_dam_rev _ _ G). }
  2:{ apply exists_node. }
  intros v H.
  destruct (vlabel v) eqn:V.
  - exists v. by apply /eqP.
  - apply (H (source (left_tens V))).
    unfold is_connected_strict_rev, is_connected_strict.
    exists [:: left_tens V]. splitb; apply /eqP.
    apply left_e.
  - apply (H (source (left_parr V))).
    unfold is_connected_strict_rev, is_connected_strict.
    exists [:: left_parr V]. splitb; apply /eqP.
    apply left_e.
  - destruct (p_cut V) as [e [_ [E _]]].
    rewrite !in_set in E.
    apply (H (source e)).
    unfold is_connected_strict_rev, is_connected_strict.
    exists [:: e]. splitb.
  - apply (H (source (edge_of_concl V))).
    unfold is_connected_strict_rev, is_connected_strict.
    exists [:: edge_of_concl V]. splitb; apply /eqP.
    apply concl_e.
Qed.


Lemma card_edge_proof_net (G : proof_net) : #|edge G| >= 2.
Proof.
  destruct (has_ax G) as [v V].
  assert (C := pre_proper_ax V).
  assert (#|edges_at_out v| <= #|edge G|)
    by apply subset_leq_card, subset_predT.
  lia.
Qed.

Definition terminal (G : base_graph) (v : G) : bool :=
  match vlabel v with
  | c => false
  | _ => [forall e, (source e == v) ==> (vlabel (target e) == c)]
  end.

Lemma terminal_not_c (G : base_graph) (v : G) :
  vlabel v <> c ->
  terminal v = [forall e, (source e == v) ==> (vlabel (target e) == c)].
Proof. unfold terminal. by destruct (vlabel v). Qed.

Lemma not_terminal (G : base_graph) (v : G) :
  vlabel v <> c -> ~~ terminal v ->
  {e : edge G & source e = v /\ vlabel (target e) <> c}.
Proof.
  intros V T.
  enough (E : {e : edge G & (source e == v) && (vlabel (target e) != c)}).
  { destruct E as [e E]. revert E; introb. by exists e. }
  apply /sigW.
  rewrite terminal_not_c // in T.
  revert T => /forallPn[e]. rewrite negb_imply => /andP[/eqP-Se /eqP-E].
  exists e. splitb; by apply /eqP.
Qed.

Lemma terminal_source (G : proof_structure) (v : G) :
  terminal v -> forall e, source e = v -> vlabel (target e) = c.
Proof.
  intros T e E.
  rewrite terminal_not_c in T.
  2:{ intro F. contradict E. by apply no_source_c. }
  revert T => /forallP/(_ e) /implyP-T.
  by apply /eqP; apply T; apply /eqP.
Qed.

Lemma terminal_cut (G : proof_structure) (v : G) (H : vlabel v = cut) :
  terminal v.
Proof.
  rewrite /terminal H.
  apply /forallP => e. apply /implyP => /eqP-E.
  contradict E.
  by apply no_source_cut.
Qed.

Lemma terminal_tens_parr (G : proof_structure) (v : G) (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  terminal v = (vlabel (target (ccl H)) == c).
Proof.
  transitivity [forall e, (source e == v) ==> (vlabel (target e) == c)].
  { rewrite /terminal. by destruct H as [-> | ->]. }
  destruct (vlabel (target (ccl H)) == c) eqn:C.
  - apply /forallP => e. apply /implyP => /eqP-E.
    enough (e = ccl H) by by subst e.
    by apply ccl_eq.
  - apply /negP => /forallP/(_ (ccl H))/implyP-P.
    rewrite ccl_e in P.
    revert C => /eqP-C. contradict C. apply /eqP.
    by apply P.
Qed.

Lemma has_terminal (G : proof_net) : { v : G & terminal v }.
Proof.
  apply /sigW.
  apply (well_founded_induction (wf_inverse_image _ _ _
    (@projT1 _ (fun v => vlabel v <> c)) (@well_founded_dam _ _ G))).
  2:{ exact (exists_node G). }
  move => [v V] /= H.
  destruct (terminal v) eqn:T.
  { by exists v. }
  revert T => /negP/negP-T.
  elim: (not_terminal V T) => {T} [e [? E]]. subst v.
  apply (H (existT _ (target e) E)).
  rewrite /is_connected_strict /=.
  exists [:: e]. splitb.
Qed.

Lemma in_upath_of_path {Lv Le : Type} {G : graph Lv Le} (p : path) (e : edge G) (b : bool) :
  (e, b) \in upath_of_path p = (e \in p) && b.
Proof.
  destruct b; [destruct (e \in p) eqn:E | ]; rewrite /= ?andb_false_r; apply /mapP.
  - by exists e.
  - move => [a A AE]. inversion AE. subst a. by rewrite A in E.
  - by move => [? _ ?].
Qed.

Lemma walk_is_supath {G : proof_structure} {s t : G} {p : path} :
  walk s t p -> supath switching s t p.
Proof.
  revert s t. induction p as [ | p e IH] using last_ind => s t /=.
  { by rewrite supath_of_nil. }
  rewrite walk_rcons => /andP[W /eqP-?]. subst t.
  specialize (IH _ _ W).
  replace (upath_of_path (rcons p e)) with (rcons (upath_of_path p) (forward e)).
  2:{ clear. induction p as [ | ? ? IH]; trivial. by rewrite /= IH. }
  rewrite supath_rcons /= {}IH eq_refl /= andb_true_r.
  enough (Ain : forall a, a \in p -> target a <> target e).
  { clear W.
    apply /mapP. move => [[a b] A EA].
    revert A. rewrite in_upath_of_path => /andP[A B]. destruct b; try by []. clear B.
    specialize (Ain _ A). clear A.
    revert EA. move => /eqP. unfold switching. case_if.
    contradict Ain. by symmetry. }
  intros a A AE.
  rewrite in_elt_sub in A. revert A => /existsP/sigW[[n /= _] /eqP-A].
  revert W.
  rewrite A.
  replace (take n p ++ a :: drop n.+1 p) with ((take n p ++ [:: a]) ++ drop n.+1 p)
    by by rewrite -catA cat_cons.
  intro W.
  apply walk_subK in W. destruct W as [_ W].
  revert W => /= /andP[_ W].
  rewrite AE in W.
  assert (W' : walk (source e) (source e) (e :: drop n.+1 p)) by splitb.
  by assert (F := @acy _ _ G _ _ W').
Qed.


(** * About axiom expansion *)
Lemma ax_formula_pos (G : proof_structure) (v : G) (V : vlabel v = ax) :
  { x | ax_formula V = var x } + { '(A, B) | ax_formula V = A ⊗ B }.
Proof.
  destruct (ax_formula V) as [x | x | A B | A B] eqn:Hv.
  - left. by exists x.
  - contradict Hv.
    unfold ax_formula, ax_formula_edge.
    destruct (p_ax_type V) as [[e e'] [? [? ?]]]. simpl.
    destruct (flabel e) eqn:E, (flabel e') eqn:E'; by rewrite // ?E ?E'.
  - right. by exists (A, B).
  - contradict Hv.
    unfold ax_formula, ax_formula_edge.
    destruct (p_ax_type V) as [[e e'] [? [? ?]]]. simpl.
    destruct (flabel e) eqn:E, (flabel e') eqn:E'; by rewrite // ?E ?E'.
Qed.

Lemma ax_cut_formula_edge_in (G : proof_structure) (b : bool) (v : G)
  (V : vlabel v = if b then cut else ax) :
  endpoint b (ax_cut_formula_edge V) = v.
Proof.
  unfold ax_cut_formula_edge.
  destruct (p_ax_cut_type V) as [[e e'] [? [? ?]]]. simpl.
  by destruct (flabel e).
Qed.

Lemma ax_cut_formula_endpoint (G : proof_structure) (b : bool) (v : G)
  (V : vlabel v = if b then cut else ax) :
  vlabel (endpoint b (ax_cut_formula_edge V)) = if b then cut else ax.
Proof. rewrite -V. f_equal. apply ax_cut_formula_edge_in. Qed.


(* About upath_disjoint2 *)
(* TOTHINK useful lemma? to use before too *)
Lemma upath_non_disjoint2 {G : proof_net} {v : G} e (p q : upath) :
  ~~(upath_disjoint2 p q) -> upath_target v p = upath_source v q ->
  last e p <> head e q -> 
  exists p_pre p_post q_pre q_post, p = p_pre ++ p_post /\ q = q_pre ++ q_post /\
  upath_disjoint2 p_post q_pre /\
  upath_target v p_post = upath_source v q_pre /\
  upath_source v p_post = upath_target v q_pre /\
  p_post <> [::] /\ q_pre <> [::].
Proof.
  intros D TS LH.
  assert (E : [exists e, (e \in [seq a.1 | a <- p]) && (e \in [seq a.1 | a <- q])]).
  { clear -D.
    rewrite -(@negb_involutive [exists e, (e \in [seq a.1 | a <- p]) && (e \in [seq a.1 | a <- q])]).
    apply /negP => /existsPn-H.
    revert D => /disjointP-D. contradict D.
    intros e Ep Eq.
    specialize (H e). by rewrite Ep Eq in H. }
  clear D. revert E => /existsP/sigW[a /andP[Ap Aq]].
  apply in_map_fst in Ap. destruct Ap as [b Ap].
  destruct (@in_elt_sub_last _ _ (fun f => f.1 \in [seq e.1 | e <- q]) (a, b) Aq Ap)
    as [n [(x, xb) [Peq [Xin Xlast]]]].
  clear a b Ap Aq. simpl in Xin.
  apply in_map_fst in Xin. destruct Xin as [bp Xin].
  assert (Xr : (x, bp).1 == x) by trivial.
  destruct (@in_elt_sub_fst _ _ (fun f => f.1 == x) (x, bp) Xr Xin) as [k [(y, bq) [Qeq [Yeq Xfst]]]].
  revert Yeq => /= /eqP-?. subst y.
(* TODO là si bq, il faut prendre x dans q_pre, sinon ne pas le prendre (ni dans p_post) *)
Abort.

End Atoms.

Notation ax_formula_edge_in := (@ax_cut_formula_edge_in _ _ false).
Notation cut_formula_edge_in := (@ax_cut_formula_edge_in _ _ true).
Notation ax_formula_endpoint := (@ax_cut_formula_endpoint _ _ false).
Notation cut_formula_endpoint := (@ax_cut_formula_endpoint _ _ true).
