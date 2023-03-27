(* Unit-free MLL following Yalla schemas *)
(* Basic results on proof nets *)

From Coq Require Import Bool Wellfounded.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.
From HB Require Import structures.

From Yalla Require Export mll_prelim graph_more graph_uconnected_nb mgraph_dag mll_def.

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
  assert (Bl : vlabel (target b) = ⅋) by by apply /eqP.
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

Definition supath_switching_from_left {G : proof_structure} (s t : G) (p : Supath switching_left s t) :=
  {| upval := _ ; upvalK := supath_switching_from_leftK (upvalK p) |}.

Lemma uacyclic_swithching_left {G : proof_structure} :
  uacyclic (@switching G) -> uacyclic (@switching_left G).
Proof.
  move => A u P.
  specialize (A _ (supath_switching_from_left P)).
  cbnb. by revert A => /eqP; cbn => /eqP.
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
  assert (Hf : forall E : [finType of {e : edge G | (vlabel (target e) == ⅋) && (~~llabel e)}],
    (vlabel (target (val E)) == ⅋)).
  { by intros [e E]; cbn; revert E => /andP[E _]. }
  set f : [finType of {e : edge G | (vlabel (target e) == ⅋) && (~~llabel e)}] ->
    [finType of {v | vlabel v == ⅋}] :=
    fun e => Sub (target (val e)) (Hf e).
  assert (Hg : forall E : [finType of {v : G | vlabel v == ⅋}],
    (vlabel (target (right_parr (eqP (valP E)))) == ⅋) && (~~llabel (right_parr (eqP (valP E))))).
  { intros [e E]; splitb.
    - by rewrite right_e.
    - apply right_l. }
  set g : [finType of {v | vlabel v == ⅋}] ->
    [finType of {e : edge G | (vlabel (target e) == ⅋) && (~~llabel e)}] :=
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

Lemma supath_from_induced_switching (G : base_graph) (S : {set G}) s t (p : Supath (@switching (induced S)) s t) :
  supath (@switching G) (val s) (val t) [seq (val a.1, a.2) | a <- upval p].
Proof.
  apply supath_from_induced.
  - intros ? ? _. case_if.
  - move => ? ? ? ? /eqP-F. apply /eqP. revert F. unfold switching. case_if.
Qed.

Lemma uacyclic_induced (G : base_graph) (S : {set G}) :
  uacyclic (@switching G) -> uacyclic (@switching (induced S)).
Proof.
  intros U ? p.
  specialize (U _ {| upvalK := supath_from_induced_switching p |}).
  destruct p as [p ?]. cbnb. by destruct p.
Qed.

Lemma supath_from_induced_switching_left (G : base_graph) (S : {set G}) s t
  (p : Supath (@switching_left (induced S)) s t) :
  supath (@switching_left G) (val s) (val t) [seq (val a.1, a.2) | a <- upval p].
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
  fun p => {| upval := _ ; upvalK := iso_path_switchingK h (upvalK p) |}.

Lemma iso_path_switching_inj (F G : base_graph) (h : F ≃ G) s t :
  injective (@iso_path_switching _ _ h s t).
Proof.
  move => [p P] [q Q] /eqP; cbn => /eqP Heq; cbnb.
  revert Heq; apply inj_map => [[e b] [f c]] /eqP; cbn => /andP[/eqP Heq /eqP ->].
  apply /eqP; splitb; cbn; apply /eqP.
  by revert Heq; apply bij_injective.
Qed.

Lemma iso_path_nil (F G : base_graph) (h : F ≃ G) (s : F) :
  iso_path_switching h (supath_nil switching s) = supath_nil switching (h s).
Proof. by apply /eqP. Qed.

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
    all: by replace (vlabel (target e) == ⅋) with true; replace (~~llabel e) with true.
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
  fun p => {| upval := _ ; upvalK := iso_path_switching_leftK h (upvalK p) |}.

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



(** * Some results about rule carninality rcard *)(*
Lemma rset_bij {F G : base_graph} (h : F ≃ G) :
  [set h v | v : F & vlabel v == c] = [set v | vlabel v == c].
Proof. apply setP => v. by rewrite -[in LHS](bijK' h v) bij_imset_f !in_set (vlabel_iso (iso_sym h)). Qed.

Lemma rset_bij_in {F G : base_graph} (h : F ≃ G)
  (v : sig_finType (pred_of_set (~: [set v : F | vlabel v == c]))) :
  h (val v) \in ~: [set v : G | vlabel v == c].
Proof. destruct v. by rewrite -(rset_bij h) bij_imsetC bij_imset_f. Qed.

Lemma rcard_iso (F G : base_graph) :
  F ≃ G -> r#|F| = r#|G|.
Proof.
  intro h.
  rewrite /rcard -card_sig -[in RHS]card_sig.
  set f : sig_finType (pred_of_set (~: [set v : F | vlabel v == c])) ->
    sig_finType (pred_of_set (~: [set v : G | vlabel v == c])) :=
    fun v => Sub (h (val v)) (rset_bij_in h v).
  set g : sig_finType (pred_of_set (~: [set v : G | vlabel v == c])) ->
    sig_finType (pred_of_set (~: [set v : F | vlabel v == c])) :=
    fun v => Sub (h^-1 (val v)) (rset_bij_in (iso_sym h) v).
  apply (bij_card_eq (f := f)), (Bijective (g := g)); unfold f, g.
  - intros [v V]. cbnb. apply bijK.
  - intros [v V]. cbnb. apply bijK'.
Qed.

Lemma union_rcard (F G : base_graph) : r#|F ⊎ G| = r#|F| + r#|G|.
Proof.
  rewrite /rcard.
  assert (~: [set v : F ⊎ G | vlabel v == c] = ~: [set v : F ⊎ G | match v with | inl v => vlabel v == c | inr _ => true end]
    :|: ~: [set v : F ⊎ G | match v with | inr v => vlabel v == c | inl _ => true end]) as ->.
  { apply /setP. by intros [? | ?]; rewrite !in_set ?orb_false_r. }
  rewrite cardsU.
  assert (~: [set v : F ⊎ G | match v with | inl v => vlabel v == c | inr _ => true end]
    :&: ~: [set v : F ⊎ G | match v with | inl _ => true | inr v => vlabel v == c end] = set0) as ->.
  { apply /setP. by intros [? | ?]; rewrite !in_set ?andb_false_r. }
  rewrite cards0.
  enough ((~: [set v : F ⊎ G | match v with | inl v => vlabel v == c | inr _ => true end] =
    inl @: ~: [set v : F | vlabel v == c]) /\
    ~: [set v : F ⊎ G | match v with | inr v => vlabel v == c | inl _ => true end] =
    inr @: ~: [set v : G | vlabel v == c]) as [-> ->].
  { rewrite !card_imset; try by (apply inl_inj || apply inr_inj). lia. }
  split; apply /setP; intros [v | v].
  all: rewrite ?mem_imset ?in_set //; try by (apply inl_inj || apply inr_inj).
  all: symmetry; simpl.
  all: apply /imsetP; by move => [? _ /eqP-Hf].
Qed.

Lemma add_edge_rcard (G : base_graph) u v A :
  r#|G ∔ [u, A, v]| = r#|G|.
Proof. trivial. Qed.

Lemma unit_graph_rset R :
  R <> c -> [set v : (unit_graph R : base_graph) | vlabel v == c] = set0.
Proof.
  intros. apply /setP => v.
  rewrite !in_set. destruct v; by apply /eqP.
Qed.

Lemma unit_graph_rcard R :
  R <> c -> r#|(unit_graph R : base_graph)| = 1.
Proof. intros. by rewrite /rcard cardsCs setCK unit_graph_rset // cards0 /= card_unit. Qed.

Lemma two_graph_rset R :
  R <> c -> [set v : (two_graph R c : base_graph) | vlabel v == c] = [set inr tt].
Proof.
  intros. apply /setP => v.
  rewrite !in_set /=. destruct v as [[] | []]; by apply /eqP.
Qed.

Lemma two_graph_rcard R :
  R <> c -> r#|(two_graph R c : base_graph)| = 1.
Proof. intros. by rewrite /rcard cardsCs setCK /= card_sum card_unit two_graph_rset // cards1. Qed.

Lemma rem_rcard (G : base_graph) (v : G) S :
  vlabel v = c -> r#|induced (S :\ v)| = r#|induced S|.
Proof.
  intro V.
  rewrite /rcard -card_sig -[in RHS]card_sig.
  assert (Hf : forall (u : sig_finType (pred_of_set (~: [set u : induced (S :\ v) | vlabel u == c]))),
    val (val u) \in S).
  { move => [[u I] /= _]. revert I. by rewrite in_set => /andP[_ I]. }
  assert (Hf' : forall (u : sig_finType (pred_of_set (~: [set u : induced (S :\ v) | vlabel u == c]))),
    Sub (val (val u)) (Hf u) \in ~: [set u : induced S | vlabel u == c]).
  { move => [[u I] U] /=.
    rewrite !in_set /=. by rewrite -in_set finset_of_pred_of_set !in_set /= in U. }
  set f : sig_finType (pred_of_set (~: [set u : induced (S :\ v) | vlabel u == c])) ->
    sig_finType (pred_of_set (~: [set u : induced S | vlabel u == c])) :=
    fun u => Sub (Sub (val (val u)) (Hf u)) (Hf' u).
  assert (Hg : forall (u : sig_finType (pred_of_set (~: [set u : induced S | vlabel u == c]))),
    val (val u) \in S :\ v).
  { move => [[u I] U] /=.
    rewrite !in_set /=. rewrite -in_set finset_of_pred_of_set !in_set /= in U.
    splitb. apply /eqP => ?; subst u. contradict V. by apply /eqP. }
  assert (Hg' : forall (u : sig_finType (pred_of_set (~: [set u : induced S | vlabel u == c]))),
    Sub (val (val u)) (Hg u) \in ~: [set u : induced (S :\ v) | vlabel u == c]).
  { move => [[u I] U] /=.
    rewrite !in_set /=. by rewrite -in_set finset_of_pred_of_set !in_set /= in U. }
  set g : sig_finType (pred_of_set (~: [set u : induced S | vlabel u == c])) ->
    sig_finType (pred_of_set (~: [set u : induced (S :\ v) | vlabel u == c])) :=
    fun u => Sub (Sub (val (val u)) (Hg u)) (Hg' u).
  apply (bij_card_eq (f := f)), (Bijective (g := g)); intros [[u I] U]; cbnb.
Qed.*)


(** * About strong paths *)(* TODO need its own file? *)
(* A switching path is strong if it does not start from a ⅋-vertex through
   one of its switch edges *)
(* More general definition on path for it to be more simply manipulated *)
Definition strong {G : base_graph} (p : @upath _ _ G) : bool :=
  match p with
  | [::] => true
  | e :: _ => (vlabel (usource e) != ⅋) || e.2
  end.
(* TODO or := head true [seq (vlabel (utarget e) != ⅋) || e.2 | e <- p]. ? *)

Lemma concat_strong {G : base_graph} (p q : @upath _ _ G) :
  strong p -> strong q -> strong (p ++ q).
Proof. by destruct p. Qed.

Lemma supath_prefixK {G : base_graph} (s t : G) (p q : upath) :
  supath switching s t (p ++ q) -> supath switching s (upath_target s p) p.
Proof. apply supath_subKK. Defined.

Definition supath_prefix {G : base_graph} (s t : G) (p q : upath) (H : supath switching s t (p ++ q)) :=
  {| upval := p ; upvalK := supath_prefixK H |}. (* TODO can be generalized *)

Lemma prefix_strong {G : base_graph} (p q : @upath _ _ G) :
  strong (p ++ q) -> strong p.
Proof. by destruct p. Qed.
(*
Definition strong {G : base_graph} {u v : G} (P : Supath switching u v) : bool :=
  match upval P with
  | [::] => true
  | e :: _ => (vlabel (usource e) != ⅋) || e.2
  end.

Lemma concat_strong {G : base_graph} {s i t : G} (P : Supath switching s i)
  (Q : Supath switching i t) (D : upath_disjoint switching P Q) :
  strong P -> strong Q -> strong (supath_cat D).
Proof. by destruct P as [[ | ? ?] ?], Q as [[ | ? ?] ?]. Qed.

Lemma prefix_strong {G : base_graph} {s t : G} (p q : upath) (H : supath switching s t (p ++ q)) :
  strong {| upvalK := H |} -> strong (supath_prefix H).
Proof. by destruct p. Qed.
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
  apply in_elt_sub in A. destruct A as [n A].
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

Lemma descending_couple (G : proof_net) (s : G) :
  vlabel s <> c -> { '(t, p) : G * path & walk s t p & terminal t }.
Proof.
  intro S.
  apply (well_founded_induction_type (wf_inverse_image _ _ _
    (@projT1 _ (fun v => {p : path & walk s v p /\ vlabel v <> c})) (@well_founded_dam _ _ G))).
  2:{ exists s, [::]. by simpl. }
  move => [t [p [W C]]] H.
  destruct (terminal t) eqn:T.
  { now exists (t, p). }
  revert T => /negP/negP-T.
  elim: (not_terminal C T) => {T} [e [? E]]. subst t.
  assert (W' : walk s (target e) (rcons p e : path)).
  { rewrite walk_rcons. splitb. }
  apply (H ⟨ target e, ⟨ rcons p e, conj W' E ⟩ ⟩).
  exists [:: e]. splitb.
Qed.

(* Terminal node below the node s *)
Definition descending_node (G : proof_net) (s : G) (S : vlabel s <> c) :=
  let (tp, _, _) := descending_couple S in let (t, _) := tp in t.

Lemma descending_node_terminal (G : proof_net) (s : G) (S : vlabel s <> c) :
  terminal (descending_node S).
Proof. unfold descending_node. by destruct (descending_couple _) as [[? _] _ ?]. Qed.

Definition descending_path (G : proof_net) (s : G) (S : vlabel s <> c) :=
  let (tp, _, _) := descending_couple S in let (_, p) := tp in p.

Lemma descending_supath {G : proof_net} {s : G} (S : vlabel s <> c) :
  supath switching s (descending_node S) (descending_path S).
Proof.
  unfold descending_path, descending_node. destruct (descending_couple _) as [[? ?] ? _].
  by apply walk_is_supath.
Qed.

(* A descending path is a strong path *)
Lemma descending_path_strong {G : proof_net} {s : G} (S : vlabel s <> c) :
  strong {| upvalK := descending_supath S |}.
Proof. unfold strong. simpl. destruct (descending_path S); caseb. Qed.

Lemma descending_path_nil (G : proof_net) (s : G) (S : vlabel s <> c) :
  (descending_path S == [::]) = (descending_node S == s).
Proof.
  unfold descending_path, descending_node.
  destruct (descending_couple _) as [[t p] W _].
  destruct (eq_comparable t s) as [ | Hneq]; [subst t | ].
  - by rewrite (ps_acyclic W) !eq_refl.
  - transitivity false; last by symmetry; apply /eqP.
    destruct p; last by by [].
    contradict Hneq. by revert W => /= /eqP-->.
Qed.

Lemma descending_path_terminal (G : proof_net) (s : G) (S : vlabel s <> c) :
  terminal s = (descending_node S == s).
Proof.
  rewrite -descending_path_nil.
  unfold descending_path, descending_node.
  destruct (descending_couple _) as [[t p] W T].
  destruct p as [ | e p].
  { revert W => /= /eqP-?. by subst s. }
  destruct (terminal s) eqn:Ts; last by by [].
  revert W => /= /andP[/eqP-E W].
  assert (H := terminal_source Ts E).
  destruct p as [ | f p].
  - revert W => /= /eqP-?. subst t.
    contradict T. by rewrite /terminal H.
  - revert W => /= /andP[/eqP-F _].
    contradict F. by apply no_source_c.
Qed.

Lemma descending_node_ax (G : proof_net) (s : G) (S : vlabel s <> c) :
  vlabel (descending_node S) = ax -> terminal s.
Proof.
  intro V.
  rewrite descending_path_terminal -descending_path_nil.
  assert (W := descending_supath S). revert W => /andP[/andP[W _] _]. rewrite uwalk_walk in W.
  revert W. set p := descending_path S. case/lastP: p => [ | p e] //.
  rewrite walk_rcons => /andP[_ /eqP-TS].
  contradict TS. by apply no_target_ax.
Qed.

Lemma descending_not_ax (G : proof_net) (s : G) (S : vlabel s <> c) :
  vlabel s <> ax -> vlabel (descending_node S) <> ax.
Proof.
  intros S' F. contradict S'.
  assert (H := descending_node_ax F).
  revert H. by rewrite descending_path_terminal => /eqP-<-.
Qed.

Lemma terminal_only_ax (G : proof_net) :
  (forall (v : G), vlabel v = ax \/ vlabel v = c) ->
  { t : G & terminal t /\ vlabel t = ax}.
Proof.
Abort. (* TODO if needed *)


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
(* TODO un fichier strong et upath_disjoint2 ? *)
Lemma strong_upath_disjoint_switching {G : proof_net} {s i t : G} (P : Supath switching s i)
  (Q : Supath switching i t) :
  (t \notin [seq usource e | e <- (upval P)]) || (vlabel t != ⅋) ->
  strong P -> strong Q -> upath_disjoint2 P Q -> forall a b, a \in upval P -> b \in upval Q ->
switching a.1 <> switching b.1.
Proof.
(* The first hypothesis is really needed, unless we replace edge-disjoint (upath_disjoint2) by
vertex-disjoint. *)
(* Proof sketch :
Otherwise, we take a the last edge of P and b the first of Q with the same image by switching,
with P' and Q' respectively P from a to its end, and Q from its start to b.
Then P' Q' is a switching cycle, non empty as P and Q are strong. *)
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
      clear QN. rewrite {}QN' in Q. apply supath_subK in Q.
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
      clear PK. rewrite {}PK' in P. apply supath_subK in P.
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
  { destruct (p_correct G) as [Ac _].
    assert (F := Ac _ (supath_cat D)). contradict F.
    cbnb. }
  rewrite /upath_disjoint /=.
  apply /disjointP => f /mapP[x Xq ?] /mapP[y Yp]. subst f.
  by apply Kl.
Qed.

(* If two strong path are edge-disjoint, and the target of the second is not
a ⅋-vertex inside the first, then they are switching-disjoint, meaning
we can concatenate them to obtain a switching path. *)
Lemma strong_upath_disjoint2 {G : proof_net} {s i t : G} (P : Supath switching s i)
  (Q : Supath switching i t) :
  (t \notin [seq usource e | e <- (upval P)]) || (vlabel t != ⅋) ->
  strong P -> strong Q -> upath_disjoint2 P Q -> upath_disjoint switching P Q.
Proof.
  intros T SP SQ D.
  rewrite /upath_disjoint.
  apply /disjointP.
  move => E /mapP[a A AE] /mapP[b B BE]. subst E.
  contradict BE. by apply (strong_upath_disjoint_switching T SP SQ).
Qed.

Lemma strong_rev {G : base_graph} (p : @upath _ _ G) :
  strong (upath_rev p) = last true [seq (vlabel (utarget e) != ⅋) || ~~e.2 | e <- p].
Proof.
  case: (lastP p) => {p} [ // | p e].
  by rewrite upath_rev_rcons map_rcons last_rcons /= negb_involutive.
Qed.

End Atoms.

Notation ax_formula_edge_in := (@ax_cut_formula_edge_in _ _ false).
Notation cut_formula_edge_in := (@ax_cut_formula_edge_in _ _ true).
Notation ax_formula_endpoint := (@ax_cut_formula_endpoint _ _ false).
Notation cut_formula_endpoint := (@ax_cut_formula_endpoint _ _ true).
