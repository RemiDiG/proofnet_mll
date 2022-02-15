(* Unit-free MLL following Yalla schemas *)
(* Basic results on proof nets *)

From Coq Require Import Bool Wellfounded.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.
From HB Require Import structures.

From Yalla Require Export mll_prelim graph_more mgraph_dag mll_def.

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
Lemma no_selfloop (G : proof_structure) : forall (e : edge G), source e <> target e.
Proof.
  intros e H.
  assert (W := walk_edge e). rewrite H in W.
  now assert (F := ps_acyclic W).
Qed.



(** * Properties on switching & switching_left *)
Lemma switching_eq (G : base_graph) :
  forall (a b : edge G), switching a = switching b -> target a = target b.
Proof.
  intros ? ?. unfold switching => /eqP; cbn => /eqP.
  case: ifP; case: ifP; by move => // _ _ /eqP; cbn => /eqP ->.
Qed.

Lemma switching_None (G : base_graph) :
  forall (p : @upath _ _ G), None \notin [seq switching e.1 | e <- p].
Proof. intro p. by induction p. Qed.

Lemma switching_left_sinj {G : base_graph} :
  {in ~: (@switching_left G) @^-1 None &, injective switching_left}.
Proof.
  move => a b; rewrite !in_set => A B /eqP; revert A B.
  unfold switching_left; case_if.
Qed.

Lemma swithching_to_left_eq {G : proof_structure} :
  forall (a b : edge G), switching_left a <> None -> switching_left b <> None ->
  switching a = switching b -> switching_left a = switching_left b.
Proof.
  move => a b A B S.
  assert (T := switching_eq S).
  apply /eqP; revert S A B => /eqP.
  rewrite /switching/switching_left T; cbn.
  case_if; apply /eqP.
  assert (llabel a) by (by apply /negPn);
  assert (llabel b) by by apply /negPn.
  assert (Bl : vlabel (target b) = ⅋) by by apply /eqP.
  transitivity (left_parr Bl); [ | symmetry];
  by apply left_eq.
Qed.

Lemma supath_switching_from_leftK {G : proof_structure} :
  forall (u v : G) p, supath switching_left u v p ->
  supath switching u v p.
Proof.
  move => u v p /andP[/andP[? U] N].
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
Proof.
  intros ? [? ?]. split; trivial.
  apply uconnected_to_nb1; trivial. apply switching_left_sinj.
Qed.

Lemma correct_to_weak (G : base_graph) :
  correct G -> correct_weak G.
Proof.
  intros [? ?]. split; trivial.
  apply uconnected_from_nb1; trivial. apply switching_left_sinj.
Qed.

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



(** * Isomorphism for each strata *)
(** Correction is preserved by isomorphism on base graphs *)
Definition switching_map (F G : base_graph) (h : F ≃ G) :=
  fun e => match e with
  | Some (inl a) => Some (inl (h.e a))
  | Some (inr a) => Some (inr (h a))
  | None => None
 end.

Lemma iso_switching (F G : base_graph) (h : F ≃ G) :
  forall e, switching (h.e e) = switching_map h (switching e).
Proof.
  intro e; cbnb.
  rewrite !endpoint_iso iso_noflip vlabel_iso; cbn.
  by destruct (vlabel (target e)) eqn:Hl; rewrite Hl; case_if.
Qed.

Lemma iso_switching_left (F G : base_graph) (h : F ≃ G) :
  forall e, switching_left (h.e e) = option_map h.e (switching_left e).
Proof.
  intros.
  rewrite /switching_left/switching_left endpoint_iso iso_noflip vlabel_iso llabel_iso.
  case_if.
Qed.


Lemma iso_path_switchingK (F G : base_graph) (h : F ≃ G) : forall p s t,
  supath switching s t p -> supath switching (h s) (h t) (iso_path h p).
Proof.
  move => p s t /andP[/andP[W U] N]. splitb.
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

Lemma iso_path_switching_inj (F G : base_graph) (h : F ≃ G) :
  forall s t, injective (@iso_path_switching _ _ h s t).
Proof.
  move => s t [p P] [q Q] /eqP; cbn => /eqP Heq; cbnb.
  revert Heq; apply inj_map => [[e b] [f c]] /eqP; cbn => /andP[/eqP Heq /eqP ->].
  apply /eqP; splitb; cbn; apply /eqP.
  by revert Heq; apply bij_injective.
Qed.

Lemma iso_path_nil (F G : base_graph) (h : F ≃ G) :
  forall (s : F), iso_path_switching h (supath_nil switching s) = supath_nil switching (h s).
Proof. intros. by apply /eqP. Qed.

Lemma iso_path_switching_leftK (F G : base_graph) (h : F ≃ G) : forall p s t,
  supath switching_left s t p -> supath switching_left (h s) (h t) (iso_path h p).
Proof.
  move => p s t /andP[/andP[W U] N].
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

Lemma order_iso_weak (F G : proof_structure) : forall (h : F ≃ G),
  forall e, e \in order F <-> h.e e \in order G.
Proof.
  intros h e.
  destruct (p_order F) as [? _].
  destruct (p_order G) as [? _].
  transitivity (vlabel (target e) = c); [by symmetry | ].
  by replace (vlabel (target e)) with (vlabel (target (h.e e)))
    by by rewrite endpoint_iso iso_noflip vlabel_iso.
Qed.

Definition order_iso_perm (F G : proof_structure) : forall (h : F ≃ G),
  Permutation_Type (order G) [seq h.e e | e <- order F].
Proof.
  intro h.
  destruct (p_order F) as [_ ?].
  destruct (p_order G) as [_ ?].
  by apply Permutation_Type_bij_uniq, order_iso_weak.
Defined.

Lemma sequent_iso_weak (F G : proof_structure) :
  forall (h : F ≃ G),
  sequent F = [seq flabel e | e <- [seq h.e e | e <- order F]].
Proof.
  intro h. rewrite /sequent -map_comp. apply eq_map => ? /=. by rewrite flabel_iso.
Qed.

Definition sequent_iso_perm (F G : proof_structure) : F ≃ G ->
  Permutation_Type (sequent G) (sequent F).
Proof.
  intro h.
  rewrite (sequent_iso_weak h).
  exact (Permutation_Type_map_def _ (order_iso_perm h)).
Defined.

Lemma perm_of_sequent_iso_perm (F G : proof_structure) :
  forall (h : F ≃ G),
  perm_of (sequent_iso_perm h) (order G) = [seq h.e e | e <- order F].
Proof.
  intros. by rewrite -(perm_of_consistent (order_iso_perm _)) perm_of_rew_r
    perm_of_Permutation_Type_map.
Qed.
(* TODO lemma iso_to_isod ici ? Nécressite d'y mettre perm_graph aussi *)
(* TODO si besoin de proprietes comme left (h ) = h left, les mettre ici *)



(** * Some results about rule carninality rcard *)
Lemma rset_bij {F G : base_graph} (h : F ≃ G) :
  [set h v | v : F & vlabel v == c] = [set v | vlabel v == c].
Proof. apply setP => v. by rewrite -[in LHS](bijK' h v) bij_imset_f !in_set (vlabel_iso (iso_sym h)). Qed.

Lemma rset_bij_in {F G : base_graph} (h : F ≃ G) :
  forall (v : sig_finType (pred_of_set (~: [set v : F | vlabel v == c]))),
    h (val v) \in ~: [set v : G | vlabel v == c].
Proof. intros []. by rewrite -(rset_bij h) bij_imsetC bij_imset_f. Qed.

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
Qed.


(** * Useful results for sequentialization *)
Lemma has_ax (G : proof_net) : { v : G & vlabel v == ax }.
Proof.
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

Lemma descending_couple (G : proof_net) :
  forall (s : G), vlabel s <> c ->
  { '(t, p) : G * path & walk s t p & terminal t }.
Proof.
  intros s S.
  apply (well_founded_induction_type (wf_inverse_image _ _ _
    (@projT1 _ (fun v => {p : path & walk s v p /\ vlabel v <> c})) (@well_founded_dam _ _ G))).
  2:{ exists s, [::]. by simpl. }
  move => [t [p [W C]]] H.
  destruct (terminal t) eqn:T.
  { now exists (t, p). }
  revert T => /negP/negP T.
  elim: (not_terminal C T) => {T} [e [? E]]. subst t.
  assert (W' : walk s (target e) (rcons p e)) by (rewrite walk_rcons; splitb).
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

Lemma descending_walk (G : proof_net) (s : G) (S : vlabel s <> c) :
  walk s (descending_node S) (descending_path S).
Proof. unfold descending_path, descending_node. by destruct (descending_couple _) as [[? ?] ? _]. Qed.

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
  assert (W := descending_walk S).
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
Abort. (* TODO si besoin *)


(** * About axiom expansion *)
Lemma ax_formula_pos (G : proof_net) (v : G) (V : vlabel v = ax) :
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

Lemma ax_cut_formula_edge_in (G : proof_net) (b : bool) (v : G)
  (V : vlabel v = if b then cut else ax) :
  endpoint b (ax_cut_formula_edge V) = v.
Proof.
  unfold ax_cut_formula_edge.
  destruct (p_ax_cut_type V) as [[e e'] [? [? ?]]]. simpl.
  by destruct (flabel e).
Qed.

End Atoms.

Notation ax_formula_edge_in := (@ax_cut_formula_edge_in _ _ false).
Notation cut_formula_edge_in := (@ax_cut_formula_edge_in _ _ true).
