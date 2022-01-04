(* Sequentialisation *)
(* From a Proof Net, return a LL proof of the same sequent *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export graph_more mll_prelim mll_def mll_seq_to_pn.

Import EqNotations.

Set Mangle Names.
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

Definition iso_to_isod (F G : proof_structure) : forall (h : F ≃ G),
  F ≃d perm_graph_data G (p_order_iso_weak h).
Proof.
  intros. eexists; simpl. apply perm_of_p_order_iso_weak.
Defined.

(* sequentialisation : fonction reliant regles à noeuds => nb cut + quels tens lies à des cut *)
(* seuentialisation sans coupure puis avec (+ de cas ou en remplacant par des tens )*)

Definition terminal (G : base_graph) (v : G) : bool :=
  match vlabel v with
  | ax | ⊗ | ⅋ => [forall e, (source e == v) ==> (vlabel (target e) == c)]
  | cut => true
  | c => false
  end.

Definition splitting (G : proof_net) (v : G) : Type :=
  match vlabel v with
  | ax => {A & G ≃d ax_graph_data A}
  | ⊗ => {'(G0, G1) : proof_net * proof_net & G ≃d add_node_ps_tens G0 G1}
  | ⅋ => {G0 : proof_net & G ≃d add_node_ps_parr G0}
  | cut => {'(G0, G1) : proof_net * proof_net & G ≃d add_node_ps_cut G0 G1}
  | c => void (* a conclusion node is never splitting *)
  end.

(** Base graph for removing a node *) (* TODO faire comme add_node des cas selon vlabel_v pour factoriser ? *)
(* Remove the node and its eventual conclusion *)
Definition rem_node_graph_1 {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :=
  induced (setT :\ v :\ target (ccl H)).

Lemma rem_node_sources_stay {G : proof_net} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  source (left H) \in setT :\ v :\ target (ccl H) /\
  source (right H) \in setT :\ v :\ target (ccl H).
Proof.
  assert (C := p_correct G). destruct C as [C _].
  rewrite !in_set. splitb; apply /eqP => F.
  - set p := forward (left H) :: forward (ccl H) :: nil.
    assert (P : supath switching (source (left H)) (source (left H)) p).
    { rewrite /supath /p switching_None andb_true_r. cbn. apply /andP; split.
      - rewrite left_e ccl_e F. splitb.
      - rewrite !in_cons /= orb_false_r andb_true_r.
        unfold switching. cbnb. case_if; apply /eqP.
        + rewrite -F. apply nesym, no_selfloop.
        + intro FF. contradict F. rewrite FF. apply no_selfloop. }
    specialize (C _ (Sub p P)).
    by contradict C.
  - assert (Eq : left H = ccl H) by by apply ccl_eq.
    assert (FF : source (left H) = target (left H)) by by rewrite left_e Eq ccl_e.
    contradict FF. apply no_selfloop.
  - set p := forward (right H) :: forward (ccl H) :: nil.
    assert (P : supath switching (source (right H)) (source (right H)) p).
    { rewrite /supath /p switching_None andb_true_r. cbn. apply /andP; split.
      - rewrite right_e ccl_e F. splitb.
      - rewrite !in_cons /= orb_false_r andb_true_r.
        unfold switching. cbnb. case_if; apply /eqP.
        + rewrite -F. apply nesym, no_selfloop.
        + intro FF. contradict F. rewrite FF. apply no_selfloop. }
    specialize (C _ (Sub p P)).
    by contradict C.
  - assert (Eq : right H = ccl H) by by apply ccl_eq.
    assert (FF : source (right H) = target (right H)) by by rewrite right_e Eq ccl_e.
    contradict FF. apply no_selfloop.
Qed.

(* Add two new conclusions *)
Definition rem_node_graph {G : proof_net} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :=
  @add_concl_graph _
  (@add_concl_graph _ (rem_node_graph_1 H) (Sub (source (right H)) (proj2 (rem_node_sources_stay H))) c (flabel (right H)))
  (inl (Sub (source (left H)) (proj1 (rem_node_sources_stay H)))) c (flabel (left H)).
(* TODO faire pareil dans d'autres cas pour se passer de lemmas inutiles *)

(*
Definition rem_node_transport {G : proof_net} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
    edge G -> edge (rem_node_graph H) :=
    fun e => if @boolP _ is AltTrue p then Some (inl (Some (inl (Sub e p : edge (rem_node_graph_1 H)))))
    else if e == left H then None else Some (inl None).

Definition rem_node_order {G : proof_net} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  seq (edge (rem_node_graph H)) := None :: [seq rem_node_transport H x | x <- order G].

Definition rem_node_graph_data {G : proof_net} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) := {|
  graph_of := rem_node_graph H;
  order := rem_node_order _;
  |}.
*) (* TODO voir si on peut s'en passer à coups de p_deg_iso et iso_to_isod *)
(* ou plutot sequent G privé de left tens right
Lemma rem_node_sequent {G : proof_net} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  sequent (rem_node_graph_data H) = flabel (left H) :: flabel (right H) :: behead (sequent G).
Proof.
  rewrite /rem_node_order.
  unfold 
Admitted.
*)

Lemma test {G : proof_net} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  terminal v -> add_node_graph (if vlabel v == ⅋ then parr_t else tens_t)
  (None : edge (rem_node_graph H)) (Some (inl None)) ≃ G.
Abort.
Definition test2 : forall r, r = ⊗ \/ r = ⅋ -> trilean.
intros r H.
assert (H' : (r == ⊗) || (r == ⅋)).
{ apply /orP. elim: H => /eqP-->; caseb. }
elim: (orb_sum H') => _.
- exact tens_t.
- exact parr_t.
Defined.




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
faire des vues pour se retrouver avec des il existes equi = [S S'] (il existe sur
set de finset, donc ok je pense) puis définir les Gi à partir de là,
montrer qu'ils sont uconnected_nb = 1, puis finalement que
G iso à add_node Gi *)


Lemma has_ax (G : proof_net) :
  exists (v : G), vlabel v = ax.
Proof. (* avec correct_not_empty, puis en remontant tant que non ax, avec uacyclic pour terminaison *)
Admitted. (* TODO si utile dans mll_def, ou ajouter un fichier ac resultats sur mll *)

Lemma has_terminal (G : proof_net) :
  exists (v : G), terminal v.
Proof.
  enough (E : ~~[forall v : G, ~~ terminal v]).
  { revert E => /forallPn/sigW[v /negPn-?]. by exists v. }
  apply /negP => /forallP F.
  assert (E : exists (v : G), vlabel v == ax).
  { destruct (has_ax G) as [v ?]. exists v. by apply /eqP. }
  revert E => /sigW[v /eqP-V].
  (* v a un descendant qui n'est pas une c ni un cut,
  puis construire suite de noeuds avec cette propriété
  et conclure par finitude et absence de cycles,
  car comme on ne fait que descendre, ce cycle serait un
  switching cycle *)
Admitted.

Lemma terminal_ax_is_splitting_step0 (G : proof_net) (v : G) :
  vlabel v = ax -> terminal v ->
  {'(e, e') & flabel e = flabel e'^ & source e = v /\ source e' = v /\ vlabel (target e) = c /\
  vlabel (target e') = c}.
Proof.
  intro V.
  rewrite /terminal V => /forallP T.
  assert (p_ax_bis := pb_ax V).
  revert p_ax_bis => /existsP/sigW[e /existsP/sigW[e' /andP[/andP[E E'] /eqP-F]]].
  revert E E'. rewrite !in_set => /eqP-E /eqP-E'. subst v.
  assert (vlabel (target e) = c /\ vlabel (target e') = c) as [Te Te'].
  { split; [set a := e | set a := e'].
    all: revert T => /(_ a) /implyP-P.
    all: apply /eqP; apply P; by apply /eqP. }
  exists (e, e'); splitb.
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
  e' <> e -> target e' <> target e -> order G = [:: e'; e] ->
  G ≃d ax_graph_data (flabel e).
Proof.
  intros V e e' F E E' Te Te' Cu Ca T'S TS En T'T O. subst v.
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
  { intro u. unfold v_bij_bwd, v_bij_fwd. destruct_I3 u; case_if. }
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
  { intro a. unfold e_bij_bwd, e_bij_fwd. destruct_I2 a; case_if. }
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
  exists ({| iso_v := _; iso_e := _; iso_d := _; iso_ihom := iso_ihom |}).
  rewrite O /= /e_bij_fwd; case_if.
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
  wlog : e e' V F E' Te Te' Cu Ca T'S TS En T'T / order G = e' :: e :: nil.
  { intro Hw.
    assert (e <> e') by by apply nesym.
    assert (e \in order G /\ e' \in order G) as [Oe Oe'] by by split; apply p_order.
    destruct (order G) as [ | a [ | a' [ | a'' o]]] eqn:O; try by [].
    all: rewrite !in_cons ?in_nil ?orb_false_r in Oe.
    all: rewrite !in_cons ?in_nil ?orb_false_r in Oe'.
    - elim: (orb_sum (Ca a)) => /eqP-?; subst a;
      revert Oe Oe'; introb.
    - elim: (orb_sum (Ca a)) => /eqP-?; subst a;
      elim: (orb_sum (Ca a')) => /eqP-?; subst a';
      elim: (orb_sum Oe) => /eqP-?;
      elim: (orb_sum Oe') => /eqP-? //.
      + rewrite -E'. apply (Hw e' e); subst; rewrite // ?E' //.
        * by rewrite F bidual.
        * intro u. destruct (Cu u) as [? | [? | ?]]; caseb.
        * intro a. elim: (orb_sum (Ca a)) => /eqP-?; subst a; caseb.
        * by apply nesym.
      + by apply (Hw e e').
    - exfalso.
      destruct (p_order G) as [_ U].
      revert U. rewrite O /= !in_cons. introb.
      elim: (orb_sum (Ca a)) => /eqP-?; subst a;
      elim: (orb_sum (Ca a')) => /eqP-?; subst a';
      elim: (orb_sum (Ca a'')) => /eqP-?; by subst a''. }
  intro O.
  rewrite /splitting V.
  enough (G ≃d ax_graph_data (flabel e)) by by exists (flabel e).
  by apply (@terminal_ax_is_splitting_step4 _ _ V _ e').
Qed.


Lemma supath_induced (G : base_graph) (S : {set G}) :
  forall s t (p : Supath (@switching _ (induced S)) s t),
  {q : Supath (@switching _ G) (val s) (val t) & upval q = [seq (val a.1, a.2) | a <- upval p]}.
Proof.
  intros s t [p P]. revert s t P.
  induction p as [ | ([a A], b) p IH]; simpl => s t; rewrite /supath /=.
  { introb. subst t. by exists (supath_nil _ _). }
  rewrite in_cons => /andP[/andP[/andP[/eqP-? W] /andP[u U]] /norP[n N]]. subst s. simpl.
  assert (P : supath switching (Sub (endpoint b a) (induced_proof b (valP (exist _ a A))) : induced S)
    t p) by splitb.
  specialize (IH _ _ P). destruct IH as [[q Q] HQ].
  revert HQ; cbnb => ?; subst q. simpl in Q.
  enough (QS : supath switching (endpoint (~~ b) a) (val t) ((a, b) :: _))
    by by exists {| upval := _ ; upvalK := QS|}.
  revert Q. rewrite /supath /= in_cons. introb. splitb.
  revert u. clear. induction p as [ | c p IH]; trivial.
  rewrite /= !in_cons. move => /norP[i I]. splitb.
  - revert i. unfold switching. case_if.
  - by apply IH.
Qed.
(* TODO generalise ? *)

Lemma uacyclic_induced (G : base_graph) (S : {set G}) :
  uacyclic (@switching _ G) -> uacyclic (@switching _ (induced S)).
Proof.
  intros U ? p.
  destruct (supath_induced p) as [q Q].
  specialize (U _ q). subst q.
  destruct p as [p P]. cbnb. by destruct p.
Qed.


Lemma terminal_parr_is_splitting_cc (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal v -> splitting_cc v.
Proof.
  intro V.
  rewrite /terminal V => /forallP T.
  rewrite /splitting_cc.
  generalize (erefl (vlabel v)). rewrite {2 3}V => V'.
  assert (V = V') by apply eq_irrelevance. subst V'.
  enough (C : correct (rem_node_graph (or_intror V))) by by apply /eqP; destruct C.
  unfold rem_node_graph.
  destruct (rem_node_sources_stay (or_intror V)) as [e f].
  apply add_concl_correct, add_concl_correct_weak. split.
  { apply uacyclic_induced, p_correct. }
  intros [x X] [y Y].
  destruct (correct_to_weak (p_correct G)) as [_ C].
  revert C => /(_ x y)/sigW[[p P] _].
  enough ({q : Supath switching_left (Sub x X : rem_node_graph_1 (or_intror V)) (Sub y Y) &
    p = [seq (val a.1, a.2) | a <- upval q]}) as [q _] by by exists q.
  revert x X P. induction p as [ | a p IH] => x X; rewrite /supath /=.
  { introb. subst y. replace Y with X by apply eq_irrelevance.
    by exists (supath_nil _ _). }
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
    enough (D : upath_disjoint switching_left {| upval := _ ; upvalK := PA |} q).
    { exists (supath_cat D). cbn. rewrite Hq. f_equal. simpl. by destruct a. }
    rewrite /= /upath_disjoint disjoint_has /= orb_false_r.
    revert u. subst p.
    destruct q as [q Q]. rewrite -map_comp /=. clear.
    induction q as [ | c q IH]; trivial.
    rewrite /= !in_cons => /norP[k K]. apply /norP. rewrite IH //. splitb.
    revert k. rewrite /switching_left /=. case_if.
  - clear IH.
    assert (Vc : vlabel (target (ccl_parr V)) = c).
    { revert T => /(_ (ccl_parr V)) /implyP-T.
      apply /eqP. apply T. apply /eqP. apply ccl_e. }
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
          apply left_eq. splitb. by apply /negPn.
        + assert (a = ccl_parr V) by by apply ccl_eq.
          subst a.
          contradict X; apply /negP.
          rewrite !in_set /=. caseb. }
    subst a.
    assert (Cp : p = [::] \/ p = [:: forward (ccl_parr V)]).
    { destruct p as [ | s p].
      - caseb.
      - right.
        assert (s = forward (ccl_parr V)).
        { revert W => /= /andP[/eqP-S W].
          rewrite left_e in S.
          destruct s as [s []]; simpl in *.
          + apply /eqP. cbn. rewrite andb_true_r. apply /eqP.
            by apply ccl_eq.
          + revert u N. rewrite !in_cons => /norP[S1 _] /norP[S2 _]. revert S1 S2.
            rewrite /switching_left left_e left_l S V /=.
            case_if.
            enough (left_parr V = s) by by [].
            symmetry. apply left_eq. splitb. by apply /negPn. }
        subst s.
        destruct p as [ | r p]; trivial.
        exfalso. revert U W. clear - T.
        rewrite /= !in_cons => /andP[/norP[U _] _] /andP[_ /andP[/eqP-W _]].
        assert (Vc : vlabel (target (ccl_parr V)) = c).
        { revert T => /(_ (ccl_parr V)) /implyP-T.
          apply /eqP. apply T. apply /eqP. apply ccl_e. }
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
  vlabel v = ⅋ -> splitting_cc v -> splitting v.
Proof.
  intro V.
  rewrite /splitting_cc.
  generalize (erefl (vlabel v)). rewrite {2 3}V => V' S.
  assert (V = V') by apply eq_irrelevance. subst V'.
  rewrite /splitting V.
  assert (C : correct (rem_node_graph (or_intror V))).
  { split; [ | by apply /eqP].
    apply add_concl_uacyclic, add_concl_uacyclic, uacyclic_induced, p_correct. }
  (* puis montrer que rem_node_graph est un ps,
    puis isomophisme avec G (necessite probablement un lemme intermediaire *)
Abort.

(* tenseur scindant ici, avec cut ... *)


Lemma splitting_cc_is_splitting (G : proof_net) (v : G) :
  splitting_cc v -> splitting v.
Proof.
Admitted.

Lemma terminal_parr_is_splitting (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal v -> splitting v.
Proof. intros. by apply splitting_cc_is_splitting, terminal_parr_is_splitting_cc. Qed.

Lemma has_splitting (G : proof_net) :
  {v : G & splitting v}.
Proof.
(* utiliser has_terminal, se ramener au cas où il n'y a que des cut / tens term
puis tenseur scindant *)
Admitted.

(* TODO admettre lemme tenseur scindant puis sequantialisation directement *)
Definition sequentialize : forall (G : proof_net), ll (sequent G).
Proof.
  enough (Hm : forall n (G : proof_net), r#|G| = n -> ll (sequent G))
    by by intro G; apply (Hm r#|G|).
  intro n; induction n as [n IH] using lt_wf_rect; intros G ?; subst n.
  destruct (has_splitting G) as [v V].
  unfold splitting in V. destruct (vlabel v); try by [].
  - destruct V as [A h].
    rewrite (sequent_iso_data h) ax_sequent.
    apply ax_exp.
  - destruct V as [[G0 G1] h].
    assert (C : correct (add_node_ps_tens G0 G1)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_tens_correct_contra C) as [[[[e0 l0] e1] l1] [Hl0 Hl1]].
    rewrite (sequent_iso_data h) add_node_sequent union_sequent /sequent /=
      /union_order Hl0 Hl1 /=.
    assert ((r#|G0| < r#|G|)%coq_nat /\ (r#|G1| < r#|G|)%coq_nat) as [C0 C1].
    { rewrite (rcard_iso h) add_node_ps_tens_rcard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    assert (IH1 := IH _ C1 G1 erefl).
    revert IH0 IH1.
    rewrite /sequent Hl0 Hl1 /=.
    apply tens_r.
  - destruct V as [G0 h].
    assert (C : correct (add_node_ps_parr G0)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_parr_correct_contra C) as [[[e0 e1] l] Hl].
    rewrite (sequent_iso_data h) add_node_sequent /sequent /= Hl /=.
    assert (C0 : (r#|G0| < r#|G|)%coq_nat).
    { rewrite (rcard_iso h) add_node_ps_parr_rcard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    revert IH0.
    rewrite /sequent Hl /=.
    apply parr_r.
  - destruct V as [[G0 G1] h].
    assert (C : correct (add_node_ps_cut G0 G1)) by apply (iso_correct (iso_sym h)), p_correct.
    destruct (add_node_cut_correct_contra C) as [[[[e0 l0] e1] l1] [Hl0 [Hl1 Hf]]].
    rewrite (sequent_iso_data h) add_node_sequent union_sequent /sequent /=
      /union_order Hl0 Hl1 Hf /=.
    assert ((r#|G0| < r#|G|)%coq_nat /\ (r#|G1| < r#|G|)%coq_nat) as [C0 C1].
    { rewrite (rcard_iso h) add_node_ps_cut_rcard //. lia. }
    assert (IH0 := IH _ C0 G0 erefl).
    assert (IH1 := IH _ C1 G1 erefl).
    revert IH0 IH1.
    rewrite /sequent Hl0 Hl1 /=.
    replace (flabel e1) with (flabel e0^) by by symmetry; apply /eqP.
    apply cut_r.
Qed.
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
    apply /setP; intro v; destruct_I3 v;
    by rewrite !in_set.
  - by [].
  - rewrite /= -H0 -H1.
Abort. *)
(* TODO Lemma : nb cut ps (pi) = nb cut pi, idem other rules, et dans le sens sequentialisation aussi *)
End Atoms.
