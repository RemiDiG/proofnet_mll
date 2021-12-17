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

Definition splitting (G : proof_structure) (v : G) : Type :=
  match vlabel v with
  | ax => {A & G ≃d ax_graph_data A}
  | ⊗ => {'(G0, G1) & G ≃d add_node_tens G0 G1 & #|G0| + #|G1| + 1 = #|G|}
  | ⅋ => {G0 & G ≃d add_node_parr G0 & #|G0| + 1 = #|G|}
  | cut => {'(G0, G1) & G ≃d add_node_cut G0 G1 & #|G0| + #|G1| + 1 = #|G|}
  | c => void (* a conclusion node is never splitting *)
  end. (* Contraint on size as add_node is defined even when no conclusion *)

(* autre solution : définir opération retirer noeuds (en reutilisant correct ?)
et demander le bon nombre de composantes connexes, en montrant que
ça reste acyclique. Puis les graphes à considérer sont les graphes induits par
les composantes connexes.
à réfléchir *) (*

(** Base graph for removing a node *) (* TODO faire comme add_node des cas selon vlabel_v pour factoriser ? *)
(* Remove the node and its eventual conclusion *)
Definition rem_node_graph_1 {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :=
  induced (setT :\ v :\ target (ccl H)).

Lemma rem_node_sources_stay {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) :
  terminal v ->
  source (left H) \in setT :\ v :\ target (ccl H) /\
  source (right H) \in setT :\ v :\ target (ccl H).
(* TODO en vrai pas besoin de terminal, mais ca simplifie la preuve *)
Proof.
  unfold terminal => T.
  assert (T' : forall u, source u = v -> vlabel (target u) = c).
  { destruct H as [H | H]; rewrite H in T;
    intro u; revert T => /forallP/(_ u)/implyP-I /eqP-?; apply /eqP; by apply I. }
  assert (vlabel (target (ccl H)) = c).
  { apply T', ccl_e. }
  rewrite !in_set. splitb; apply /eqP.
  - by apply no_source_c.
  - intro F.
    assert (C : left H = ccl H) by by apply ccl_eq.
    assert (FF : source (left H) = target (left H)) by by rewrite left_e C ccl_e.
    contradict FF. apply no_selfloop.
  - by apply no_source_c.
  - intro F.
    assert (C : right H = ccl H) by by apply ccl_eq.
    assert (FF : source (right H) = target (right H)) by by rewrite right_e C ccl_e.
    contradict FF. apply no_selfloop.
Qed.

(* Add two new conclusions *)
Definition rem_node_graph {G : proof_structure} {v : G} (H : vlabel v = ⊗ \/ vlabel v = ⅋) (T : terminal v) :=
  let (LP, RP) := rem_node_sources_stay H T in (* TODO faire pareil dans d'autres cas pour se passer de lemmas inutiles *)
  @add_concl_graph _
  (@add_concl_graph _ (rem_node_graph_1 H) (Sub (source (left H)) LP) c (flabel (left H)))
  (inl (Sub (source (right H)) RP)) c (flabel (right H)).

Definition splitting_cc (G : proof_structure) (v : G) (T : terminal v) : bool :=
  match vlabel v as V return vlabel v = V -> bool with
  | ax => fun _ => true
  | ⊗ => fun H => uconnected_nb (@switching_left _ (rem_node_graph (or_introl H) T)) == 2
  | ⅋ => fun H => uconnected_nb (@switching_left _ (rem_node_graph (or_intror H) T)) == 1
  | cut => fun _ => false (* TODO sans coupure pour commencer *)
  | c => fun _ => false
  end Logic.eq_refl.

(* puis définir les graphes avec induced_sub S pour S dans 
equivalence_partition (is_uconnected f) [set: G] et là ça devient galère,
faire des vues pour se retrouver avec des il existes equi = [S S'] (il existe sur
set de finset, donc ok je pense) puis définir les Gi à partir de là,
montrer qu'ils sont uconnected_nb = 1, puis finalement que
G iso à add_node Gi 

Comme c'est des choses qu'on aura besoin de faire de toute façon,
autant le faire là et se passer de ces pbs de il existe *)
*)

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

Lemma terminal_ax_is_splitting (G : proof_net) (v : G) :
  vlabel v = ax -> terminal v -> splitting v.
Proof.
  intro V.
  rewrite /terminal /splitting V => /forallP T.
  assert (p_ax_bis : [exists el : edge G, exists er, (el \in edges_at_out v) &&
    (er \in edges_at_out v) && (flabel el == dual (flabel er))]).
  { destruct (p_ax V) as [e [e' [E [E' F]]]].
    apply /existsP. exists e. apply /existsP. exists e'. splitb. by apply /eqP. }
(* TODO faire lemma qui passe ces lemmes en bool *)
  revert p_ax_bis => /existsP/sigW [e /existsP/sigW [e' /andP[/andP[E E'] /eqP-F]]].
  revert E E'. rewrite !in_set => /eqP-E /eqP-E'. subst v.
  assert (vlabel (target e) = c /\ vlabel (target e') = c) as [Te Te'].
  { split; [set a := e | set a := e'].
    all: revert T => /(_ a) /implyP P.
    all: apply /eqP; apply P; by apply /eqP. }
  assert (Cu : forall u, u = source e \/ u = target e \/ u = target e').
  { intro u.
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
    all: contradict F; apply nesym, no_selfdual. }
  assert (Ca : forall a, (a == e) || (a == e')).
  { intro a.
    destruct (Cu (target a)) as [A | [A | A]].
    - contradict A. by apply no_target_ax.
    - apply /orP; left; apply /eqP. by apply one_target_c.
    - apply /orP; right; apply /eqP. by apply one_target_c. }
  assert (T'S : target e' <> source e).
  { rewrite -E'. apply nesym, no_selfloop. }
  assert (TS : target e <> source e) by apply nesym, no_selfloop.
  assert (En : e' <> e).
  { intros ?. subst e'.
    contradict F. apply nesym, no_selfdual. }
  assert (En' : e <> e') by by apply nesym.
  assert (T'T : target e' <> target e).
  { intros ?. contradict En. by by apply one_target_c. }
   wlog : e e' T V F E' Te Te' Cu Ca T'S TS En En' T'T / order G = e' :: e :: nil.
  { intro Hw.
    assert (e \in order G /\ e' \in order G) as [Oe Oe'] by by split; apply p_order.
    destruct (order G) as [ | a [ | a' [ | a'' o]]] eqn:O; try by [].
    all: rewrite !in_cons ?in_nil ?orb_false_r in Oe.
    all: rewrite !in_cons ?in_nil ?orb_false_r in Oe'.
    - elim: (orb_sum (Ca a)) => /eqP-?; by subst a;
      by revert Oe Oe'; introb.
    - elim: (orb_sum (Ca a)) => /eqP-?; subst a;
      elim: (orb_sum (Ca a')) => /eqP-?; subst a';
      elim: (orb_sum Oe) => /eqP-?;
      elim: (orb_sum Oe') => /eqP-? //.
      + apply (Hw e' e); rewrite // ?E' //.
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
  enough (G ≃d ax_graph_data (flabel e)) by by exists (flabel e).
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
  { intro u. unfold v_bij_bwd, v_bij_fwd. case_if.
    by destruct (Cu u) as [? | [? | ?]]. }
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
(* TODO ugly proof, simplify and break it *)

Lemma terminal_parr_is_splitting (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal v -> splitting v.
Proof.
Admitted.

Lemma has_splitting (G : proof_net) :
  {v : G & splitting v}.
Proof.
(* utiliser has_terminal, se ramener au cas où il n'y a que des cut / tens term
puis tenseur scindant *)
Admitted.

(* TODO admettre lemme tenseur scindant puis sequantialisation directement *)
Definition sequentialize : forall (G : proof_net), ll (sequent G).
Proof.
  enough (Hm : forall n (G : proof_net), #|G| = n -> ll (sequent G))
    by by intro G; apply (Hm #|G|).
  intro n; induction n as [n IH] using lt_wf_rect; intros G ?; subst n.
  destruct (has_splitting G) as [v V].
  unfold splitting in V. destruct (vlabel v); try by [].
  - destruct V as [A h].
    rewrite (sequent_iso_data h) ax_sequent.
    apply ax_exp.
  - destruct V as [[G0 G1] h C].
    rewrite (sequent_iso_data h) add_node_sequent.
    admit.
  - destruct V as [G0 h C].
    rewrite (sequent_iso_data h) add_node_sequent.
    destruct (order G0) as [ | o0 O] eqn:HO.
    { admit. (* contradict C *) }
    admit.
  - destruct V as [[G0 G1] h C].
    rewrite (sequent_iso_data h) add_node_sequent.
    admit.
Admitted.
(* TODO Induction sur le nombre de noeuds ? *)
(* TODO va nécessiter des calculs de cardinaux sur add_node, pour induction *)
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
