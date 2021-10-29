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
Notation ll := (@ll atom).
Notation base_graph := (graph (flat rule) (flat (formula * bool))).
Notation graph_data := (@graph_data atom).
Notation proof_structure := (@proof_structure atom).
Notation proof_net := (@proof_net atom).

(* sequentialisation : fonction reliant regles à noeuds => nb cut + quels tens lies à des cut *)
(* seuentialisation sans coupure puis avec (+ de cas ou en remplacant par des tens )*)

Definition terminal_node (G : base_graph) (v : G) : bool :=
  match vlabel v with
  | ax | ⊗ | ⅋ => [forall e, (source e == v) ==> (vlabel (target e) == c)]
  | cut => true
  | c => false
  end.

Definition splitting_node (G : proof_structure) (v : G) : Prop :=
  match vlabel v with
  | ax => terminal_node v
  | ⊗ | cut => exists (G0 G1 : proof_structure) (h : remove_vertex v ≃ G0 ⊎ G1), true
  | ⅋ => exists (G0 : proof_structure) (h : remove_vertex v ≃ G0), true
  | c => false
  end.
(* iso de graph data ? *)


Lemma splitting_ax (G : proof_net) (v : G) :
  vlabel v = ax -> terminal_node v -> exists A (h : G ≃ ax_graph A), true.
Proof.
  intro V.
  rewrite /terminal_node V => /forallP T.
  destruct (p_ax V) as [e [e' [E [E' F]]]].
  revert E E'. rewrite !in_set => /eqP-E /eqP-E'. subst v.
  assert (vlabel (target e) = c /\ vlabel (target e') = c) as [? ?].
  { split; [set a := e | set a := e'].
    all: revert T => /(_ a) /implyP P.
    all: apply /eqP; apply P; by apply /eqP. }
  enough (h : G ≃ ax_graph (flabel e)) by by exists (flabel e), h.
  assert (Cu : forall u, u = source e \/ u = target e \/ u = target e').
  { intro u.
    assert (C : correct G) by apply p_correct.
    apply correct_to_weak in C.
    destruct C as [_ C]. elim: (C (source e) u) => [[p /andP[/andP[W U] N]] _].
    destruct p as [ | (a, b) p].
    { revert W => /= /eqP-->. caseb. }
    revert W => /= /andP[/eqP-Hf W].
    destruct b; last by (contradict Hf; by apply no_target_ax).
    enough (A : a = e \/ a = e').
    { destruct A; [set ae := e | set ae := e']; subst a.
      all: destruct p as [ | (a, b) p];
        first by (revert W => /= /eqP-->; caseb).
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
  assert (Ca : forall a, a = e \/ a = e').
  { intro a.
    destruct (Cu (target a)) as [A | [A | A]].
    - contradict A. by apply no_target_ax.
    - left. by apply one_target_c.
    - right. by apply one_target_c. }
  assert (target e' <> source e).
  { rewrite -E'. apply nesym, no_selfloop. }
  assert (target e <> source e) by apply nesym, no_selfloop.
  assert (En : e' <> e).
  { intros ?. subst e'.
    contradict F. apply nesym, no_selfdual. }
  assert (target e' <> target e).
  { intros ?. contradict En. by by apply one_target_c. }
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
    by destruct (Ca a) as [? | ?]. }
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
    - intros a []; destruct (Ca a) as [? | ?]; subst a; simpl.
      all: unfold e_bij_fwd, v_bij_fwd; case_if.
      enough (source e' <> target e) by by [].
      rewrite E'. by apply nesym.
    - intros u; destruct (Cu u) as [? | [? | ?]]; subst u; simpl.
      all: unfold v_bij_fwd; case_if.
    - intros a; destruct (Ca a) as [? | ?]; subst a; simpl.
      all: unfold e_bij_fwd; case_if.
      + destruct (elabel e) as [Fe Le] eqn:LL.
        apply /eqP. revert LL => /eqP. cbn => /andP[? /eqP-L]. splitb.
        rewrite -L. apply p_noleft. caseb.
      + destruct (elabel e') as [Fe Le] eqn:LL.
        apply /eqP. revert LL => /eqP. cbn => /andP[/eqP-F' /eqP-L]. subst Fe Le. splitb.
        * rewrite F bidual. cbnb.
        * apply p_noleft. caseb. }
  exact ({|
  iso_v := _;
  iso_e := _;
  iso_d := _;
  iso_ihom := iso_ihom |}).
Qed.
(* TODO ugly proof, simplify and break it *)

Lemma splitting_parr (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal_node v -> splitting_node v.
Proof.
Admitted.

Lemma has_splitting (G : proof_net) :
  exists (v : G), splitting_node v.
Proof.
Admitted.

(* TOTHINK si remove vertex donne le bon nb de cc, alors les cc sont des proof_structures ? *)

(* TOTHINK connected subgraph for splitting tens ?? *)

(* TODO admettre lemme tenseur scindant puis sequantialisation directement *)
(* Lemma splitting_tens (G : graph_data) : [exists v, (vlabel v == ⊗) && (terminal_node v) &&
exists G0 : proof_net, exists G1 : proof_net, (#|G0| < #|G|) && (#|G1| < #|G|) && (sequent G == elabel (ccl v)
:: sequent G0 ++ sequent G1)].
Admitted. (* TODO hyp : non terminal ax, parr, cut *) *)
(* exists v, vlabel v = tens, exists Gl, exists Gr, G iso_left (add_tens Gl Gr) *)

Definition sequentialisation (G : proof_net) : ll (sequent G).
Proof.
  revert G.
  enough (Hm : forall n (G : proof_net), #|G| = n -> ll (sequent G))
    by (intro G; by apply (Hm #|G|)).
  intro n; induction n as [n IH] using lt_wf_rect; intros G Hc.
Abort.
(* TODO voir derniere quest exam et focalisation + seqpn *)


(** ** Sequentialization *)
(* many things to do: spliting tens / cut, blocking parr, always a
  terminal parr or a splitting *)
(* function to turn a ps into a sequential proof *)
(* TOTHINK utiliser seulement connexité left possible (ie pas besoin de demontrer que
un graphe de correc correct ac notre def) ? to check, parr bloquant *)



Fixpoint nb_cut l (pi : ll l) := match pi with
  | ax_r x                 => 0
  | ex_r _ _ pi0 _         => nb_cut pi0
  | tens_r _ _ _ _ pi0 pi1 => nb_cut pi0 + nb_cut pi1
  | parr_r _ _ _ pi0       => nb_cut pi0
  | cut_r _ _ _ pi0 pi1    => nb_cut pi0 + nb_cut pi1 + 1
  end.
(* UTILISE ps, AUTRE FICHIER 
Lemma ps_nb_cut l (pi : ll l) : #|[set v : ps pi | vlabel v == cut]| = nb_cut pi.
Proof.
  induction pi as [x | | A B l0 l1 pi0 H0 pi1 H1 | A B l0 pi0 H0 | A l0 l1 pi0 H0 pi1 H1].
  - enough (H : [set v : ax_ps x | vlabel v == cut] = set0) by by rewrite H cards0.
    apply /setP; intro v; destruct_I3 v;
    by rewrite !in_set.
  - by [].
  - rewrite /= -H0 -H1.
Abort. *)
(* TODO Lemma : nb cut ps (pi) = nb cut pi, idem other rules + mettre ça vers ps
-> vraiment utile ? ça a l'air mieux dans le sens sequentialisation ... *)
End Atoms.
