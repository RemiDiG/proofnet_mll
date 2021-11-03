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

Definition splitting (G : proof_structure) (v : G) : Prop :=
  match vlabel v with
  | ax => exists A (h : G ≃d ax_graph_data A), true
  | ⊗ => exists (G0 G1 : proof_net) (h : G ≃d add_node_tens G0 G1), true
  | ⅋ => exists (G0 : proof_net) (h : G ≃d add_node_parr G0), true
  | cut => exists (G0 G1 : proof_net) (h : G ≃d add_node_cut G0 G1), true
  | c => false
  end.
(* pour passer ça en bool :
- possible de remplacer exists A par exists e, flabel e
- pour les isod, devrait être en nombre finis donc devrait être ok (définir eq type
entre graphes par == <-> exists iso entre les 2
- pour les exists G, les factoriser en produit (prod de choice est choice) et montrer
que graphs est choice -> nécessite size formules (pour label) bornée
si en plus borne card et card edge, devrait être fini *)
(* autre solution : définir opération retirer noeuds (en reutilisant correct ?)
et demander le bon nombre de composantes connexes, en montrant que
ça reste acyclique. Puis les graphes à considérer sont les graphes induits par
les composantes connexes.
Semble galère, mais pas forcément plus qu'en passant par des choiceType : à réfléchir *)

(*
Definition rem_tens_parr (G : proof_structure) (v : G) : proof_structure.
Admitted.
(* à definir en plusieurs étapes : retirer v, sa conclusion,
puis ajouter 2 conclusions reliéesaux prémisses de v,
avec les bonnes étiquettes
(réutiliser add_concl_graph de mll_correct.v pour les ajouter
-> long mais faisable *)

Definition splitting_cc (G : proof_structure) (v : G) : bool :=
  match vlabel v with
  | ax => terminal v
  | ⊗ => uconnected_nb (@switching_left _ (rem_tens_parr v)) == 2
  | ⅋ => uconnected_nb (@switching_left _ (rem_tens_parr v)) == 1
  | cut => false (* sans coupure pour commencer *)
  | c => false
  end.
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
Proof. (* avec correct_not_empty, puis en remontant tant que non ax, avecacyclic pour terminaison *)
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
  destruct (p_ax V) as [e [e' [E [E' F]]]].
  revert E E'. rewrite !in_set => /eqP-E /eqP-E'. subst v.
  assert (vlabel (target e) = c /\ vlabel (target e') = c) as [? ?].
  { split; [set a := e | set a := e'].
    all: revert T => /(_ a) /implyP P.
    all: apply /eqP; apply P; by apply /eqP. }
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
  assert (En' : e <> e') by by apply nesym.
  assert (target e' <> target e).
  { intros ?. contradict En. by by apply one_target_c. }
   wlog : e e' T V F E' _0 _1 Cu Ca _2 _3 En En' _4 / order G = e' :: e :: nil.
  { intro Hw.
    assert (e \in order G /\ e' \in order G) as [Oe Oe'] by by split; apply p_order.
    destruct (order G) as [ | a [ | a' [ | a'' o]]] eqn:O; try by [].
    all: rewrite !in_cons ?in_nil ?orb_false_r in Oe.
    all: rewrite !in_cons ?in_nil ?orb_false_r in Oe'.
    - destruct (Ca a) as [? | ?]; by subst a;
      revert Oe Oe'; introb; try by [].
    - destruct (Ca a) as [? | ?]; subst a;
      destruct (Ca a') as [? | ?]; subst a';
      revert Oe Oe'; introb; try by [].
      + apply (Hw e' e); rewrite // ?E' //.
        * by rewrite F bidual.
        * intro u. destruct (Cu u) as [? | [? | ?]]; caseb.
        * intro a. destruct (Ca a) as [? | ?]; caseb.
        * by apply nesym.
      + by apply (Hw e e').
    - exfalso.
      destruct (p_order G) as [_ U].
      revert U. rewrite O /= !in_cons. introb.
      destruct (Ca a) as [? | ?]; subst a;
      destruct (Ca a') as [? | ?]; subst a';
      destruct (Ca a'') as [? | ?]; subst a''; by []. }
    intro O.
  enough (h : G ≃d ax_graph_data (flabel e)) by by exists (flabel e), h.
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
  exists ({| iso_v := _; iso_e := _; iso_d := _; iso_ihom := iso_ihom |}).
  rewrite O /= /e_bij_fwd; case_if.
Qed.
(* TODO ugly proof, simplify and break it *)
(* puis si graphes iso, meme sequentialisation, et seq de ax est juste une regle ax ? *)

Lemma terminal_parr_is_splitting (G : proof_net) (v : G) :
  vlabel v = ⅋ -> terminal v -> splitting v.
Proof.
Admitted.

Lemma has_splitting (G : proof_net) :
  exists (v : G), splitting v.
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
(*   destruct (has_splitting G). -> Nécessite du fintype sur les iso, voir mll_def.v *)
(* nécessite aussi d'avoir formula comme choicetype pour le cas axiome *)
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
