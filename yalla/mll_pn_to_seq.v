(* Sequentialisation *)
(* From a Proof Net, return a LL proof of the same sequent *)

From Coq Require Import Bool Wf_nat.
From OLlibs Require Import dectype Permutation_Type_more.
From mathcomp Require Import all_ssreflect zify.
From GraphTheory Require Import preliminaries mgraph setoid_bigop structures bij.

From Yalla Require Export graph_more mll_prelim mll_def.

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
Infix "⊗" := tens (left associativity, at level 25). (* TODO other way to overload notations ? *)(* zulip *)
Infix "⅋" := parr (at level 40).
Notation "A ^" := (dual A) (at level 12, format "A ^").
Notation ll := (@ll atom).
Notation base_graph := (graph (flat rule) (flat formula)).
Notation graph_left := (@graph_left atom).
Notation graph_data := (@graph_data atom).
Notation geos := (@geos atom).
Notation proof_structure := (@proof_structure atom).
Notation proof_net := (@proof_net atom).
Infix "≃l" := iso_left (at level 79).

(* sequentialisation : fonction reliant regles à noeuds => nb cut + quels tens lies à des cut *)
(* seuentialisation sans coupure puis avec (+ de cas ou en remplacant par des tens )*)

Definition terminal_node (G : graph_left) (v : G) : bool :=
  match vlabel v with
  | ax => [forall e, (source e != v) || (vlabel (target e) == c)]
  | ⊗ | ⅋ => vlabel (target (ccl v)) == c
  | cut => true
  | concl_l => false
  end.
(* TODO correct faible et fort = faible et non vide *)

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
  enough (Hm : forall n (G : proof_structure), #|G| = n -> ll (sequent G))
    by (intro G; by apply (Hm #|G|)).
  intro n; induction n as [n IH] using lt_wf_rect; intros G Hc.
Abort.
(* TODO voir derniere quest exam et focalisation *)


(** ** Sequentialization *)
(* many things to do: spliting tens / cut, blocking parr, always a
  terminal parr or a splitting *)
(* function to turn a ps into a sequential proof *)
(* TOTHINK utiliser seulement connexité left possible (ie pas besoin de demontrer que
un graphe de correc correct ac notre def) ? to check, parr bloquant *)
End Atoms.