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
  enough (Hm : forall n (G : proof_structure), #|G| = n -> ll (sequent G))
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
