(* Sequentialisation - Definition of a sequentializing vertex *)
(* From a Proof Net, return a LL proof of the same sequent *)

From Coq Require Import Bool.
From OLlibs Require Import dectype.
Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden, notation-incompatible-prefix".
From GraphTheory Require Import mgraph setoid_bigop structures.

From Yalla Require Export mll_def mll_seq_to_pn.

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
Notation proof_structure := (@proof_structure atom).
Notation proof_net := (@proof_net atom).

Definition sequentializing {G : proof_net} (v : G) : Type :=
  match vlabel v with
  | ax => {A : formula & G ≃ ax_pn A}
  | ⊗ => {'(G0, G1) : proof_net * proof_net & G ≃ add_node_ps_tens G0 G1}
  | ⅋ => {G0 : proof_net & G ≃ add_node_ps_parr G0}
  | cut => {'(G0, G1) : proof_net * proof_net & G ≃ add_node_ps_cut G0 G1}
  | c => void (* a conclusion node is never sequentializing *)
  end.

(* TODO almost useless file? put this definition in mll_basic? or take lemmas from mll_basic here? *)
End Atoms.
