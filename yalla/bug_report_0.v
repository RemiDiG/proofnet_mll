(*
Compilation time increases greatly by nomming vertices with let,
relativily to the number of sum types.
Slow down occurs when computing "induced S".
The given run times are at best inaccurate.
*)
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden".
From GraphTheory Require Import mgraph.
Open Scope graph_scope.
Set Default Timeout 10. (* Stop running after 10 secondes *)

Time Definition quick_lv2 {Lv Le : Type} (l0 l1 l2 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 in
  let G2 := G1 ∔ [inl (inl (inl (source e))), elabel e, inr tt]
               ∔ [inr tt, elabel e, inl (inr tt)]
               ∔ [inl (inr tt), elabel e, inl (inl (inr tt))] in
  let S : {set G2} := setT :\ inl (inl (inl (target e))) in
  induced S. (* 0.02 secs *)

Time Definition inter_lv2 {Lv Le : Type} (l0 l1 l2 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 in
  let s := inl (inl (inl (source e))) : G1 in
  let v0 := inr tt : G1 in
  let v1 := inl (inr tt) : G1 in
  let v2 := inl (inl (inr tt)) : G1 in
  let G2 := G1 ∔ [s, elabel e, v0]
               ∔ [v0, elabel e, v1]
               ∔ [v1, elabel e, v2] in
  let S : {set G2} := setT :\ inl (inl (inl (target e))) in
  induced S. (* 0.13 secs *)

Time Definition slow_lv2 {Lv Le : Type} (l0 l1 l2 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 in
  let s := inl (inl (inl (source e))) : G1 in
  let v0 := inr tt : G1 in
  let v1 := inl (inr tt) : G1 in
  let v2 := inl (inl (inr tt)) : G1 in
  let G2 := G1 ∔ [s, elabel e, v0]
               ∔ [v0, elabel e, v1]
               ∔ [v1, elabel e, v2] in
  let t := inl (inl (inl (target e))) : G2 in
  let S : {set G2} := setT :\ t in
  induced S. (* 0.5 secs *)

Time Definition quick_lv3 {Lv Le : Type} (l0 l1 l2 l3 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 ∔ l3 in
  let G2 := G1 ∔ [inl (inl (inl (inl (source e)))), elabel e, inr tt]
               ∔ [inr tt, elabel e, inl (inr tt)]
               ∔ [inl (inr tt), elabel e, inl (inl (inr tt))]
               ∔ [inl (inl (inr tt)), elabel e, inl (inl (inl (inr tt)))] in
  let S : {set G2} := setT :\ inl (inl (inl (inl (target e)))) in
  induced S. (* 0.03 secs *)

Time Definition inter_lv3 {Lv Le : Type} (l0 l1 l2 l3 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 ∔ l3 in
  let s := inl (inl (inl (inl (source e)))) : G1 in
  let v0 := inr tt : G1 in
  let v1 := inl (inr tt) : G1 in
  let v2 := inl (inl (inr tt)) : G1 in
  let v3 := inl (inl (inl (inr tt))) : G1 in
  let G2 := G1 ∔ [s, elabel e, v0]
               ∔ [v0, elabel e, v1]
               ∔ [v1, elabel e, v2]
               ∔ [v2, elabel e, v3] in
  let S : {set G2} := setT :\ inl (inl (inl (inl (target e)))) in
  induced S. (* 3 secs *)

Fail Time Definition slow_lv3 {Lv Le : Type} (l0 l1 l2 l3 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 ∔ l3 in
  let s := inl (inl (inl (inl (source e)))) : G1 in
  let v0 := inr tt : G1 in
  let v1 := inl (inr tt) : G1 in
  let v2 := inl (inl (inr tt)) : G1 in
  let v3 := inl (inl (inl (inr tt))) : G1 in
  let G2 := G1 ∔ [s, elabel e, v0]
               ∔ [v0, elabel e, v1]
               ∔ [v1, elabel e, v2]
               ∔ [v2, elabel e, v3] in
  let t := inl (inl (inl (inl (target e)))) : G2 in
  let S : {set G2} := setT :\ t in
  induced S. (* > 10 secs + crash computer if remove timeout *)

Time Definition quick_lv4 {Lv Le : Type} (l0 l1 l2 l3 l4 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 ∔ l3 ∔ l4 in
  let G2 := G1 ∔ [inl (inl (inl (inl (inl (source e))))), elabel e, inr tt]
               ∔ [inr tt, elabel e, inl (inr tt)]
               ∔ [inl (inr tt), elabel e, inl (inl (inr tt))]
               ∔ [inl (inl (inr tt)), elabel e, inl (inl (inl (inr tt)))]
               ∔ [inl (inl (inl (inr tt))), elabel e, inl (inl (inl (inl (inr tt))))] in
  let S : {set G2} := setT :\ inl (inl (inl (inl (inl (target e))))) in
  induced S. (* 0.2 secs *)

Fail Time Definition inter_lv4 {Lv Le : Type} (l0 l1 l2 l3 l4 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 ∔ l3 ∔ l4 in
  let s := inl (inl (inl (inl (inl (source e))))) : G1 in
  let v0 := inr tt : G1 in
  let v1 := inl (inr tt) : G1 in
  let v2 := inl (inl (inr tt)) : G1 in
  let v3 := inl (inl (inl (inr tt))) : G1 in
  let v4 := inl (inl (inl (inl (inr tt)))) : G1 in
  let G2 := G1 ∔ [s, elabel e, v0]
               ∔ [v0, elabel e, v1]
               ∔ [v1, elabel e, v2]
               ∔ [v2, elabel e, v3]
               ∔ [v3, elabel e, v4] in
  let S : {set G2} := setT :\ inl (inl (inl (inl (inl (target e))))) in
  induced S. (* > 10 secs + crash computer if remove timeout *)

(* unification matchcomp, inference structure canonique ? *)
(* classe ? échelle coq *) (* TOTHINK Damien Pous *)
(* TODO deconstruct induced to see where the problem arise *)

(* Unfold the definition of induced *)
Time Definition inter_lv3' {Lv Le : Type} (l0 l1 l2 l3 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 ∔ l3 in
  let s := inl (inl (inl (inl (source e)))) : G1 in
  let v0 := inr tt : G1 in
  let v1 := inl (inr tt) : G1 in
  let v2 := inl (inl (inr tt)) : G1 in
  let v3 := inl (inl (inl (inr tt))) : G1 in
  let G2 := G1 ∔ [s, elabel e, v0]
               ∔ [v0, elabel e, v1]
               ∔ [v1, elabel e, v2]
               ∔ [v2, elabel e, v3] in
  let S : {set G2} := setT :\ inl (inl (inl (inl (target e)))) in
  subgraph_for (@induced_proof _ _ _ S). (* 3 secs *)

Fail Time Definition inter_lv3'' {Lv Le : Type} (l0 l1 l2 l3 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 ∔ l3 in
  let s := inl (inl (inl (inl (source e)))) : G1 in
  let v0 := inr tt : G1 in
  let v1 := inl (inr tt) : G1 in
  let v2 := inl (inl (inr tt)) : G1 in
  let v3 := inl (inl (inl (inr tt))) : G1 in
  let G2 := G1 ∔ [s, elabel e, v0]
               ∔ [v0, elabel e, v1]
               ∔ [v1, elabel e, v2]
               ∔ [v2, elabel e, v3] in
  let S : {set G2} := setT :\ inl (inl (inl (inl (target e)))) in
  (@induced_proof _ _ _ S). (* Timeout ! *)
(* Euh, kezako ? *)

