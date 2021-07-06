(*
Compilation time increases greatly by nomming vertices with let,
relativily to the number of sum types.
Slow down occurs when computing "induced S".
The given run times are at best inaccurate.
*)
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import mgraph.
Open Scope graph_scope.

Definition quick_lv2 {Lv Le : Type} (l0 l1 l2 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 in
  let G2 := G1 ∔ [inl (inl (inl (source e))), elabel e, inr tt]
               ∔ [inr tt, elabel e, inl (inr tt)]
               ∔ [inl (inr tt), elabel e, inl (inl (inr tt))] in
  let S : {set G2} := setT :\ inl (inl (inl (target e))) in
  induced S. (* < 1 s *)
Definition inter_lv2 {Lv Le : Type} (l0 l1 l2 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 in
  let s := inl (inl (inl (source e))) : G1 in
  let v0 := inr tt : G1 in
  let v1 := inl (inr tt) : G1 in
  let v2 := inl (inl (inr tt)) : G1 in
  let G2 := G1 ∔ [s, elabel e, v0]
               ∔ [v0, elabel e, v1]
               ∔ [v1, elabel e, v2] in
  let S : {set G2} := setT :\ inl (inl (inl (target e))) in
  induced S. (* < 1 s *)
Definition slow_lv2 {Lv Le : Type} (l0 l1 l2 : Lv) {G : graph Lv Le} (e : edge G) :=
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
  induced S. (* 1 s *)
Definition quick_lv3 {Lv Le : Type} (l0 l1 l2 l3 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 ∔ l3 in
  let G2 := G1 ∔ [inl (inl (inl (inl (source e)))), elabel e, inr tt]
               ∔ [inr tt, elabel e, inl (inr tt)]
               ∔ [inl (inr tt), elabel e, inl (inl (inr tt))]
               ∔ [inl (inl (inr tt)), elabel e, inl (inl (inl (inr tt)))] in
  let S : {set G2} := setT :\ inl (inl (inl (inl (target e)))) in
  induced S. (* < 1 s *)
Definition inter_lv3 {Lv Le : Type} (l0 l1 l2 l3 : Lv) {G : graph Lv Le} (e : edge G) :=
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
  induced S. (* 3 s *)
(*
Definition slow_lv3 {Lv Le : Type} (l0 l1 l2 l3 : Lv) {G : graph Lv Le} (e : edge G) :=
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
  induced S. (* > 10 s + crash computer *) *)
Definition quick_lv4 {Lv Le : Type} (l0 l1 l2 l3 l4 : Lv) {G : graph Lv Le} (e : edge G) :=
  let G1 := G ∔ l0 ∔ l1 ∔ l2 ∔ l3 ∔ l4 in
  let G2 := G1 ∔ [inl (inl (inl (inl (inl (source e))))), elabel e, inr tt]
               ∔ [inr tt, elabel e, inl (inr tt)]
               ∔ [inl (inr tt), elabel e, inl (inl (inr tt))]
               ∔ [inl (inl (inr tt)), elabel e, inl (inl (inl (inr tt)))]
               ∔ [inl (inl (inl (inr tt))), elabel e, inl (inl (inl (inl (inr tt))))] in
  let S : {set G2} := setT :\ inl (inl (inl (inl (inl (target e))))) in
  induced S. (* < 1 s *)
(*
Definition inter_lv4 {Lv Le : Type} (l0 l1 l2 l3 l4 : Lv) {G : graph Lv Le} (e : edge G) :=
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
  induced S. (* > 10 s + crash computer *) *)

(* unification matchcomp, inference structure canonique ? *)
(* classe ? échelle coq *) (* TOTHINK Damien Pous *)
(* TODO deconstruct induced to see where the problem arise *)