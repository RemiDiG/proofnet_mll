(* Unit-free MLL following Yalla schemas *)


From Coq Require Import Bool Wf_nat Lia.
From OLlibs Require Import dectype funtheory List_more List_Type Permutation_Type_more.
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries mgraph.
(* Bizarrement les arguments implicitent ne fonctionnent plus .... *)
(* ex: Arguments ex_r {l1} {l2} pi0 sigma.
  sans effet, demande toujours 4 arguments *)

Import EqNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(** * MLL formulas *)

Section Atoms.

(** A set of atoms for building formulas *)
Context { atom : DecType }.

(** Formulas *)
Inductive formula :=
| var : atom -> formula
| covar : atom -> formula
| tens : formula -> formula -> formula
| parr : formula -> formula -> formula.
Notation "'ν' X" := (var X) (at level 12).
Notation "'κ' X" := (covar X) (at level 12).
Infix "⊗" := tens (at level 40).
Infix "⅋" := parr (at level 40).

(** ** Equality of [formula] in [bool] *)
Fixpoint eqb_form A B :=
match A, B with
| var X, var Y => dectype.eqb X Y
| covar X, covar Y => dectype.eqb X Y
| tens A1 A2, tens B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| parr A1 A2, parr B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| _, _ => false
end.

Lemma eqb_eq_form : forall A B, eqb_form A B = true <-> A = B.
Proof.
induction A; destruct B; (split; intros Heq); inversion Heq; auto.
- now apply eqb_eq in H0; subst.
- now subst; cbn; apply eqb_eq.
- now apply eqb_eq in H0; subst.
- now subst; cbn; apply eqb_eq.
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  now apply IHA1 in H1; apply IHA2 in H2; subst.
- now subst; cbn; apply andb_true_iff; split; [ apply IHA1 | apply IHA2 ].
- apply andb_true_iff in H0 as [H1 H2].
  now apply IHA1 in H1; apply IHA2 in H2; subst.
- now subst; cbn; apply andb_true_iff; split; [ apply IHA1 | apply IHA2 ].
Qed.

Definition formulas_dectype := {|
  car := formula;
  dectype.eqb := eqb_form;
  eqb_eq := eqb_eq_form |}.

(** ** Dual of a [formula] *)
Fixpoint dual A :=
match A with
| var x     => covar x
| covar x   => var x
| tens A B  => parr (dual B) (dual A)
| parr A B  => tens (dual B) (dual A)
end.
Notation "A ^" := (dual A) (at level 12, format "A ^").

Lemma bidual A : dual (dual A) = A.
Proof. now induction A; cbn; rewrite ? IHA1 ? IHA2 ? IHA. Qed.

Lemma codual A B : dual A = B <-> A = dual B.
Proof. now split; intro H; rewrite <- (bidual A), <- (bidual B), H, ? bidual. Qed.

Lemma dual_inj : injective dual.
Proof. now intros A B H; rewrite <- (bidual A), <- (bidual B), H. Qed.

(** ** Size of a [formula] as its number of symbols *)
Fixpoint fsize A :=
match A with
| var X    => 1
| covar X  => 1
| tens A B => S (fsize A + fsize B)
| parr A B => S (fsize A + fsize B)
end.

Lemma fsize_pos A : 0 < fsize A.
Proof. induction A; cbn; by []. Qed.

Lemma fsize_dual A : fsize (dual A) = fsize A.
Proof. induction A; cbn; rewrite ? IHA1 ? IHA2; trivial; apply eq_S; apply addnC. Qed.


(** * MLL Proofs *)
Inductive ll : list formula -> Type :=
| ax_r : forall X, ll (covar X :: var X :: nil)
| ex_r : forall l1 l2, ll l1 -> Permutation_Type l1 l2 -> ll l2
| tens_r : forall A B l1 l2, ll (A :: l1) -> ll (B :: l2) -> ll (tens A B :: l2 ++ l1)
| parr_r : forall A B l, ll (A :: B :: l) -> ll (parr A B :: l)
| cut_r : forall A l1 l2 l3 l4, ll (l1 ++ A :: l2) ->
             ll (l3 ++ dual A :: l4) -> ll (l3 ++ l2 ++ l1 ++ l4).
Notation "⊢ l" := (ll l) (at level 70).



(** ** Size of proofs *)
Fixpoint psize l (pi : ll l) :=
match pi with
| ax_r _ => 1
| ex_r _ _ pi0 _ => S (psize pi0)
| tens_r _ _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
| parr_r _ _ _ pi0 => S (psize pi0)
| cut_r _ _ _ _ _ pi0 pi1 => S (psize pi0 + psize pi1)
end.

Lemma psize_pos l (pi : ll l) : 0 < psize pi.
Proof. destruct pi; cbn; by []. Qed.

Lemma psize_rew l l' (pi : ll l) (Heq : l = l') : psize (rew Heq in pi) = psize pi.
Proof. now subst. Qed.


(*******************************************************************************************************************)
(** * Preliminaries: Cases on 'I_2 and 'I_3 *)
(* todo, cases for 'I_2 and I_3 *)
(* use val as a coercion 'I_n >-> nat ? *)

Lemma case_2 : forall n : 'I_2, n = inord 0 \/ n = inord 1.
destruct n as [n o].
destruct n as [ | n].
- left. Search inord. rewrite (inord_val ord0). admit.
- destruct n as [ | n].
  + right. admit.
  + contradict o. by [].
Admitted.
Lemma case_3 : forall n : 'I_3, n = inord 0 \/ n = inord 1 \/ n = inord 2. Admitted.

Definition case2 {A : Type} (n : 'I_2) (a0 a1 : A) := match val n with | 0 => a0 | _ => a1 end.
Definition ftest : 'I_2 -> 'I_3 := fun (n : 'I_2) => match val n with | 0 => inord 1 | _ => inord 0 end.
Goal injective ftest.
unfold injective.
(* case study that must be done by case2 *)
case; case.
  intro i. case; case.
    intro j. admit.
    case.
      intro j. admit.
      intros nj j. contradict j. by [].
  case.
    intro i. case; case.
      intro j. admit.
      case.
        intro j. admit.
        intros nj j. contradict j. by [].
    intros ni i. contradict i. by [].
Abort.

(** * Level 0: Multigraphs *)
(* From the library GraphTheory *)
Open Scope graph_scope.
(* Notations from the library:
  G0 ⊎ G1 = disjoint union
  G ∔ [ x , u , y ] = add an arrow from x to y labelled u *)


(** * Level 1: Multigraphs with some more data *)

(** Type [rule] for the labels of the vertices *)
Inductive rule : Type :=
| ax_l
| tens_l
| parr_l
| cut_l
| concl_l.

(* Equality of [rule] *)
Definition eqb_rule (A : rule) (B : rule) : bool :=
match A, B with
| ax_l, ax_l => true
| tens_l, tens_l => true
| parr_l, parr_l => true
| cut_l, cut_l => true
| concl_l, concl_l => true
| _, _ => false
end.

Lemma eqb_eq_rule : forall A B, eqb_rule A B = true <-> A = B.
Proof.
destruct A, B; split; intro H; simpl; simpl in H; trivial; contradict H; easy.
Qed.

Definition rules_dectype := {|
  car := rule;
  dectype.eqb := eqb_rule;
  eqb_eq := eqb_eq_rule |}. (* see if necessary or not *)


Set Primitive Projections.
Record graph_data : Type :=
  Graph_data {
      graph_of :> graph rule formula; (* Vertex label: rule ; Arrow label: formula *)
      order : [finType of { v : graph_of | eqb_rule (vlabel v) concl_l}] -> 'I_#|[finType of { v : graph_of | eqb_rule (vlabel v) concl_l}]|;
      order_inj : injective order;
      direction : bool -> [finType of { v : graph_of | eqb_rule (vlabel v) tens_l || eqb_rule (vlabel v) parr_l }] -> edge graph_of;
  }.
Unset Primitive Projections.
Notation left := (direction false).
Notation right := (direction true).
(* TOTHINK other possibilities for the functions:
  - use [set v : vertex graph_of| eqb_rule (vlabel v) concl_l], once known how to turn it into a functional domain
    ou bien avec des v \in [f @^-1: {set}] pour les conditions sur label
  - faire des fonctions depuis les ensembles totaux vers option _ puis lemma pour label ok <-> Some _
    ex:
      order : graph_of -> option nat;
      order_ok : forall v, exists n, order v = Some n <-> vlabel v = concl_l /\ order v <= nb nodes concl;
          en fait si injectif, pas necessaire d'avoir la dernière condition, qui semble etre la plus difficile comme #|_| est dur à calculer
      direction : bool -> graph_of -> option_finType (edge graph_of);
      direction_ok : forall b v, direction b v = Some _ <-> (vlabel c = tens_l \/ vlabel c = parr_l);
  - see sig_finType, used for the function sub_edge in the graph lib
  - other way to define bijections for order: surj instead of inj, from I_n -> vertices, ...
  - something else ?
  + define order as a permutation of the finset
    as finset = seq = list, easier to manipulate (see the book, 7.7)
*)
(* TOTHINK define only left (instead of direction) and deduce right from it ? *)

(* /!\ faire lemma (admitted dependant des defs), pour utiliser independamment de la def choisie *)

Lemma bij_order {G : graph_data} : bijective (order (g:=G)).
Proof.
Admitted.
(* if not bij : use lemma f_finv pour inverse à gauche *)


(** Base case: graph of an axiom **)
Definition graph_ax (x : atom) : graph rule formula := {|
  vertex := [finType of 'I_3];
  edge := [finType of 'I_2];
  endpoint := fun b => match b with
    | true => fun e => match val e with
        | 0 => inord 1
        | _ => inord 2
    end
    | false => fun _ => inord 0
  end;
  vlabel := fun v => match val v with
    | 0 => ax_l
    | _ => concl_l
  end;
  elabel := fun e => match val e with
    | 0 => covar x
    | _ => var x
  end;
|}.

Lemma ax_nb_concl (x : atom) : #|[set v : vertex (graph_ax x) | eqb_rule (vlabel v) concl_l]| = 2.
Proof.
Compute #|[set v : vertex (graph_ax x) | eqb_rule (vlabel v) concl_l]|.
rewrite cardsE. cbn.
Admitted. (* voir cmt faire des pruves sur #|_| *)

(* error with 'I_#|[set v : vertex graph_of| eqb_rule (vlabel v) concl_l]|: coq donesn't know if 1\in I_... *)
Definition order_ax (x : atom) : [finType of { v : graph_ax x | eqb_rule (vlabel v) concl_l}] -> 'I_2 :=
  fun v => match val (val v) with
  | 1 => inord 0
  | _ => inord 1
  end.
(* possible d'utiliser le lemma pour remplacer 'I_2 par 'I_#|[set v : vertex (graph_ax x) | eqb_rule (vlabel v) concl_l]| ? *)
(* ça fait bizarre de mettre 2 val, je ne suis pas sur que ça se fait comme ça -> utiliser val comme coercion ? *)
(* To see why we use val val *)(*
Variable y:atom.
Variable w:[finType of { v : graph_ax y | eqb_rule (vlabel v) concl_l}].
Check val.
Check val w.
Check val (val w).
Check nat_choiceType.
*)

Lemma order_ax_inj (x : atom) : injective (order_ax (x := x)).
Proof.
  unfold injective.
Admitted. (* use preliminaries *)

Lemma graph_ax_no_dir (x : atom) : { v : (graph_ax x) | eqb_rule (vlabel v) tens_l || eqb_rule (vlabel v) parr_l } = void.
Proof.
Admitted. (* pas sur que ce soit la bonne facon de dire que c'est vide *)

Definition direction_ax (x : atom) : bool -> { v : (graph_ax x) | eqb_rule (vlabel v) tens_l || eqb_rule (vlabel v) parr_l } -> edge (graph_ax x) :=
  fun b => fun _ => inord 0.
(* faire comprendre avec lemma au-dessus que vfun suffit *)

(* Coq cannot identify 'I_2 and 'I_#|[set v : vertex (graph_ax x) | eqb_rule (vlabel v) concl_l]|
Definition graph_data_ax (x : atom) : graph_data := {|
  graph_of := graph_ax x;
  order := order_ax (x := x);
  order_inj := order_ax_inj x;
  direction := direction_ax x |}.
*)


(** * Level 2: Proof Structure *)
(* The rule of a node gives conditions on its arrows *)
Section Propertness.

Definition edges_out_at {G : graph_data} (v : G) := [set e | source e == v].
Definition edges_in_at {G : graph_data} (v : G) := [set e | target e == v].

(* Out-degree of a node according to its rule *)
Definition out_deg (r : rule) := match r with
| ax_l => 2
| tens_l => 1
| parr_l => 1
| cut_l => 0
| concl_l => 0
end.

(* In-degree of a node according to its rule *)
Definition in_deg (r : rule) := match r with
| ax_l => 0
| tens_l => 2
| parr_l => 2
| cut_l => 2
| concl_l => 1
end.

Definition proper_degree (G : graph_data) :=
  [forall v in G, (#|edges_out_at v| == out_deg (vlabel v))
               && (#|edges_in_at v| == in_deg (vlabel v))].

Definition proper_direction (G : graph_data) :=
  [forall v in [finType of { v : G | eqb_rule (vlabel v) tens_l || eqb_rule (vlabel v) parr_l }],
  [forall b, direction b v \in edges_in_at (proj1_sig v)] &&
  ~~(direction false v == direction true v)].
(* make coercions to forget the proj and val ? *)

(* error: atom = DecType <> finType -> refuses to use it in [...] *)
(*
Definition proper_ax (G : graph_data) :=
  [forall (v : G | eqb_rule (vlabel v) ax_l), exists x,
  (exists e, (e \in edges_out_at v) && eqb_form (elabel e) (covar x))
  && (exists e, (e \in edges_out_at v) && eqb_form (elabel e) (var x))].
*)

(* possible de mieux faire si on a une fonction qui recupère l'unique element d'un set *)
(* function {s} |-> s : essayer pick ? *)
Definition proper_tens (G : graph_data) :=
  [forall v in [finType of { v : G | eqb_rule (vlabel v) tens_l || eqb_rule (vlabel v) parr_l }],
  eqb_rule (vlabel (proj1_sig v)) tens_l ==>
  [exists e, (e \in edges_out_at (proj1_sig v)) &&
  eqb_form (elabel e) (tens (elabel (left v)) (elabel (right v)))]].

Definition proper_parr (G : graph_data) :=
  [forall v in [finType of { v : G | eqb_rule (vlabel v) tens_l || eqb_rule (vlabel v) parr_l }],
  eqb_rule (vlabel (proj1_sig v)) parr_l ==>
  [exists e, (e \in edges_out_at (proj1_sig v)) &&
  eqb_form (elabel e) (parr (elabel (left v)) (elabel (right v)))]].

(* meme pb que pout ax *)
(*
Definition proper_cut (G : graph_data) :=
  [forall (v : G | eqb_rule (vlabel v) cut_l), exists x,
  (exists e, (e \in edges_in_at v) && eqb_form (elabel e) (covar x))
  && (exists e, (e \in edges_in_at v) && eqb_form (elabel e) (var x))].
*)

Record proof_structure : Type :=
  Proof_structure {
    graph_ps :> graph_data;
    p_deg : proper_degree graph_ps;
    p_dir : proper_direction graph_ps;
    (* p_ax : proper_ax graph_ps; *)
    p_tens : proper_tens graph_ps;
    p_parr : proper_parr graph_ps;
    (* p_cut : proper_cut graph_ps; *)
  }.

End Propertness.

(*
(* Function which takes a conclusion vertex and return its unique (input) edge *)
(* same as always, only for v where vlavel v = concl_l *)
Definition edge_of_concl {G : proof_structure} (v : G) : edge G := ???.
(* use fintype1 ? *)

(* Function which takes a conclusion vertex and return the formula on its edge *)
Definition formula_of_concl {G : proof_structure} (v : G) : formula :=  elabel (edge_of_concl v).

(* Sequent proved by the proof structure *)
Definition sequent (G : proof_structure) : list formula := ???.

Lemma proper_graph_ax (x : atom): proper_... (graph_data_ax x).
Proof.
Admitted.

Definition ps_ax (x : atom) : proof_structure := {|
  graph_ps := graph_data_ax x;
  ... |}.
*)

(** * Proof Structure of a Proof Sequent *)
(* Function at each level *)
(* pas au level 0: on doit savoir qui est le premier sommet conclusion pour le retirer (tens et parr)
-> faire la construction au level 1, puis lemma pour proper de la construction par induction
  ce qui donne level 2 *)

(*
Fixpoint graph_proof {l : list formula} (pi : ll l) : graph_data := match pi with
| ax_r x => graph_data_ax x
| ex_r _ _ pi0 sigma => graph_proof pi0
| tens_r _ _ _ _ pi0 pi1 => let gd0 := graph_proof pi0 in let gd1 := graph_proof pi1 in
    let gd := gd0 ⊎ gd1 in gd0
(* take 1st concl with order-1(0) -> use finv *)
| parr_r _ _ _ pi0 => 
| cut_r _ _ _ _ _ pi0 pi1 => 
end.
*)

(*
+inductive proof that ps(pi) is a proof_structure
+inductive proof that order list of l (pi : ll l) corresponds to order c_i of the graph
*)


(*
Fixpoint ps {l : list formula} (pi : ll l) : proof_structure :=
match pi with
| ax_r X => graph with a node labelled ax, two nodes c_1 and c_2, 
    an edge ax->c_1 labelled covar X, another ax->c_2 labelled var X

| ex_r pi0 sigma => take ps (pi_0), re-label the c_i into c_sigma(i):
  turn the perm on list of formulas into one on list of integers, should be easy?
About Permutation_Type. -> make the list of [c_i], apply perm on it, then re-label nodes c

| tens_r pi0 pi1 => take G0=ps (pi0) and G1=ps (pi1)
    In G0: turn c_i into c_n+i-1 for i\neq0, for c_0 turn into c_inf, with n =#conc in G1
    make a disjoint union of G0 and G1
    find edges on c_0 and c_n, and their endpoints (char. proof str. -> unicity)
    remove edges ?1->c_0 (B), ?0->c_inf(A)
    remove nodes c0 c_inf
    add nodes t(tens) c0
    add edges ?0->t (A,0), ?1->t (B,1), t->c_0 (tens A B)

| parr_r pi0 => take G0=ps (pi0)
    find edges on c_0 and c_1, and their endpoints (char. proof str. -> unicity)
    remove edges ?0->c_0 (A), ?1->c_1(B)
    remove nodes c0 c_1
    re-label c_i into c_i-1
    add nodes p(parr) c0
    add edges ?0->p (A,0), ?1->p (B,1), p->c_0 (parr A B)

| cut_r A l1 l2 l3 l4 pi0 pi1 => take 0=ps (pi0) and G1=ps (pi1), ni=#li for all i
    In G0: turn c_i into c_n3+n2+i for i<n1, for c_n1 turn into c_inf1, c_n3+(i-n1) otherwise
    In G1: for c_n3 turn into c_inf2,  c_n3+n2+n1+(i-n3) for i>n3
    make a disjoint union of G0 and G1
    find edges on c_inf0 and c_inf1, and their endpoints (char. proof str. -> unicity)
    remove edges ?0->c_inf0 (var A), ?1->c_inf1(covar A)
    remove nodes cinf0 c_inf1
    add nodes c(cut)
    add edges ?0->c (var A,0), ?1->c (covar A,1)
*)


(** * Correctness Criteria: Danos-Regnier *)
(* Switching Graph *)
(* SG (PS):
for a proof structure PS, get P the nodes labelled parr, then a s.g. is given by:
phi: P -> B, G_phi = G where on node v\in P, arrow ?->v(A,phi(v)) is deleted, add node c_v, edge ?->c_v(A)
    then remove direction
*)

(* Criteria: acyclic and connected *)
(* need def for acyclic + connected, or just for tree (tree in the lib) ?-> considering trees may change the proofs *)

(*
Definition is_correct PS :=
  forall phi, acyclic SG (PS) (phi) /\ connected SG (PS) (phi).
or with is_tree (already in the lib) ???
  forall phi, is_tree SG (PS) (phi).
*)

(* Soundness of correctness *)
(*
Lemma sound l (pi : ll l) : is_correct ps (pi).
*)

(** * Cut Elimination *)
(*
Inductive red : 
| ax->cut: merge the 2 nodes, then merge the final node with the node above, keep label of above
| tens->cut<-parr: merge the 3 nodes into the cut one, then split it with the good edges, give label cut to both
=> need procedure merge, where a parent node absorb another, keeping its own label (may be used before instead of removing edge then adding edge ???)
*)
(* lemma: if R is correct and R reduces to R', then R' is correct *)
(* lemma: applying red while we can yields a cut-free ps:
    there is a cut node => one of the two subgraphs (*2 by symmetry) => reduction to another graph *)
(* lemma: sub-confluence + convergence *)

(** * Sequentialization *)
(* many things to do: spliting tens / cut, blocking parr, always a terminal parr or a splitting *)
(* function to turn a ps into a sequential proof *)



(*******************************************************************************************************************)
(** * PREVIOUS CONTENT of the file mll.v *)

(** * Cut Elimination *)

Ltac destruct_eqrefl H :=
list_simpl in H;
match goal with
| H : ?x = ?x |- _ => assert (H = eq_refl) as ->
                        by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                      cbn
end.

(** Symmetric induction principle *)
Lemma sym_induction_ll (P : forall [A B l1 l2 l3 l4], ll (l1 ++ A :: l2) -> ll (l3 ++ B :: l4)
                          -> Type) :
  (forall A B l1 l2 l3 l4 (pi1 : ll (l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)),
     P pi2 pi1 -> P pi1 pi2) ->
  (forall X B l3 l4 (pi2 : ll (l3 ++ B :: l4)),
     P (ax_r X : ll (nil ++ covar X :: var X :: nil)) pi2) ->
  (forall X B l3 l4 (pi2 : ll (l3 ++ B :: l4)),
     P (ax_r X : ll ((covar X :: nil) ++ var X :: nil)) pi2) ->
  (forall A B l1 l2 l3 l4 l' (pi1 : ll l') (pi2 : ll (l3 ++ B :: l4))
     (HP : Permutation_Type l' (l1 ++ A :: l2)),
     P (rew (rew (surjective_pairing (proj1_sig (Permutation_Type_vs_elt_inv _ _ _ HP)))
              in proj2_sig (Permutation_Type_vs_elt_inv _ _ _ HP)) in pi1) pi2 ->
     P (ex_r pi1 HP) pi2) ->
  (forall A B C D l0 l1 l2 l3 l4 (pi0 : ll (C :: l0))
     (pi1 : ll (D :: l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)),
     P (pi1 : ll ((D :: l1) ++ A :: l2)) pi2 ->
     P (rew <- (app_assoc (tens C D :: l1) (A :: l2) _) in tens_r pi0 pi1) pi2) ->
  (forall A B C D l0 l1 l2 l3 l4 (pi0 : ll (D :: l0))
     (pi1 : ll (C :: l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)),
     P (pi1 : ll ((C :: l1) ++ A :: l2)) pi2 ->
     P (rew (app_assoc (tens C D :: l0) _ (A :: l2)) in tens_r pi1 pi0 ) pi2) ->
  (forall A B C D l1 l2 l3 l4 (pi1 : ll (C :: D :: l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)),
     P (pi1 : ll ((C :: D :: l1) ++ A :: l2)) pi2 ->
     P (parr_r pi1 : ll ((parr C D :: l1) ++ A :: l2)) pi2) ->
  (forall C D C' D' l2' l2'' (pi1' : ll (C :: l2')) (pi1'' : ll (D :: l2'')),
     (forall l3 l4 (pi2 : ll (l3 ++ C' :: l4)), P (pi1' : ll (nil ++ _)) pi2) ->
     (forall l3 l4 (pi2 : ll (l3 ++ D' :: l4)), P (pi1'' : ll (nil ++ _)) pi2) ->
     forall l4' l4'' (pi2' : ll (C' :: l4')) (pi2'' : ll (D' :: l4'')),
       P (tens_r pi1' pi1'' : ll (nil ++ _)) (tens_r pi2' pi2'' : ll (nil ++ _))) ->
  (forall C D C' D' l2 (pi1 : ll (C :: D :: l2)),
     (forall l3 l4 (pi2 : ll (l3 ++ C' :: l4)), P (pi1 : ll (nil ++ _)) pi2) ->
      forall l4 (pi2 : ll (C' :: D' :: l4)),
       P (parr_r pi1 : ll (nil ++ _)) (parr_r pi2 : ll (nil ++ _))) ->
  (forall C D C' D' l1' l1'' (pi1' : ll (C :: l1')) (pi1'' : ll (D :: l1'')),
     (forall l3 l4 (pi2 : ll (l3 ++ C' :: l4)), P (pi1' : ll (nil ++ _)) pi2) ->
     (forall l3 l4 (pi2 : ll (l3 ++ D' :: l4)), P (pi1'' : ll (nil ++ _)) pi2) ->
     forall l4 (pi2 : ll (D' :: C' :: l4)),
       P (tens_r pi1' pi1'' : ll (nil ++ _)) (parr_r pi2 : ll (nil ++ _))) ->
  forall A B l1 l2 l3 l4 (pi1 : ll (l1 ++ A :: l2)) (pi2 : ll (l3 ++ B :: l4)), P pi1 pi2.
Proof.
intros Hsym Hax1 Hax2 Hex Htens1 Htens2 Hparr Htt Hpp Htp.
enough (forall c s A B s1 s2 (pi1 : ll s1) (pi2 : ll s2),
          s = psize pi1 + psize pi2 -> fsize A <= c -> fsize B <= c ->
          forall l1 l2 l3 l4 (Heq1 : s1 = l1 ++ A :: l2) (Heq2 : s2 = l3 ++ B :: l4),
          P A B l1 l2 l3 l4 (rew Heq1 in pi1) (rew Heq2 in pi2)) as IH
  by (now intros A B l1 l2 l3 l4 pi1 pi2;
          refine (IH (max (fsize A) (fsize B)) _ _ _ _ _ pi1 pi2 _ _ _ _ _ _ _ eq_refl eq_refl);
          try lia).
induction c as [c IHf0] using lt_wf_rect.
assert (forall A B, fsize A < c -> fsize B < c ->
          forall l1 l2 l3 l4 pi1 pi2, P A B l1 l2 l3 l4 pi1 pi2) as IHf
  by (now intros A B HA HB l1 l2 l3 l4 pi1 pi2;
          refine (IHf0 (max (fsize A) (fsize B)) _ _ A _ _ _ pi1 pi2 _ _ _ _ _ _ _ eq_refl eq_refl);
          try lia); clear IHf0.
induction s as [s IHp0] using lt_wf_rect.
assert (forall A B l1 l2 l3 l4 pi1 pi2, psize pi1 + psize pi2 < s -> fsize A <= c -> fsize B <= c ->
          P A B l1 l2 l3 l4 pi1 pi2) as IHp
  by (now intros A B l1 l2 l3 l4 pi1 pi2 Hp HA HB;
          refine (IHp0 _ Hp _ _ _ _ pi1 pi2 _ _ _ _ _ _ _ eq_refl eq_refl)); clear IHp0.
intros A B s1 s2 pi1 pi2 Heqs HA HB l1 l2 l3 l4 Heq1 Heq2; rewrite_all Heqs; clear s Heqs.
destruct pi1.
- destruct l1; inversion Heq1; subst; cbn in Heq1.
  + destruct_eqrefl Heq1; apply Hax1.
  + destruct l1; inversion Heq1; subst.
    * destruct_eqrefl Heq1; apply Hax2.
    * exfalso; destruct l1; inversion Heq1.
- subst; cbn; apply Hex, IHp; cbn; rewrite ? psize_rew; lia.
- destruct l1; inversion Heq1.
  + destruct pi2; subst; cbn in HA; destruct_eqrefl Heq1.
    * repeat (destruct l3; inversion Heq2); subst; destruct_eqrefl Heq2; apply Hsym;
        [ apply Hax1 | apply Hax2 ].
    * apply Hsym, Hex, IHp; cbn; rewrite ? psize_rew; lia.
    * destruct l3; inversion Heq2; subst; cbn in HB.
      -- destruct_eqrefl Heq2.
         apply Htt; intros; apply IHf; lia.
      -- apply Hsym.
         dichot_elt_app_inf_exec H1; subst.
         ++ replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew <- (app_assoc (tens A1 B1 :: l3) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens1, IHp; cbn; try lia.
            ** rewrite <- (rew_opp_l ll (app_assoc (tens A1 B1 :: l3) (B :: l) l1)).
               f_equal; rewrite rew_compose.
               now assert (eq_trans Heq2 (app_assoc (tens A1 B1 :: l3) (B :: l) l1) = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
         ++ replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew (app_assoc (tens A1 B1 :: l6) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens2, IHp; cbn; lia.
            ** rewrite <- (rew_opp_r ll (app_assoc (tens A1 B1 :: l6) l2 (B :: l4))).
               f_equal; unfold eq_rect_r; rewrite rew_compose.
               now assert (eq_trans Heq2 (eq_sym (app_assoc (tens A1 B1 :: l6) l2 (B :: l4)))
                         = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
    * destruct l3; inversion Heq2; subst; destruct_eqrefl Heq2; cbn in HB.
      -- apply Htp; intros; apply IHf; lia.
      -- apply Hsym, Hparr, IHp; cbn; lia.
  + subst; cbn.
    dichot_elt_app_inf_exec H1; subst.
    * change ((tens A0 B0 :: l1) ++ A :: l ++ l0) with (tens A0 B0 :: l1 ++ A :: l ++ l0) in Heq1.
      replace (rew [ll] Heq1 in tens_r pi1_1 pi1_2)
         with (rew <- (app_assoc (tens A0 B0 :: l1) _ _) in tens_r pi1_1 pi1_2).
      -- apply Htens1, IHp; cbn; lia.
      -- rewrite <- (rew_opp_l ll (app_assoc (tens A0 B0 :: l1) (A :: l) l0)).
           f_equal; rewrite rew_compose.
           now assert (eq_trans Heq1 (app_assoc (tens A0 B0 :: l1) (A :: l) l0) = eq_refl)
                 as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
               cbn.
    * change ((tens A0 B0 :: l5 ++ l6) ++ A :: l2)
        with (tens A0 B0 :: (l5 ++ l6) ++ A :: l2) in Heq1.
      replace (rew [ll] Heq1 in tens_r pi1_1 pi1_2)
         with (rew (app_assoc (tens A0 B0 :: l5) _ _) in tens_r pi1_1 pi1_2).
      -- apply Htens2, IHp; cbn; lia.
      -- rewrite <- (rew_opp_r ll (app_assoc (tens A0 B0 :: l5) l6 (A :: l2))).
         f_equal; unfold eq_rect_r; rewrite rew_compose.
         now assert (eq_trans Heq1 (eq_sym (app_assoc (tens A0 B0 :: l5) l6 (A :: l2))) = eq_refl)
               as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
             cbn.
- destruct l1; inversion Heq1.
  + destruct pi2; subst; cbn in HA; destruct_eqrefl Heq1.
    * repeat (destruct l3; inversion Heq2); subst; destruct_eqrefl Heq2; apply Hsym;
        [ apply Hax1 | apply Hax2 ].
    * apply Hsym, Hex, IHp; cbn; rewrite ? psize_rew; lia.
    * destruct l3; inversion Heq2; subst; cbn in HB.
      -- destruct_eqrefl Heq2.
         apply Hsym, Htp; intros; apply IHf; lia.
      -- apply Hsym; cbn.
         dichot_elt_app_inf_exec H1; subst.
         ++ change ((tens A1 B1 :: l3) ++ B :: l ++ l1)
              with (tens A1 B1 :: l3 ++ B :: l ++ l1) in Heq2.
            replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew <- (app_assoc (tens A1 B1 :: l3) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens1, IHp; cbn; lia.
            ** rewrite <- (rew_opp_l ll (app_assoc (tens A1 B1 :: l3) (B :: l) l1)).
               f_equal; rewrite rew_compose.
               now assert (eq_trans Heq2 (app_assoc (tens A1 B1 :: l3) (B :: l) l1) = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
         ++ change ((tens A1 B1 :: l0 ++ l5) ++ B :: l4)
              with (tens A1 B1 :: (l0 ++ l5) ++ B :: l4) in Heq2.
            replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew (app_assoc (tens A1 B1 :: l0) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens2, IHp; cbn; lia.
            ** rewrite <- (rew_opp_r ll (app_assoc (tens A1 B1 :: l0) l5 (B :: l4))).
               f_equal; unfold eq_rect_r; rewrite rew_compose.
               now assert (eq_trans Heq2 (eq_sym (app_assoc (tens A1 B1 :: l0) l5 (B :: l4)))
                         = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
    * destruct l3; inversion Heq2; subst; cbn in HB; destruct_eqrefl Heq2.
      -- apply Hpp; intros; apply IHf; lia.
      -- apply Hsym, Hparr, IHp; cbn; lia.
  + subst; cbn; destruct_eqrefl Heq1.
    apply Hparr, IHp; cbn; lia.
Qed.

Theorem cut A l1 l2 l3 l4 :
  ll (l1 ++ A :: l2) -> ll (l3 ++ dual A :: l4) -> ll (l3 ++ l2 ++ l1 ++ l4).
Proof.
intros pi1 pi2; assert (Heq := eq_refl (dual A)); revert pi1 pi2 Heq.
apply (sym_induction_ll (fun A B l1 l2 l3 l4 pi1 pi2 => B = dual A -> ll (l3 ++ l2 ++ l1 ++ l4)));
  clear A l1 l2 l3 l4; cbn; try now intuition subst.
- intros A B l1 l2 l3 l4 pi1 pi2 pi ->.
  apply (ex_r (pi (eq_sym (bidual A)))).
  rewrite (app_assoc l1), (app_assoc l3); apply Permutation_Type_app_comm.
- intros A B l1 l2 l3 l4 l' pi1 pi2 HP.
  destruct (Permutation_Type_vs_elt_inv A l1 l2 HP) as [(l1', l2') ->]; cbn in pi1, HP; cbn.
  intros pi0' pi0; apply pi0' in pi0; clear - HP pi0.
  apply (ex_r pi0).
  apply Permutation_Type_app_head; rewrite ? app_assoc; apply Permutation_Type_app_tail.
  transitivity (l1' ++ l2'); [ apply Permutation_Type_app_comm | ].
  transitivity (l1 ++ l2); [ | apply Permutation_Type_app_comm ].
  apply (Permutation_Type_app_inv _ _ _ _ _ HP).
- intros A B C D l0 l1 l2 l3 l4 pi1 pi2 pi3 pi4 ->.
  change (ll (l3 ++ (l2 ++ l0) ++ tens C D :: l1 ++ l4)).
  apply ex_r with (tens C D :: ((l1 ++ l4) ++ l3 ++ l2) ++ l0); [ apply tens_r; trivial | ].
  + apply (ex_r (pi4 eq_refl)).
    rewrite app_assoc; apply Permutation_Type_app_comm.
  + list_simpl; rewrite app_comm_cons, app_assoc, ? (app_assoc l3), (app_assoc (l3 ++ l2)).
    apply Permutation_Type_app_comm.
- intros A B C D l0 l1 l2 l3 l4 pi1 pi2 pi3 pi4' pi4; apply pi4' in pi4; clear pi4'.
  apply ex_r with (tens C D :: l0 ++ (l1 ++ l4) ++ l3 ++ l2); [ apply tens_r; trivial | ].
  + apply (ex_r pi4).
    rewrite app_assoc; apply Permutation_Type_app_comm.
  + list_simpl; rewrite app_comm_cons, ? (app_assoc l3), ? app_assoc, <- app_assoc.
    apply Permutation_Type_app_comm.
- intros A B C D l1 l2 l3 l4 pi1 pi2 pi3' pi3; apply pi3' in pi3; clear pi3'.
  apply ex_r with (parr C D :: (l1 ++ l4) ++ l3 ++ l2); [ apply parr_r, (ex_r pi3) | ].
  + rewrite app_assoc; apply Permutation_Type_app_comm.
  + list_simpl; rewrite app_comm_cons, ? app_assoc, <- app_assoc.
    apply Permutation_Type_app_comm.
- intros C D C' D' l1 l2 pi1 pi2 IHC IHD l0 pi0 Heq; injection Heq as -> ->.
  rewrite <- app_assoc; apply IHC; auto.
  now rewrite <- app_nil_l; apply IHD.
Qed.
*)

End Atoms.
