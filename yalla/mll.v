(* Unit-free MLL following Yalla schemas *)

From Coq Require Import Bool Wf_nat Lia.
From OLlibs Require Import dectype funtheory List_more List_Type Permutation_Type_more.
From GraphTheory Require Import mgraph.

Import EqNotations.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


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
| var X, var Y => eqb X Y
| covar X, covar Y => eqb X Y
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
  eqb := eqb_form;
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
Proof. now induction A; cbn; rewrite ? IHA1, ? IHA2, ? IHA. Qed.

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
Proof. induction A; cbn; lia. Qed.

Lemma fsize_dual A : fsize (dual A) = fsize A.
Proof. induction A; cbn; rewrite ? IHA1, ? IHA2; lia. Qed.


(** * MLL Proofs *)
Inductive ll : list formula -> Type :=
| ax_r : forall X, ll (covar X :: var X :: nil)
| ex_r : forall l1 l2, ll l1 -> Permutation_Type l1 l2 -> ll l2
| tens_r : forall A B l1 l2, ll (A :: l1) -> ll (B :: l2) -> ll (tens A B :: l2 ++ l1)
| parr_r : forall A B l, ll (A :: B :: l) -> ll (parr A B :: l)
| cut_r : forall A l1 l2 l3 l4, ll (l1 ++ A :: l2) ->
             ll (l3 ++ dual A :: l4) -> ll (l3 ++ l2 ++ l1 ++ l4).
Notation "⊢ l" := (ll l) (at level 70).

(* Bizarrement les arguments implicitent ne fonctionnent plus .... *)
Arguments ex_r {l1} {l2} pi0 sigma. (* sans effet, demande toujours 4 arguments *)

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
Proof. destruct pi; cbn; lia. Qed.

Lemma psize_rew l l' (pi : ll l) (Heq : l = l') : psize (rew Heq in pi) = psize pi.
Proof. now subst. Qed.


(* TODO from here on *)
From mathcomp Require Import all_ssreflect. (* produces errors if done before TODO solve it*)

(** * Level 0: Multigraphs *)
(* From the library GraphTheory *)
Print graph.
(* inductive def of graphs + common operations -> from library *)

(* Vertex label: rule ; Arrows label: formula *)
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

Print DecType.
About eqb_rule.
About eqb_form.
(* ERROR eqb: Not a projection of inductive DecType.
Definition rules_dectype := {|
  car := rule;
  eqb := eqb_rule;
  eqb_eq := eqb_eq_rule |}.
*)

(** * Level 1: Multigraphs with some more data *)

(*  graph_of: multigraph
    sequent: conclusion of the proof
    order: to each formula of sequent, associate the unique corresponding concl node
    left (resp. right) gives the corresponding premisse of the node *)
Set Primitive Projections.
Record graph_data : Type :=
  Graph_data {
      graph_of:> graph rule formula;
      sequent : list formula;
      order: 'I_(size sequent) -> vertex graph_of; (* [set x | eqb_rule (vlabel x) concl_l] *)
      left: vertex graph_of -> edge graph_of;
      right: vertex graph_of -> edge graph_of }.
Unset Primitive Projections.
(*TODO make order into nodes concl, left and right from nodes parr+tens *)


Definition graph_ax (x : atom) : graph rule formula :=
  add_edge (
    add_vertex (
      add_edge (
        add_vertex (
          unit_graph ax_l)
        concl_l)
      (inl tt) (inr tt) (covar x))
    concl_l)
  (inl (inl tt)) (inr tt) (var x).

Definition sequent_ax (x : atom) : list formula := covar x :: var x :: nil.

Check Ordinal. Check 'I_2.
Lemma o : 0<2.
easy. Qed.
Lemma oo : 1<2.
easy. Qed.
Definition order_ax (x : atom) : 'I_2 -> vertex (graph_ax x) :=
fun n => match n with
| Ordinal 0 o => inl (inr tt)
| Ordinal 1 oo => inr tt
| _ => inr tt end.
(* ugly, must be improved *)

Definition left_ax (x : atom) : vertex (graph_ax x) -> edge (graph_ax x) := fun _ => None.
Definition right_ax (x : atom) : vertex (graph_ax x) -> edge (graph_ax x) := fun _ => None.

Definition graph_data_ax (x : atom) : graph_data := Graph_data (graph_of := graph_ax x) (sequent := sequent_ax x) (order_ax x) (left_ax (x := x)) (right_ax (x := x)).
(* ugly too *)



(** * Level 2: Proof Structure *)
(* def of proof_structure: label on node implies [conditions on arrows] *)
(* def: record with graph_data + proof of properness *)
Section Propertness.
Variables (G : graph_data).
Implicit Types (x : G).
Definition edges_out_at x := [set e | source e == x].
Definition edges_in_at x := [set e | target e == x].


Definition proper_concl :=
  forall x, (vlabel x = concl_l) -> (#|edges_out_at x| == 0) /\ (#|edges_in_at x| == 1)
.

Definition proper := proper_concl.
End Propertness.

Lemma proper_ax : forall (x : atom), proper (graph_data_ax x).
Proof.
intro; unfold proper.
unfold proper_concl.
intros y Hlabel. split.
- unfold edges_out_at. rewrite cards_eq0.
  assert (H: forall e, source e <> y).
      case. case. case. case. easy. easy. simpl.
      case. intro H. rewrite <-H in Hlabel. simpl in Hlabel. contradict Hlabel. easy.
      intro e. case. intro H. rewrite <-H in Hlabel. simpl in Hlabel. contradict Hlabel. easy.
(* euh ça devrait pas du tout marcher ... *)
      case. intro H. rewrite <-H in Hlabel. simpl in Hlabel. contradict Hlabel. easy.
Search (_==set0).
  admit.
- Search (#|_|==1).
(*  assert (forall (e : edges_in_at y), e = Some (inl tt)).
Print graph_ax. *)
Admitted.


(** * Proof Structure of a Proof Sequent *)
(* from sequent proof to proof structure:
Fixpoint ps l (pi : ll l) : graph :=
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

(*
+inductive proof that ps(pi) is a proof_structure
+inductive proof that order list of l (pi : ll l) corresponds to order c_i of the graph
*)


(** * Correctness Criteria: Danos-Regnier *)
(* Switching Graph *)
(* SG (PS):
for a proof structure PS, get P the nodes labelled parr, then a s.g. is given by:
phi: P -> B, G_phi = G where on node v\in P, arrow ?->v(A,phi(v)) is deleted, add node c_v, edge ?->c_v(A)
    then remove direction /!/ depends on the trees in the library
*)

(* Criteria: acyclic and connected *)
(* need def for acyclic + connected, or just for tree ?-> considering tree may change the proofs ?! *)

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
