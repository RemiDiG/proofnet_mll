(* Extension for [mgraph] of the library GraphTheory
   About Trees
 *)

From Coq Require Import Bool.
Set Warnings "-notation-overridden". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect zify.
Set Warnings "notation-overridden".
From GraphTheory Require Import preliminaries mgraph structures bij setoid_bigop.
From Yalla Require Import mll_prelim graph_more upath supath.

Import EqNotations.

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


Section Tree.
Context {Lv Le : Type} {G : graph Lv Le}.

(* Tree = acyclic and connected graph *)
Definition utree {I : eqType} (f : edge G -> option I) :=
  uacyclic f /\ uconnected f.

(* In an acyclic graph (where we removed only edges), there is at most one path between two vertices *)
Lemma uacyclic_unique_path {I : finType} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> uacyclic f -> forall (s t : G) (p q : Supath f s t), p = q.
Proof.
  intros F A s t [p P] [q Q]. cbnb.
  destruct (eq_comparable p q) as [ | Neq]; trivial.
  exfalso.
  revert s P q Q Neq. induction p as [ | [ep bp] p IHp] => s P q Q Neq; destruct q as [ | [eq bq] q]; try by [].
  - revert P. rewrite /supath /= !andb_true_r => /eqP-?. subst t.
    by specialize (A _ (Sub _ Q)).
  - revert Q. rewrite /supath /= !andb_true_r => /eqP-?. subst t.
    by specialize (A _ (Sub _ P)).
  - assert (Pe : supath f s t ((ep, bp) :: p)) by assumption.
    assert (Qe : supath f s t ((eq, bq) :: q)) by assumption.
    revert P. rewrite /supath /= in_cons => /andP[/andP[/andP[/eqP-SP WP] /andP[uP UP]] /norP[/eqP-nP NP]].
    revert Q. rewrite /supath /= in_cons => /andP[/andP[/andP[/eqP-SQ WQ] /andP[uQ UQ]] /norP[/eqP-nQ NQ]].
    destruct (eq_comparable ep eq) as [ | Hneq]; [subst eq | ].
    + assert (bp = bq).
      { destruct (eq_comparable bp bq) as [ | Hneq]; trivial.
        contradict SQ. rewrite -SP.
        destruct bp, bq; try by [].
        - by apply nesym, (uacyclic_loop A), nesym.
        - by apply (uacyclic_loop A), nesym. }
      subst bq.
      revert Neq => /eqP. cbn. move => /nandP[/nandP[/eqP // | /eqP //] | /eqP-Neq].
      eapply (IHp (endpoint bp ep) _ q _ Neq). Unshelve. splitb. splitb.
    + clear Neq IHp.
      set pq : upath := p ++ upath_rev q.
      assert (WPQ : uwalk (endpoint bp ep) (endpoint bq eq) pq).
      { apply (uwalk_cat WP). by rewrite uwalk_rev. }
      assert (NPQ : None \notin [seq f e.1 | e <- pq]).
      { rewrite /pq map_cat mem_cat. splitb.
        by rewrite map_comp upath_rev_fst map_rev in_rev -map_comp. }
      destruct (uconnected_simpl F WPQ NPQ) as [PQ' HPQ'].
      assert (Eq : supath f (endpoint bq eq) (endpoint (~~bq) eq) [:: (eq, ~~bq)]).
      { rewrite /supath !in_cons /= orb_false_r negb_involutive. splitb. by apply /eqP. }
      set EQ : Supath _ _ _ := Sub _ Eq.
      assert (Ep : supath f (endpoint (~~bp) ep) (endpoint bp ep) [:: (ep, bp)]).
      { rewrite /supath !in_cons /= orb_false_r. splitb. by apply /eqP. }
      set EP : Supath _ _ _ := Sub _ Ep.
      assert (Qep : ep \notin [seq e.1 | e <- q]).
      { remember (ep \in [seq e.1 | e <- q]) as b eqn:In. symmetry in In.
        destruct b; trivial.
        apply in_map_fst in In. destruct In as [b In].
        rewrite in_elt_sub in In.
        revert In => /existsP/sigW[[n /= _] /eqP-Qeq].
        rewrite Qeq in Qe.
        destruct (eq_comparable b bp).
        - subst b.
          assert (Hr : (eq, bq) :: take n q ++ (ep, bp) :: drop n.+1 q =
            ((eq, bq) :: take n q) ++ [:: (ep, bp)] ++ drop n.+1 q).
          { by rewrite -(cat1s (ep, bp) (drop n.+1 q))
                       -(cat1s (eq, bq) ((take n q) ++ ([:: (ep, bp)] ++ (drop n.+1 q))))
                       -(cat1s (eq, bq) (take n q)) -!catA. }
          rewrite Hr {Hr} in Qe.
          destruct (supath_subKK Qe) as [L _].
          assert (Hr : (upath_target s ((eq, bq) :: (take n q))) = s).
          { transitivity (upath_source t ([:: (ep, bp)] ++ (drop n.+1 q))); last by rewrite /= SP.
            apply uwalk_sub_middle.
            by revert Qe => /andP[/andP[-> _] _]. }
          rewrite Hr {Hr} in L.
          specialize (A s (Sub _ L)).
          contradict A. cbnb.
        - assert (b = ~~bp) by by destruct b, bp.
          subst b.
          assert (Hr : (eq, bq) :: take n q ++ (ep, ~~ bp) :: drop n.+1 q =
            (((eq, bq) :: take n q) ++ [:: (ep, ~~ bp)]) ++ drop n.+1 q).
          { by rewrite -(cat1s (ep, ~~ bp) (drop n.+1 q))
                       -(cat1s (eq, bq) ((take n q) ++ ([:: (ep, ~~ bp)] ++ (drop n.+1 q))))
                       -(cat1s (eq, bq) (take n q)) -!catA. }
          rewrite Hr {Hr} in Qe.
          destruct (supath_subKK Qe) as [L _].
          rewrite /= map_cat /= last_cat /= SP in L.
          specialize (A s (Sub _ L)).
          contradict A. cbnb. }
      assert (Peq : eq \notin [seq e.1 | e <- p]).
      (* TODO same as Qep above: possible to do the 2 in 1 with a wlog/forall? *)
      { remember (eq \in [seq e.1 | e <- p]) as b eqn:In. symmetry in In.
        destruct b; trivial.
        apply in_map_fst in In. destruct In as [b In].
        rewrite in_elt_sub in In.
        revert In => /existsP/sigW[[n /= _] /eqP-Peq].
        rewrite Peq in Pe.
        destruct (eq_comparable b bq).
        - subst b.
          assert (Hr : (ep, bp) :: take n p ++ (eq, bq) :: drop n.+1 p =
            ((ep, bp) :: take n p) ++ [:: (eq, bq)] ++ drop n.+1 p).
          { by rewrite -(cat1s (eq, bq) (drop n.+1 p))
                       -(cat1s (ep, bp) ((take n p) ++ ([:: (eq, bq)] ++ (drop n.+1 p))))
                       -(cat1s (ep, bp) (take n p)) -!catA. }
          rewrite Hr {Hr} in Pe.
          destruct (supath_subKK Pe) as [L _].
          assert (Hr : (upath_target s ((ep, bp) :: (take n p))) = s).
          { transitivity (upath_source t ([:: (eq, bq)] ++ (drop n.+1 p))); last by rewrite /= SQ.
            apply uwalk_sub_middle.
            by revert Pe => /andP[/andP[-> _] _]. }
          rewrite Hr {Hr} in L.
          specialize (A s (Sub _ L)).
          contradict A. cbnb.
        - assert (b = ~~bq) by by destruct b, bq.
          subst b.
          assert (Hr : (ep, bp) :: take n p ++ (eq, ~~ bq) :: drop n.+1 p =
            (((ep, bp) :: take n p) ++ [:: (eq, ~~ bq)]) ++ drop n.+1 p).
          { by rewrite -(cat1s (eq, ~~ bq) (drop n.+1 p))
                       -(cat1s (ep, bp) ((take n p) ++ ([:: (eq, ~~ bq)] ++ (drop n.+1 p))))
                       -(cat1s (ep, bp) (take n p)) -!catA. }
          rewrite Hr {Hr} in Pe.
          destruct (supath_subKK Pe) as [L _].
          rewrite /= map_cat /= last_cat /= SQ in L.
          specialize (A s (Sub _ L)).
          contradict A. cbnb. }
      assert (DQ : upath_disjoint f (val PQ') (val EQ)).
      { rewrite /upath_disjoint disjoint_sym disjoint_has /= orb_false_r.
        apply /mapP. move => [[k b] K /= KEQ].
        specialize (HPQ' _ K). clear K.
        assert (eq = k).
        { apply F; trivial.
          - rewrite !in_set. apply /eqP. by apply nesym.
          - rewrite !in_set. apply /eqP => FK.
            contradict NPQ. apply /negP/negPn.
            rewrite -FK.
            replace k with ((k, b).1) by trivial.
            by apply (map_f (fun e => f e.1)). }
        subst k. clear KEQ.
        revert HPQ'. rewrite /pq mem_cat upath_rev_in => /orP[In | In].
        - contradict Peq. apply /negP/negPn.
          replace eq with ((eq, b).1) by trivial.
          by apply map_f.
        - contradict uQ. apply /negP/negPn.
          replace eq with ((eq, ~~b).1) by trivial.
          by apply (map_f (fun e => f e.1)). }
      set PQ'Q := supath_cat DQ.
      assert (DP : upath_disjoint f (val EP) (val PQ'Q)).
      { rewrite /upath_disjoint disjoint_has /= map_cat mem_cat /= in_cons in_nil !orb_false_r.
        assert ((f ep) == (f eq) = false) as ->.
        { apply /eqP => FPQ.
          contradict Hneq.
          apply F; trivial.
          all: by rewrite !in_set; apply /eqP; apply nesym. }
        rewrite orb_false_r.
        apply /mapP. move => [[k b] K /= KEQ].
        specialize (HPQ' _ K). clear K.
        assert (ep = k).
        { apply F; trivial.
          - rewrite !in_set. apply /eqP. by apply nesym.
          - rewrite !in_set. apply /eqP => FK.
            contradict NPQ. apply /negP/negPn.
            rewrite -FK.
            replace k with ((k, b).1) by trivial.
            by apply (map_f (fun e => f e.1)). }
        subst k. clear KEQ.
        revert HPQ'. rewrite /pq mem_cat upath_rev_in => /orP[In | In].
        - contradict uP. apply /negP/negPn.
          replace ep with ((ep, b).1) by trivial.
          by apply (map_f (fun e => f e.1)).
        - contradict Qep. apply /negP/negPn.
          replace ep with ((ep, ~~b).1) by trivial.
          by apply map_f. }
      set PPQ'Q := supath_cat DP.
      assert (Nnil : val PPQ'Q <> [::]) by by [].
      clearbody PPQ'Q. revert PPQ'Q Nnil. rewrite SP SQ => PPQ'Q Nnil.
      contradict Nnil.
      by rewrite (A _ PPQ'Q).
Qed.
(* Proof:
  By induction, we can assume P and Q differ on their first edges, respectively ep and eq.
  We denote by p and q the rest of P and Q respectively.
  With p and q, we get a path pq from the target of ep to the target of eq (this is the part where we need
  the infectivity of f).
  Remark that q does not contain ep. Otherwise, (eq ++ q) would go back to s, by following q until
  reaching ep (ep being in q or not according to signs). This would yield a non-trivial cycle,
  contradicting acyclicity.
  Similarly, p does not contain eq.
  Thus, the path pq does not contain ep nor eq, as it is contain in the walk p ++ q.
  But then, ep ++ pq ++ eq give us a non-trivial cycle, a contradiction
*)

Lemma utree_unique_path {I : finType} (f : edge G -> option I) :
  {in ~: f @^-1 None &, injective f} -> utree f -> forall (s t : G),
  { p : Supath f s t & forall (q : Supath f s t), p = q}.
Proof.
  intros F [A C] s t.
  revert C => /(_ s t)/sigW[P _].
  exists P.
  by apply uacyclic_unique_path.
Qed.

(* Function to define a partition of the vertices of a tree: given a vertex v,
   we partitione the tree into v itself, and a class for each edge of v,
   containing vertices accessible from this edge *)
Definition utree_part {I : finType} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v : G) (x : G) : option (edge G) :=
  match utree_unique_path F T v x with
  | existT (exist [::]          _) _ => None   (* class of v *)
  | existT (exist ((e, _) :: _) _) _ => Some e (* a class for each edge of v *)
  end.

(* In a tree, for any vertex v, we can partition the graph according to the edges of v *)
Lemma tree_partition {I : finType} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v : G) :
  partition (preim_partition (utree_part F T v) setT) setT.
Proof. exact (preim_partitionP (utree_part F T v) setT). Qed. (* TODO notation? *)

Lemma inside_utree_part (S : {set G}) {I : finType} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v : G) :
  S \in (preim_partition (utree_part F T v) [set: G]) ->
  forall a p (x : G) (X : x \in S),
  supath f v x (a :: p) ->
  forall e, e \in p -> e.1 \in edge_set S.
Proof.
  intros Sin a p.
  induction p as [ | p ep IH] using last_ind; first by by [].
  intros x X P e E.
  rewrite -rcons_cons in P.
  assert (P' := P).
  rewrite supath_rcons in P. revert P => /andP[/andP[/andP[P /eqP-?] ?] ?]. subst x.
  enough (TepS : usource ep \in S).
  { specialize (IH _ TepS P).
    revert E. rewrite in_rcons => /orP[/eqP-? | ]; last by apply IH.
    subst e. rewrite /= in_set.
    destruct ep as [? []]; splitb. }
  clear IH E e.
  apply (preim_partition_im_eq Sin X); trivial.
  clear Sin X S.
  unfold utree_part.
  destruct (utree_unique_path F T v (usource ep)) as [[ps Ps] Us].
  assert (ps = a :: p).
  { specialize (Us (Sub _ P)). by inversion Us. }
  subst ps. clear Us Ps .
  destruct (utree_unique_path F T v (utarget ep)) as [[pt Pt] Ut].
  assert (pt = rcons (a :: p) ep).
  { specialize (Ut (Sub _ P')). by inversion Ut. }
  subst pt. clear Ut Pt P'.
  reflexivity.
Qed.

Lemma uconnected_utree_part_in (S : {set G})
  {I : finType} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v : G) :
  S \in (preim_partition (utree_part F T v) [set: G]) ->
  forall x y, x \in S -> y \in S ->
  forall e, e \in val (projT1 (utree_unique_path F T x y)) -> e.1 \in edge_set S.
(* Sketch of the proof :
   We have a path from v to x and one from v to y.
   Their concatenation, after reversing the first path and simplification,
   yields the unique path from x to y.
   This is a subpath of the previous two paths, without their
   first edges (the one involving v).
   These subpaths are included in S by Lemma inside_utree_part. *)
Proof.
  intros Sin x y X Y.
  destruct (utree_unique_path F T x y) as [P Pu]. simpl.
  assert (XY := preim_partition_in_eq Sin X Y).
  unfold utree_part in XY.
  destruct (utree_unique_path F T v x) as [[px Px] _].
  destruct (utree_unique_path F T v y) as [[py Py] _].
  destruct px as [ | (ex, box) px], py as [ | (ey, boy) py]; try by [].
  { revert Px Py => /supath_of_nilP-? /supath_of_nilP-?. subst x y.
    specialize (Pu (supath_nil _ v)). by subst P. }
  inversion XY. subst ey. clear XY.
  assert (PxS := inside_utree_part Sin X Px).
  assert (PyS := inside_utree_part Sin Y Py).
  rewrite !supath_cons in Px, Py.
  revert Px => /andP[/andP[/andP[Px /eqP-Usex] _] /eqP-FexN]. simpl in FexN.
  revert Py => /andP[/andP[/andP[Py /eqP-Usey] _] _].
  assert (box = boy).
  { clear P Pu px Px PxS py Py PyS x X y Y Sin F.
    destruct T as [A _].
    destruct (eq_comparable box boy) as [ | B]; trivial.
    apply nesym in FexN. assert (F := uacyclic_loop A FexN). contradict F.
    subst v. by destruct box, boy. }
  subst boy. clear Usey Usex FexN.
  apply supath_revK in Px. revert Px => /andP[/andP[Wx _] Nx].
  revert Py => /andP[/andP[Wy _] Ny].
  assert (Nxy : None \notin [seq f _e.1 | _e <- upath_rev px ++ py]).
  { by rewrite map_cat mem_cat negb_orb Nx Ny. }
  destruct (uconnected_simpl F (uwalk_cat Wx Wy) Nxy) as [Pxy Exy].
  specialize (Pu Pxy). subst Pxy.
  clear Nx Ny Nxy Wx Wy ex box X Y Sin T F.
  intros (e, b) E.
  revert Exy => /(_ _ E) {E}. rewrite mem_cat upath_rev_in => /orP[E | E].
  - exact (PxS _ E).
  - exact (PyS _ E).
Qed.

(* The partition of a tree yields connected components *)
Lemma uconnected_utree_part (S : {set G})
  {I J : finType} (f : edge G -> option I) (f' : edge (induced S) -> option J)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v : G) :
  (forall e (E : e \in edge_set S), None <> f e -> None <> f' (Sub e E : edge (induced S))) ->
  (forall e a (E : e \in edge_set S) (A : a \in edge_set S),
    f' (Sub e E) = f' (Sub a A) -> f e = f a) ->
  S \in (preim_partition (utree_part F T v) [set: G]) -> uconnected f'.
Proof.
  intros F0 F1 Sin [x X] [y Y].
  destruct (supath_to_induced F0 F1 (uconnected_utree_part_in Sin X Y) X Y) as [Q _].
  by exists Q.
Qed. (* TODO voir ce qui tient avec cette définition de f', plus générale *)

Lemma utree_part_None {I : finType} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v x : G) :
  utree_part F T v x = None -> x = v.
Proof.
  unfold utree_part.
  destruct (utree_unique_path F T v x) as [[[ | (e, b) p] P] _]; last by [].
  revert P. rewrite /supath /=. introb.
Qed.

Lemma utree_part_v_v {I : finType} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v : G) :
  utree_part F T v v = None.
Proof.
  unfold utree_part. destruct (utree_unique_path F T v v) as [P Pu].
  specialize (Pu (supath_nil _ v)). by subst P.
Qed.

Lemma utree_part_v {I : finType} (f : edge G -> option I)
  (F : {in ~: f @^-1 None &, injective f}) (T : utree f) (v : G) :
  pblock (preim_partition (utree_part F T v) [set: G]) v = [set v].
Proof.
  assert (Spart := preim_partitionP (utree_part F T v) [set: G]).
  revert Spart => /andP[/eqP-Cov /andP[Triv _]].
  apply /setP => y.
  rewrite in_set1 -eq_pblock // ?Cov // preim_partition_pblock_eq //.
  destruct (eq_comparable y v) as [? | Y].
  { subst y. by rewrite !eq_refl. }
  transitivity false; last by (symmetry; apply /eqP).
  rewrite utree_part_v_v.
  destruct (utree_part F T v y) eqn:H; first by [].
  contradict Y. by apply (utree_part_None H).
Qed.

End Tree.