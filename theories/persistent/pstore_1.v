(* Based on:
   https://gitlab.com/basile.clement/store/-/blob/main/src/store.ml?ref_type=heads
*)

(* https://coq.inria.fr/doc/master/refman/proof-engine/ltac.html?highlight=goal%20selector#goal-selectors *)
Set Default Goal Selector "!".

Ltac TODO admit := admit.

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.mono_set.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Import
  assert
  lst.
From zoo.persistent Require Export
  base.
From zoo Require Import
  options.

#[local] Definition generation :=
  nat.

Implicit Types l : location.
Implicit Types v t s : val.
Implicit Types σ : gmap location val.
Implicit Types gen : generation.

#[local] Notation "'root'" := (
  in_type "t" 0
)(in custom zoo_field
).
#[local] Notation "'gen'" := (
  in_type "t" 1
)(in custom zoo_field
).

#[local] Notation "'sref_value'" := (
  in_type "sref" 0
)(in custom zoo_field
).

#[local] Notation "'snap_store'" := (
  in_type "snap" 0
)(in custom zoo_proj
).
#[local] Notation "'snap_root'" := (
  in_type "snap" 1
)(in custom zoo_proj
).
#[local] Notation "'snap_gen'" := (
  in_type "snap" 2
)(in custom zoo_proj
).

#[local] Notation "'Root'" := (
  in_type "descr" 0
)(in custom zoo_tag
).
#[local] Notation "'Diff'" := (
  in_type "descr" 1
)(in custom zoo_tag
).

(* ------------------------------------------------------------------------ *)
(* Code. *)

Definition pstore_create : val :=
  λ: <>,
    { ref §Root; #0 }.

Definition pstore_ref : val :=
  λ: "t" "v",
    { "v" }.

Definition pstore_get : val :=
  λ: "t" "r",
    "r".{sref_value}.

Definition pstore_set : val :=
  λ: "t" "r" "v",
    let: "root" := ref §Root in
    "t".{root} <- ‘Diff{ "r", "r".{sref_value}, "root" } ;;
    "r" <-{sref_value} "v" ;;
    "t" <-{root} "root".

Definition pstore_capture : val :=
  λ: "t",
    let: "g" := "t".{gen} in
    "t" <-{gen} #1 + "g" ;;
    ("t", "t".{root}, "g").

Definition pstore_collect : val :=
  rec: "pstore_collect" "node" "acc" :=
    match: !"node" with
    | Root =>
        ("node", "acc")
    | Diff <> <> "node'" =>
        "pstore_collect" "node'" ‘Cons{ "node", "acc" }
    end.
Definition pstore_revert : val :=
  rec: "pstore_revert" "node" "seg" :=
    match: "seg" with
    | Nil =>
        "node" <- §Root
    | Cons "node'" "seg" =>
        match: !"node'" with
        | Root =>
            Fail
        | Diff "r" "v" "node_" =>
            assert ("node_" = "node") ;;
            "node" <- ‘Diff{ "r", "r".{sref_value}, "node'" } ;;
            "r" <-{sref_value} "v" ;;
            "pstore_revert" "node'" "seg"
        end
    end.
Definition pstore_reroot : val :=
  λ: "node",
    let: "root", "nodes" := pstore_collect "node" §Nil in
    pstore_revert "root" "nodes".

Definition pstore_restore : val :=
  λ: "t" "s",
    if: "t" ≠ "s".<snap_store> then (
      Fail
    ) else (
      let: "root" := "s".<snap_root> in
      match: !"root" with
      | Root =>
          ()
      | Diff <> <> <> =>
          pstore_reroot "root" ;;
          "t" <-{gen} #1 + "s".<snap_gen> ;;
          "t" <-{root} "root"
      end
    ).

(* ------------------------------------------------------------------------ *)
(* Lemmas on maps and lists. *)

Section map.
  Context `{Countable K}.
  Context {V : Type}.

  Lemma gmap_included_insert (σ1 σ2:gmap K V) (l:K) (v:V) :
    σ1 ⊆ σ2 ->
    <[l:=v]>σ1 ⊆ <[l:=v]>σ2.
  Proof.
    intros ? l'. destruct_decide (decide (l=l')).
    { subst. rewrite !lookup_insert //. }
    { rewrite !lookup_insert_ne //. }
  Qed.

  Lemma gmap_included_insert_notin (σ1 σ2:gmap K V) (l:K) (v:V) :
    l ∉ dom σ1 ->
    σ1 ⊆ σ2 ->
    σ1 ⊆ <[l:=v]>σ2.
  Proof.
    intros ?? l'. destruct_decide (decide (l=l')).
    { subst. rewrite lookup_insert // not_elem_of_dom_1 //. }
    { rewrite !lookup_insert_ne //. }
  Qed.

  Lemma incl_dom_incl (σ1 σ2:gmap K V)  :
    σ1 ⊆ σ2 ->
    dom σ1 ⊆ dom σ2.
  Proof.
    intros X1.
    intros l Hl. apply elem_of_dom in Hl. destruct Hl as (?&Hl).
    eapply map_subseteq_spec in X1; last done. by eapply elem_of_dom.
  Qed.
End map.

Section list.
  Context {A : Type}.

  Lemma list_case_r (l:list A) :
    l = nil \/ exists (l':list A) x, l = l' ++ [x].
  Proof.
    induction l using rev_ind.
    - naive_solver.
    - right.
      destruct IHl as [-> | (?&?&->)]; eauto.
  Qed.

  Lemma elem_of_middle (x:A) (xs:list A) :
    x ∈ xs ->
    exists (l1 l2:list A), xs = l1 ++ x::l2.
  Proof.
    intros Hx. apply elem_of_list_lookup_1 in Hx.
    destruct Hx as (?&?).
    eexists _,_. symmetry. eapply take_drop_middle. done.
  Qed.
End list.

(* ------------------------------------------------------------------------ *)
(* Define a labeled graph as a set of edges. *)

Section graph.
  Definition graph (A B : Type) `{Countable A} `{Countable B} :=
    gset (A * B * A).

  Context `{Countable A} `{Countable B}.
  Definition vertices (g:graph A B) : gset A :=
    set_fold (fun '(x,_,y) acc => {[x;y]} ∪ acc) ∅ g.

  Lemma vertices_empty :
    vertices ∅ = ∅.
  Proof.
    compute_done.
  Qed.

  Definition proj1 {A B C:Type} (x:(A*B*C)) : A :=
    match x with (x,_,_) => x end.
  Definition proj2 {A B C:Type} (x:(A*B*C)) : B :=
    match x with (_,x,_) => x end.
  Definition proj3 {A B C:Type} (x:(A*B*C)) : C :=
    match x with (_,_,x) => x end.

  Lemma elem_of_vertices x (g:graph A B) :
    x ∈ vertices g <-> exists b y, ((x,b,y) ∈ g \/ (y,b,x) ∈ g).
  Proof.
    apply set_fold_ind_L with (P := fun f g => x ∈ f  <-> exists b y, ((x,b,y) ∈ g \/ (y,b,x) ∈ g)).
    - set_solver.
    - intros ((?,?),?). set_solver.
  Qed.

  Lemma left_vertex: forall g x d y,
    (x, d, y) ∈ g -> x ∈ vertices g.
  Proof.
    intros. rewrite elem_of_vertices; eauto.
  Qed.

  Lemma right_vertex: forall g x d y,
    (x, d, y) ∈ g -> y ∈ vertices g.
  Proof.
    intros. rewrite elem_of_vertices; eauto.
  Qed.

  Lemma vertices_singleton (x:(A*B*A)) :
    vertices {[x]} = {[proj1 x; proj3 x]}.
  Proof.
    rewrite /vertices set_fold_singleton. destruct x as ((?&?)&?); set_solver.
  Qed.

  Lemma vertices_union (g1 g2:graph A B) :
    vertices (g1 ∪ g2) = vertices g1 ∪ vertices g2.
  Proof.
    revert g2. induction g1 using set_ind_L; intros g2.
    { rewrite /vertices set_fold_empty !left_id_L //. }
    replace ({[x]} ∪ X ∪ g2) with (X ∪ ({[x]} ∪ g2)) by set_solver.
    rewrite (union_comm_L _  X).
    rewrite !IHg1. rewrite -union_assoc_L. f_equal.
    destruct_decide (decide (x ∈ g2)).
    { replace ({[x]} ∪ g2) with g2 by set_solver.
      rewrite vertices_singleton.
      assert ({[proj1 x; proj3 x]} ⊆ vertices g2); last by set_solver.
      intros l Hl. apply elem_of_vertices.
      rewrite elem_of_union !elem_of_singleton in Hl. destruct x as ((?,?),?). set_solver. }
    rewrite {1}/vertices /set_fold. simpl.
    rewrite (foldr_permutation _ _ _ _ (x::elements g2)).
    { intros. destruct a1 as ((?,?),?),a2 as ((?,?),?); set_solver. }
    { by apply elements_union_singleton. }
    { simpl. rewrite vertices_singleton. destruct x as ((?,?),?). set_solver. }
  Qed.

  Definition edge (g:graph A B) x c y :=
    (x,c,y) ∈ g.

  Definition has_edge (g:graph A B) x y := exists c,
    (x,c,y) ∈ g.

  Lemma edge_of_union : forall g1 g2 x y,
      has_edge (g1 ∪ g2) x y <-> (has_edge g1 x y ∨ has_edge g2 x y).
  Proof.
    rewrite /has_edge. set_solver.
  Qed.

  Definition graph_incl g1 g2 :=
    forall x y, has_edge g1 x y -> has_edge g2 x y.

  Definition graph_iso g1 g2 :=
    graph_incl g1 g2 /\ graph_incl g2 g1.

  (* TODO a 'proper' instance or something? *)
  Lemma union_incl g1 g1' g2 g2' :
    graph_incl g1 g1' -> graph_incl g2 g2' -> graph_incl (g1 ∪ g2) (g1' ∪ g2').
  Proof.
    intros H1 H2.
    intros x y (diff & Hkl).
    rewrite elem_of_union in Hkl.
    assert (forall g g' x y diff, graph_incl g g' -> (x, diff, y) ∈ g -> has_edge g' x y) as Hglue.
    {
      intros g g' k' l' diff' Hincl Helem.
      destruct Hincl with k' l'; unfold has_edge; eauto.
    }
    rewrite edge_of_union.
    destruct Hkl as [ Hkl | Hkl ]; [ left | right ]; eapply Hglue; eauto.
  Qed.

  Lemma union_iso g1 g1' g2 g2' :
    graph_iso g1 g1' -> graph_iso g2 g2' -> graph_iso (g1 ∪ g2) (g1' ∪ g2').
  Proof.
    intros (H1 & H1') (H2 & H2').
    split; eapply union_incl; eauto.
  Qed.

  Inductive path (g:graph A B) : A -> list (A*B*A) -> A -> Prop :=
  | path_nil : forall a, path g a [] a
  | path_cons : forall a1 b a2 bs a3,
      (a1,b,a2) ∈ g ->
      path g a2 bs a3 ->
      path g a1 ((a1,b,a2)::bs) a3.

  Lemma path_app_inv g a1 a2 xs ys :
    path g a1 (xs ++ ys) a2 ->
    exists a, path g a1 xs a /\ path g a ys a2.
  Proof.
    revert a1 ys a2. induction xs as [| ((?,?),?)].
    { eauto using path_nil. }
    { intros. rewrite -app_comm_cons in H1. inversion H1. subst.
      apply IHxs in H9. destruct H9 as (?&?&?).
      eauto using path_cons. }
  Qed.

  Lemma path_snoc_inv g a1 a2 a3 a4 b xs :
    path g a1 (xs ++ [(a2,b,a3)]) a4 ->
    path g a1 xs a2 /\ a3 = a4 /\ (a2,b,a3) ∈ g.
  Proof.
    intros Hpath. apply path_app_inv in Hpath. destruct Hpath as (?&?&Hpath).
    inversion Hpath. subst. inversion H9. naive_solver.
  Qed.

  Definition acyclic g := forall a xs, path g a xs a -> xs = nil.

  Record rooted_dag g (r:A) :=
    { ti1 : forall a, a ∈ vertices g -> exists xs, path g a xs r;
      ti2 : acyclic g
    }.

  Definition unaliased (g:graph A B) :=
      forall r x1 r1 x2 r2,
      (r,x1,r1) ∈ g ->
      (r,x2,r2) ∈ g ->
      x1 = x2 /\ r1 = r2.

  Lemma path_app (g:graph A B) x3 x1 xs ys x2 :
    path g x1 xs x3 ->
    path g x3 ys x2 ->
    path g x1 (xs++ys) x2.
  Proof.
    intros Hp.
    revert x2 ys. induction Hp.
    - eauto.
    - intros. rewrite -app_comm_cons. apply path_cons; eauto.
  Qed.

  Definition all_uniq_path g :=
    forall a1 a2 xs ys, path g a1 xs a2 -> path g a1 ys a2 -> xs = ys.

  Lemma rooted_tree_impl_acyclic_unaliased g r :
    (forall a, a ∈ vertices g -> exists xs, path g a xs r) -> (* If every vertex can reach the root, *)
    all_uniq_path g -> (* then the property of uniq path *)
    acyclic g /\ unaliased g. (* implies acyclicity + unalising *)
  Proof.
    intros Hroot  Huniq. split.
    { intros ?? Hpath.
      assert (path g a (xs++xs) a) as Hloop.
      { by eapply path_app. }
      specialize (Huniq a a xs (xs++xs) Hpath Hloop).
      apply (@f_equal _ _ length) in Huniq. rewrite app_length in Huniq.
      assert (length xs = 0) by lia. destruct xs; simpl in *; try done; lia. }
    { intros ????? X1 X2.
      destruct (Hroot r1) as (xs1&Hxs1).
      { eapply elem_of_vertices. eauto. }
      destruct (Hroot r2) as (xs2&Hxs2).
      { eapply elem_of_vertices. eauto. }
      assert (path g r0 ((r0,x1,r1)::xs1) r) as Hp1 by (by eapply path_cons).
      assert (path g r0 ((r0,x2,r2)::xs2) r) as Hp2 by (by eapply path_cons).
      specialize (Huniq _ _ _ _ Hp1 Hp2). naive_solver. }
  Qed.

  Lemma acyclic_unaliased_impl_uniq_path g :
    acyclic g ->
    unaliased g ->
    all_uniq_path g.
  Proof.
    intros Hacy Hinj. intros ???? Hpath.
    revert ys. induction Hpath; intros ys.
    { intros Hpath. apply Hacy in Hpath. done. }
    { inversion 1; subst.
      { exfalso.
        assert (path g a3 ((a3, b, a2)::bs) a3) as Z.
        { apply path_cons; done. }
        apply Hacy in Z. congruence. }
      destruct (Hinj _ _ _ _ _ H1 H3). subst.
      f_equal. eapply IHHpath. done. }
  Qed.

  Lemma rooted_dag_empty (r:A) :
      rooted_dag (∅ : graph A B) r.
  Proof.
    constructor.
    { intros ?. rewrite vertices_empty. set_solver. }
    { intros ??. inversion 1; set_solver. }
  Qed.

  Lemma path_cycle_end_inv_aux g (r r':A) b ds x1 x2 :
    r ≠ r' ->
    x2 ≠ r' ->
    r' ∉ vertices g ->
    path ({[(r, b, r')]} ∪ g) x1 ds x2 ->
    path g x1 ds x2.
  Proof.
    induction 4.
    { apply path_nil. }
    { eapply path_cons.
      { rewrite /edge elem_of_union elem_of_singleton in H4.
        destruct H4 as [|]; last done.
        inversion H4. subst. inversion H5.
        - congruence.
        - subst.
          exfalso. apply H3. apply elem_of_vertices. set_solver. }
      by eapply IHpath. }
  Qed.

  Lemma path_cycle_end_inv g (r r':A) b ds x :
    r ≠ r' ->
    r' ∉ vertices g ->
    path ({[(r, b, r')]} ∪ g) x ds x ->
    path g x ds x.
  Proof.
    intros.
    destruct_decide (decide (x=r')).
    { subst. inversion H3.
      - apply path_nil.
      - subst. exfalso. apply H2. apply elem_of_vertices. set_solver. }
    eapply path_cycle_end_inv_aux; last done. all:done.
  Qed.

  Lemma path_snoc g a1 b a2 bs a3 :
    path g a1 bs a2 ->
    (a2,b,a3) ∈ g ->
    path g a1 (bs++[(a2,b,a3)]) a3.
  Proof.
    induction 1.
    { intros. apply path_cons; first done. apply path_nil. }
    { intros. rewrite -app_comm_cons. eauto using path_cons. }
  Qed.

  Lemma path_weak g1 g2 x bs y :
    path g1 x bs y ->
    g1 ⊆ g2 ->
    path g2 x bs y.
  Proof.
    induction 1; intros Hi.
    - apply path_nil.
    - eapply path_cons.
      + by apply Hi.
      + by apply IHpath.
  Qed.

  Lemma rooted_dag_add (r r':A) g x:
    r ≠ r' ->
    r' ∉ vertices g ->
    rooted_dag g r ->
    rooted_dag ({[(r, x, r')]} ∪ g) r'.
  Proof.
    intros Hne Hg Hroot. inversion Hroot as [X1 X2].
    constructor.
    { rewrite vertices_union vertices_singleton. intros a.
      rewrite !elem_of_union !elem_of_singleton.
      intros [[-> | ->] | Hx].
      { exists [(r, x, r')]. simpl. eapply path_cons.
        - set_solver.
        - apply path_nil. }
      { exists nil. apply path_nil. }
      { apply X1 in Hx. destruct Hx as (ds,Hx). exists (ds++[(r, x, r')]).
        eapply path_snoc.
        { eapply path_weak; first done. set_solver. }
        { set_solver. } } }
    { intros ?? Hpath. apply path_cycle_end_inv in Hpath; eauto. }
  Qed.

  Lemma acyclic_weak (g1 g2:graph A B) :
    acyclic g1 ->
    g2 ⊆ g1 ->
    acyclic g2.
  Proof.
    intros Hacy ? ???. eapply Hacy. by eapply path_weak.
  Qed.

  Lemma path_all_in (g:graph A B) a1 xs a2 :
    path g a1 xs a2 ->
    list_to_set xs ⊆ g.
  Proof.
    induction 1; simpl; set_solver.
  Qed.

  Lemma path_restrict (g:graph A B) r xs r' :
    path g r xs r' ->
    path (list_to_set xs) r xs r'.
  Proof.
    induction 1; eauto using path_nil.
    apply path_cons; first set_solver.
    eapply path_weak; first done. set_solver.
  Qed.

  Lemma path_inv_r (g:graph A B) x bs z :
    path g x bs z ->
    (x = z /\ bs = nil) ∨ ∃ bs' b y, bs = bs' ++ [(y,b,z)] /\ path g x bs' y ∧ (y,b,z) ∈ g.
  Proof.
    induction 1.
    { naive_solver.  }
    right. destruct IHpath as [(->&->)|(bs'&b'&y&->&?&?)].
    { exists nil. eexists _,_. split; first done. split.
      - eauto using path_nil.
      - naive_solver. }
    { exists ((a1, b, a2) :: bs'). eexists _,_. rewrite app_comm_cons //. split_and !; try done.
      apply path_cons; eauto. }
  Qed.

  Lemma path_add_inv_r (r r':A) b x xs g :
    r ≠ r' ->
    r' ∉ vertices g ->
    path ({[(r, b, r')]} ∪ g) x xs r' ->
    (xs = nil /\ x = r') \/ (exists xs', xs = xs' ++ [(r, b, r')] /\ path g x xs' r).
  Proof.
    intros Hrr' Hr' Hreach. apply path_inv_r in Hreach.
    destruct Hreach as [(->&->)|(bs'&b0&y&->&Hreach&Hedge)].
    { eauto. }
    right.
    assert (b0=b /\ y=r) as (->&->).
    { rewrite /edge elem_of_union elem_of_singleton in Hedge.
      destruct Hedge; first naive_solver.
      exfalso. apply Hr', elem_of_vertices. eauto. }
    eexists. split; first done.
    eauto using path_cycle_end_inv_aux.
  Qed.

  (* [mirror xs ys] asserts that, up-to labels, the path xs is the reverse of ys *)
  Inductive mirror :
    list (A*B*A) -> list (A*B*A) -> Prop :=
  | mirror_nil :
    mirror [] []
  | mirror_cons :
    forall r x x' r' xs ys,
      mirror xs ys  ->
      mirror (xs++[(r,x,r')]) ((r',x',r)::ys).

  Lemma mirror_snoc ys xs a a' x x' :
    mirror ys xs ->
    mirror ((a,x,a') :: ys) (xs ++ [(a',x',a)]).
  Proof.
    induction 1.
    { apply (mirror_cons _ _ _ _ nil nil). apply mirror_nil. }
    rewrite -!app_comm_cons app_comm_cons. by apply mirror_cons.
  Qed.

  Lemma mirror_symm xs ys :
    mirror xs ys -> mirror ys xs.
  Proof.
    induction 1.
    - eauto using mirror_nil.
    - apply mirror_snoc; done.
  Qed.

  Lemma use_mirror xs ys (g:graph A B) r y :
    mirror xs ys ->
    path g r xs y ->
    path (list_to_set ys) y ys r.
  Proof.
    intros Hu. revert r y. induction Hu; intros r0 y.
    { inversion 1. subst. apply path_nil. }
    intros Hp. apply path_snoc_inv in Hp. destruct Hp as (?&?&?). subst.
    apply path_cons; first by set_solver.
    eapply path_weak.
    - apply IHHu; eauto.
    - set_solver.
  Qed.

  Lemma mirror_vertices (xs ys:list (A*B*A)) :
    mirror xs ys ->
    vertices (list_to_set ys) = vertices (list_to_set xs).
  Proof.
    revert xs. induction ys; intros xs; inversion 1; subst; first done.
    simpl. rewrite list_to_set_app_L !vertices_union !vertices_singleton. simpl.
    erewrite IHys; last done. rewrite vertices_empty. set_solver.
  Qed.

  Lemma mirror_same_length (xs ys:list (A*B*A)):
    mirror xs ys ->
    length xs = length ys.
  Proof. induction 1; first done. rewrite app_length. simpl. lia. Qed.

  Lemma mirror_mirrored_edges xs ys r x r' :
    mirror xs ys ->
    (r,x,r') ∈ xs -> exists x', (r',x',r) ∈ ys.
  Proof.
    induction 1; first by set_solver.
    rewrite elem_of_app elem_of_list_singleton.
    intros [X|X].
    { apply IHmirror in X. set_solver. }
    { set_solver. }
  Qed.

  Lemma mirror_nil_inv_r xs :
    mirror xs [] -> xs = [].
  Proof.
    intro Hr.
    inversion Hr. done.
  Qed.

  Lemma mirror_nil_inv_l xs :
    mirror [] xs -> xs = [].
  Proof.
    intro Hl.
    assert (mirror xs []) as Hr by (apply mirror_symm; eauto).
    inversion Hr. done.
  Qed.

  Lemma mirror_app : forall xs1 ys1 xs2 ys2,
    mirror xs1 ys1 -> mirror xs2 ys2 -> mirror (xs1 ++ xs2) (ys2 ++ ys1).
  Proof.
    intros xs1 ys1. revert xs1. induction ys1; intros xs1 xs2 ys2 H1 H2.
    - inversion H1.
      rewrite app_nil_r. assumption.
    - inversion H1; subst.
      replace ((xs ++ [(r, x, r')]) ++ xs2) with (xs ++ ([(r, x, r')] ++ xs2)); first last.
      { rewrite assoc; eauto. }
      replace (ys2 ++ (r', x', r) :: ys1) with ((ys2 ++ [(r', x', r)]) ++ ys1); first last.
      { rewrite -assoc; eauto. }
      apply IHys1; eauto.
      simpl.
      apply mirror_symm. constructor. apply mirror_symm.
      assumption.
  Qed.

  Lemma mirror_app_inv (xs ys1 ys2 : list (A * B * A)) :
    mirror xs (ys1 ++ ys2) ->
    exists xs1 xs2,
      mirror xs1 ys1 /\
      mirror xs2 ys2 /\
      xs = xs2 ++ xs1.
  Proof.
    revert xs ys2. induction ys1; intros xs ys2 Hmirror.
    - exists nil, xs. rewrite right_id_L. split; eauto using mirror_nil.
    - rewrite -app_comm_cons in Hmirror. inversion Hmirror. subst.
      apply IHys1 in H3. destruct H3 as (xs1&xs2&?&?&->).
      eexists _,xs2.
      { split_and !.
      - apply mirror_cons; eauto.
      - eauto.
      - rewrite -assoc_L //.
      }
  Qed.

  Lemma mirror_mirror_incl xs xsm1 xsm2 :
      mirror xsm1 xs ->
      mirror xsm2 xs ->
      graph_incl (list_to_set xsm1) (list_to_set xsm2).
  Proof.
    intros M1 M2.
    assert (mirror xs xsm2) as M2symm by (eapply mirror_symm; eauto).
    intros x y (diff & Hkl).
    rewrite elem_of_list_to_set in Hkl.
    destruct (mirror_mirrored_edges xsm1 xs x diff y) as (d1 & Hd1); eauto.
    destruct (mirror_mirrored_edges xs xsm2 y d1 x) as (d2 & Hd2); eauto.
    exists d2; rewrite elem_of_list_to_set; done.
  Qed.

  Lemma mirror_mirror xs xsm1 xsm2 :
      mirror xsm1 xs ->
      mirror xsm2 xs ->
      graph_iso (list_to_set xsm1) (list_to_set xsm2).
  Proof.
    intros. split; eapply mirror_mirror_incl; eauto.
  Qed.

  Lemma path_middle (g:graph A B) x xs ys z :
    path g x (xs ++ ys) z ->
    exists y, path g x xs y /\ path g y ys z.
  Proof.
    revert g x ys z. induction xs; intros g x ys z.
    { simpl. eauto using path_nil. }
    inversion 1; simpl in *; subst.
    apply IHxs in H7. destruct H7 as (y,(?&?)).
    exists y. split; last done. eauto using path_cons.
  Qed.

  Lemma use_mirror_subset xs ys xs' g r y :
    xs' ⊆ xs ->
    mirror xs ys ->
    path g r xs' y ->
    exists zs, path (list_to_set ys) y zs r /\ length xs' = length zs.
  Proof.
    intros Hincl Hundo Hpath.
    induction Hpath.
    { exists nil. split; last done. apply path_nil. }
    { destruct IHHpath as (zs&Hzs&?).
      { set_solver. }
      eapply (mirror_mirrored_edges _ _ a1 b a2) in Hundo. 2:set_solver.
      destruct Hundo as (b'&?).
      exists (zs ++ [(a2, b', a1)]). split.
      { eapply path_app; first done.
        apply path_cons; first set_solver. apply path_nil. }
      { rewrite app_length. simpl. lia. } }
  Qed.

  Lemma mirror_path_disjoint g na xs b xsm :
    acyclic g ->
    path g na xs b ->
    mirror xs xsm ->
    g ## list_to_set xsm.
  Proof.
    intros Hacyclic Pxs Mxs.
    intros ((k, diff), l) Hklg1 Hklxsm.
    rewrite elem_of_list_to_set in Hklxsm.
    assert (exists diff', (l, diff', k) ∈ xs) as (diff' & Hlkxs).
    { eapply mirror_mirrored_edges; eauto.
      apply mirror_symm; eauto.
    }
    assert (path g k [(k, diff, l)] l) as Pkl.
    { constructor; eauto. constructor. }
    assert (path g l [(l, diff', k)] k) as Plk.
    { apply path_weak with (list_to_set xs); eauto.
    - { constructor; eauto.
      - rewrite elem_of_list_to_set; eauto.
      - constructor.
      }
    - eapply path_all_in.
      apply Pxs.
    }
    discriminate (Hacyclic k ([(k, diff, l)] ++ [(l, diff', k)])); eauto.
    { eapply path_app; eauto. }
  Qed.

  Lemma mirror_preserves_disjoint (g: graph A B) xs ys xs' ys' :
    mirror xs xs' ->
    mirror ys ys' ->
    unaliased g ->
    list_to_set xs ⊆ g ->
    list_to_set ys ⊆ g ->
    xs ## ys ->
    xs' ## ys'.
  Proof.
    intros M1 M2 Hu ?? E . apply mirror_symm in M1,M2.
    intros ((x,l),y) R1 R2.
    destruct (mirror_mirrored_edges _ _ _ _ _ M1 R1) as (l1,R1').
    destruct (mirror_mirrored_edges _ _ _ _ _ M2 R2) as (l2,R2').
    assert ((y, l1, x) ∈ g /\ (y, l2, x) ∈ g) as (G1&G2) by set_solver.
    destruct (Hu _ _ _ _ _ G1 G2) as (->&_).
    eapply E with (y,l2,x); set_solver.
  Qed.

  Definition pathlike (ys:list (A*B*A)) r :=
    forall a b a', (a,b,a') ∈ ys -> a' = r \/ exists b' a'', (a',b',a'') ∈ ys.

  Lemma path_pathlike g r ys y :
    path g y ys r ->
    pathlike ys r.
  Proof.
    intros Hpath a b a' Hedge.
    apply elem_of_middle in Hedge. destruct Hedge as (?&?&->).
    rewrite cons_middle assoc_L in Hpath.
    apply path_app_inv in Hpath. destruct Hpath as (?&Hpath&Hp').
    apply path_snoc_inv in Hpath. destruct Hpath as (?&?&?). subst.
    inversion Hp'; set_solver.
  Qed.

  Lemma same_path g (xs:list (A*B*A)) a1 a2 a3 a4 :
    path g a1 xs a2 ->
    path g a3 xs a4 ->
    xs ≠ nil ->
    a1 = a3 /\ a2=a4.
  Proof.
    intros Hp1. revert a3 a4. induction Hp1.
    { intros. congruence. }
    intros a3' a4'. inversion 1. subst. intros _. destruct bs.
    { inversion Hp1; inversion H10. subst. done. }
    apply IHHp1 in H10. 2:done. naive_solver.
  Qed.

  Lemma path_ends_vertices g x1 xs x2 :
    path g x1 xs x2 ->
    (x1 = x2) \/ (x1 ∈ vertices g /\ x2 ∈ vertices g).
  Proof.
     inversion 1; first eauto.
     subst. right.
     split.
     - apply elem_of_vertices. eauto.
     - apply path_inv_r in H3. destruct H3 as [(->&->)|(?&?&?&->&?&?)].
       all:apply elem_of_vertices; eauto.
  Qed.

  (* 'undo_graph' is in fact a generic substitution operation on graphs *)
  Definition undo_graph (g : graph A B) (xs ys : list (A * B * A)) : graph A B :=
    list_to_set ys ∪ g ∖ list_to_set xs.

  Lemma undo_path g r xs rs ys :
    path g rs xs r ->
    mirror xs ys ->
    path (undo_graph g xs ys) r ys rs.
  Proof.
    intros Hxs Hxsys.
    enough (path (list_to_set ys) r ys rs) as Pys.
    { eapply path_weak.
    - eapply Pys.
    - unfold undo_graph; set_solver. }
    eapply use_mirror; eauto.
  Qed.

  Lemma mirror_app_inv_in_graph g na ys1 nb ys2 nc ysm :
    let ys := ys1 ++ ys2 in
    let g' := undo_graph g ys ysm in
    path g na ys1 nb ->
    path g nb ys2 nc ->
    mirror ysm ys ->
    exists ys1m ys2m,
      ysm = ys2m ++ ys1m /\
      mirror ys1m ys1 /\
      mirror ys2m ys2 /\
      path g' nc ys2m nb /\
      path g' nb ys1m na
  .
  Proof.
    revert ysm ys2 na.
    induction ys1; intros ysm ys2 na ys g' Pab Pbc Hmirror.
    - exists nil, ysm.
      { split_and!; eauto.
        - rewrite app_nil_r; done.
        - constructor; done.
        - apply (undo_path g nc ys2 nb ysm); eauto; [].
          apply mirror_symm; eauto.
        - inversion Pab; subst; constructor.
      }
    - unfold ys in Hmirror.
      rewrite -app_comm_cons in Hmirror.
      inversion Hmirror; subst.
      inversion Pab; subst.
      destruct (IHys1 xs ys2 r) as (ys1m & ys2m & Hxs & Mys1 & Mys2 & Pcb & Pbr); eauto; [].
      exists (ys1m ++ [(r, x, r')]), ys2m.
      { split_and!; eauto.
      - subst xs.
        rewrite assoc.
        done.
      - constructor; done.
      - inversion Pab; subst.
        apply path_weak with (list_to_set ys2m); first last.
        {
          unfold g'; unfold undo_graph.
          intros elem Helem.
          repeat rewrite list_to_set_app.
          repeat (apply elem_of_union; left); done.
        }
        apply path_restrict with (undo_graph g (ys1 ++ ys2) (ys2m ++ ys1m)); done.
      - inversion Pab; subst.
        { apply path_app with r.
        - apply path_weak with (list_to_set ys1m); first last.
          {
            unfold g'; unfold undo_graph.
            intros elem Helem.
            repeat rewrite list_to_set_app.
            do 2 (apply elem_of_union; left).
            apply elem_of_union; right.
            done.
          }
          apply path_restrict with
            (undo_graph g (ys1 ++ ys2) (ys2m ++ ys1m)); done.
        - constructor; [ | constructor; done ].
          unfold g'.
          unfold undo_graph.
          set_solver.
        }
      }

  Qed.

  Lemma undo_iso g xs ys :
    list_to_set xs ⊆ g ->
    graph_iso (list_to_set xs) (list_to_set ys) -> graph_iso g (undo_graph g xs ys).
  Proof.
    intros Hincl Hiso.
    set g' := list_to_set xs ∪ (g ∖ list_to_set xs).
    assert (g = g') as Hg.
    {
      apply leibniz_equiv.
      subst g'.
      rewrite union_comm.
      rewrite difference_union.
      set_solver.
    }
    replace (graph_iso g) with (graph_iso g') by (rewrite Hg; eauto).
    unfold g', undo_graph.
    apply union_iso; eauto; [].
    unfold graph_iso; unfold graph_incl; intuition.
  Qed.

  Lemma undo_mirror_vertices g xs ys :
    mirror xs ys ->
    list_to_set xs ⊆ g ->
    vertices g = vertices (undo_graph g xs ys).
  Proof.
    intros Mxsys Hincl.
    assert (g = undo_graph g xs xs) as Hg.
    { unfold undo_graph.
      apply leibniz_equiv.
      rewrite union_comm.
      rewrite difference_union.
      set_solver. }
    replace (vertices g) with (vertices (undo_graph g xs xs)) by (rewrite -Hg; eauto).
    unfold undo_graph.
    repeat rewrite vertices_union.
    rewrite (mirror_vertices xs); eauto.
  Qed.
End graph.

(* ------------------------------------------------------------------------ *)
(* Define apply_diffl, a function applying a list of diff. *)

Section adiffl.
  Notation diff := (
    (* location and its old value *)
    location*val
  )%type.

  Definition apply_diffl (ds:list diff) (σ:gmap location val) : gmap location val :=
    foldr (fun '(l,v) σ => <[l:=v]> σ) σ ds.

  Lemma dom_apply_diffl ds σ :
    dom (apply_diffl ds σ) = dom σ ∪ (list_to_set ds.*1).
  Proof.
    induction ds as [|(?&?)]; set_solver.
  Qed.

  Lemma apply_diffl_insert_ne ds l v σ :
    l ∉ ds.*1 ->
    apply_diffl ds (<[l:=v]> σ) = <[l:=v]> (apply_diffl ds σ).
  Proof.
    induction ds as [|(?&?)].
    { intros ?. reflexivity. }
    { intros. simpl. rewrite IHds; first by set_solver.
      rewrite insert_commute //. set_solver. }
  Qed.

  Lemma apply_diffl_app ds ds' σ :
    apply_diffl (ds++ds') σ = apply_diffl ds (apply_diffl ds' σ).
  Proof.
    rewrite /apply_diffl foldr_app //.
  Qed.

  Lemma apply_diffl_snoc xs l v σ :
    apply_diffl (xs ++ [(l,v)]) σ = apply_diffl xs (<[l:=v]> σ).
  Proof.
    rewrite apply_diffl_app //.
  Qed.

  Lemma apply_diffl_cons l v xs σ :
    apply_diffl ((l,v)::xs) σ = <[l:=v]> (apply_diffl xs σ).
  Proof.
    done.
  Qed.

  Lemma apply_diffl_included xs σ1 σ2 :
    σ1 ⊆ σ2 ->
    apply_diffl xs σ1 ⊆ apply_diffl xs σ2.
  Proof.
    revert σ1 σ2. induction xs as [|(?,?)]; intros;
      [ done | eauto using gmap_included_insert ].
  Qed.
End adiffl.

(* ------------------------------------------------------------------------ *)
(* Proof. *)

Notation snapshot_model := (location * gmap location val * generation)%type.

Class PstoreG Σ `{zoo_G : !ZooG Σ} := {
  #[local] pstore_G_set_G :: MonoSetG Σ snapshot_model ;
}.

Definition pstore_Σ := #[
  mono_set_Σ snapshot_model
].
#[global] Instance subG_pstore_Σ Σ `{zoo_G : !ZooG Σ} :
  subG pstore_Σ Σ →
  PstoreG Σ.
Proof.
  solve_inG.
Qed.

Section pstore_G.
  Context `{pstore_G : PstoreG Σ}.

  Notation diff := (
    (* location and its old value. *)
    location*val
  )%type.
  Notation graph_store := (
    graph location diff
  ).
  Notation map_model := (
    gmap location (gmap location val)
  ).
  Notation generation_model := (
    gmap location generation
  ).
  Notation snapshots_model := (
    gset snapshot_model
  ).

  Implicit Types g h : graph_store.
  Implicit Types M : map_model.
  Implicit Types C : snapshots_model.
  Implicit Types G : generation_model.

  Definition correct_path_diff (M:map_model) (g:graph_store) :=
    forall r1 ds r2 σ1 σ2,
      path g r1 ds r2 -> M !! r1 = Some σ1 -> M !! r2 = Some σ2 ->
      σ1 = (apply_diffl (proj2 <$> ds) σ2).

  Record store_inv (M:map_model) (G:generation_model) (g:graph_store) (r:location) (σ σ0:gmap location val) :=
    { si1M : dom M = vertices g ∪ {[r]};
      si1G : dom M = dom G;
      si2 : σ ⊆ σ0;
      si3 : M !! r = Some σ0 ;
      si4 : correct_path_diff M g
    }.

  Definition locations_of_edges_in g (X:gset location) :=
    forall (r:location) l v r', edge g r (l,v) r' -> l ∈ X.

  Record coherent (M:map_model) (σ0:gmap location val) (g:graph_store) :=
    { coh1 : forall r σ, M !! r = Some σ -> dom σ = dom σ0;
      coh2 : locations_of_edges_in g (dom σ0);
    }.

  Definition captured C l :=
    exists σ gen, (l, σ, gen) ∈ C.

  (* TODO include in stdpp ?
     https://gitlab.mpi-sws.org/iris/stdpp/-/issues/209 *)
  Lemma Decision_transport : forall P Q, (P <-> Q) -> Decision P -> Decision Q.
  Proof.
    unfold Decision. tauto.
  Qed.

  #[global] Instance captured_decision C l :
    Decision (captured C l).
  Proof.
    { apply Decision_transport with (set_Exists (fun '(k, _, _) => k = l) C).
      - unfold captured.
        unfold set_Exists.
        { constructor.
        - intros (((k, σ), gen), (H, ->)). eauto.
        - intros (σ & gen & H).
          exists (l, σ, gen). eauto. }
      - apply set_Exists_dec.
        intros ((l' , σ), gen).
        unfold Decision.
        destruct_decide (decide (l' = l)); auto.
    }
  Qed.

  Lemma captured_incl C C' l :
    C ⊆ C' -> captured C l -> captured C' l.
  Proof.
    unfold captured. set_solver.
  Qed.

  Definition no_succ g k :=
    forall k', not (has_edge g k k').

  Definition at_most_one_child g k :=
    forall k1 k2, has_edge g k1 k -> has_edge g k2 k -> k1 = k2.

  Definition topology_inv g M C r :=
    (* If a node is not captured, then:
       - if it is the current root, it has no children
       - otherwise it has at most one child *)
    forall k, k ∈ dom M -> not (captured C k) ->
      ((k = r) -> no_succ g k)
      /\
      (at_most_one_child g k)
    .

  Lemma topology_domM_transport : forall g M M' C r,
    dom M = dom M' -> topology_inv g M C r -> topology_inv g M' C r.
  Proof.
    intros g M M' C r H Htop.
    intros k Hk.
    rewrite <- H in Hk.
    exact (Htop k Hk).
  Qed.

  Definition history_inv g r h orig :=
    exists xs ys,
      path g orig xs r /\
      mirror xs ys /\
      h ≡ undo_graph g xs ys.

  Lemma history_vertices g r h orig :
    history_inv g r h orig ->
    vertices g = vertices h.
  Proof.
    intros (xs & ys & Pxs & Mxsys & Hundo).
    replace h with (undo_graph g xs ys) by (by apply leibniz_equiv).
    apply undo_mirror_vertices; eauto.
    eapply path_all_in; eauto.
  Qed.

  Lemma history_vertices_have_a_generation M C G g r σ σ0 h orig :
    store_inv M G g r σ σ0 ->
    history_inv g r h orig ->
    forall k, k ∈ vertices h ->
    exists kgen, G !! k = Some kgen.
  Proof.
    intros Hstore_inv Histo_inv k Hk.
    rewrite -(history_vertices g r h orig) in Hk; eauto.
    destruct Hstore_inv.
    assert (k ∈ dom G) as HkG by set_solver.
    apply elem_of_dom; eauto.
  Qed.

  (* The relation between the generation of a node and the generational of
     its (historical) parent:
     - if the parent is captured, the generation was incremented by the capture(s)
       so the child has a strictly greater generation
     - otherwise they have the same generation. *)
  Definition gen_succ_rel C G (child_gen : generation) (parent : location) :=
    match G !! parent with
    | None => False
    | Some parent_gen =>
      if (decide (captured C parent)) then
        child_gen > parent_gen
      else
        child_gen = parent_gen
    end.

  Definition global_gen_inv h C G r store_gen :=
    (* All nodes respect the parent-child generation relation. *)
    (forall k gk l, has_edge h k l -> G !! k = Some gk ->
      gen_succ_rel C G gk l)
    /\
    (* The global generation of the store would be a valid generation
       for a child of the current root. *)
    (gen_succ_rel C G store_gen r).

  Definition snapshot_inv M C G l σ snap_gen :=
    exists σ',
      M !! l = Some σ' /\
      σ ⊆ σ' /\
      (* /!\ [snap_gen] is the value store in the [snap_gen] field of
         the snapshot, which corresponds to the current store
         generation *before* the snapshot was captured. It is not in
         general a valid store generation *after* the capture, but [1
         + snap_gen] will be, and this is what the implementation of
         [restore] will use. *)
      gen_succ_rel C G (1 + snap_gen) l.

  Definition snapshots_inv M C G :=
    forall l σ snap_gen, (l, σ, snap_gen) ∈ C ->
      snapshot_inv M C G l σ snap_gen.

  #[local] Definition pstore_map_auth (γ:gname) (s:gset snapshot_model) :=
    mono_set_auth γ (DfracOwn 1) s.
  #[local] Definition pstore_map_elem γ l σ gen :=
    mono_set_elem γ (l, σ, gen).

  Lemma extract_unaliased (g : graph_store) :
    ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : location), v, #(r' : location) }) -∗
    ⌜unaliased g⌝.
  Proof.
    iIntros "Hg" (???????).
    destruct_decide (decide (a0 = a2 ∧ a1 = a3)); first done.
    rewrite (big_sepS_delete _ _ (a, a0, a1)); first set_solver.
    rewrite (big_sepS_delete _ _ (a, a2, a3)); first set_solver.
    iDestruct "Hg" as "(?&?&_)". destruct a0,a2.
    iDestruct (pointsto_ne with "[$][$]") as "%". congruence.
  Qed.

  Lemma generations_decrease_along_history_edge h M C G r store_gen k l gk gl :
    global_gen_inv h C G r store_gen ->
    has_edge h k l ->
    G !! k = Some gk ->
    G !! l = Some gl ->
    gk >= gl.
  Proof.
    intros (Hglobgeninv & _) Ekl Gk Gl .
    pose proof (Hglobgeninv k gk l Ekl Gk) as Hkl.
    unfold gen_succ_rel in Hkl.
    rewrite Gl in Hkl.
    destruct_decide (decide (captured C l)); lia.
  Qed.

  Lemma generations_decrease_along_history_path h M C G r store_gen na xs nb gena genb :
    global_gen_inv h C G r store_gen ->
    vertices h ⊆ dom G ->
    path h na xs nb ->
    G !! na = Some gena ->
    G !! nb = Some genb ->
    gena >= genb.
  Proof.
    intros (Hglobgen & _) Hdom.
    revert xs na gena.
    induction xs; intros na gena Pxs Ga Gb.
    - inversion Pxs; subst.
      rewrite Ga in Gb.
      inversion Gb; subst.
      eauto.
    - inversion Pxs; subst.
      assert (exists gena2, G !! a2 = Some gena2 /\ gena >= gena2) as (gena2 & Ga2 & Hgena2). {
        assert (a2 ∈ dom G) as Ha2dom. {
          enough (a2 ∈ vertices h) by set_solver.
          eapply right_vertex; eauto.
        }
        destruct (elem_of_dom G a2) as [H1 _].
        destruct H1 as (gena2, Ga2); eauto.
        exists gena2; split; eauto.
        pose proof (Hglobgen na gena a2 ltac:(eexists; eauto) Ga).
        unfold gen_succ_rel in H. rewrite Ga2 in H.
        revert H.
        destruct_decide (decide (captured C a2)); lia.
      }
      pose proof (IHxs a2 gena2 H4 Ga2 Gb); lia.
  Qed.

  (* NB our invariant asserts that g is indeed a rooted tree: a rooted DAG
     with unicity of paths. Indeed, from the set of pointsto we can extract [unaliased],
     (see [extract_unaliased]), and a DAG with unaliased guarantees unicity of paths
     (see [acyclic_unaliased_impl_uniq_path] ) *)

  #[local] Definition snapshots (t0:location) M C G : iProp Σ :=
    ∃ (γ:gname),
      ⌜snapshots_inv M C G⌝ ∗ meta t0 nroot γ ∗ pstore_map_auth γ C.

  #[local] Definition pstore (t:val) (σ:gmap location val) : iProp Σ :=
    ∃ (t0 r orig:location) gen
      (σ0:gmap location val) (* the global map, with all the points-to ever allocated *)
      (g:graph_store) (* the current graph *)
      (h:graph_store) (* the historic graph *)
      (M:map_model) (* the map model, associating to each node its model *)
      (C:snapshots_model) (* the subset of nodes captured as snapshots *)
      (G:generation_model) (* the generation of each node *)
      ,
    ⌜t=#t0 /\
     store_inv M G g r σ σ0 /\
     topology_inv g M C r /\
     history_inv g r h orig /\
     coherent M σ0 g /\
     rooted_dag g r /\
     global_gen_inv h C G r gen⌝ ∗
    t0.[root] ↦ #r ∗
    t0.[gen] ↦ #gen ∗
    r ↦ §Root ∗
    snapshots t0 M C G ∗
    ([∗ map] l ↦ v ∈ σ0, l.[sref_value] ↦ v) ∗
    ([∗ set] x ∈ g, let '(r,(l,v),r') := x in r ↦ ’Diff{ #(l : location), v, #(r' : location) }) .

  Definition open_inv : string :=
    "[%t0 [%r [%orig [%gen [%σ0 [%g [%h [%M [%C [%G
       ((-> &
         %Hinv &
         %Htopo &
         %Hist &
         %Hcoh &
         %Hgraph &
         %Hglobgen
        ) &
        Ht0 &
        Hgen &
        Hr &
        HC &
        Hσ0 &
        Hg
       )]]]]]]]]]]".

  Definition pstore_snapshot t s σ : iProp Σ :=
    ∃ γ (t0:location) l gen,
      ⌜t=#t0 /\ s=ValTuple [t;#l;ValInt gen]⌝ ∗ meta t0 nroot γ ∗ pstore_map_elem γ l σ gen.

  #[global] Instance pstore_snapshot_timeless t s σ :
    Timeless (pstore_snapshot t s σ).
  Proof.
    apply _.
  Qed.
  #[global] Instance pstore_snapshot_persistent t s σ :
    Persistent (pstore_snapshot t s σ).
  Proof.
    apply _.
  Qed.

  Lemma pstore_create_spec :
    {{{ True }}}
      pstore_create ()
    {{{ t,
      RET t;
        pstore t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_alloc r as "Hroot".
    wp_record t0 as "Hmeta" "(Ht0 & Hgen & _)".
    iMod (mono_set_alloc ∅) as "[%γ ?]".
    iMod (meta_set _ _ _ nroot with "Hmeta") as "Hmeta"; first set_solver.
    iApply "HΦ". iModIntro.
    iExists t0,r,r,0,∅,∅,∅,{[r := ∅]},∅,{[r := 0]}. iFrame.
    rewrite !big_sepM_empty big_sepS_empty !right_id.
    iSplitR.
    2:{ iExists γ. iFrame. iPureIntro. intros ??. set_solver. }
    iPureIntro. split_and!; first done.
    { (* store_inv *)
      constructor.
      { rewrite dom_singleton_L vertices_empty //. set_solver. }
      { set_solver. }
      { set_solver. }
      { rewrite lookup_insert //. }
      { intros ????? Hr.
        rewrite !lookup_singleton_Some.
        inversion Hr; set_solver. } }
    { (* topology_inv *)
      constructor.
    - intro Hr; subst. intros l' (diff & Hedge).
      set_solver.
    - assert (k = r) by set_solver; subst.
      intros k1 k2 H1 H2.
      destruct H1; set_solver.
    }
    { (* history_inv *)
      exists []. exists []. unfold undo_graph.
      split_and!; eauto; constructor.
    }
    { (* coherent *)
      constructor.
      { intros ??. rewrite lookup_singleton_Some. intros (->&->). reflexivity. }
      { intros ????. set_solver. } }
    { (* rooted_dag *)
      eauto using rooted_dag_empty. }
    { (* global_gen_inv *)
      constructor.
    - intros k gk l (d, Habsurd).
      set_solver.
    - unfold gen_succ_rel.
      rewrite lookup_singleton.
      { destruct_decide (decide (captured ∅ r)) as Hcap.
      - unfold captured in Hcap.
        set_solver.
      - auto.
      }
    }
  Qed.

  Lemma use_locations_of_edges_in g r xs r' X :
    locations_of_edges_in g X ->
    path g r xs r' ->
    (list_to_set (proj2 <$> xs).*1) ⊆ X.
  Proof.
    intros He.
    induction 1; first set_solver.
    apply He in H. set_solver.
  Qed.

  Lemma pstore_ref_spec t σ v :
    {{{
      pstore t σ
    }}}
      pstore_ref t v
    {{{ l,
      RET #l;
      ⌜l ∉ dom σ⌝ ∗
      pstore t (<[l := v]> σ)
    }}}.
  Proof.
    iIntros (ϕ) open_inv. iIntros "HΦ".

    wp_rec. wp_record l as "( Hl & _ )".

    iApply "HΦ".

    iAssert ⌜σ0 !! l = None⌝%I as %Hl0.
    { rewrite -not_elem_of_dom. iIntros "%Hldom".
      iDestruct (big_sepM_lookup with "Hσ0") as "( Hl_ & Hfoo & _ )".
      { apply lookup_lookup_total_dom. exact Hldom. }
      iDestruct (pointsto_ne with "Hl Hl_") as %?. done.
    }
    assert (σ !! l = None).
    { eapply not_elem_of_dom. apply not_elem_of_dom in Hl0.  destruct Hinv as [_ _ X].
      apply incl_dom_incl in X. set_solver. }
    iDestruct (pointsto_ne with "Hl Hr") as %Hlr.

    iModIntro. iSplitR. { iPureIntro. by eapply not_elem_of_dom. }
    iExists t0,r,orig,gen, (<[l:=v]>σ0),g,h,((fun σ => <[l:=v]>σ)<$> M),C,G.

    rewrite big_sepM_insert //. iFrame "∗".
    iSplitR "HC"; first (iPureIntro; split_and!; eauto).
    { (* store_inv *)
      destruct Hinv as [X1 X2 X3 X4].
      constructor.
      { rewrite dom_fmap_L; set_solver. }
      { rewrite dom_fmap_L; set_solver. }
      { eauto using gmap_included_insert. }
      { rewrite lookup_fmap X4 //. }
      { intros r1 ds r2 σ1 σ2 Hr. rewrite !lookup_fmap. generalize Hr. intros Hreach.
        intros Hr1 Hr2.
        destruct (M !! r1) eqn:Hor1. 2:simpl in *; congruence.
        inversion Hr1. subst.
        destruct (M !! r2) eqn:Hor2. 2:simpl in *; congruence.
        inversion Hr2. subst.
        destruct Hcoh as [Z1 Z2].
        eapply use_locations_of_edges_in in Z2. 2:done.
        rewrite apply_diffl_insert_ne.
        { apply not_elem_of_dom in Hl0. set_solver. }
        { f_equal. eauto. } } }
    { (* topology_inv *)
      apply (topology_domM_transport g M).
      { set_solver. }
      { assumption. }
    }
    { (* coherent *)
      destruct Hcoh as [X1 X2].
      constructor.
      { intros r' ?. rewrite lookup_fmap. intros E.
        destruct (M !! r') eqn:Hor. 2:simpl in *; congruence.
        inversion E. subst. rewrite !dom_insert_L. set_solver. }
      { intros. rewrite dom_insert_L. intros ??. set_solver. } }
    { (* snapshots *)
      iDestruct "HC" as "[% (%Hsnap&?&?)]".
      iExists _. iFrame. iPureIntro.
      intros r' ? ? HC. apply Hsnap in HC. destruct HC as (x & Hx & ? & ?).
      exists (<[l:=v]>x).
      split_and!; eauto.
      - rewrite lookup_fmap Hx; eauto.
      - apply gmap_included_insert_notin; eauto.
        apply incl_dom_incl in H0. intros X. apply H0 in X.
        destruct Hcoh as [X1 X2]. apply X1 in Hx.
        apply not_elem_of_dom in Hl0. set_solver. }
  Qed.

  Lemma pstore_get_spec {t σ l} v :
    σ !! l = Some v →
    {{{
      pstore t σ
    }}}
      pstore_get t #l
    {{{
      RET v;
      pstore t σ
    }}}.
  Proof.
    iIntros (Hl ϕ) open_inv. iIntros "HΦ".
    wp_rec. iStep 4. iModIntro.

    iDestruct (big_sepM_lookup_acc _ _ l v with "Hσ0") as "(Hl & Hclose)".
    { destruct Hinv as [_ _ Hincl _ _].
      specialize (Hincl l). rewrite Hl in Hincl. destruct (σ0!!l); naive_solver. }

    wp_load. iStep. iModIntro.

    iExists t0,r,orig,gen,σ0,g,h,M,C,G.
    iFrame.
    { iSplit.
    - iPureIntro.
      split_and!; eauto.
    - iApply "Hclose"; iSteps.
    }
  Qed.

  Lemma pstore_set_spec t σ l v :
    l ∈ dom σ →
    {{{
      pstore t σ
    }}}
      pstore_set t #l v
    {{{
      RET ();
      pstore t (<[l := v]> σ)
    }}}.
  Proof.
    iIntros (Hl Φ) open_inv. iIntros "HΦ".
    wp_rec. iStep 8. iModIntro.
    wp_alloc r' as "Hr'".

    assert (exists w, σ0 !! l = Some w) as (w&Hl0).
    { apply elem_of_dom. destruct Hinv as [_ _ Hincl].
      apply incl_dom_incl in Hincl.
      set_solver. }

    iDestruct (big_sepM_insert_acc with "Hσ0") as "( Hl & Hσ0 )"; first done.
    wp_load. wp_load. wp_store. iStep 4. iModIntro.
    wp_store. wp_store. iApply "HΦ".

    iSpecialize ("Hσ0" with "[$]").

    iAssert ⌜r ≠ r'⌝%I as %?.
    { iClear "Ht0". iDestruct (pointsto_ne with "[$][$]") as %?. done. }

    iAssert ⌜r' ∉ vertices g⌝%I as %Hr'.
    { iIntros (Hr'). destruct Hgraph as [X1 X2].
      apply X1 in Hr'. destruct Hr' as (?&Hr'). inversion Hr'; subst.
      { done. }
      { destruct b. iDestruct (big_sepS_elem_of with "[$]") as "?"; first done.
        iDestruct (pointsto_ne r' r' with "[$][$]") as %?. congruence. } }

    iModIntro.
    iExists
      t0,r',orig,gen,
      (<[l:=v]> σ0),
      ({[(r,(l,w),r')]} ∪ g),
      ({[(r',(l,w),r)]} ∪ h),
      (<[r':=<[l:=v]> σ0]>M),
      C,
      (<[r':=gen]>G).
    rewrite big_sepS_union.
    { apply disjoint_singleton_l. intros ?. apply Hr'.
      apply elem_of_vertices. eauto. }
    rewrite big_sepS_singleton. iFrame "#∗".

    iDestruct "HC" as "[% (%Hsnap&?&?)]".
    { iSplitR; first (iPureIntro; split_and!; first done).
    - (* store_inv *)
      destruct Hinv as [X1 X2 X3 X4 X5].
      constructor.
      { rewrite dom_insert_L vertices_union vertices_singleton //. set_solver. }
      { set_solver. }
      { apply gmap_included_insert. done. }
      { rewrite lookup_insert //. }
      { intros r1 ds r2 σ1 σ2 Hreach.
        destruct_decide (decide (r'=r1)).
        { subst. rewrite lookup_insert. inversion_clear 1.
          inversion Hreach.
          2:{ exfalso. subst. rewrite /edge elem_of_union in H0.
              destruct H0; first set_solver. apply Hr'. apply elem_of_vertices. set_solver. }
          subst.
          rewrite lookup_insert. inversion 1. done. }
        rewrite lookup_insert_ne //. intros E1.
        destruct_decide (decide (r2=r')).
        { subst. rewrite lookup_insert. inversion 1. subst.
          apply path_add_inv_r in Hreach; try done.
          destruct Hreach as [(->&->)|(ds'&->&Hreach)].
          { congruence. }
          specialize (X5 _ _ _ _ _ Hreach E1 X4).
          rewrite fmap_app apply_diffl_snoc insert_insert insert_id //. }
        { rewrite lookup_insert_ne //. intros. eapply X5; eauto.
          apply path_cycle_end_inv_aux in Hreach; eauto. } }
    - (* topology_inv *)
      intros k Hk_dom Hk_cap.
      { constructor.
      - (* no_succ *)
        intros Hk; subst.
        intros k' (diff & Hk').
        rewrite elem_of_union in Hk'.
        rewrite elem_of_singleton in Hk'.
        { destruct Hk' as [ Hk' | Hk' ].
        - injection Hk'; intros; subst. auto.
        - contradiction Hr'.
          eapply left_vertex; eauto.
        }
      - (* at_most_one_child *)
        intros k1 k2 (d1 & Hk1) (d2 & Hk2).
        rewrite -> elem_of_union in Hk1.
        rewrite -> elem_of_union in Hk2.
        { destruct Hk1; destruct Hk2.
        - set_solver.
        - assert (k = r') by set_solver. subst.
          contradiction Hr'. eapply right_vertex. eauto.
        - assert (k = r') by set_solver. subst.
          contradiction Hr'. eapply right_vertex. eauto.
        - assert (k ∈ dom M) as Hkm.
          { rewrite -> dom_insert in Hk_dom.
            rewrite -> elem_of_union in Hk_dom.
            { destruct Hk_dom as [ Hk_dom | Hk_dom ]; last assumption.
            - rewrite elem_of_singleton in Hk_dom; subst.
              contradiction Hr'. eapply right_vertex. eauto.
            }
          }
          apply (Htopo k); try eexists; eauto.
        }
      }
    - (* history_inv *)
      destruct Hist as (xs & ys & Hpath & Hmirror & Hhisto).
      exists (xs ++ [(r, (l, w), r')]).
      exists ((r', (l, w), r) :: ys).
      { split_and!.
      - { apply path_snoc.
        - eapply path_weak; set_solver.
        - set_solver. }
      - { apply mirror_symm.
          apply mirror_snoc.
          apply mirror_symm.
          assumption.
        }
      - rewrite Hhisto.
        unfold undo_graph.
        rewrite list_to_set_cons.
        rewrite list_to_set_app.
        rewrite list_to_set_singleton.
        enough (
          g ∖ list_to_set xs
          ≡
          ({[(r, (l, w), r')]} ∪ g) ∖ (list_to_set xs ∪ {[(r, (l, w), r')]})
        ) as Henough by (setoid_rewrite Henough; set_solver).
        rewrite difference_union_distr_l.
        setoid_replace
          ({[(r, (l, w), r')]} ∖ (list_to_set xs ∪ {[(r, (l, w), r')]}) : graph_store)
          with (∅ : graph_store) by set_solver.
        rewrite difference_union_distr_r.
        setoid_replace
          (g ∖ {[(r, (l, w), r')]}) with g; first last.
        { apply difference_disjoint.
          unfold disjoint.
          intros tri Hg Htri.
          assert (tri = (r, (l, w), r')) by set_solver; subst.
          contradiction Hr'.
          eapply right_vertex; eauto. }
        set_solver.
      }
    - (* coherent *)
      destruct Hcoh as [X1 X2].
      constructor.
      { intros r0 ?. destruct_decide (decide (r0=r')).
        { subst. rewrite lookup_insert. inversion 1. done. }
        rewrite lookup_insert_ne //. intros HM.
        apply X1 in HM. rewrite dom_insert_lookup_L //. }
      { intros ?. set_solver. }
    - (* rooted_dag *)
      eauto using rooted_dag_add.
    - (* global_gen_inv *)
      assert (not (captured C r')) as Hncapr'.
      {
        intros (σ' & r'gen & Hr'C).
        assert (r' ∈ dom M) as Hr'M.
        {
          rewrite elem_of_dom.
          unfold snapshots_inv, snapshot_inv in Hsnap.
          destruct (Hsnap r' σ' r'gen Hr'C) as (σ'', (H', _)).
          eexists; eauto.
        }
        destruct Hinv.
        erewrite -> si1M0 in Hr'M.
        set_solver.
      }
      { constructor.
      - (* gen_succ_rel between nodes *)
        intros k gk j Hkj Hgk.
        unfold gen_succ_rel.
        rewrite edge_of_union in Hkj.
        { destruct Hkj as [ (diff, Hkj) | (diff, Hkj) ].
        - rewrite elem_of_singleton in Hkj.
          invert Hkj; subst.
          rewrite lookup_insert in Hgk.
          injection Hgk; intro; subst gk.
          rewrite lookup_insert_ne; first eauto.
          destruct Hglobgen as [Hglobgen1 Hglobgen2].
          unfold gen_succ_rel in Hglobgen2.
          destruct (G !! r) as [ gr | ] eqn:Hgr; last contradiction Hglobgen2.
          rewrite Hgr.
          apply Hglobgen2.
        - assert (forall n, n ∈ vertices h -> r' ≠ n) as Hnotr'.
          {
            intros n Hn Heq; subst n.
            rewrite -(history_vertices g r h orig) in Hn; eauto.
          }
          rewrite lookup_insert_ne; first (apply Hnotr'; eauto; eapply right_vertex; eauto).
          rewrite lookup_insert_ne in Hgk; first (apply Hnotr'; eauto; eapply left_vertex; eauto).
          destruct Hglobgen as [Hglobgen1 Hglobgen2].
          apply (Hglobgen1 k gk j); eauto.
          eexists; eauto.
        }
      - (* gen_succ_rel between the store generation and the current root *)
        unfold gen_succ_rel.
        rewrite lookup_insert.
        { destruct_decide (decide (captured C r')).
        - by contradiction Hncapr'.
        - trivial. }
      }
    - (* snapshots *)
      iExists _. iFrame.
      iPureIntro.
      intros r0 ? ? HC. apply Hsnap in HC.
      unfold snapshot_inv. destruct HC as (?&HC&?&?).
      assert (r0 ≠ r') as Hneqr0r'.
      { intro Hr0r.
        subst. destruct Hinv as [X1 X2 X3].
        assert (r' ∉ dom M) as F by set_solver. apply F. by eapply elem_of_dom. }
      rewrite lookup_insert_ne //.
      exists x.
      split_and!; eauto; [].
      unfold gen_succ_rel.
      rewrite lookup_insert_ne //.
    }
  Qed.

  Lemma pstore_capture_spec t σ :
    {{{
      pstore t σ
    }}}
      pstore_capture t
    {{{ s,
      RET s;
      pstore t σ ∗
      pstore_snapshot t s σ
    }}}.
  Proof.
    iIntros (Φ) open_inv. iIntros "HΦ".
    wp_rec.
    wp_load. wp_store. wp_load. iStep 5.

    iDestruct "HC" as "[% (%Hsnap & Hmeta & HC)]".
    iMod (mono_set_insert' (r, σ, gen) with "HC") as "(HC&Hsnap)".
    iModIntro.
    iSplit. 2:iSteps.

    set C' : snapshots_model := {[(r, σ, gen)]} ∪ C.

    assert (gen_succ_rel C' G (1 + gen) r) as HgenC'r. {
      destruct Hglobgen as [Hglobgen1 Hglobgen2].
      unfold gen_succ_rel in Hglobgen2.
      unfold gen_succ_rel.
      destruct (G !! r) as [ rgen | ]; eauto.
      assert (captured C' r) by (unfold captured; set_solver).
      rewrite decide_True; eauto.
      destruct_decide (decide (captured C r)) as HcapC; lia.
   }

    unfold pstore.
    iExists t0, r, orig, (1+gen), _, _, _, _, C'.
    { iSteps; iPureIntro.

    - (* topology_inv g M C' *)
      intros l Hl_dom Hl_cap.
      assert (not (captured C l)) as Hl_cap'
        by (unfold captured in *; set_solver).
      apply (Htopo l Hl_dom Hl_cap').

    (* global_gen_inv. *)
    - (* gen_succ_rel between nodes (k, l) *)
      destruct Hglobgen as (Hglobgen1 & Hglobgen2).
      intros k gk l Hkl Hgk.
      unfold gen_succ_rel.
      pose proof (history_vertices_have_a_generation M C G g r σ σ0 h orig ltac:(eauto) ltac:(eauto))
        as generation_finder.
      destruct (generation_finder l) as (gl & Hgl); first (destruct Hkl; eapply right_vertex; eauto).
      rewrite Hgl.
      pose proof (Hglobgen1 k gk l ltac:(eauto) ltac:(eauto)) as HgenC.
      unfold gen_succ_rel in HgenC.
      rewrite Hgl in HgenC.
      { destruct_decide (decide (l = r)) as Hlr.
      - subst l.
        assert (captured C' r) as HcapC'r by (unfold captured, C'; set_solver).
        assert (captured C r) as HcapCr.
        {
          (* If 'l' is the current root r and has a historic child k (we
             have (k, r) ∈ h), then the current root must be captured
             already in C.

             The reasoning is a bit subtle:

             - if k is on the path from r to orig, then we have the
               converse relation (r, k) ∈ g, which implies that r is
               captured by the no_succ invariant: the root has no
               successor unless it is captured.

             - if k is *not* on path from r to orig, then *some other
               node* k' is, and we have (k, r) ∈ g and also (k', r) ∈ g,
               so r must be captured by the at_most_one_child invariant.
           *)
          TODO admit.
        }
        rewrite decide_True; eauto.
        rewrite decide_True in HgenC; eauto.
      - assert (captured C l <-> captured C' l) as Hcapequiv by (unfold captured; set_solver).
        { destruct_decide (decide (captured C l)) as HcapC; rewrite Hcapequiv in HcapC.
        - rewrite decide_True; eauto.
        - rewrite decide_False; eauto.
        }
      }

    - (* snapshots_inv M C' G *)
      intros r' ? ? HC. rewrite elem_of_union elem_of_singleton in HC.
      { destruct HC as [HC|HC].
      - inversion HC. subst. destruct Hinv.
        destruct Hglobgen as [Hglobgen1 Hglobgen2].
        exists σ0; split_and!; eauto.
      - destruct (Hsnap r' σ1 snap_gen) as (σ' & HMr' & Hσ' & Hsnapgen); eauto.
        exists σ'; split_and!; eauto.
        unfold gen_succ_rel.
        unfold gen_succ_rel in Hsnapgen.
        destruct (G !! r') as [ gr' | ]; eauto.
        assert (captured C r' <-> captured C' r') as Hcapeq. {
          destruct_decide (decide (r = r')).
          - subst r.
            unfold captured; set_solver.
          - unfold C'.
            unfold captured; set_solver.
        }
        { destruct_decide (decide (captured C r')) as Hcap; rewrite Hcapeq in Hcap.
        - rewrite decide_True //.
        - rewrite decide_False //.
        }
    }
  Admitted.

  Definition fsts  (ys:list (location*(location*val)*location)) : list val :=
    (fun '(x,_,_) => ValLoc x) <$> ys.

  Lemma pstore_collect_spec_aux (r r':location) t' (xs:list val) (ys:list (location*(location*val)*location)) (g:graph_store) :
    lst_model' t' xs ->
    path g r ys r' ->
    {{{
      r' ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : location), v, #(r' : location) })
    }}}
      pstore_collect #r t'
    {{{ t,
      RET (#r',t);
      r' ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : location), v, #(r' : location) }) ∗
      lst_model t (rev_append (fsts ys) xs)
    }}}.
  Proof.
    iIntros (-> Hpath Φ) "(Hr'&Hg) HΦ".
    iInduction ys as [|] "IH" forall (r xs r' Hpath); wp_rec.
    { inversion Hpath. subst. iSteps. }
    { inversion Hpath. subst.
      iDestruct (big_sepS_elem_of_acc _ _ (r,b,a2) with "[$]") as "(?&Hg)".
      { set_solver. } destruct b.
      wp_load.
      iSpecialize ("Hg" with "[$]").
      iSpecialize ("IH" with "[%//][$][$][$]").
      iSteps.
    }
  Qed.

  Lemma pstore_collect_spec (r r':location) (ys:list (location*(location*val)*location)) (g:graph_store) :
    path g r ys r' ->
    {{{
      r' ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : location), v, #(r' : location) })
    }}}
      pstore_collect #r §Nil
    {{{ t,
      RET (#r',t);
      r' ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : location), v, #(r' : location) }) ∗
      lst_model t (rev (fsts ys))
    }}}.
  Proof.
    iIntros (? Φ) "(?&?) HΦ".
    iDestruct (pstore_collect_spec_aux with "[$]") as "Go"; [done.. |].
    rewrite -lst_to_val_nil.
    iApply "Go". rewrite -rev_alt //.
  Qed.

  Lemma use_path r g (xs:list (location*(location*val)*location)) r0 x r1 r':
    list_to_set xs ⊆ g ->
    path g r (xs ++ [(r0, x, r1)]) r' ->
    (r0, x, r1) ∈ (list_to_set xs : gset(location*(location*val)*location) ) ->
    exists ds, path g r0 ds r0 /\ ds ≠ nil.
  Proof.
    revert r r0 r1 r' x. induction xs; intros r r0 r1 r' x ?.
    { set_solver. }
    rewrite -app_comm_cons. inversion 1. subst.
    rewrite list_to_set_cons.
    destruct_decide (decide ((r0, x, r1) = (r, b, a2))) as X.
    { inversion X. subst. intros _. clear IHxs.
      rewrite app_comm_cons in H0. apply path_snoc_inv in H0.
      destruct H0 as (?&?&?). subst a2.
      exists (((r, b, r') :: xs)). done. }
    { intros ?. apply IHxs in H6. 2,3:set_solver.
      destruct H6 as (?&?&?). eexists. split; last done.
      eapply path_weak; first done. set_solver. }
  Qed.

  (* [undo xs ys σ] asserts [mirror xs ys] and that [σ = apply_diffl (proj2 <$> ys ++ xs) σ],
     ie, ys undo the changes of xs *)
  Inductive undo :
    list (location*(location*val)*location) -> list (location*(location*val)*location) -> gmap location val -> Prop :=
  | undo_nil :
    forall σ, undo [] [] σ
  | undo_cons :
    forall σ r l v v' r' xs ys,
      σ !! l = Some v' ->
      undo xs ys (<[l:=v]> σ) ->
      undo (xs++[(r,(l,v),r')]) ((r',(l,v'),r)::ys) σ.

  Lemma use_undo xs ys σ :
    undo xs ys σ ->
    σ = apply_diffl (proj2 <$> ys ++ xs) σ.
  Proof.
    induction 1.
    { done. }
    rewrite !assoc_L fmap_app apply_diffl_snoc.
    rewrite -app_comm_cons fmap_cons apply_diffl_cons.
    rewrite -IHundo insert_insert insert_id //.
  Qed.

  Lemma undo_mirror xs ys m :
    undo xs ys m ->
    mirror xs ys.
  Proof.
    induction 1; eauto using mirror_cons,mirror_nil.
  Qed.

  Lemma pstore_revert_spec_aux g g1 r t g2 xs r' w σ σ0 :
    lst_model' t (fsts (rev xs)) ->
    locations_of_edges_in g2 (dom σ) ->
    g2 = list_to_set xs ->
    acyclic g ->
    g2 ⊆ g ->
    path g r xs r' ->
    {{{
      r' ↦ w ∗
      ([∗ map] l0↦v0 ∈ σ, l0.[sref_value] ↦ v0) ∗
      ([∗ set] '(r, (l, v), r') ∈ g1, r ↦ ’Diff{ #(l : location), v, #(r' : location) }) ∗
      ([∗ set] '(r, (l, v), r') ∈ g2, r ↦ ’Diff{ #(l : location), v, #(r' : location) })
    }}}
      pstore_revert #r' t
    {{{
      RET ();
      ∃ ys,
      ⌜undo xs ys σ⌝ ∗
      r ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ (g1 ∪ list_to_set ys), r ↦ ’Diff{ #(l : location), v, #(r' : location) }) ∗
      ([∗ map] l0↦v0 ∈ (apply_diffl (proj2 <$> xs) σ), l0.[sref_value] ↦ v0)
    }}}.
  Proof.
    iIntros (-> Hlocs Hg Hacy Hsub Hpath Φ) "(Hr'&Hσ&Hg1&Hg2) HΦ".
    iInduction xs as [|((r0,(l,v)),r1) ] "IH" using rev_ind forall (σ w r r' g1 g2  Hpath Hg Hlocs Hacy Hsub).
    { wp_rec. simpl.
      iStep 4. iModIntro.
      inversion Hpath. subst. wp_store. iModIntro.
      iApply "HΦ". iExists nil. rewrite !right_id_L. iFrame.
      iPureIntro. eauto using undo_nil. }
    { wp_rec. simpl. rewrite rev_unit. simpl.
      iStep 4. iModIntro.
      rewrite Hg list_to_set_app_L list_to_set_cons list_to_set_nil right_id_L.
      rewrite Hg list_to_set_app_L in Hsub.
      assert ((r0, (l, v), r1) ∉ (list_to_set xs : gset (location * diff * location))).
      { intros ?. apply use_path in Hpath; last done.
        - destruct Hpath as (?&Hpath&?).
          apply Hacy in Hpath. congruence.
        - set_solver. }
      iDestruct (big_sepS_union with "Hg2") as "(Hg2&?)".
      { set_solver. }
      rewrite big_sepS_singleton. wp_load. iStep 4. iModIntro.

      rewrite Hg list_to_set_app_L list_to_set_cons list_to_set_nil right_id_L in Hlocs.
      assert (exists v', σ !! l = Some v') as (v',Hl).
      { apply elem_of_dom. eapply Hlocs. rewrite /edge.

        rewrite elem_of_union elem_of_singleton. right. reflexivity. }

      apply path_snoc_inv in Hpath. destruct Hpath as (?&->&?).
      wp_smart_apply assert_spec. { rewrite bool_decide_eq_true_2 //. }
      iStep 4. iModIntro.

      iDestruct (big_sepM_insert_acc with "Hσ") as "(Hl & Hσ)"; first done.

      wp_load. wp_store. wp_store. iStep 4. iModIntro.

      iSpecialize ("Hσ" with "[$]").
      iSpecialize ("IH" with "[%//][%//][%][%//][%][$][$] Hg1 Hg2").
      { rewrite dom_insert_lookup_L //. intros x1 x2 x3 x4.
        specialize (Hlocs x1 x2 x3 x4). set_solver. }
      { set_solver. }

      rewrite fmap_app -apply_diffl_snoc. simpl.
      iApply "IH". iModIntro.
      iIntros "[%ys (%Hundo&?&?&?)]". iApply "HΦ".
      iExists ((r',(l,v'),r0)::ys). iFrame.
      iSplitR.
      { iPureIntro. eauto using undo_cons. }
      rewrite list_to_set_cons.
      iAssert ⌜(r', (l, v'), r0) ∉ g1 ∪ list_to_set ys⌝%I as "%".
      { iIntros (?). iDestruct (big_sepS_elem_of with "[$]") as "?"; first done.
        iDestruct (pointsto_ne r' r' with "[$][$]") as "%". congruence. }
      replace (g1 ∪ ({[(r', (l, v'), r0)]} ∪ list_to_set ys)) with ({[(r', (l, v'), r0)]} ∪ ((g1 ∪ list_to_set ys))). 2:set_solver.
      iApply big_sepS_union; first set_solver.
      iFrame. rewrite big_sepS_singleton //. }
  Qed.

  Lemma pstore_revert_spec r t g xs r' w σ σ0 :
    lst_model' t (fsts (rev xs)) ->
    locations_of_edges_in g (dom σ) ->
    g = list_to_set xs ->
    acyclic g ->
    path g r xs r' ->
    {{{
      r' ↦ w ∗
      ([∗ map] l0↦v0 ∈ σ, l0.[sref_value] ↦ v0) ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : location), v, #(r' : location) })
    }}}
      pstore_revert #r' t
    {{{
      RET ();
      ∃ ys,
      ⌜undo xs ys σ⌝ ∗
      r ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ (list_to_set ys), r ↦ ’Diff{ #(l : location), v, #(r' : location) }) ∗
      ([∗ map] l0↦v0 ∈ (apply_diffl (proj2 <$> xs) σ), l0.[sref_value] ↦ v0)
    }}}.
  Proof.
    iIntros (->???? Φ) "(?&?&?) HΦ".
    iApply (pstore_revert_spec_aux g ∅ with "[-HΦ]"); try done.
    { rewrite big_sepS_empty. iFrame. }
    { iModIntro. iIntros "[% ?]". iApply "HΦ". iExists _. rewrite left_id_L //. }
  Qed.

  Lemma rev_fsts xs :
    rev (fsts xs) = fsts (rev xs).
  Proof.
    induction xs as [|((?,?),?)]; simpl; eauto.
    rewrite IHxs /fsts fmap_app //.
  Qed.

  Lemma pstore_reroot_spec r (xs:list (location*(location*val)*location)) r' g σ :
    locations_of_edges_in g (dom σ) ->
    g = list_to_set xs ->
    acyclic g ->
    path g r xs r' ->
    {{{
      r' ↦ §Root ∗
      ([∗ map] l0↦v0 ∈ σ, l0.[sref_value] ↦ v0) ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : location), v, #(r' : location) })
    }}}
      pstore_reroot #r
    {{{
      RET ();
      ∃ ys,
      ⌜undo xs ys σ⌝ ∗
      r ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ (list_to_set ys), r ↦ ’Diff{ #(l : location), v, #(r' : location) }) ∗
      ([∗ map] l0↦v0 ∈ (apply_diffl (proj2 <$> xs) σ), l0.[sref_value] ↦ v0)
    }}}.
  Proof.
    iIntros (???? Φ) "(Hr'&Hσ&Hg) HΦ".
    wp_rec. wp_apply (pstore_collect_spec with "[$]"); first done.
    iIntros (?) "(?&?&%Heq)". rewrite {}Heq.
    wp_smart_apply (pstore_revert_spec with "[-HΦ]"); try done; first rewrite rev_fsts //.
    iSteps.
  Qed.

  Lemma locations_of_edges_weak g1 g2 X :
    locations_of_edges_in g1 X ->
    g2 ⊆ g1 ->
    locations_of_edges_in g2 X.
  Proof.
    intros Z ? a b c d ?. eapply (Z a b c d). set_solver.
  Qed.

  Lemma undo_same_fst_label xs ys r l v r' σ :
    undo xs ys σ ->
    (r, (l, v), r') ∈ (list_to_set ys :  gset (location*(location*val)*location)) ->
    l ∈ (list_to_set (proj2 <$> xs).*1 : gset location).
  Proof.
    revert xs σ. induction ys as [|(?,?)]; first set_solver.
    intros xs σ. inversion 1. subst.
    simpl. rewrite !fmap_app list_to_set_app_L. simpl in *. subst.
    destruct_decide (decide ((r, (l, v), r') = (r'0, (l1, v'), l0))) as Heq.
    { inversion Heq. subst. intros _. set_solver. }
    intros ?. simpl. apply elem_of_union. left. eapply IHys; first done. set_solver.
  Qed.

  Definition diff_last {A:Type} (ys1 ys2:list A) :=
    match last ys1, last ys2 with
    | Some x, Some y =>
        x ≠ y
    | _, _ =>
        True
    end.

  Lemma path_extract_suffix (g:gset (location*(location*val)*location)) a1 a2 xs1 r xs2 :
    unaliased g ->
    path g a1 xs1 r ->
    path g a2 xs2 r  ->
    exists ys1 ys2 xs,
      xs1 = ys1 ++ xs /\
      xs2 = ys2 ++ xs /\ diff_last ys1 ys2.
  Proof.
    intros Hinj.
    revert r a1 a2 xs2. induction xs1 using rev_ind; intros r a1 a2 xs2.
    { inversion 1. subst. intros. exists nil,xs2,nil.
      simpl. rewrite right_id_L. set_solver. }
    intros Hp1 Hp2. apply path_inv_r in Hp1.
    destruct Hp1 as [? | (bs'&b'&y&X1&X2&X3)].
    { destruct xs1; naive_solver. }
    apply app_inj_tail in X1. destruct X1 as (<-&->).

    apply path_inv_r in Hp2. destruct Hp2 as [(->&->) | (bs'&b&y'&->&?&?)].
    { exists (xs1 ++ [(y, b', r)]),nil,nil. rewrite right_id. split_and !; try done.
      unfold diff_last. destruct (last (xs1 ++ [(y, b', r)])); try done. }

    destruct_decide (decide (y'=y)); last first.
    { eexists _,_,nil. rewrite !right_id_L. split_and!; try done.
      unfold diff_last. rewrite !last_app. simpl. naive_solver. }
    subst.

    destruct (IHxs1 _ _ _ _ X2 H) as (ys1&ys2&xs&->&->&Hdiff).
    destruct (Hinj _ _ _ _ _ X3 H0) as (->&_).
    eexists _,_,(xs++[(y, b, r)]). rewrite !assoc_L. done.
  Qed.

  Lemma diff_last_app_middle {A:Type} x (l1' l2' l1 l2:list A) :
    diff_last (l1' ++ x :: l2') (l1 ++ x :: l2) ->
    diff_last (x :: l2') (x :: l2).
  Proof.
    unfold diff_last. rewrite !last_app !last_cons.
    destruct (last l2),(last l2'); eauto.
  Qed.

  Lemma diff_last_irrefl {A:Type} (l:list A) :
    l ≠ nil ->
    ¬ (diff_last l l).
  Proof.
    destruct (list_case_r l) as [|(?&?&->)]; first naive_solver.
    intros _. unfold diff_last.
    rewrite !last_app //. simpl. naive_solver.
  Qed.

  Lemma path_use_diff_last (g:gset (location*(location*val)*location)) a1 a2 ys1 ys2 xs r :
    acyclic g ->
    unaliased g ->
    path g a1 (ys1 ++ xs) r ->
    path g a2 (ys2 ++ xs) r  ->
    diff_last ys1 ys2 ->
    forall x, x ∈ ys2 -> x ∉ (ys1 ++ xs).
  Proof.
    intros Hacy Hroot Hp1 Hp2 Hdiff x Hx Hx'.
    apply elem_of_app in Hx'. destruct Hx' as [Hx'|Hx'].
    (* contradicts diff_last. *)
    { apply elem_of_middle in Hx,Hx'.
      destruct Hx as (l1&l2&->).
      destruct Hx' as (l1'&l2'&->).
      rewrite -!assoc_L in Hp1,Hp2.
      apply path_app_inv in Hp1,Hp2.
      destruct Hp1 as (x1&_&Hp1).
      destruct Hp2 as (x2&_&Hp2).
      rewrite -!app_comm_cons in Hp1,Hp2.
      assert (x1=proj1 x).
      { inversion Hp1. subst. done. }
      assert (x2=proj1 x).
      { inversion Hp2. subst. done. }
      subst.
      eapply acyclic_unaliased_impl_uniq_path in Hp2; eauto.
      apply Hp2 in Hp1.
      rewrite !app_comm_cons in Hp1.
      apply app_inv_tail in Hp1.
      apply diff_last_app_middle in Hdiff.
      rewrite Hp1 in Hdiff.
      eapply diff_last_irrefl; last done. done. }
    (* There is a loop. *)
    { apply elem_of_middle in Hx,Hx'.
      destruct Hx as (l1&l2&->).
      destruct Hx' as (l1'&l2'&->).
      rewrite -assoc_L in Hp2.
      apply path_app_inv in Hp2.
      destruct Hp2 as (?&_&Hp2).
      rewrite assoc_L  in Hp2.
      apply path_app_inv in Hp2.
      destruct Hp2 as (?&Hp2&Hp2').
      assert (x0 = proj1 x) as ->.
      { inversion Hp2. subst. done. }
      assert (x1 = proj1 x) as ->.
      { inversion Hp2'. subst. done. }
      rewrite -app_comm_cons in Hp2.
      eapply Hacy in Hp2. congruence. }
  Qed.

  Lemma path_use_diff_last_subseteq
    g (a1 a2 : location) (ys1 ys2 xs : list (location * diff * location)) (r : location) :
    acyclic g ->
    unaliased g ->
    path g a1 (ys1 ++ xs) r ->
    path g a2 (ys2 ++ xs) r ->
    diff_last ys1 ys2 ->
    list_to_set ys2 ⊆ g ∖ list_to_set (ys1 ++ xs).
  Proof.
    intros.
    apply subseteq_difference_r.
    - intros el Hel1 Hel2.
      rewrite elem_of_list_to_set in Hel1.
      rewrite elem_of_list_to_set in Hel2.
      eapply (path_use_diff_last g a1 a2); eauto.
    -
      destruct (path_middle g a2 ys2 xs r ltac:(subst; auto))
        as (mid & Hmid1 & Hmid2).
      eapply path_all_in; eauto.
  Qed.

  Lemma diff_last_comm {A:Type} (l1 l2:list A) :
    diff_last l1 l2 <-> diff_last l2 l1.
  Proof.
    unfold diff_last.
    destruct (last l1),(last l2); naive_solver.
  Qed.

  Lemma path_union_inv (g1: graph location (location*val)) g2 a1 xs a2 :
    path (g1 ∪ g2) a1 xs a2 ->
    path g1 a1 xs a2 \/ exists a' x xs1 xs2, path g1 a1 xs1 a' /\ x ∈ g2 /\ path (g1 ∪ g2) a' (x::xs2) a2 /\ xs=xs1++x::xs2.
  Proof.
    induction 1.
    - left. eauto using path_nil.
    - destruct IHpath as [|(x&?&?&?&?&?&?&->)].
    { destruct_decide (decide ((a1,b,a2) ∈ g1)).
      { left. apply path_cons; eauto. }
      { right. exists a1,(a1,b,a2),nil. eexists. split_and !.
        - apply path_nil.
        - set_solver.
        - apply path_cons; eauto.
        - done.
    } }
    { right.
      destruct_decide (decide ((a1,b,a2) ∈ g1)).
      { eexists _,_,_,_. split_and !;eauto.
        2:{ rewrite app_comm_cons. reflexivity. }
        apply path_cons; eauto. }
      eexists a1, (a1, b, a2),_,_.
      split_and !.
      - apply path_nil.
      - set_solver.
      - apply path_cons; last done. set_solver.
      - reflexivity.
    }
  Qed.

  Lemma path_cannot_escape (x:(location * diff * location)) (xs ys:list (location * diff * location)) (g1: graph location (location*val)) a a' r :
    no_succ (g1 ∪ list_to_set ys) r ->
    unaliased (g1 ∪ list_to_set ys) ->
    x ∈ (list_to_set ys : gset _) ->
    pathlike ys r ->
    path (g1 ∪ list_to_set ys) a (x :: xs) a' ->
    path (list_to_set ys) a (x::xs) a'.
  Proof.
    intros ? X1 X2 X3. remember (x::xs) as zs.
    revert a a' x xs Heqzs X1 X2 X3.
    induction zs; intros a0 a' x xs Heqzs X1 X2 X3; first congruence.
    inversion 1. subst. inversion Heqzs. subst. apply path_cons; first eauto.
    destruct xs as [|((?,?),?)].
    { inversion H6. subst. eauto using path_nil. }
    eapply IHzs; eauto. inversion H6. subst.
    apply elem_of_list_to_set in X2. apply X3 in X2.
    { destruct X2 as [|(?&?&?)].
    - subst. contradiction H with l0. eexists. eauto.
    - assert ((l, x, x0) ∈  g1 ∪ list_to_set ys) as Z by set_solver.
      destruct (X1 _ _ _ _ _ H9 Z). subst. set_solver.
    }
  Qed.

  Lemma path_in_seg_complete (r a a':location) (x:(location * diff * location)) (xs0 xs1 ys: list (location * diff * location)) (g1:graph location (location*val)) :
    no_succ (g1 ∪ list_to_set ys) r ->
    unaliased (g1 ∪ list_to_set ys) ->
    pathlike ys r ->
    path (g1 ∪ list_to_set ys) a xs0 a' ->
    path (list_to_set ys) a' (x :: xs1) a ->
    exists zs, path (list_to_set ys) a zs a'.
  Proof.
    intros Hroot Hinj Hclosed Hp1 Hp2.
    inversion Hp1; subst.
    { exists nil. apply path_nil. }
    eapply path_cannot_escape in Hp1; eauto.
    apply path_inv_r in Hp2.
    destruct Hp2 as [|(?&?&?&Heq&Hp2&Hys)].
    { exfalso. destruct xs1; naive_solver. }
    apply elem_of_list_to_set in Hys.
    apply Hclosed in Hys. destruct Hys as [->|(?&?&Hys)].
    { contradiction Hroot with a2. eexists. eauto. }
    assert ((a, x3, x4) ∈  g1 ∪ list_to_set ys) as Z; first set_solver.
    destruct (Hinj _ _ _ _ _ H Z). set_solver.
  Qed.

  Lemma undo_preserves_rooted_dag (g:graph location (location*val)) xs ys rs r :
    no_succ (undo_graph g xs ys) rs ->
    unaliased g ->
    unaliased (list_to_set ys ∪ g ∖ list_to_set xs) ->
    path g rs xs r ->
    mirror xs ys ->
    rooted_dag g r ->
    rooted_dag (undo_graph g xs ys) rs.
  Proof.
    intros Hnr Hinj Hinj' Hpath Hmirror Hroot. inversion Hroot as [X1 X2].
    assert (vertices (undo_graph g xs ys) = vertices g) as Hvg.
    { apply mirror_vertices in Hmirror.
      rewrite vertices_union Hmirror -vertices_union -union_difference_L //.
      eauto using path_all_in. }

    constructor.
    { intros a. rewrite Hvg => Ha.
      apply X1 in Ha. destruct Ha as (zs&Ha).
      edestruct (path_extract_suffix g a rs) as (ys1&ys2&us&?&?&Hlast); eauto. subst.

      apply path_middle in Ha. destruct Ha as (y&Hy1&Hy2).
      apply path_middle in Hpath. destruct Hpath as (y'&Hy'1&Hy'2).
      assert (y'=y) as ->.
      { inversion Hy'2; subst; inversion Hy2; naive_solver. }
      eapply use_mirror_subset in Hmirror. 3:apply Hy'1. 2:set_solver.
      destruct Hmirror as (zs&Hzs&_).
      exists (ys1++zs). eapply path_app.
      2:{ eapply path_weak; first done. set_solver. }
      clear X2. induction Hy1.
      { apply path_nil. }
      apply path_cons.
      { rewrite elem_of_union elem_of_difference. right. split; first set_solver.
        apply not_elem_of_list_to_set.
        eapply path_use_diff_last. 1,2: eauto using ti2.
        3:{ apply diff_last_comm. done. }
        { eapply path_app; eauto. }
        { rewrite -app_comm_cons. eapply path_cons; first done.
          eapply path_app; eauto. }
        { set_solver. } }
      { apply IHHy1; eauto.  unfold diff_last in *. rewrite last_cons in Hlast.
        destruct (last bs), (last ys2); try done. } }
    { unfold undo_graph. intros a zs Hzs. rewrite comm_L in Hzs.
      apply path_union_inv in Hzs. destruct Hzs as [Hsz|Hsz].
      (* The cycle is only in g, easy. *)
      { eapply X2. eapply path_weak; first done. set_solver. }
      (* There is at least a vertex in ys.
         We are going to construct a cycle in ys, implying a cycle in xs. *)
      exfalso. destruct Hsz as (a'&x&l1&l2&E1&Hx&E2&->).

      apply path_cannot_escape with (r:=rs) in E2; last first.
      { eapply path_pathlike. eapply use_mirror; eauto. }
      { done. }
      { rewrite comm_L //. }
      { rewrite comm_L //. }

      apply path_weak with (g2 := g ∖ list_to_set xs ∪ list_to_set ys) in E1; last set_solver.
      eapply path_in_seg_complete with (r:=rs) in E1; last first; first done.
      { eapply path_pathlike. eapply use_mirror; eauto. }
      { rewrite comm_L //. }
      { rewrite comm_L //. }
      destruct E1 as (?&E1).

      assert (path (list_to_set ys) a (x0 ++ x::l2) a ) as Hcycle.
      { eapply path_app; done. }

      eapply use_mirror_subset with (ys:=xs) in Hcycle.
      3:{ by apply mirror_symm. }
      2:{ apply path_all_in in Hcycle. set_solver. }
      destruct Hcycle as (?&Hcycle&F).
      eapply path_weak in Hcycle. 2:eapply path_all_in; done.
      eapply ti2 in Hcycle; eauto. subst. destruct x0; simpl in *; lia. }
  Qed.

  Lemma undo_app_inv xs ys1 ys2 σ :
    undo xs (ys1 ++ ys2) σ ->
    exists xs1 xs2, xs = xs2 ++ xs1 /\ undo xs2 ys2 (apply_diffl (proj2 <$> xs1) σ) /\ undo xs1 ys1 σ.
  Proof.
    revert xs ys2 σ. induction ys1; intros xs ys2 σ Hundo.
    { exists nil,xs. rewrite right_id_L. split; eauto using undo_nil. }
    rewrite -app_comm_cons in Hundo. inversion Hundo. subst.
    apply IHys1 in H4. destruct H4 as (xs1&xs2&->&?&?).
    eexists _,xs2. split_and !.
    { rewrite -assoc_L //. }
    { rewrite fmap_app apply_diffl_app. done. }
    { apply undo_cons; done. }
  Qed.

  Lemma construct_middlepoint (g:graph location (location*val)) a1 xs ys a2 a2' :
    unaliased g ->
    no_succ g a2 ->
    path g a1 xs a2 ->
    path g a1 ys a2' ->
    exists zs, xs = ys ++ zs.
  Proof.
    intros Hinj Hroot Hpath. revert ys. induction Hpath; intros ys.
    { intros Hpath. inversion Hpath; eauto. subst. contradiction Hroot with a2. eexists. eauto. }
    { intros X. inversion X; subst.
      { exists ((a2', b, a2) :: bs ). done. }
      destruct (Hinj _ _ _ _ _ H H0). subst.
      apply IHHpath in H1; last eauto. destruct H1 as (?&?).
      eexists. rewrite -app_comm_cons H1 //.
    }
  Qed.

  Lemma undo_preserves_model g (M:map_model) (xs ys:list (location* (location*val)*location)) rs σ0 r:
    dom M = vertices g ∪ {[r]} ->
    correct_path_diff M g ->
    no_succ (undo_graph g xs ys) rs ->
    unaliased (undo_graph g xs ys) ->
    path g rs xs r ->
    undo xs ys σ0 ->
    M !! r = Some σ0 ->
    correct_path_diff M (undo_graph g xs ys).
  Proof.
    intros Hdom Hinv Hroot Hinj' Hrs Hundo E0.
    unfold undo_graph.
    intros r1 zs r2 σ1 σ2 Hpath E1 E2. rewrite comm_L in Hpath.
    apply path_union_inv in Hpath. destruct Hpath as [Hpath|Hpath].

    (* If the path is entirely in g, easy. *)
    { eapply Hinv; eauto. eapply path_weak; first done. set_solver. }

    assert (mirror xs ys) as Hmirror by eauto using undo_mirror.

    destruct Hpath as (a'&x&l1&l2&X1&Hx&X2&Hzs).
    eapply path_cannot_escape with (r:=rs) in X2; eauto; last first.
    { eapply path_pathlike. eapply use_mirror; eauto. }
    { replace (g ∖ list_to_set xs ∪ list_to_set ys)
                with (undo_graph g xs ys) by set_solver.
      assumption. }
    { rewrite comm_L //. }

    (* otherwise the path includes a part in g, and a part in ys. *)

    assert (vertices (undo_graph g xs ys) = vertices g) as Hvg.
    { apply mirror_vertices in Hmirror.
      rewrite vertices_union Hmirror -vertices_union -union_difference_L //.
      eauto using path_all_in. }

    assert (a' ∈ dom M) as Ha'.
    { rewrite Hdom -Hvg elem_of_union. left. apply elem_of_vertices.
      inversion X2. set_solver. }
    apply elem_of_dom in Ha'. destruct Ha' as (σ',Ea').
    assert (σ1 = (apply_diffl (proj2 <$> l1) σ')).
    { eapply path_weak in X1.
    - eapply (Hinv _ _ _ _ _ X1 E1 Ea').
    - set_solver.
    }

    (* The part in g is preserved. *)
    etrans; first done. rewrite Hzs. rewrite fmap_app apply_diffl_app.
    f_equal. clear dependent σ1 l1.

    (* XXX facto a lemma. *)
    assert (exists u1 u2, ys = u1 ++ (x::l2) ++ u2) as (u1&u2&Hys).
    { eapply use_mirror in Hrs. 2:done.
      apply elem_of_list_to_set, elem_of_middle in Hx.
      destruct Hx as (p1&p2&->).
      apply path_app_inv in Hrs. destruct Hrs as (?&Hp1&Hp2).
      inversion Hp2; inversion X2. subst. inversion H5. subst.
      eapply construct_middlepoint in H10. 4:apply H4.
      2:{ unfold undo_graph in *.
          intros z1 z2 z3 z4 z5 ??. eapply (Hinj' z1 z2 z3 z4 z5); try done.
          all:rewrite elem_of_union elem_of_difference; left; set_solver.
      }
      2:{ intros k (d, Hk). eapply (Hroot k).
          exists d.
          rewrite elem_of_union. left. set_solver. }
      destruct H10.
      eexists _,_. f_equal. rewrite -app_comm_cons. f_equal. done. }

    rewrite Hys assoc_L in Hundo. apply undo_app_inv in Hundo.
    destruct Hundo as (xs1&xs2&->&Hundo1&Hundo2).
    apply undo_app_inv in Hundo2.
    destruct Hundo2 as (xs4&xs3&->&Hundo2&Hundo3).

    eapply use_mirror in Hmirror. 2:done.
    rewrite {2}Hys in Hmirror.
    apply path_app_inv in Hmirror. destruct Hmirror as (n1&T1&T2).
    apply path_app_inv in T2. destruct T2 as (n2&T2&T3).
    edestruct (same_path (list_to_set ys) (x::l2) n1 n2 a') as (?&?); try done.
    subst n1 n2.

    assert (path g a' xs4 r) as R1.
    { eapply path_weak.
    - eapply use_mirror; last done. eapply mirror_symm. eauto using undo_mirror.
    - apply path_all_in in Hrs. set_solver. }
    apply (Hinv _ _ _ σ' σ0) in R1; try done.

    assert (path g r2 xs3 a') as R2.
    { eapply path_weak.
    - eapply use_mirror; last done. eapply mirror_symm. eauto using undo_mirror.
    - apply path_all_in in Hrs. set_solver. }
    eapply (Hinv _ _ _ σ2 σ') in R2; try done.
    rewrite R2. rewrite -apply_diffl_app -fmap_app.
    eapply use_undo. rewrite R1. done.
  Qed.

  Lemma undo_graph_edges g a xs b ys :
    path g a xs b ->
    mirror xs ys ->
    forall k l,
    has_edge (undo_graph g xs ys) k l ->
    has_edge (g ∖ list_to_set xs) k l
    \/
    has_edge (list_to_set xs) l k
  .
  Proof.
   intros Hpath Hmirror k l (d, Hkl).
   rewrite elem_of_union in Hkl.
   { destruct Hkl as [Hkl | Hkl]; first last.
   - left. eexists; eauto.
   - right.
     revert a b Hpath.
     { induction Hmirror; intros a b Hpath.
     - set_solver.
     - rewrite -> list_to_set_cons in Hkl.
       rewrite elem_of_union in Hkl.
       { destruct Hkl as [ Hkl | Hkl ].
       - eexists.
         rewrite list_to_set_app.
         rewrite elem_of_union.
         rewrite list_to_set_singleton.
         right.
         rewrite elem_of_singleton.
         rewrite elem_of_singleton in Hkl.
         injection Hkl; intros; subst.
         reflexivity.
       - { destruct IHHmirror with a r as (d' & Hd').
           - assumption.
           - destruct (path_middle g a xs [(r, x, r')] b Hpath) as (b' & Hpath1 & Hpath2).
             inversion Hpath2; subst.
             assumption.
           - exists d'; eauto.
             rewrite list_to_set_app.
             set_solver.
         }
       }
     }
   }
  Qed.

  Lemma into_a_path g rs xs r :
    unaliased g ->
    path g rs xs r ->
    forall k1 d1 k d2 k2,
    edge (g ∖ list_to_set xs) k1 d1 k ->
    edge (list_to_set xs) k d2 k2 ->
    k = rs \/ (exists k1' d1', k1 ≠ k1' /\ edge (list_to_set xs) k1' d1' k)
  .
  Proof.
    { revert rs. induction xs; intro rs.
    - set_solver.
    - rewrite list_to_set_cons.
      unfold edge.
      intros Hunaliased Hpath k1 d1 k d2 k2 H1 H2.
      rewrite -> elem_of_difference in H1.
      rewrite -> elem_of_union in H1.
      rewrite -> elem_of_singleton in H1.
      rewrite -> elem_of_union in H2.
      rewrite -> elem_of_singleton in H2.
      destruct H1 as (H1g, H1xs).
      { destruct H2 as [ H2a | H2xs ].
      - inversion Hpath; subst.
        injection H; auto.
      - inversion Hpath; subst.
        { destruct (IHxs a2 Hunaliased H4 k1 d1 k d2 k2); eauto.
        - unfold edge. rewrite -> elem_of_difference.
          constructor; first assumption.
          intro hyp. apply H1xs. right. assumption.
        - replace a2 with k in *.
          right. exists rs, b.
          { constructor.
          - intro Heq. apply H1xs. left.
            subst. destruct (Hunaliased rs d1 k b k); auto.
            subst. reflexivity.
          - set_solver. }
        - right.
          set_solver.
        }
      }
    }
  Qed.

  Lemma into_a_path_captured g C M rs xs r :
    dom M = vertices g ∪ {[r]} ->
    topology_inv g M C r ->
    unaliased g ->
    captured C rs ->
    path g rs xs r ->
    forall k1 d1 k d2 k2,
    edge (g ∖ list_to_set xs) k1 d1 k ->
    edge (list_to_set xs) k d2 k2 ->
    not (not (captured C k))
  .
    intros Hdom Htopo Hunaliased Hcap Hpath k1 d1 k d2 k2 Hk1 Hk2 Hk_cap.
    { destruct (into_a_path g rs xs r Hunaliased Hpath k1 d1 k d2 k2) as [ Hend | Hmid ]; eauto.
    - subst. exact (Hk_cap Hcap).
    - destruct Hmid as (k1' & d1' & Hneq & Hedge).
      assert (k ∈ dom M).
      { rewrite Hdom.
        rewrite elem_of_union.
        left.
        apply right_vertex with k1 d1.
        set_solver. }
      destruct (Htopo k) as (_ & H_at_most_one); eauto.
      contradiction Hneq.
      { apply H_at_most_one.
        - exists d1. set_solver.
        - exists d1'.
          assert (list_to_set xs ⊆ g) by (eapply path_all_in; eauto).
          set_solver.
      }
    }
  Qed.

  Lemma undo_preserves_topo g M C (xs ys:list (location* (location*val)*location)) r rs :
    dom M = vertices g ∪ {[r]} ->
    unaliased g ->
    captured C rs ->
    path g rs xs r ->
    mirror xs ys ->
    topology_inv g M C r ->
    topology_inv (undo_graph g xs ys) M C rs.
  Proof.
    intros Hdom Hunaliased Hrs_cap Hpath Hmirror Htopo.
    intros k Hk_dom Hk_cap.
    { constructor.
    - intro; subst. contradiction.
    - intros k1 k2 Hk1 Hk2.
      { destruct (undo_graph_edges g rs xs r ys Hpath Hmirror _ _ Hk1) as [ (d1, Hk1') | (d1, Hk1') ];
          destruct (undo_graph_edges g rs xs r ys Hpath Hmirror _ _ Hk2) as [ (d2, Hk2') | (d2, Hk2') ];
            clear Hk1 Hk2.
      - { apply (Htopo k); auto.
        - exists d1. set_solver.
        - exists d2. set_solver.
        }
      - { destruct into_a_path_captured with g C M rs xs r k1 d1 k d2 k2; eauto. }
      - { destruct into_a_path_captured with g C M rs xs r k2 d2 k d1 k1; eauto. }
      - { eapply Hunaliased; eauto.
          - apply (path_all_in g rs xs r Hpath); eauto.
          - apply (path_all_in g rs xs r Hpath); eauto.
        }
      }
    }
  Qed.

  Lemma undo_preserves_outside_path g r xs rs ys a zs b :
    path g rs xs r ->
    path g a zs b ->
    mirror xs ys ->
    list_to_set zs ⊆ g ∖ list_to_set xs ->
    path (undo_graph g xs ys) a zs b.
  Proof.
    intros Hxs Hzs Hxsys Hincl.
    apply path_weak with (list_to_set zs); eauto.
    - apply path_restrict with g; eauto.
    - unfold undo_graph.
      intros elem Helem.
      rewrite elem_of_union. right.
      apply Hincl; done.
  Qed.

  Lemma undo_preserves_histo g1 r1 h1 orig r2 xs xsm :
    acyclic g1 ->
    unaliased g1 ->
    history_inv g1 r1 h1 orig ->
    path g1 r2 xs r1 ->
    mirror xs xsm ->
    exists h2,
      graph_iso h1 h2
      /\
      history_inv (undo_graph g1 xs xsm) r2 h2 orig.
  Proof.
    intros Hacyclic Hunalias (ys & ysm & Hys & Hysysm & Hhisto) Hxs Hxsxsm.
    unfold history_inv.
    set g2 := undo_graph g1 xs xsm.
    assert (h1 = undo_graph g1 ys ysm) as Hhisto_strict.
    { apply leibniz_equiv; done. }
    assert (path g2 r1 xsm r2) as Hxsm by (eapply undo_path; eauto).
    assert (path h1 r1 ysm orig) as Hysm by (subst h1; eapply undo_path; eauto).
    destruct
      (path_extract_suffix g1 r2 orig xs r1 ys Hunalias Hxs Hys)
      as (xs' & ys' & suf & Hxs' & Hys' & Hdiff).
    destruct (path_middle g1 r2 xs' suf r1 ltac:(subst; auto))
      as (xmid & Hxmid1 & Hxmid2).
    destruct (path_middle g1 orig ys' suf r1 ltac:(subst; auto))
      as (ymid & Hymid1 & Hymid2).
    assert (xmid = ymid) as Hmid; [ | subst ymid ].
    {
      destruct_decide (decide (suf = [])).
      - subst suf.
        inversion Hxmid2; inversion Hymid2; subst; done.
      - destruct (same_path g1 suf _ _ _ _ Hxmid2 Hymid2 ltac:(assumption)); done.
    }
    assert (mirror ysm (ys' ++ suf)) as Htemp1 by (subst; apply mirror_symm; done).
    assert (mirror xsm (xs' ++ suf)) as Htemp2 by (subst; apply mirror_symm; done).
    destruct (mirror_app_inv_in_graph g1 orig ys' xmid suf r1 ysm)
      as (ys'm & sufm & Dysm & Mys' & Msuf & Psufm & Pys'm); eauto; [].
    destruct (mirror_app_inv_in_graph g1 r2 xs' xmid suf r1 xsm)
      as (xs'm & sufm' & Dysm' & Mxs' & Msuf' & Psufm' & Pxs'm); eauto; [].

    (* A bunch of facts that help [set_solver] with the proofs below. *)
    assert (list_to_set ys' ⊆ g1) by (eauto using path_all_in).
    assert (list_to_set xs' ⊆ g1) by (eauto using path_all_in).
    assert (list_to_set suf ⊆ g1) by (eauto using path_all_in).

    assert (ys' ## (xs' ++ suf)) as Hdiffxs'ys'.
    { pose proof path_use_diff_last. set_solver. }
    assert (xs' ## (ys' ++ suf)) as Hdiffys'xs'.
    { subst. rewrite diff_last_comm in Hdiff.
      pose proof path_use_diff_last. set_solver. }

    assert (xs' ## ys') by set_solver.
    assert (xs' ## suf) by set_solver.
    assert (suf ## ys') by set_solver.

    assert (sufm ## ys'm).
    { subst.
      apply mirror_app_inv in Htemp1. destruct Htemp1 as (a1&a2&M1&M2&Eq).
      apply app_inj_1 in Eq.
      2:{ apply mirror_same_length in M2,Msuf. lia. }
      destruct Eq. subst a1 a2. apply mirror_symm in M1,M2.
      eapply mirror_preserves_disjoint; try done. }

    assert (sufm ## xs') by TODO admit.
    assert (xs'm ## sufm') by TODO admit.
    assert (xs'm ## ys') by TODO admit.
    assert (ys' ## sufm') by TODO admit.
    assert (ys' ## xs'm) by TODO admit.

(* behold a marvelous ASCII art diagram:

  ys = ys' ++ suf
  ysm = sufm ++ ys'm
  xs = xs' ++ suf
  xsm = sufm' ++ xs'm

        g1:               h1 = undo g1 ys ysm
        orig               orig
         | ys'              ↑ ys'm
         v                  |
       -> \ suf           -> <-
  xs' /    > r1      xs' /     \ sufm
     r2                r2       r1

   g2 = undo g1 xs xsm           h2 = undo g2 (ys' ++ xs'm) (xs' ++ ys'm)
                                    = undo h1 sufm sufm'  (note: sufm, sufm' are not mirrors)
        orig                         orig
          |ys'                         ↑ ys'm
          v                            |
    xs'm / <-                        -> <-
     r2 <    \ sufm'          xs'   /    \ sufm'
              r1                  r2     r1
*)
    set h2 := undo_graph h1 sufm sufm'.

    (* show the *D*ecompositions that can be read from the diagram *)
    set grest := g1 ∖ (list_to_set ys' ∪ list_to_set suf ∪ list_to_set xs').

    assert (list_to_set sufm ## grest) by TODO admit.
    assert (list_to_set xs'm ## grest) by TODO admit.
    assert (list_to_set ys' ## grest) by TODO admit.

    assert (g1 = grest ∪ (list_to_set ys' ∪ list_to_set suf ∪ list_to_set xs')) as Dg1.
    {
      apply leibniz_equiv.
      subst grest. rewrite difference_union. set_solver.
    }
    assert (h1 = grest ∪ (list_to_set ys'm ∪ list_to_set sufm ∪ list_to_set xs')) as Dh1 by set_solver.
    assert (g2 = grest ∪ (list_to_set ys' ∪ list_to_set sufm' ∪ list_to_set xs'm)) as Dg2 by set_solver.
    assert (h2 = grest ∪ (list_to_set ys'm ∪ list_to_set sufm' ∪ list_to_set xs')) as Dh2.
    {
      subst h2.
      rewrite Dh1.
      set_solver.
    }
    assert (graph_iso h1 h2) as Hiso2.
    {
      unfold h2.
      assert (graph_iso (list_to_set sufm) (list_to_set sufm'))
        as Hsufmiso
        by (eapply mirror_mirror; eauto).
      apply undo_iso; eauto; [].
      enough (list_to_set ysm ⊆ h1) by set_solver.
      apply path_all_in with r1 orig; eauto.
    }
    exists h2.
    constructor; eauto; [].
    set zs := ys' ++ xs'm.
    set zsm := xs' ++ ys'm.
    exists zs, zsm.
    { split_and!.
    - { apply path_app with xmid.
      - unfold g2.
        eapply undo_preserves_outside_path; eauto.
        subst xs ys. eapply path_use_diff_last_subseteq; eauto.
      - unfold g2. subst xs. done.
      }
    - apply mirror_app; eauto.
      apply mirror_symm; eauto.
    - rewrite Dh2.
      rewrite Dg2.
      unfold undo_graph.
      subst zs zsm.
      repeat rewrite list_to_set_app.
      replace
        ((grest ∪ (list_to_set ys' ∪ list_to_set sufm' ∪ list_to_set xs'm))
         ∖ (list_to_set ys' ∪ list_to_set xs'm))
      with
        ((grest ∪ list_to_set sufm')
         ∖ (list_to_set ys' ∪ list_to_set xs'm))
      by set_solver.
      replace
        ((grest ∪ list_to_set sufm')
         ∖ (list_to_set ys' ∪ list_to_set xs'm))
      with
        (grest ∖ (list_to_set ys' ∪ list_to_set xs'm)
         ∪ list_to_set sufm')
      by set_solver.
      replace
        (grest ∖ (list_to_set ys' ∪ list_to_set xs'm))
      with
        grest
      by set_solver.
      set_solver.
    }
  Admitted.

  Lemma use_snapshots γ (t0:location) M C G r σ gen :
    meta t0 nroot γ -∗
    snapshots t0 M C G -∗
    pstore_map_elem γ r σ gen -∗
    ⌜(r, σ, gen) ∈ C /\ snapshot_inv M C G r σ gen⌝.
  Proof.
    iIntros "Hmeta [%γ' (%Hsnap&Hmeta'&HC)] Helem".
    iDestruct (meta_agree with "Hmeta' Hmeta") as "->".
    iDestruct (mono_set_elem_valid with "[$][$]") as "%Hrs".

    iPureIntro.
    destruct Hsnap with r σ gen as (σ', (H1 & H2 & H3)); [ auto | ].
    unfold captured.
    eexists; eauto.
  Qed.

  Lemma pstore_restore_spec t σ s σ' :
    {{{
      pstore t σ ∗
      pstore_snapshot t s σ'
    }}}
      pstore_restore t s
    {{{
      RET ();
      pstore t σ'
    }}}.
  Proof.
    iIntros (Φ) "(HI&Hsnap) HΦ".
    iDestruct "HI" as open_inv.

    iDestruct "Hsnap" as "[%γ [%t0' [%rs [%snap_gen ((%Eq&->)&Hmeta'&Hsnap)]]]]".
    inversion Eq. subst t0'. clear Eq.

    iDestruct (use_snapshots with "[$][$][$]") as %(HC & σ1 & HMrs &Hincl & Hsnapgen).

    wp_rec. iStep 20.

    iDestruct (extract_unaliased with "Hg") as "%".
    destruct_decide (decide (rs=r)).
    { subst.
      wp_load. iStep 4. iModIntro.
      iExists _,_,_,_,_,_,_,_,_,_. iFrame. iPureIntro. split_and!; eauto.
      { destruct Hinv as [X1 X2 X3 X4]. constructor; eauto. naive_solver. } }

    assert (rs ∈ vertices g) as Hrs.
    { destruct Hinv. apply elem_of_dom_2 in HMrs. set_solver. }

    eapply ti1 in Hrs; eauto. destruct Hrs as (ds,Hrs).
    inversion Hrs; first congruence. subst. rename a2 into r'. destruct b.
    iDestruct (big_sepS_elem_of_acc with "[$]") as "(?&Hg)"; first done. simpl.
    wp_load. iStep 2. iModIntro.
    iSpecialize ("Hg" with "[$]").

    remember ((rs, (l, v), r') :: bs) as xs.
    assert (list_to_set xs ⊆ g).
    { eauto using path_all_in. }

    rewrite (union_difference_L (list_to_set xs) g) //.

    iDestruct (big_sepS_union with "Hg") as "(Hxs&Hg)"; first set_solver.
    wp_apply (pstore_reroot_spec with "[Hr Hxs Hσ0]").
    4:{ eapply path_restrict. done. }
    2:done.
    { destruct Hcoh as [_ X]. eapply locations_of_edges_weak; eauto. }
    { eapply acyclic_weak; eauto using ti2. }
    { iFrame. }

    iIntros "[%ys (%Hundo&?&?&?)]".
    assert (mirror xs ys) as Hmirror by eauto using undo_mirror.
    wp_store. wp_store. iStep. iModIntro.
    iDestruct (big_sepS_union_2 with "[$][$]") as "Hs".

    iDestruct (extract_unaliased with "Hs") as "%".

    assert (({[(rs, (l, v), r')]} ∪ list_to_set bs) = (list_to_set xs : gset _)) as Hbs.
    { subst xs. reflexivity. }

    set g' : graph_store := undo_graph g xs ys.

    iAssert ⌜forall x y, (rs,x,y) ∉ g'⌝%I as "%".
    { iIntros (???). destruct a. iDestruct (big_sepS_elem_of with "Hs") as "?"; first done.
      iDestruct (pointsto_ne rs rs with "[$][$]") as "%". congruence. }

    assert (exists h', graph_iso h h' /\ history_inv g' rs h' orig) as (h' & Hiso & Hist').
    {
      destruct Hgraph.
      unfold g'.
      eapply undo_preserves_histo; eauto.
    }

    assert (vertices g' = vertices g) as Hvg.
    { apply mirror_vertices in Hmirror.
      rewrite vertices_union Hmirror -vertices_union -union_difference_L //. }

    assert (σ1 = (apply_diffl (proj2 <$> xs) σ0)).
    { destruct Hinv as [X1 X2 X3 X4]. eauto. }

    assert (rooted_dag g' rs) as Hroot.
    { eapply undo_preserves_rooted_dag; eauto.
    - intros k (d, Hk).
      apply (H5 d k).
      assumption.
    }

    iExists t0,rs,orig,(1 + snap_gen),_,g',h',M,_,_. iFrame.
    iSplitR. 2: iSteps. 1: iPureIntro; split_and!; try done.

    { (* store_inv *)
      destruct Hinv as [X1 X2 X3 X4 X5]. constructor.
      { rewrite X1 Hvg.
        apply elem_of_dom_2 in X4, HMrs.
        apply path_ends_vertices in Hrs.
        set_solver. }
      { set_solver. }
      { set_solver. }
      { set_solver. }
      { intros. eapply undo_preserves_model; eauto.
        intros k (d, Hk). apply (H5 d k). eauto. }
    }

    { (* topology_inv *)
      apply undo_preserves_topo with r; eauto.
      - { destruct Hinv; eauto. }
      - unfold captured; eexists _, _; eapply HC.
    }

    { (* coherent *)
      destruct Hcoh as [X1 X2]. constructor.
      { intros ???. rewrite dom_apply_diffl. apply X1 in H7.
        eapply use_locations_of_edges_in in Hrs. 2:done.
        set_solver.
      } {
        rewrite dom_apply_diffl. intros ???? Hedge.
        rewrite /edge elem_of_union in Hedge. rewrite elem_of_union.
        destruct Hedge as [Hedge|Hedge].
        { right. eauto using undo_same_fst_label. }
        { left. eapply (X2 r0). eapply elem_of_subseteq. 2:done. set_solver. }
    } }

    { (* global_gen_inv *)
      constructor.
      - (* gen_succ_rel between two nodes (k, j) ∈ h *)
        intros k gk j Hedge Hgk.
        assert (has_edge h k j) by (destruct Hiso; eauto).
        destruct Hglobgen as (Hglobgen1 & _).
        apply (Hglobgen1 k gk j); eauto.
      - (* gen_succ_rel between the snapshot generation and the snapshot root. *)
        apply Hsnapgen.
    }
  Qed.
End pstore_G.

#[global] Opaque pstore_create.
#[global] Opaque pstore_ref.
#[global] Opaque pstore_get.
#[global] Opaque pstore_set.
#[global] Opaque pstore_capture.
#[global] Opaque pstore_restore.

#[global] Opaque pstore.
#[global] Opaque pstore_snapshot.
