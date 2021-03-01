From Coq Require Import Ensembles Relations.
From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From stdpp Require relations. (* no Import: notation conflict *)
From Catincoq.lib Require Import proprel defs Cat tactics acyclic.

(* Equivalence between the many definitions of transitive closure *)

Lemma itr_clos_trans {A} (r : relation A) : r^+ ≡ clos_trans _ r.
Proof.
  apply antisym.
  - apply itr_ind_l1.
    + compute; intuition.
    + intros x z [y xy yz]. apply t_trans with y; compute; intuition.
  - intros x z xz. induction xz.
    + now rel rewrite <-itr_ext.
    + rel rewrite <-itr_trans. exists y; eauto.
Qed.

Lemma clos_trans__n1 {A} (r : relation A) :
  clos_trans _ r ≡ clos_trans_n1 _ r.
Proof.
  intros x y; apply clos_trans_tn1_iff.
Qed.

Lemma clos_trans__1n {A} (r : relation A) :
  clos_trans _ r ≡ clos_trans_1n _ r.
Proof.
  intros x y; apply clos_trans_t1n_iff.
Qed.

Lemma clos_trans_1n_n1 {A} (r : relation A) :
  clos_trans_1n _ r ≡ clos_trans_n1 _ r.
Proof.
  now rewrite <-clos_trans__1n, clos_trans__n1.
Qed.

Lemma itr_tc {X} (R : relation X) : R^+ ≡ relations.tc R.
Proof.
  rewrite itr_clos_trans, clos_trans__1n.
  intros x y; split; (induction 1; [ constructor 1 | econstructor 2 ]); eauto.
Qed.

(* Facts about well foundedness *)

Instance wf_leq {A} : Proper (flip leq ==> impl) (@well_founded A).
Proof.
  intros r s i w x; revert x.
  apply (well_founded_induction w _); intros x IH.
  constructor. intros y yx. apply IH, i, yx.
Qed.

Instance wf_weq {A} : Proper (weq ==> iff) (@well_founded A).
Proof.
  intros r s e; split; apply wf_leq; auto; intros x y xy; apply e, xy.
Qed.

Lemma Acc_itr {A} (r : relation A) x : Acc r x -> Acc (clos_trans_n1 _ r) x.
Proof.
  intros a.
  induction a as [x ax IH].
  constructor; intros p px.
  destruct px as [x px | x y xy px]; auto.
  apply IH in xy.
  apply xy in px.
  exact px.
Qed.

Lemma wf_itr {A} (r : relation A) : well_founded r -> well_founded r^+.
Proof.
  intros wf.
  rewrite itr_clos_trans, clos_trans__n1.
  unfold well_founded.
  pose proof @Acc_itr; eauto.
Qed.

(* Wrapper for stdpp's tc_finite_sn lemma *)

Lemma finite_Type_acyclic_wf {X} (R : relation X) :
  finite X -> acyclic R -> well_founded R.
Proof.
  intros f a x.
  apply relations.tc_finite_sn.
  - (* Acyclic *)
    rewrite is_irreflexive_spec3, <-itr_tc.
    rewrite acyclic_cnv in a.
    unfold acyclic, is_irreflexive in *.
    compute in *; intuition.
  - (* {y | x R+ y} is finite, since X is finite *)
    destruct f as [l hl].
    exists l. intros y _.
    now apply base.elem_of_list_In.
Qed.
