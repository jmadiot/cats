From Coq Require Import Ensembles Relations.
From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From stdpp Require relations. (* no Import: notation conflict *)
From Catincoq.lib Require Import proprel defs Cat tactics antitransitive acyclic.

(* Equivalence between RelationAlgebra's and stdpp's definitions of
   transitive closure *)

Lemma itr_tc {X} (R : relation X) : R^+ ≡ relations.tc R.
Proof.
  rewrite itr_clos_trans, clos_trans__1n.
  intros x y; split; (induction 1; [ constructor 1 | econstructor 2 ]); eauto.
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
  - (* {y | x R+ y} is finite, of course *)
    destruct f as [l hl].
    exists l. intros y _.
    now apply base.elem_of_list_In.
Qed.
