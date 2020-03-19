(* Proof that a simplification of tso.cat is weaker than a simplification of sc.cat *)

From Coq Require Import String Ensembles.
From RelationAlgebra Require Import all.

From Catincoq Require Import Cat.
Require sc tso.

Instance acyclic_leq A: Proper (leq --> impl) (@acyclic A).
Proof.
  intros R S H. unfold acyclic. now rewrite H.
Qed.

Instance acyclic_weq A: Proper (weq --> iff) (@acyclic A).
Proof.
  intros R S H. split; apply acyclic_leq; compute in *; apply H.
Qed.

Open Scope cat_scope.

Notation " ⟦ x ⟧ " := (diagonal x) (at level 12) : cat_scope.

Lemma leq_diag_1 {A} (X : set A) : ⟦ X ⟧ ≦ 1.
Proof.
  compute; tauto.
Qed.

Lemma diag_empty {A} : ⟦ empty : set A ⟧ ≡ 0.
Proof.
  intros a b; split. compute.
  - intros [ [ ] <- ]; auto.
  - intros [].
Qed.

Lemma diag_union {A} (X Y : set A) : ⟦ Union _ X Y ⟧ ≡ ⟦ X ⟧ ⊔ ⟦ Y ⟧.
Proof.
  intros a b; split. compute.
  - intros [ [ | ] <- ]; auto.
  - intros [ [? <-] | [? <-] ].
    + repeat split; left; auto.
    + repeat split; right; auto.
Qed.

Lemma tso_is_weaker_than_sc c : is_transitive (po c) -> sc.valid c -> tso.valid c.
Proof.
  intros Hpo.
  unfold sc.valid, tso.valid.
  intros (co & Hco & SC). exists co. split. apply Hco. clear Hco.
  revert SC.

  destruct c as
      [events W R IW FW B RMW F po addr data ctrl rmw amo
              rf loc ext int unknown_set unknown_relation];
    repeat autounfold with * in *.

  intros sc.
  split.
  - (* sc => uniproc *)
    revert sc.
    apply acyclic_leq; unfold flip.
    lattice.
  - (* sc => tso *)
    revert sc.
    apply acyclic_leq. unfold flip.
    repeat rewrite diag_union.
    repeat rewrite diag_empty.
    repeat rewrite leq_diag_1.
    assert (Epo : po ⋅ po ≦ po) by lattice.
    ra_normalise.
    rewrite (Epo).
    lattice.
Qed.

