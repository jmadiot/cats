(** Common definitions *)
From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From Catincoq.lib Require Import proprel.

Definition partial_order {A} (R : relation A) := 1 ≦ R /\ R ⋅ R ≦ R /\ R ⊓ R° ≦ 1.

Definition strict_order {A} (R : relation A) := R ⋅ R ≦ R /\ R ⊓ 1 ≦ 0.

Definition is_strict_order {A} (R : relation A) :=
  relalg.is_irreflexive R /\
  is_transitive R.

Definition total_on {A} (E : set A) (R : relation A) := [E] ⋅ !1 ⋅ [E] ≦ R ⊔ R°.

Definition total {A} (R : relation A) := !1 ≦ R ⊔ R°.

Definition finite_set {A} (E : set A) :=
  exists (l : list A), forall a, E a -> List.In a l.

Lemma leq_tst_1 {X} (a : set X) : [a] ≦ (1 : relation X).
Proof.
  compute; intuition eauto.
Qed.

Lemma tst_cap_1 {X} (a : set X) : [a] ≡ [a] ⊓ (1 : relation X).
Proof.
  compute; intuition eauto.
Qed.
