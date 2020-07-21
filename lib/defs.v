(** Common definitions *)
From Coq Require Import Ensembles.
From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From Catincoq.lib Require Import proprel.

Definition partial_order {A} (R : relation A) := 1 ≦ R /\ R ⋅ R ≦ R /\ R ⊓ R° ≦ 1.

Definition strict_order {A} (R : relation A) := R ⋅ R ≦ R /\ R ⊓ 1 ≦ 0.

Definition is_strict_order {A} (R : relation A) :=
  relalg.is_irreflexive R /\
  is_transitive R.

Lemma is_strict_order_spec {A} (R : relation A) : is_strict_order R <-> strict_order R.
Proof.
  compute. firstorder.
Qed.

Definition is_irreflexive {X} (R : relation X) := R ⊓ 1 ≦ 0.

Definition irreflexive {A} (R : relation A) := cap R 1 ≦ bot.

Lemma is_irreflexive_spec1 {X} (R : relation X) : irreflexive R <-> is_irreflexive R.
Proof.
  reflexivity.
Qed.

Lemma is_irreflexive_spec2 {X} (R : relation X) : relalg.is_irreflexive R <-> is_irreflexive R.
Proof.
  compute. firstorder (subst; firstorder).
Qed.

Lemma is_irreflexive_spec3 {X} (R : relation X) : RelationClasses.Irreflexive R <-> is_irreflexive R.
Proof.
  compute. firstorder (subst; firstorder).
Qed.

Definition acyclic {A} (R : relation A) := leq (cap (itr _ R) 1) bot.

Definition is_acyclic {X} (R : relation X) := R^+ ⊓ 1 ≦ 0.

Lemma is_acyclic_spec {X} (R : relation X) : acyclic R <-> is_acyclic R.
Proof.
  split; intros A x y; specialize (A x y); rewrite A; compute; tauto.
Qed.

Definition total {A} (R : relation A) := !1 ≦ R ⊔ R°.

(** TODO merge those two *)
Definition total_on {A} (E : set A) (R : relation A) := [E] ⋅ !1 ⋅ [E] ≦ R ⊔ R°.

Definition linear_extension_on {A} (E : set A) (R : relation A) : set (relation A) :=
  fun S => strict_order S /\ S ≦ [E] ⋅ top ⋅ [E] /\ total_on E S /\ [E] ⋅ R ⋅ [E] ≦ S.

Definition finite_set {A} (E : set A) :=
  exists (l : list A), forall a, E a -> List.In a l.

Definition relational_image {A B} (R : A -> B -> Prop) : Ensemble A -> Ensemble B :=
  fun x b => exists a, x a /\ R a b.

Definition functional_relation_domain {A B} (dom : Ensemble A) (R : A -> B -> Prop) :=
  (forall a, dom a <-> exists b, R a b) /\
  (forall a b b', R a b -> R a b' -> b = b').

Definition one_of_each {X} : Ensemble (Ensemble X) -> Ensemble (Ensemble X) :=
  fun A b => exists f : Ensemble X -> X -> Prop,
      (forall e fe, f e fe -> e fe) /\
      functional_relation_domain A f /\
      Same_set _ b (relational_image f A).

Definition subset_image {A B} (f : A -> B) (X : Ensemble A) : Ensemble B
  := fun y => exists x, X x /\ y = f x.

Definition union_of_relations {A} : Ensemble (relation A) -> relation A :=
  fun Rs x y => exists R, Rs R /\ R x y.

Definition equivalence_classes {A} (R : relation A) : Ensemble (Ensemble A) :=
  fun C => exists x, C x /\ forall y, R x y <-> C y.
