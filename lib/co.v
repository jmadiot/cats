From Coq Require Import String Ensembles.
From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From Catincoq Require Import Cat proprel acyclic.
Open Scope string_scope.
Open Scope program_scope.

Definition strict_total_order_on {A}  (E : dpset A) (R : relation A) :=
  R ⊓ 1 ≦ 0 /\
  R ⋅ R ≦ R /\
  [E] ⋅ !1 ⋅ [E] ≡ R ⊔ R°.

Definition linearisations {A} (E : dpset A) (R : relation A) : Ensemble (relation A) :=
  fun S => strict_total_order_on E S /\ [E] ⋅ R ⋅ [E] ≦ S.

Section s.
  Variable A : Type.
  Variable loc : relation A.
  Definition classes_loc : set A -> Ensemble (Ensemble A) :=
    fun S Si => (forall x, Si x -> Ensemble_of_dpset S x) /\ forall x y, Si x -> Si y -> loc x y.
  Definition partition := classes_loc.
  Definition generate_orders s pco := cross (co_locs pco (partition s)).
End s.

Axiom generate_orders_spec : forall {A} (E : dpset A) (loc R S : relation A),
  generate_orders A loc E R S <->
  (S ≦ [E] ⋅ S ⋅ [E] /\
  S ⊓ 1 ≦ 0 /\
  S ⋅ S ≦ S /\
  S ≦ loc /\
  forall x y : A,
    loc x y ->
    proj1_sig (E x) ->
    proj1_sig (E y) ->
    (R x y -> S x y) /\ (x <> y -> S x y \/ S y x)).

Lemma generate_orders_bounds {A} (E : dpset A) (loc R S : relation A) :
  generate_orders A loc E R S -> S ≦ [E] ⋅ S ⋅ [E].
Proof.
  rewrite generate_orders_spec.
  tauto.
Qed.
