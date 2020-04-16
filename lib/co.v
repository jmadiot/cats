From Coq Require Import String Ensembles List Lia.
From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From Catincoq.lib Require Import Cat proprel tactics.

Definition is_strict_order {A} (R : relation A) :=
  is_irreflexive R /\
  is_transitive R.

(* if R is a partial strict order R, then S extends R, is a strict
   order, and is "total along" the equivalence relation ER *)
Definition extends_along {A} (R ER S : relation A) :=
  R ≦ S /\
  is_strict_order S /\
  ER ≡ S ⊔ S° ⊔ 1.

Definition equivalence_classes {A} (R : relation A) : Ensemble (Ensemble A) :=
  fun C => exists x, C x /\ forall y, R x y <-> C y.

Definition strict_total_order_on {A}  (E : dpset A) (R : relation A) :=
  is_strict_order R /\
  R ≦ [E]⋅top⋅[E] /\
  [E]⋅!1⋅[E] ≦ R ⊔ R°.

Definition linear_extension_on {A} (E : dpset A) (R S : relation A) :=
  R ≦ S /\
  strict_total_order_on E S.

(** [linearisations E R] is the set of strict total orders that
contain ([R] restricted to [E]). When [R] is not itself transitive, it
is possible that the result is different from [linearisations E (R^+)]
*)

Definition linearisations {A} (E : dpset A) (R : relation A) : Ensemble (relation A) :=
  fun S => strict_total_order_on E S /\ [E] ⋅ R ⋅ [E] ≦ S.

(** [partition equiv X] splits [X] into the set of sets [Xi] that are
each included in an equivalence class of the relation [equiv] *)

Definition partition {A} (equiv : relation A) (X : Ensemble A) : Ensemble (Ensemble A) :=
  fun Xi => (forall x, Xi x -> X x) /\ forall x y, Xi x -> Xi y -> equiv x y.

(* ---> wrong. The set is too big. *)

Section s.
  Variable A : Type.
  Variable loc : relation A.
  Definition generate_orders (s : dpset A) pco := cross (co_locs pco (partition loc (Ensemble_of_dpset s))).
End s.

Definition spec1 {A} (E : dpset A) (loc R S : relation A) :=
  S ≦ [E] ⋅ S ⋅ [E] /\
  S ⊓ 1 ≦ 0 /\
  S ⋅ S ≦ S /\
  S ≦ loc /\
  forall x y : A,
    loc x y ->
    proj1_sig (E x) ->
    proj1_sig (E y) ->
    (R x y -> S x y) /\ (x <> y -> S x y \/ S y x).

Lemma generate_orders_spec {A} (E : dpset A) (loc R S : relation A) :
  generate_orders A loc E R S <->
  spec1 E loc R S.

Proof.
  unfold generate_orders, cross.
  split.
  - intros (l & L & lS & RL & lL).
    split 5.
    + intros x y. rewrite lS. admit.
    + admit.
    + admit.
    + admit.
    + admit.
Admitted.

Lemma generate_orders_bounds {A} (E : dpset A) (loc R S : relation A) :
  generate_orders A loc E R S -> S ≦ [E] ⋅ S ⋅ [E].
Proof.
  rewrite generate_orders_spec. unfold spec1.
  tauto.
Qed.

Lemma generate_orders_spec_2 {A} (W : dpset A) (loc R S : relation A) :
  generate_orders A loc W R S <->
  extends_along R ([W] ⋅ loc ⋅ [W]) S.
Admitted.

Lemma spec1_spec2 {A} (E : dpset A) (loc R S : relation A) :
  spec1 E loc R S <-> extends_along R ([E]⋅loc⋅[E]) S.
Proof.
  split.
  - intros (Sdom & Sirr & St & Sloc & Stot). split 3.
    + destruct_rel. spec Stot x y. destruct Stot as [RS Stot]; auto.
      admit.
Admitted.

Lemma generate_cos_spec {A} (W IW FW : dpset A) (loc : relation A) :
  let co0 := loc ⊓ ([IW] ⋅ top ⋅ [(W ⊓ !IW)] ⊔ [(W ⊓ !FW)] ⋅ top ⋅ [FW]) in
  let generate_orders s pco := cross (co_locs pco (partition loc (Ensemble_of_dpset s))) in
  let generate_cos pco := generate_orders W pco in
  forall co,
    generate_cos co0 co ->
    is_strict_order co /\
    [W] ⋅ loc ⋅ [W] ≡ co ⊔ co° ⊔ 1 /\
    [IW] ⋅ loc ⋅ [W ⊓ !IW] ≦ co /\
    [W ⊓ !FW] ⋅ loc ⋅ [FW] ≦ co /\
    True
.
Admitted.
