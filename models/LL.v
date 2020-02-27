(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model LL *)
From Coq Require Import Relations Ensembles String.
From RelationAlgebra Require Import lattice prop monoid rel.
Require Import Cat.
Section Model.
Open Scope cat_scope.
Variable c : candidate.
Definition events := events c.
Definition R := R c.
Definition W := W c.
Definition IW := IW c.
Definition FW := FW c.
Definition B := B c.
Definition RMW := RMW c.
Definition F := F c.
Definition rf := rf c.
Definition po := po c.
Definition int := int c.
Definition ext := ext c.
Definition loc := loc c.
Definition addr := addr c.
Definition data := data c.
Definition ctrl := ctrl c.
Definition amo := amo c.
Definition unknown_set := unknown_set c.
Definition unknown_relation := unknown_relation c.
Definition M := R ⊔ W.
Definition emptyset : set events := empty.
Definition classes_loc : Ensemble events -> Ensemble (Ensemble events) := fun S Si => (forall x, Si x -> S x) /\ forall x y, Si x -> Si y -> loc x y.
Definition co := unknown_relation "co".
Definition dmb_st := unknown_relation "dmb.st".
Definition dsb_st := unknown_relation "dsb.st".
Definition fr := unknown_relation "fr".
Definition tag2events := unknown_relation "tag2events".
Definition emptyset_0 : set events := domain 0.
Definition partition := classes_loc.
Definition tag2instrs := tag2events.
Definition po_loc := po ⊓ loc.
Definition rfe := rf ⊓ ext.
Definition rfi := rf ⊓ int.
Definition co0 := loc ⊓ (cartesian IW (W ⊓ !IW) ⊔ cartesian (W ⊓ !FW) FW).
Definition toid s : relation events := diagonal s.
Definition fencerel B := (po ⊓ cartesian top B) ⋅ po.
Definition ctrlcfence CFENCE := (ctrl ⊓ cartesian top CFENCE) ⋅ po.
Definition imply (A : relation events) (B : relation events) := !A ⊔ B.
Definition nodetour (R1 : relation events) (R2 : relation events) (R3 : relation events) := R1 ⊓ !(R2 ⋅ R3).
Definition singlestep (R : relation events) := nodetour R R R.
(* Definition of map already included in the prelude *)
Definition LKW := (*failed: try LKW with emptyset_0*) emptyset_0.
Definition RW r := r ⊓ cartesian R W.
Definition WR r := r ⊓ cartesian W R.
Definition WW r := r ⊓ cartesian W W.
Definition chapo := fr ⊔ (rf ⊔ (co ⊔ (co ⋅ rf ⊔ fr ⋅ rf))).
Definition poi := WW po_loc ⊔ (RW po_loc ⊔ WR po_loc).
Definition test := irreflexive (poi ⋅ chapo).
Definition dmb_st_0 := WW dmb_st.
Definition dsb_st_0 := WW dsb_st.
Definition witness_conditions := True.
Definition model_conditions := test.
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo unknown_set unknown_relation M emptyset classes_loc co dmb_st dsb_st fr tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW RW WR WW chapo poi test dmb_st_0 dsb_st_0 witness_conditions model_conditions : cat.

Definition valid (c : candidate) := model_conditions c.

(* End of translation of model LL *)
