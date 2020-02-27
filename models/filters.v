(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model filters *)
From Coq Require Import Relations Ensembles String.
From RelationAlgebra Require Import lattice prop monoid rel.
From Catincoq Require Import Cat.
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
Definition A := ((*failed: try X with emptyset_0*) emptyset_0) ⊔ ((*failed: try A with emptyset_0*) emptyset_0).
Definition P := M ⊓ !A.
Definition WW r := r ⊓ cartesian W W.
Definition WR r := r ⊓ cartesian W R.
Definition RW r := r ⊓ cartesian R W.
Definition RR r := r ⊓ cartesian R R.
Definition RM r := r ⊓ cartesian R M.
Definition MR r := r ⊓ cartesian M R.
Definition WM r := r ⊓ cartesian W M.
Definition MW r := r ⊓ cartesian M W.
Definition MM r := r ⊓ cartesian M M.
Definition AA r := r ⊓ cartesian A A.
Definition AP r := r ⊓ cartesian A P.
Definition PA r := r ⊓ cartesian P A.
Definition PP r := r ⊓ cartesian P P.
Definition AM r := r ⊓ cartesian A M.
Definition MA r := r ⊓ cartesian M A.
Definition noid r : relation events := r ⊓ !id.
Definition atom := diagonal A.
Definition witness_conditions := True.
Definition model_conditions := True.
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo unknown_set unknown_relation M emptyset classes_loc tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW A P WW WR RW RR RM MR WM MW MM AA AP PA PP AM MA noid atom witness_conditions model_conditions : cat.

Definition valid (c : candidate) := True.

(* End of translation of model filters *)