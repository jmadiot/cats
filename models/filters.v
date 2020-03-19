(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model filters *)
From Coq Require Import Relations Ensembles String.
From RelationAlgebra Require Import lattice prop monoid rel kat.
From Catincoq.lib Require Import Cat proprel.
Section Model.
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
Definition rmw := rmw c.
Definition unknown_set := unknown_set c.
Definition unknown_relation := unknown_relation c.
Definition M := R ⊔ W.
Definition emptyset : set events := empty.
Definition classes_loc : set events -> Ensemble (Ensemble events) := fun S Si => (forall x, Si x -> Ensemble_of_dpset S x) /\ forall x y, Si x -> Si y -> loc x y.
Definition tag2events := unknown_relation "tag2events".
Definition emptyset_0 : set events := domain 0.
Definition partition := classes_loc.
Definition tag2instrs := tag2events.
Definition po_loc := po ⊓ loc.
Definition rfe := rf ⊓ ext.
Definition rfi := rf ⊓ int.
Definition co0 := loc ⊓ ([IW] ⋅ top ⋅ [(W ⊓ !IW)] ⊔ [(W ⊓ !FW)] ⋅ top ⋅ [FW]).
Definition toid (s : set events) : relation events := [s].
Definition fencerel (B : set events) := (po ⊓ [top] ⋅ top ⋅ [B]) ⋅ po.
Definition ctrlcfence (CFENCE : set events) := (ctrl ⊓ [top] ⋅ top ⋅ [CFENCE]) ⋅ po.
Definition imply (A : relation events) (B : relation events) := !A ⊔ B.
Definition nodetour (R1 : relation events) (R2 : relation events) (R3 : relation events) := R1 ⊓ !(R2 ⋅ R3).
Definition singlestep (R : relation events) := nodetour R R R.
(* Definition of map already included in the prelude *)
Definition LKW := (*failed: try LKW with emptyset_0*) emptyset_0.
Definition A := ((*failed: try X with emptyset_0*) emptyset_0) ⊔ ((*failed: try A with emptyset_0*) emptyset_0).
Definition P := M ⊓ !A.
Definition WW r := r ⊓ [W] ⋅ top ⋅ [W].
Definition WR r := r ⊓ [W] ⋅ top ⋅ [R].
Definition RW r := r ⊓ [R] ⋅ top ⋅ [W].
Definition RR r := r ⊓ [R] ⋅ top ⋅ [R].
Definition RM r := r ⊓ [R] ⋅ top ⋅ [M].
Definition MR r := r ⊓ [M] ⋅ top ⋅ [R].
Definition WM r := r ⊓ [W] ⋅ top ⋅ [M].
Definition MW r := r ⊓ [M] ⋅ top ⋅ [W].
Definition MM r := r ⊓ [M] ⋅ top ⋅ [M].
Definition AA r := r ⊓ [A] ⋅ top ⋅ [A].
Definition AP r := r ⊓ [A] ⋅ top ⋅ [P].
Definition PA r := r ⊓ [P] ⋅ top ⋅ [A].
Definition PP r := r ⊓ [P] ⋅ top ⋅ [P].
Definition AM r := r ⊓ [A] ⋅ top ⋅ [M].
Definition MA r := r ⊓ [M] ⋅ top ⋅ [A].
Definition noid r : relation events := r ⊓ !id.
Definition atom := [A].
Definition witness_conditions := True.
Definition model_conditions := True.
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo rmw unknown_set unknown_relation M emptyset classes_loc tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW A P WW WR RW RR RM MR WM MW MM AA AP PA PP AM MA noid atom witness_conditions model_conditions : cat.

Definition valid (c : candidate) := True.

(* End of translation of model filters *)
