(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model PPCChecks *)
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
Definition X := unknown_set "X".
Definition co := unknown_relation "co".
Definition coe := unknown_relation "coe".
Definition fre := unknown_relation "fre".
Definition light := unknown_relation "light".
Definition ppo := unknown_relation "ppo".
Definition strong := unknown_relation "strong".
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
Definition fence := strong ⊔ light.
Definition hb := ppo ⊔ (fence ⊔ rfe).
Definition thinair := acyclic hb.
Definition hbstar := hb^*.
Definition propbase := (fence ⊔ rfe ⋅ fence) ⋅ hbstar.
Definition chapo := rfe ⊔ (fre ⊔ (coe ⊔ (fre ⋅ rfe ⊔ coe ⋅ rfe))).
Definition prop := propbase ⊓ [W] ⋅ top ⋅ [W] ⊔ (chapo ⊔ 1) ⋅ (propbase^* ⋅ (strong ⋅ hbstar)).
Definition propagation := acyclic (co ⊔ prop).
Definition observation := irreflexive (fre ⋅ (prop ⋅ hbstar)).
Definition xx := po ⊓ [X] ⋅ top ⋅ [X].
Definition scXX := acyclic (co ⊔ xx).
Definition witness_conditions := True.
Definition model_conditions := thinair /\ (propagation /\ (observation /\ scXX)).
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo rmw unknown_set unknown_relation M emptyset classes_loc X co coe fre light ppo strong tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW fence hb thinair hbstar propbase chapo prop propagation observation xx scXX witness_conditions model_conditions : cat.

Definition valid (c : candidate) := model_conditions c.

(* End of translation of model PPCChecks *)
