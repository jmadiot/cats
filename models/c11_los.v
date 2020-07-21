(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model C++11, generate lock-order *)
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
Definition classes_loc : set events -> Ensemble (Ensemble events) := partition loc.
Definition A := unknown_set "A".
Definition I := unknown_set "I".
Definition LS := unknown_set "LS".
Definition UL := unknown_set "UL".
Definition coi := unknown_relation "coi".
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
(* Definition of co_locs already included in the prelude *)
(* Definition of cross already included in the prelude *)
Definition generate_orders s pco := cross (co_locs pco (partition s)).
Definition generate_cos pco := generate_orders W pco.
Definition mobase := co0.
Variable mo : relation events.
Definition moi := mo ⊓ int.
Definition moe := mo ⊓ ext.
Definition co := mo.
Definition coe := moe.
Definition coi_0 := coi.
Definition fr := rf° ⋅ mo ⊓ !id.
Definition fri := fr ⊓ int.
Definition fre := fr ⊓ ext.
Definition crit := let Mutex := LS ⊔ UL in let poMutex := po_loc ⊓ [Mutex] ⋅ top ⋅ [Mutex] in po_loc ⊓ [LS] ⋅ top ⋅ [UL] ⊓ !(poMutex ⋅ poMutex).
Variable loLL : relation events.
Definition loLU := (loLL ⊔ 1) ⋅ crit.
Definition loUL := crit° ⋅ loLL.
Definition lo := (loLL ⊔ (loLU ⊔ loUL))^+.
Definition witness_conditions := generate_orders (W ⊓ (A ⊔ I)) mobase mo /\ generate_orders LS po loLL.
Definition model_conditions := True.
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo rmw unknown_set unknown_relation M emptyset classes_loc A I LS UL coi tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW generate_orders generate_cos mobase moi moe co coe coi_0 fr fri fre crit loLU loUL lo witness_conditions model_conditions : cat.

Definition valid (c : candidate) :=
  exists mo loLL : relation (events c),
    witness_conditions c mo loLL /\
    True.

(* End of translation of model C++11, generate lock-order *)
