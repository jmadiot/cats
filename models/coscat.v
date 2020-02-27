(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model Uniproc, no co generated *)
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
Definition WW r := r ⊓ cartesian W W.
Definition RW r := r ⊓ cartesian R W.
Definition U0 := po_loc ⊔ (rf ⊔ co0).
Inductive U : relation _ := U_c : incl (U0 ⊔ (WW (U ⋅ rf°) ⊓ !id ⊔ (RW (rf° ⋅ U) ⊓ !id ⊔ U ⋅ U))) U.
Section scheme.
Variables U' : relation events.
Variable HU' : incl (U0 ⊔ (WW (U' ⋅ rf°) ⊓ !id ⊔ (RW (rf° ⋅ U') ⊓ !id ⊔ U' ⋅ U'))) U'.

  Fixpoint U_ind' x y (r : U x y) : U' x y.
  Proof.
    destruct r as [x y r]; apply HU'.
    destruct r as [r | r]; [ left | right ].
     exact r.
     destruct r as [r | r]; [ left | right ].
       destruct r as [r1 r2]; split.
        destruct r1 as [r11 r12]; split.
         destruct r11 as [x_y r111 r112]; exists x_y.
          apply U_ind'; exact r111.
          exact r112.
         exact r12.
        exact r2.
      destruct r as [r | r]; [ left | right ].
        destruct r as [r1 r2]; split.
         destruct r1 as [r11 r12]; split.
          destruct r11 as [x_y r111 r112]; exists x_y.
           exact r111.
           apply U_ind'; exact r112.
          exact r12.
         exact r2.
       destruct r as [x_y r1 r2]; exists x_y.
        apply U_ind'; exact r1.
        apply U_ind'; exact r2.
  Qed.
End scheme.
Definition co := WW U.
Definition fr := RW U.
Definition coi := co ⊓ int.
Definition coe := co ⊓ !coi.
Definition fri := fr ⊓ int.
Definition fre := fr ⊓ !fri.
Definition witness_conditions := True.
Definition model_conditions := True.
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo unknown_set unknown_relation M emptyset classes_loc tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW WW RW U0 co fr coi coe fri fre witness_conditions model_conditions : cat.

Definition valid (c : candidate) := True.

(* End of translation of model Uniproc, no co generated *)