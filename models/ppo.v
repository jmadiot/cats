(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model PPO *)
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
Definition cc0 := unknown_relation "cc0".
Definition ci0 := unknown_relation "ci0".
Definition ic0 := unknown_relation "ic0".
Definition ii0 := unknown_relation "ii0".
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
Inductive ci : relation _ := ci_c : incl (ci0 ⊔ (ci ⋅ ii ⊔ cc ⋅ ci)) ci
     with ii : relation _ := ii_c : incl (ii0 ⊔ (ci ⊔ (ic ⋅ ci ⊔ ii ⋅ ii))) ii
     with cc : relation _ := cc_c : incl (cc0 ⊔ (ci ⊔ (ci ⋅ ic ⊔ cc ⋅ cc))) cc
     with ic : relation _ := ic_c : incl (ic0 ⊔ (ii ⊔ (cc ⊔ (ic ⋅ cc ⊔ ii ⋅ ic)))) ic.
Section scheme.
Variables ci' ii' cc' ic' : relation events.
Variable Hci' : incl (ci0 ⊔ (ci' ⋅ ii' ⊔ cc' ⋅ ci')) ci'.
Variable Hii' : incl (ii0 ⊔ (ci' ⊔ (ic' ⋅ ci' ⊔ ii' ⋅ ii'))) ii'.
Variable Hcc' : incl (cc0 ⊔ (ci' ⊔ (ci' ⋅ ic' ⊔ cc' ⋅ cc'))) cc'.
Variable Hic' : incl (ic0 ⊔ (ii' ⊔ (cc' ⊔ (ic' ⋅ cc' ⊔ ii' ⋅ ic')))) ic'.

  Fixpoint ci_ind' x y (r : ci x y) : ci' x y
      with ii_ind' x y (r : ii x y) : ii' x y
      with cc_ind' x y (r : cc x y) : cc' x y
      with ic_ind' x y (r : ic x y) : ic' x y.
  Proof.
    destruct r as [x y r]; apply Hci'.
    destruct r as [r | r]; [ left | right ].
     exact r.
     destruct r as [r | r]; [ left | right ].
      destruct r as [x_y r1 r2]; exists x_y.
       apply ci_ind'; exact r1.
       apply ii_ind'; exact r2.
      destruct r as [x_y r1 r2]; exists x_y.
       apply cc_ind'; exact r1.
       apply ci_ind'; exact r2.
    destruct r as [x y r]; apply Hii'.
    destruct r as [r | r]; [ left | right ].
     exact r.
     destruct r as [r | r]; [ left | right ].
      apply ci_ind'; exact r.
      destruct r as [r | r]; [ left | right ].
       destruct r as [x_y r1 r2]; exists x_y.
        apply ic_ind'; exact r1.
        apply ci_ind'; exact r2.
       destruct r as [x_y r1 r2]; exists x_y.
        apply ii_ind'; exact r1.
        apply ii_ind'; exact r2.
    destruct r as [x y r]; apply Hcc'.
    destruct r as [r | r]; [ left | right ].
     exact r.
     destruct r as [r | r]; [ left | right ].
      apply ci_ind'; exact r.
      destruct r as [r | r]; [ left | right ].
       destruct r as [x_y r1 r2]; exists x_y.
        apply ci_ind'; exact r1.
        apply ic_ind'; exact r2.
       destruct r as [x_y r1 r2]; exists x_y.
        apply cc_ind'; exact r1.
        apply cc_ind'; exact r2.
    destruct r as [x y r]; apply Hic'.
    destruct r as [r | r]; [ left | right ].
     exact r.
     destruct r as [r | r]; [ left | right ].
      apply ii_ind'; exact r.
      destruct r as [r | r]; [ left | right ].
       apply cc_ind'; exact r.
       destruct r as [r | r]; [ left | right ].
        destruct r as [x_y r1 r2]; exists x_y.
         apply ic_ind'; exact r1.
         apply cc_ind'; exact r2.
        destruct r as [x_y r1 r2]; exists x_y.
         apply ii_ind'; exact r1.
         apply ic_ind'; exact r2.
  Qed.
End scheme.
Definition ppo := let ppoR := ii ⊓ [R] ⋅ top ⋅ [R] in let ppoW := ic ⊓ [R] ⋅ top ⋅ [W] in ppoR ⊔ ppoW.
Definition witness_conditions := True.
Definition model_conditions := True.
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo rmw unknown_set unknown_relation M emptyset classes_loc cc0 ci0 ic0 ii0 tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW ppo witness_conditions model_conditions : cat.

Definition valid (c : candidate) := True.

(* End of translation of model PPO *)
