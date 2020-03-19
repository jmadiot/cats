(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/herd/libdir/aarch64.cat *)
(* Translation of model ARMv8 AArch64 *)
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
Definition T := unknown_set "T".
Definition iico_ctrl := unknown_relation "iico_ctrl".
Definition iico_data := unknown_relation "iico_data".
Definition sm := unknown_relation "sm".
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
Definition cobase := co0.
Variable co : relation events.
Definition coi := co ⊓ int.
Definition coe := co ⊓ !coi.
Definition fr := rf° ⋅ co ⊓ !id.
Definition fri := fr ⊓ int.
Definition fre := fr ⊓ !fri.
Definition DMB_ISH := (*failed: try DMB.ISH with emptyset_0*) emptyset_0.
Definition DMB_ISHLD := (*failed: try DMB.ISHLD with emptyset_0*) emptyset_0.
Definition DMB_ISHST := (*failed: try DMB.ISHST with emptyset_0*) emptyset_0.
Definition DSB_ISH := (*failed: try DSB.ISH with emptyset_0*) emptyset_0.
Definition DSB_ISHLD := (*failed: try DSB.ISHLD with emptyset_0*) emptyset_0.
Definition DSB_ISHST := (*failed: try DSB.ISHST with emptyset_0*) emptyset_0.
Definition DMB_SY := (*failed: try DMB.SY with emptyset_0*) emptyset_0.
Definition DMB_ST := (*failed: try DMB.ST with emptyset_0*) emptyset_0.
Definition DMB_LD := (*failed: try DMB.LD with emptyset_0*) emptyset_0.
Definition DSB_SY := (*failed: try DSB.SY with emptyset_0*) emptyset_0.
Definition DSB_ST := (*failed: try DSB.ST with emptyset_0*) emptyset_0.
Definition DSB_LD := (*failed: try DSB.LD with emptyset_0*) emptyset_0.
Definition DMB_OSH := (*failed: try DMB.OSH with emptyset_0*) emptyset_0.
Definition DSB_OSH := (*failed: try DSB.OSH with emptyset_0*) emptyset_0.
Definition DMB_OSHLD := (*failed: try DMB.OSHLD with emptyset_0*) emptyset_0.
Definition DSB_OSHLD := (*successful: try DSB.OSH with emptyset_0*) DSB_OSH.
Definition DMB_OSHST := (*failed: try DMB.OSHST with emptyset_0*) emptyset_0.
Definition DSB_OSHST := (*failed: try DSB.OSHST with emptyset_0*) emptyset_0.
Definition ISB := (*failed: try ISB with emptyset_0*) emptyset_0.
Definition A := (*failed: try A with emptyset_0*) emptyset_0.
Definition L := (*failed: try L with emptyset_0*) emptyset_0.
Definition Q := (*failed: try Q with emptyset_0*) emptyset_0.
Definition NoRet := (*failed: try NoRet with emptyset_0*) emptyset_0.
Definition dmb_ish := fencerel DMB_ISH.
Definition dmb_ishld := fencerel DMB_ISHLD.
Definition dmb_ishst := fencerel DMB_ISHST.
Definition dmb_fullsy := fencerel DMB_SY.
Definition dmb_fullst := fencerel DMB_ST.
Definition dmb_fullld := fencerel DMB_LD.
Definition dmb_sy := dmb_fullsy ⊔ dmb_ish.
Definition dmb_st := dmb_fullst ⊔ dmb_ishst.
Definition dmb_ld := dmb_fullld ⊔ dmb_ishld.
Definition dsb_sy := fencerel DSB_SY.
Definition dsb_st := fencerel DSB_ST.
Definition dsb_ld := fencerel DSB_LD.
Definition isb := fencerel ISB.
Definition ctrlisb := (*successful: try ctrlcfence ISB with 0*) ctrlcfence ISB.
Definition dsb_full := DSB_ISH ⊔ (DSB_OSH ⊔ DSB_SY).
Definition dsb_ld_0 := DSB_ISHLD ⊔ (DSB_OSHLD ⊔ DSB_LD).
Definition dsb_st_0 := DSB_ISHST ⊔ (DSB_OSHST ⊔ DSB_ST).
Definition dmb_full := DMB_ISH ⊔ (DMB_OSH ⊔ (DMB_SY ⊔ dsb_full)).
Definition dmb_ld_0 := DMB_ISHLD ⊔ (DMB_OSHLD ⊔ (DMB_LD ⊔ dsb_ld_0)).
Definition dmb_st_0 := DMB_ISHST ⊔ (DMB_OSHST ⊔ (DMB_ST ⊔ dsb_st_0)).
Definition Assuming_common_inner_shareable_domain := not (is_empty ((dmb_full ⊔ (dmb_ld_0 ⊔ dmb_st_0)) ⊓ !(DMB_SY ⊔ (DMB_LD ⊔ (DMB_ST ⊔ (DSB_SY ⊔ (DSB_LD ⊔ DSB_ST))))))).
Definition intrinsic := (iico_data ⊔ iico_ctrl)^+.
Definition ca := fr ⊔ co.
Definition lrs := [W] ⋅ ((po_loc ⊓ !(po_loc ⋅ ([W] ⋅ po_loc))) ⋅ [R]).
Definition lws := po_loc ⋅ [W].
Definition si := sm.
Definition obs := rfe ⊔ (fre ⊔ coe).
Definition dob := addr ⊔ (data ⊔ (ctrl ⋅ [W] ⊔ ((ctrl ⊔ addr ⋅ po) ⋅ ([ISB] ⋅ (po ⋅ [R])) ⊔ (addr ⋅ (po ⋅ [W]) ⊔ (addr ⊔ data) ⋅ lrs)))).
Definition aob := rmw ⊔ [(range rmw)] ⋅ (lrs ⋅ [(A ⊔ Q)]).
Definition bob := po ⋅ (([dmb_full] ⊔ [A] ⋅ (amo ⋅ [L])) ⋅ po) ⊔ ([L] ⋅ (po ⋅ [A]) ⊔ ([(R ⊓ !NoRet)] ⋅ (po ⋅ ([dmb_ld_0] ⋅ po)) ⊔ ([(A ⊔ Q)] ⋅ po ⊔ ([W] ⋅ (po ⋅ ([dmb_st_0] ⋅ (po ⋅ [W]))) ⊔ po ⋅ [L])))).
Definition tob := [(R ⊓ T)] ⋅ (intrinsic ⋅ [(M ⊓ !T)]).
Inductive lob : relation _ := lob_c : incl (lws ⋅ si ⊔ (dob ⊔ (aob ⊔ (bob ⊔ (tob ⊔ lob ⋅ lob))))) lob.
Section scheme.
Variables lob' : relation events.
Variable Hlob' : incl (lws ⋅ si ⊔ (dob ⊔ (aob ⊔ (bob ⊔ (tob ⊔ lob' ⋅ lob'))))) lob'.

  Fixpoint lob_ind' x y (r : lob x y) : lob' x y.
  Proof.
    destruct r as [x y r]; apply Hlob'.
    destruct r as [r | r]; [ left | right ].
     exact r.
     destruct r as [r | r]; [ left | right ].
      exact r.
      destruct r as [r | r]; [ left | right ].
       exact r.
       destruct r as [r | r]; [ left | right ].
        exact r.
        destruct r as [r | r]; [ left | right ].
         exact r.
         destruct r as [x_y r1 r2]; exists x_y.
          apply lob_ind'; exact r1.
          apply lob_ind'; exact r2.
  Qed.
End scheme.
Inductive ob : relation _ := ob_c : incl (obs ⋅ si ⊔ (lob ⊔ ob ⋅ ob)) ob.
Section scheme.
Variables ob' : relation events.
Variable Hob' : incl (obs ⋅ si ⊔ (lob ⊔ ob' ⋅ ob')) ob'.

  Fixpoint ob_ind' x y (r : ob x y) : ob' x y.
  Proof.
    destruct r as [x y r]; apply Hob'.
    destruct r as [r | r]; [ left | right ].
     exact r.
     destruct r as [r | r]; [ left | right ].
      exact r.
      destruct r as [x_y r1 r2]; exists x_y.
       apply ob_ind'; exact r1.
       apply ob_ind'; exact r2.
  Qed.
End scheme.
Definition internal := acyclic (po_loc ⊔ (ca ⊔ rf)).
Definition external := irreflexive ob.
Definition atomic := is_empty (rmw ⊓ fre ⋅ coe).
Definition witness_conditions := generate_cos cobase co.
Definition model_conditions := Assuming_common_inner_shareable_domain /\ (internal /\ (external /\ atomic)).
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo rmw unknown_set unknown_relation M emptyset classes_loc T iico_ctrl iico_data sm tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW generate_orders generate_cos cobase coi coe fr fri fre DMB_ISH DMB_ISHLD DMB_ISHST DSB_ISH DSB_ISHLD DSB_ISHST DMB_SY DMB_ST DMB_LD DSB_SY DSB_ST DSB_LD DMB_OSH DSB_OSH DMB_OSHLD DSB_OSHLD DMB_OSHST DSB_OSHST ISB A L Q NoRet dmb_ish dmb_ishld dmb_ishst dmb_fullsy dmb_fullst dmb_fullld dmb_sy dmb_st dmb_ld dsb_sy dsb_st dsb_ld isb ctrlisb dsb_full dsb_ld_0 dsb_st_0 dmb_full dmb_ld_0 dmb_st_0 Assuming_common_inner_shareable_domain intrinsic ca lrs lws si obs dob aob bob tob internal external atomic witness_conditions model_conditions : cat.

Definition valid (c : candidate) :=
  exists co : relation (events c),
    witness_conditions c co /\
    model_conditions c co.

(* End of translation of model ARMv8 AArch64 *)
