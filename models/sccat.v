(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model SC, no co generated *)
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
Definition WW r := r ⊓ [W] ⋅ top ⋅ [W].
Definition RW r := r ⊓ [R] ⋅ top ⋅ [W].
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
Definition sc_per_location := acyclic U.
Definition co := WW U.
Definition fr := RW U.
Definition mfence : relation events := (*failed: try fencerel MFENCE with 0*) 0.
Definition lfence : relation events := (*failed: try fencerel LFENCE with 0*) 0.
Definition sfence : relation events := (*failed: try fencerel SFENCE with 0*) 0.
Definition dmb_st : relation events := (*failed: try fencerel DMB.ST with 0*) 0.
Definition dsb_st : relation events := (*failed: try fencerel DSB.ST with 0*) 0.
Definition dmb : relation events := (*failed: try fencerel DMB with 0*) 0.
Definition dsb : relation events := (*failed: try fencerel DSB with 0*) 0.
Definition isb : relation events := (*failed: try fencerel ISB with 0*) 0.
Definition ctrlisb : relation events := (*failed: try ctrlcfence ISB with 0*) 0.
Definition sync : relation events := (*failed: try fencerel SYNC with 0*) 0.
Definition lwsync : relation events := (*failed: try fencerel LWSYNC with 0*) 0.
Definition eieio : relation events := (*failed: try fencerel EIEIO with 0*) 0.
Definition isync : relation events := (*failed: try fencerel ISYNC with 0*) 0.
Definition ctrlisync : relation events := (*failed: try ctrlcfence ISYNC with 0*) 0.
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
Definition dmb_st_0 := dmb_fullst ⊔ dmb_ishst.
Definition dmb_ld := dmb_fullld ⊔ dmb_ishld.
Definition dsb_sy := fencerel DSB_SY.
Definition dsb_st_0 := fencerel DSB_ST.
Definition dsb_ld := fencerel DSB_LD.
Definition isb_0 := fencerel ISB.
Definition ctrlisb_0 := (*successful: try ctrlcfence ISB with 0*) ctrlcfence ISB.
Definition ctrlcfence_0 := ctrlisb_0 ⊔ ctrlisync.
Definition S0 := po ⊔ U.
Inductive S : relation _ := S_c : incl (S0 ⊔ (WW (Sloc ⋅ rf°) ⊓ !id ⊔ (RW (rf° ⋅ Sloc) ⊓ !id ⊔ S ⋅ S))) S
     with Sloc : relation _ := Sloc_c : incl (S ⊓ loc) Sloc.
Section scheme.
Variables S' Sloc' : relation events.
Variable HS' : incl (S0 ⊔ (WW (Sloc' ⋅ rf°) ⊓ !id ⊔ (RW (rf° ⋅ Sloc') ⊓ !id ⊔ S' ⋅ S'))) S'.
Variable HSloc' : incl (S' ⊓ loc) Sloc'.

  Fixpoint S_ind' x y (r : S x y) : S' x y
      with Sloc_ind' x y (r : Sloc x y) : Sloc' x y.
  Proof.
    destruct r as [x y r]; apply HS'.
    destruct r as [r | r]; [ left | right ].
     exact r.
     destruct r as [r | r]; [ left | right ].
       destruct r as [r1 r2]; split.
        destruct r1 as [r11 r12]; split.
         destruct r11 as [x_y r111 r112]; exists x_y.
          apply Sloc_ind'; exact r111.
          exact r112.
         exact r12.
        exact r2.
      destruct r as [r | r]; [ left | right ].
        destruct r as [r1 r2]; split.
         destruct r1 as [r11 r12]; split.
          destruct r11 as [x_y r111 r112]; exists x_y.
           exact r111.
           apply Sloc_ind'; exact r112.
          exact r12.
         exact r2.
       destruct r as [x_y r1 r2]; exists x_y.
        apply S_ind'; exact r1.
        apply S_ind'; exact r2.
    destruct r as [x y r]; apply HSloc'.
    destruct r as [r1 r2]; split.
     apply S_ind'; exact r1.
     exact r2.
  Qed.
End scheme.
Definition sc := acyclic S.
Definition co_0 := WW Sloc.
Definition fr_0 := RW Sloc.
Definition coe := co_0 ⊓ ext.
Definition fre := fr_0 ⊓ ext.
Definition atom := is_empty (rmw ⊓ fre ⋅ coe).
Definition witness_conditions := True.
Definition model_conditions := sc_per_location /\ (sc /\ atom).
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo rmw unknown_set unknown_relation M emptyset classes_loc tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW WW RW U0 sc_per_location co fr mfence lfence sfence dmb_st dsb_st dmb dsb isb ctrlisb sync lwsync eieio isync ctrlisync DMB_ISH DMB_ISHLD DMB_ISHST DSB_ISH DSB_ISHLD DSB_ISHST DMB_SY DMB_ST DMB_LD DSB_SY DSB_ST DSB_LD DMB_OSH DSB_OSH DMB_OSHLD DSB_OSHLD DMB_OSHST DSB_OSHST ISB A L Q NoRet dmb_ish dmb_ishld dmb_ishst dmb_fullsy dmb_fullst dmb_fullld dmb_sy dmb_st_0 dmb_ld dsb_sy dsb_st_0 dsb_ld isb_0 ctrlisb_0 ctrlcfence_0 S0 sc co_0 fr_0 coe fre atom witness_conditions model_conditions : cat.

Definition valid (c : candidate) := model_conditions c.

(* End of translation of model SC, no co generated *)
