(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model Model pretty print *)
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
Definition X := unknown_set "X".
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
Definition A := ((*successful: try X with emptyset_0*) X) ⊔ ((*failed: try A with emptyset_0*) emptyset_0).
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
(* Definition of co_locs already included in the prelude *)
(* Definition of cross already included in the prelude *)
Definition generate_orders s pco := cross (co_locs pco (partition s)).
Definition generate_cos pco := generate_orders W pco.
Variable co : relation events.
Definition fr := rf° ⋅ co.
Definition fre := fr ⊓ ext.
Definition coe := co ⊓ ext.
Definition uniproc := acyclic (po_loc ⊔ (rf ⊔ (fr ⊔ co))).
Definition dd := addr ⊔ data.
Definition rdw := po_loc ⊓ fre ⋅ rfe.
Definition detour := po_loc ⊓ coe ⋅ rfe.
Definition addrpo := addr ⋅ po.
Definition dmb_st : relation events := (*failed: try fencerel DMB.ST with 0*) 0.
Definition dsb_st : relation events := (*failed: try fencerel DSB.ST with 0*) 0.
Definition dmb : relation events := (*failed: try fencerel DMB with 0*) 0.
Definition dsb : relation events := (*failed: try fencerel DSB with 0*) 0.
Definition isb : relation events := (*failed: try fencerel ISB with 0*) 0.
Definition ctrlisb : relation events := (*failed: try ctrlcfence ISB with 0*) 0.
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
Definition A_0 := (*successful: try A with emptyset_0*) A.
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
Definition sync : relation events := (*failed: try fencerel SYNC with 0*) 0.
Definition lwsync : relation events := (*failed: try fencerel LWSYNC with 0*) 0.
Definition eieio : relation events := (*failed: try fencerel EIEIO with 0*) 0.
Definition isync : relation events := (*failed: try fencerel ISYNC with 0*) 0.
Definition ctrlisync : relation events := (*failed: try ctrlcfence ISYNC with 0*) 0.
Definition ctrlcfence_0 := ctrlisync ⊔ ctrlisb_0.
Definition ci0 := ctrlisync ⊔ (ctrlisb_0 ⊔ detour).
Definition ii0 := dd ⊔ (rfi ⊔ rdw).
Definition cc0 := dd ⊔ (po_loc ⊔ (ctrl ⊔ addrpo)).
Definition ic0 : relation events := 0.
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
Definition lwsync_eff := RM lwsync ⊔ WW lwsync.
Definition eieio_eff := WW eieio.
Definition dmb_st_eff := WW dmb_st_0.
Definition dsb_st_eff := WW dsb_st_0.
Definition f64 := dsb_sy ⊔ (dmb_sy ⊔ (WW dsb_st_0 ⊔ (WW dmb_st_0 ⊔ (RM dmb_ld ⊔ RM dsb_ld)))).
Definition strong := sync ⊔ (dmb ⊔ (dsb ⊔ (dmb_st_eff ⊔ (dsb_st_eff ⊔ f64)))).
Definition light := lwsync_eff ⊔ eieio_eff.
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
Definition witness_conditions := generate_cos co0 co.
Definition model_conditions := uniproc /\ (thinair /\ (propagation /\ (observation /\ scXX))).
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo rmw unknown_set unknown_relation M emptyset classes_loc X tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW A P WW WR RW RR RM MR WM MW MM AA AP PA PP AM MA noid atom generate_orders generate_cos fr fre coe uniproc dd rdw detour addrpo dmb_st dsb_st dmb dsb isb ctrlisb DMB_ISH DMB_ISHLD DMB_ISHST DSB_ISH DSB_ISHLD DSB_ISHST DMB_SY DMB_ST DMB_LD DSB_SY DSB_ST DSB_LD DMB_OSH DSB_OSH DMB_OSHLD DSB_OSHLD DMB_OSHST DSB_OSHST ISB A_0 L Q NoRet dmb_ish dmb_ishld dmb_ishst dmb_fullsy dmb_fullst dmb_fullld dmb_sy dmb_st_0 dmb_ld dsb_sy dsb_st_0 dsb_ld isb_0 ctrlisb_0 sync lwsync eieio isync ctrlisync ctrlcfence_0 ci0 ii0 cc0 ic0 ppo lwsync_eff eieio_eff dmb_st_eff dsb_st_eff f64 strong light fence hb thinair hbstar propbase chapo prop propagation observation xx scXX witness_conditions model_conditions : cat.

Definition valid (c : candidate) :=
  exists co : relation (events c),
    witness_conditions c co /\
    model_conditions c co.

(* End of translation of model Model pretty print *)
