(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model Model pretty print *)
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
Definition X := unknown_set "X".
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
Definition A := ((*successful: try X with emptyset_0*) X) ⊔ ((*failed: try A with emptyset_0*) emptyset_0).
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
Definition obsco := WW po_loc ⊔ (rf ⋅ RW po_loc ⊔ (noid (WR po_loc ⋅ rf°) ⊔ noid (rf ⋅ (RR po_loc ⋅ rf°)))).
Definition cobase := obsco ⊔ co0.
Definition uniproc := acyclic cobase.
Definition co := cobase^+.
Definition fr := noid (rf° ⋅ co).
Definition coi := co ⊓ int.
Definition fri := fr ⊓ int.
Definition coe := co ⊓ !coi.
Definition fre := fr ⊓ !fri.
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
Definition sync : relation events := (*failed: try fencerel SYNC with 0*) 0.
Definition lwsync : relation events := (*failed: try fencerel LWSYNC with 0*) 0.
Definition eieio : relation events := (*failed: try fencerel EIEIO with 0*) 0.
Definition isync : relation events := (*failed: try fencerel ISYNC with 0*) 0.
Definition ctrlisync : relation events := (*failed: try ctrlcfence ISYNC with 0*) 0.
Definition ci0 := ctrlisync ⊔ (ctrlisb ⊔ detour).
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
Definition ppo := let ppoR := ii ⊓ cartesian R R in let ppoW := ic ⊓ cartesian R W in ppoR ⊔ ppoW.
Definition lwsync_0 := RM lwsync ⊔ WW lwsync.
Definition eieio_0 := WW eieio.
Definition dmb_st_0 := WW dmb_st.
Definition dsb_st_0 := WW dsb_st.
Definition strong := sync ⊔ (dmb ⊔ (dsb ⊔ (dmb_st_0 ⊔ dsb_st_0))).
Definition light := lwsync_0 ⊔ eieio_0.
Definition fence := strong ⊔ light.
Definition hb := ppo ⊔ (fence ⊔ rfe).
Definition thinair := acyclic hb.
Definition hbstar := hb^*.
Definition propbase := (fence ⊔ rfe ⋅ fence) ⋅ hbstar.
Definition chapo := rfe ⊔ (fre ⊔ (coe ⊔ (fre ⋅ rfe ⊔ coe ⋅ rfe))).
Definition prop := propbase ⊓ cartesian W W ⊔ (chapo ⊔ 1) ⋅ (propbase^* ⋅ (strong ⋅ hbstar)).
Definition propagation := acyclic (co ⊔ prop).
Definition observation := irreflexive (fre ⋅ (prop ⋅ hbstar)).
Definition xx := po ⊓ cartesian X X.
Definition scXX := acyclic (co ⊔ xx).
Definition witness_conditions := True.
Definition model_conditions := uniproc /\ (thinair /\ (propagation /\ (observation /\ scXX))).
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo unknown_set unknown_relation M emptyset classes_loc X tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW A P WW WR RW RR RM MR WM MW MM AA AP PA PP AM MA noid atom obsco cobase uniproc co fr coi fri coe fre dd rdw detour addrpo dmb_st dsb_st dmb dsb isb ctrlisb sync lwsync eieio isync ctrlisync ci0 ii0 cc0 ic0 ppo lwsync_0 eieio_0 dmb_st_0 dsb_st_0 strong light fence hb thinair hbstar propbase chapo prop propagation observation xx scXX witness_conditions model_conditions : cat.

Definition valid (c : candidate) := model_conditions c.

(* End of translation of model Model pretty print *)