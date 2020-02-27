(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model Relaxed ARM llh model *)
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
Definition obsco := let ww := po_loc ⊓ cartesian W W in let rw := rf ⋅ (po_loc ⊓ cartesian R W) in let wr := (po_loc ⊓ cartesian W R) ⋅ rf° in let rr := 0 in (ww ⊔ (rw ⊔ (wr ⊔ rr))) ⊓ !id.
Definition RMW_0 := R ⊓ W.
Definition rmwco := rf ⊓ cartesian W RMW_0.
Definition cobase := obsco ⊔ (rmwco ⊔ co0).
Definition ConsCo := acyclic cobase.
(* Definition of co_locs already included in the prelude *)
(* Definition of cross already included in the prelude *)
Definition generate_orders s pco := cross (co_locs pco (partition s)).
Definition generate_cos pco := generate_orders W pco.
Variable co : relation events.
Definition coe := co ⊓ ext.
Definition coi := co ⊓ int.
Definition fr := rf° ⋅ co ⊓ !id.
Definition fre := fr ⊓ ext.
Definition fri := fr ⊓ int.
Definition poi := WW po_loc ⊔ (RW po_loc ⊔ WR po_loc).
Definition complus := fr ⊔ (rf ⊔ (co ⊔ (co ⋅ rf ⊔ fr ⋅ rf))).
Definition uniproc := irreflexive (poi ⋅ complus).
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
Definition ci0 := ctrlisb ⊔ detour.
Definition ii0 := dd ⊔ (rfi ⊔ rdw).
Definition cc0 := dd ⊔ (ctrl ⊔ addrpo).
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
Definition dmb_st_0 := WW dmb_st.
Definition dsb_st_0 := WW dsb_st.
Definition strong := dmb ⊔ (dsb ⊔ (dmb_st_0 ⊔ dsb_st_0)).
Definition light : relation events := 0.
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
Definition witness_conditions := generate_cos cobase co.
Definition model_conditions := ConsCo /\ (uniproc /\ (thinair /\ (propagation /\ (observation /\ scXX)))).
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo unknown_set unknown_relation M emptyset classes_loc X tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW A P WW WR RW RR RM MR WM MW MM AA AP PA PP AM MA noid atom obsco RMW_0 rmwco cobase ConsCo generate_orders generate_cos coe coi fr fre fri poi complus uniproc dd rdw detour addrpo dmb_st dsb_st dmb dsb isb ctrlisb ci0 ii0 cc0 ic0 ppo dmb_st_0 dsb_st_0 strong light fence hb thinair hbstar propbase chapo prop propagation observation xx scXX witness_conditions model_conditions : cat.

Definition valid (c : candidate) :=
  exists co : relation (events c),
    witness_conditions c co /\
    model_conditions c co.

(* End of translation of model Relaxed ARM llh model *)
