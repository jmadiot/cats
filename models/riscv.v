(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model Risc V partial order model *)
From Coq Require Import Relations Ensembles String.
From RelationAlgebra Require Import lattice prop monoid rel.
Require Import Cat.
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
Definition Acq := unknown_set "Acq".
Definition AcqRel := unknown_set "AcqRel".
Definition Fence_r_r := unknown_set "Fence.r.r".
Definition Fence_r_rw := unknown_set "Fence.r.rw".
Definition Fence_r_w := unknown_set "Fence.r.w".
Definition Fence_rw_r := unknown_set "Fence.rw.r".
Definition Fence_rw_rw := unknown_set "Fence.rw.rw".
Definition Fence_rw_w := unknown_set "Fence.rw.w".
Definition Fence_tso := unknown_set "Fence.tso".
Definition Fence_w_r := unknown_set "Fence.w.r".
Definition Fence_w_rw := unknown_set "Fence.w.rw".
Definition Fence_w_w := unknown_set "Fence.w.w".
Definition Rel := unknown_set "Rel".
Definition Sc := unknown_set "Sc".
Definition X := unknown_set "X".
Definition rmw := unknown_relation "rmw".
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
Definition fence_r_r := diagonal R ⋅ (fencerel Fence_r_r ⋅ diagonal R).
Definition fence_r_w := diagonal R ⋅ (fencerel Fence_r_w ⋅ diagonal W).
Definition fence_r_rw := diagonal R ⋅ (fencerel Fence_r_rw ⋅ diagonal M).
Definition fence_w_r := diagonal W ⋅ (fencerel Fence_w_r ⋅ diagonal R).
Definition fence_w_w := diagonal W ⋅ (fencerel Fence_w_w ⋅ diagonal W).
Definition fence_w_rw := diagonal W ⋅ (fencerel Fence_w_rw ⋅ diagonal M).
Definition fence_rw_r := diagonal M ⋅ (fencerel Fence_rw_r ⋅ diagonal R).
Definition fence_rw_w := diagonal M ⋅ (fencerel Fence_rw_w ⋅ diagonal W).
Definition fence_rw_rw := diagonal M ⋅ (fencerel Fence_rw_rw ⋅ diagonal M).
Definition fence_tso := let f := fencerel Fence_tso in diagonal W ⋅ (f ⋅ diagonal W) ⊔ diagonal R ⋅ (f ⋅ diagonal M).
Definition fence := fence_r_r ⊔ (fence_r_w ⊔ (fence_r_rw ⊔ (fence_w_r ⊔ (fence_w_w ⊔ (fence_w_rw ⊔ (fence_rw_r ⊔ (fence_rw_w ⊔ (fence_rw_rw ⊔ fence_tso)))))))).
Definition po_loc_no_w := po_loc ⊓ !((po_loc ⊔ 1) ⋅ (diagonal W ⋅ po_loc)).
Definition rsw := rf° ⋅ rf.
Definition AcqRel_0 := AcqRel ⊔ Sc.
Definition AQ := Acq ⊔ AcqRel_0.
Definition RL := Rel ⊔ AcqRel_0.
Definition AMO := (*failed: try AMO with R ⊓ W*) R ⊓ W.
Definition RCsc := (Acq ⊔ (Rel ⊔ AcqRel_0)) ⊓ (AMO ⊔ X).
Definition r1 := diagonal M ⋅ (po_loc ⋅ diagonal W).
Definition r2 := diagonal R ⋅ (po_loc_no_w ⋅ diagonal R) ⊓ !rsw.
Definition r3 := diagonal (AMO ⊔ X) ⋅ (rfi ⋅ diagonal R).
Definition r4 := fence.
Definition r5 := diagonal AQ ⋅ (po ⋅ diagonal M).
Definition r6 := diagonal M ⋅ (po ⋅ diagonal RL).
Definition r7 := diagonal RCsc ⋅ (po ⋅ diagonal RCsc).
Definition r8 := rmw.
Definition r9 := diagonal M ⋅ (addr ⋅ diagonal M).
Definition r10 := diagonal M ⋅ (data ⋅ diagonal W).
Definition r11 := diagonal M ⋅ (ctrl ⋅ diagonal W).
Definition r12 := diagonal M ⋅ ((addr ⊔ data) ⋅ (diagonal W ⋅ (rfi ⋅ diagonal R))).
Definition r13 := diagonal M ⋅ (addr ⋅ (diagonal M ⋅ (po ⋅ diagonal W))).
Definition ppo := r1 ⊔ (r2 ⊔ (r3 ⊔ (r4 ⊔ (r5 ⊔ (r6 ⊔ (r7 ⊔ (r8 ⊔ (r9 ⊔ (r10 ⊔ (r11 ⊔ (r12 ⊔ r13))))))))))).
Definition obsco := let ww := po_loc ⊓ cartesian W W in let rw := rf ⋅ (po_loc ⊓ cartesian R W) in let wr := (po_loc ⊓ cartesian W R) ⋅ rf° ⊓ !id in let rr := rf ⋅ ((po_loc ⊓ cartesian R R) ⋅ rf°) ⊓ !id in ww ⊔ (rw ⊔ (wr ⊔ rr)).
Definition rmwco := let _RMW := R ⊓ W in rf ⊓ cartesian W _RMW.
Definition cobase := obsco ⊔ (rmwco ⊔ co0).
Definition ConsCo := acyclic cobase.
(* Definition of co_locs already included in the prelude *)
(* Definition of cross already included in the prelude *)
Definition generate_orders s pco := cross (co_locs pco (partition s)).
Definition generate_cos pco := generate_orders W pco.
Variable co : relation events.
Definition coi := co ⊓ int.
Definition coe := co ⊓ !coi.
Definition fr := rf° ⋅ co ⊓ !id.
Definition fri := fr ⊓ int.
Definition fre := fr ⊓ !fri.
Definition Coherence := acyclic (co ⊔ (rf ⊔ (fr ⊔ po_loc))).
Definition Model := acyclic (co ⊔ (rfe ⊔ (fr ⊔ ppo))).
Definition Atomic := is_empty (rmw ⊓ fre ⋅ coe).
Definition witness_conditions := generate_cos cobase co.
Definition model_conditions := ConsCo /\ (Coherence /\ (Model /\ Atomic)).
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo unknown_set unknown_relation M emptyset classes_loc Acq AcqRel Fence_r_r Fence_r_rw Fence_r_w Fence_rw_r Fence_rw_rw Fence_rw_w Fence_tso Fence_w_r Fence_w_rw Fence_w_w Rel Sc X rmw tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW fence_r_r fence_r_w fence_r_rw fence_w_r fence_w_w fence_w_rw fence_rw_r fence_rw_w fence_rw_rw fence_tso fence po_loc_no_w rsw AcqRel_0 AQ RL AMO RCsc r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 ppo obsco rmwco cobase ConsCo generate_orders generate_cos coi coe fr fri fre Coherence Model Atomic witness_conditions model_conditions : cat.

Definition valid (c : candidate) :=
  exists co : relation (events c),
    witness_conditions c co /\
    model_conditions c co.

(* End of translation of model Risc V partial order model *)
