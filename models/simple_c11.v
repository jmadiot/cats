(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model Simple C11 *)
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
Definition A := unknown_set "A".
Definition ACQ := unknown_set "ACQ".
Definition ACQ_REL := unknown_set "ACQ_REL".
Definition I := unknown_set "I".
Definition REL := unknown_set "REL".
Definition SC := unknown_set "SC".
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
Definition CACQ := ACQ ⊔ (SC ⊓ R ⊔ ACQ_REL).
Definition CREL := REL ⊔ (SC ⊓ W ⊔ ACQ_REL).
Definition Access := R ⊔ W.
Definition a_id := toid A.
Definition rmw_id := toid RMW.
Definition crel_id := toid CREL.
Definition cacq_id := toid CACQ.
Definition sc_id := toid SC.
Definition asw := cartesian I (M ⊓ !I).
Definition A_0 := ((*failed: try X with emptyset_0*) emptyset_0) ⊔ ((*successful: try A with emptyset_0*) A).
Definition P := M ⊓ !A_0.
Definition WW r := r ⊓ cartesian W W.
Definition WR r := r ⊓ cartesian W R.
Definition RW r := r ⊓ cartesian R W.
Definition RR r := r ⊓ cartesian R R.
Definition RM r := r ⊓ cartesian R M.
Definition MR r := r ⊓ cartesian M R.
Definition WM r := r ⊓ cartesian W M.
Definition MW r := r ⊓ cartesian M W.
Definition MM r := r ⊓ cartesian M M.
Definition AA r := r ⊓ cartesian A_0 A_0.
Definition AP r := r ⊓ cartesian A_0 P.
Definition PA r := r ⊓ cartesian P A_0.
Definition PP r := r ⊓ cartesian P P.
Definition AM r := r ⊓ cartesian A_0 M.
Definition MA r := r ⊓ cartesian M A_0.
Definition noid r : relation events := r ⊓ !id.
Definition atom := diagonal A_0.
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
Definition rsElem := coi ⊔ co ⋅ rmw_id.
Definition breakRseq := co ⊓ !rsElem.
Definition rseq := id ⊔ rsElem ⊓ !(breakRseq ⋅ co).
Definition fence_id := toid F.
Definition fid := fence_id ⋅ po ⊔ 1.
Definition idf := po ⋅ fence_id ⊔ 1.
Definition sw := ext ⊓ crel_id ⋅ (fid ⋅ (rseq ⋅ (rf ⋅ (a_id ⋅ (idf ⋅ cacq_id))))).
Definition Y := po.
Definition hb := (po ⊔ (asw ⊔ sw))^+.
Definition hb_loc := hb ⊓ loc.
Definition scp := hb ⊔ co.
Definition ConsSC := acyclic scp.
Variable S : relation events.
Definition rfNA := rf ⊓ !AA rf.
Definition ConsRFna := is_empty (rfNA ⊓ !hb_loc).
Definition S_loc := MM S ⊓ loc.
Definition minWRSC := let aux := WR S_loc in aux ⊓ !(WW S_loc ⋅ aux).
Definition rfSCSC := sc_id ⋅ (rf ⋅ sc_id).
Definition rfXSC := rf ⋅ sc_id ⊓ !rfSCSC.
Definition X := hb ⋅ minWRSC.
Definition badRFSC := rfSCSC ⊓ !minWRSC ⊔ rfXSC ⊓ hb ⋅ minWRSC.
Definition SCReads := is_empty badRFSC.
Definition IrrHB := irreflexive hb.
Definition chapo := rf ⊔ (fr ⊔ (co ⊔ (co ⋅ rf ⊔ fr ⋅ rf))).
Definition Coh := acyclic (hb_loc ⊔ chapo).
Definition cosucc := co ⊓ !(co ⋅ co).
Definition AtRMW := is_empty (rf ⋅ rmw_id ⊓ !cosucc).
Definition locSomeW := loc ⊓ !RR loc.
Definition dr := let r1 := locSomeW ⊓ ext in let r2 := r1 ⊓ !AA r1 in r2 ⊓ !(hb ⊔ hb°).
Definition dataRace := is_empty dr.
Definition ur := let r1 := locSomeW ⊓ int in let r2 := noid r1 in r2 ⊓ !(po ⊔ po°).
Definition unsequencedRace := not (is_empty ur).
Definition witness_conditions := generate_cos cobase co /\ linearisations SC scp S.
Definition model_conditions := ConsSC /\ (ConsRFna /\ (SCReads /\ (IrrHB /\ (Coh /\ (AtRMW /\ (dataRace /\ unsequencedRace)))))).
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo unknown_set unknown_relation M emptyset classes_loc A ACQ ACQ_REL I REL SC tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW CACQ CREL Access a_id rmw_id crel_id cacq_id sc_id asw A_0 P WW WR RW RR RM MR WM MW MM AA AP PA PP AM MA noid atom generate_orders generate_cos cobase coi coe fr fri fre rsElem breakRseq rseq fence_id fid idf sw Y hb hb_loc scp ConsSC rfNA ConsRFna S_loc minWRSC rfSCSC rfXSC X badRFSC SCReads IrrHB chapo Coh cosucc AtRMW locSomeW dr dataRace ur unsequencedRace witness_conditions model_conditions : cat.

Definition valid (c : candidate) :=
  exists co S : relation (events c),
    witness_conditions c co S /\
    model_conditions c co S.

(* End of translation of model Simple C11 *)
