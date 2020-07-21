(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model Simple C11 *)
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
Definition co0 := loc ⊓ ([IW] ⋅ top ⋅ [(W ⊓ !IW)] ⊔ [(W ⊓ !FW)] ⋅ top ⋅ [FW]).
Definition toid (s : set events) : relation events := [s].
Definition fencerel (B : set events) := (po ⊓ [top] ⋅ top ⋅ [B]) ⋅ po.
Definition ctrlcfence (CFENCE : set events) := (ctrl ⊓ [top] ⋅ top ⋅ [CFENCE]) ⋅ po.
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
Definition asw := [I] ⋅ top ⋅ [(M ⊓ !I)].
Definition A_0 := ((*failed: try X with emptyset_0*) emptyset_0) ⊔ ((*successful: try A with emptyset_0*) A).
Definition P := M ⊓ !A_0.
Definition WW r := r ⊓ [W] ⋅ top ⋅ [W].
Definition WR r := r ⊓ [W] ⋅ top ⋅ [R].
Definition RW r := r ⊓ [R] ⋅ top ⋅ [W].
Definition RR r := r ⊓ [R] ⋅ top ⋅ [R].
Definition RM r := r ⊓ [R] ⋅ top ⋅ [M].
Definition MR r := r ⊓ [M] ⋅ top ⋅ [R].
Definition WM r := r ⊓ [W] ⋅ top ⋅ [M].
Definition MW r := r ⊓ [M] ⋅ top ⋅ [W].
Definition MM r := r ⊓ [M] ⋅ top ⋅ [M].
Definition AA r := r ⊓ [A_0] ⋅ top ⋅ [A_0].
Definition AP r := r ⊓ [A_0] ⋅ top ⋅ [P].
Definition PA r := r ⊓ [P] ⋅ top ⋅ [A_0].
Definition PP r := r ⊓ [P] ⋅ top ⋅ [P].
Definition AM r := r ⊓ [A_0] ⋅ top ⋅ [M].
Definition MA r := r ⊓ [M] ⋅ top ⋅ [A_0].
Definition noid r : relation events := r ⊓ !id.
Definition atom := [A_0].
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

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo rmw unknown_set unknown_relation M emptyset classes_loc A ACQ ACQ_REL I REL SC tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW CACQ CREL Access a_id rmw_id crel_id cacq_id sc_id asw A_0 P WW WR RW RR RM MR WM MW MM AA AP PA PP AM MA noid atom generate_orders generate_cos cobase coi coe fr fri fre rsElem breakRseq rseq fence_id fid idf sw Y hb hb_loc scp ConsSC rfNA ConsRFna S_loc minWRSC rfSCSC rfXSC X badRFSC SCReads IrrHB chapo Coh cosucc AtRMW locSomeW dr dataRace ur unsequencedRace witness_conditions model_conditions : cat.

Definition valid (c : candidate) :=
  exists co S : relation (events c),
    witness_conditions c co S /\
    model_conditions c co S.

(* End of translation of model Simple C11 *)
