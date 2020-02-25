(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model RC11 *)
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
Definition A := unknown_set "A".
Definition ACQ := unknown_set "ACQ".
Definition ACQ_REL := unknown_set "ACQ_REL".
Definition E := unknown_set "E".
Definition REL := unknown_set "REL".
Definition RLX := unknown_set "RLX".
Definition SC := unknown_set "SC".
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
Definition mo := co.
Definition sb := po.
Definition myrmw := diagonal RMW ⊔ rmw.
Definition rb := rf° ⋅ mo ⊓ !id.
Definition eco := (rf ⊔ (mo ⊔ rb))^+.
Definition rs := diagonal W ⋅ ((sb ⊓ loc ⊔ 1) ⋅ (diagonal (W ⊓ (RLX ⊔ (REL ⊔ (ACQ_REL ⊔ (ACQ ⊔ SC))))) ⋅ (rf ⋅ myrmw)^*)).
Definition sw := diagonal (REL ⊔ (ACQ_REL ⊔ SC)) ⋅ ((diagonal F ⋅ sb ⊔ 1) ⋅ (rs ⋅ (rf ⋅ (diagonal (R ⊓ (RLX ⊔ (REL ⊔ (ACQ ⊔ (ACQ_REL ⊔ SC))))) ⋅ ((sb ⋅ diagonal F ⊔ 1) ⋅ diagonal (ACQ ⊔ (ACQ_REL ⊔ SC))))))).
Definition hb := (sb ⊔ sw)^+.
Definition sbl := sb ⊓ !loc.
Definition hbl := hb ⊓ loc.
Definition scb := sb ⊔ (sbl ⋅ (hb ⋅ sbl) ⊔ (hbl ⊔ (mo ⊔ rb))).
Definition pscb := (diagonal SC ⊔ diagonal (F ⊓ SC) ⋅ (hb ⊔ 1)) ⋅ (scb ⋅ (diagonal SC ⊔ (hb ⊔ 1) ⋅ diagonal (F ⊓ SC))).
Definition pscf := diagonal (F ⊓ SC) ⋅ ((hb ⊔ hb ⋅ (eco ⋅ hb)) ⋅ diagonal (F ⊓ SC)).
Definition psc := pscb ⊔ pscf.
Definition cnf := (cartesian W top ⊔ cartesian top W) ⊓ loc ⊓ !(cartesian IW top ⊔ cartesian top IW).
Definition dr := cnf ⊓ ext ⊓ !(hb ⊔ (hb° ⊔ cartesian A A)).
Definition co0_0 := hb ⋅ eco ⊔ (hb ⊔ myrmw ⋅ eco).
Definition at0 := myrmw ⊓ rb ⋅ mo.
Definition sc0 := psc^* ⊓ diagonal E.
Definition th0 := (sb ⊔ rf)^* ⊓ diagonal E.
Definition Dr := is_empty dr.
Definition coherence1 := irreflexive (hb ⋅ (eco ⊔ 1)).
Definition coherencermw := irreflexive (myrmw ⋅ eco).
Definition atomicity := is_empty (myrmw ⊓ rb ⋅ mo).
Definition SC_0 := acyclic psc.
Definition no_thin_air := acyclic (sb ⊔ rf).
Definition witness_conditions := generate_cos cobase co.
Definition model_conditions := Dr /\ (coherence1 /\ (coherencermw /\ (atomicity /\ (SC_0 /\ no_thin_air)))).
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo unknown_set unknown_relation M emptyset classes_loc A ACQ ACQ_REL E REL RLX SC rmw tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW generate_orders generate_cos cobase coi coe fr fri fre mo sb myrmw rb eco rs sw hb sbl hbl scb pscb pscf psc cnf dr co0_0 at0 sc0 th0 Dr coherence1 coherencermw atomicity SC_0 no_thin_air witness_conditions model_conditions : cat.

Definition valid (c : candidate) :=
  exists co : relation (events c),
    witness_conditions c co /\
    model_conditions c co.

(* End of translation of model RC11 *)
