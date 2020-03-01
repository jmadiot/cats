(* This file is an automatic translation, the licence of the source can be found here: *)
(* https://github.com/herd/herdtools7/blob/master/LICENSE.txt *)
(* Translation of model C++11 *)
From Coq Require Import Relations Ensembles String.
From RelationAlgebra Require Import lattice prop monoid rel kat.
From Catincoq Require Import Cat proprel.
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
Definition unknown_set := unknown_set c.
Definition unknown_relation := unknown_relation c.
Definition M := R ⊔ W.
Definition emptyset : set events := empty.
Definition classes_loc : set events -> Ensemble (Ensemble events) := fun S Si => (forall x, Si x -> Ensemble_of_dpset S x) /\ forall x y, Si x -> Si y -> loc x y.
Definition A := unknown_set "A".
Definition ACQ := unknown_set "ACQ".
Definition ACQ_REL := unknown_set "ACQ_REL".
Definition CON := unknown_set "CON".
Definition I := unknown_set "I".
Definition LK := unknown_set "LK".
Definition LS := unknown_set "LS".
Definition REL := unknown_set "REL".
Definition SC := unknown_set "SC".
Definition UL := unknown_set "UL".
Definition coi := unknown_relation "coi".
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
Definition mobase := co0.
Variable mo : relation events.
Definition moi := mo ⊓ int.
Definition moe := mo ⊓ ext.
Definition co := mo.
Definition coe := moe.
Definition coi_0 := coi.
Definition fr := rf° ⋅ mo ⊓ !id.
Definition fri := fr ⊓ int.
Definition fre := fr ⊓ ext.
Definition crit := let Mutex := LS ⊔ UL in let poMutex := po_loc ⊓ [Mutex] ⋅ top ⋅ [Mutex] in po_loc ⊓ [LS] ⋅ top ⋅ [UL] ⊓ !(poMutex ⋅ poMutex).
Variable loLL : relation events.
Definition loLU := (loLL ⊔ 1) ⋅ crit.
Definition loUL := crit° ⋅ loLL.
Definition lo := (loLL ⊔ (loLU ⊔ loUL))^+.
Definition asw := [I] ⋅ top ⋅ [(M ⊓ !I)].
Definition sb := po.
Definition mo_0 := co.
Definition cacq := ACQ ⊔ (SC ⊓ (R ⊔ F) ⊔ (ACQ_REL ⊔ F ⊓ CON)).
Definition crel := REL ⊔ (SC ⊓ (W ⊔ F) ⊔ ACQ_REL).
Definition ccon := R ⊓ CON.
Definition fr_0 := rf° ⋅ mo_0.
Definition dd := (data ⊔ addr)^+.
Definition fsb := sb ⊓ [F] ⋅ top ⋅ [top].
Definition sbf := sb ⊓ [top] ⋅ top ⋅ [F].
Definition rs_prime := int ⊔ [top] ⋅ top ⋅ [(R ⊓ W)].
Definition rs := mo_0 ⊓ rs_prime ⊓ !((mo_0 ⊓ !rs_prime) ⋅ mo_0).
Definition swra := ext ⊓ toid crel ⋅ ((fsb ⊔ 1) ⋅ (toid (A ⊓ W) ⋅ ((rs ⊔ 1) ⋅ (rf ⋅ (toid (R ⊓ A) ⋅ ((sbf ⊔ 1) ⋅ toid cacq)))))).
Definition swul := ext ⊓ toid UL ⋅ (lo ⋅ toid LK).
Definition pp_asw := asw ⊓ !(asw ⋅ sb).
Definition sw := pp_asw ⊔ (swul ⊔ swra).
Definition cad := (rf ⊓ sb ⊔ dd)^+.
Definition dob := (ext ⊓ toid (W ⊓ crel) ⋅ ((fsb ⊔ 1) ⋅ (toid (A ⊓ W) ⋅ ((rs ⊔ 1) ⋅ (rf ⋅ toid ccon))))) ⋅ (cad ⊔ 1).
Definition ithbr := sw ⊔ (dob ⊔ sw ⋅ sb).
Definition ithb := (ithbr ⊔ sb ⋅ ithbr)^+.
Definition hb := sb ⊔ ithb.
Definition Hb := acyclic hb.
Definition hbl := hb ⊓ loc.
Definition Coh := irreflexive ((rf° ⊔ 1) ⋅ (mo_0 ⋅ ((rf ⊔ 1) ⋅ hb))).
Definition vis := hbl ⊓ [W] ⋅ top ⋅ [R] ⊓ !(hbl ⋅ (toid W ⋅ hbl)).
Definition Rf := irreflexive (rf ⋅ hb).
Definition NaRf := is_empty (rf ⋅ [(R ⊓ !A)] ⊓ !vis).
Definition NaRf_0 := is_empty ([(FW ⊓ !A)] ⋅ (hbl ⋅ [W])).
Definition Rmw := irreflexive (rf ⊔ (mo_0 ⋅ (mo_0 ⋅ rf°) ⊔ mo_0 ⋅ rf)).
Definition Lo1 := irreflexive (lo ⋅ hb).
Definition Lo2 := irreflexive (toid LS ⋅ (lo° ⋅ (toid LS ⋅ !(lo ⋅ (toid UL ⋅ lo))))).
Definition Mutex := UL ⊔ LS.
Definition cnf := ([W] ⋅ top ⋅ [top] ⊔ [top] ⋅ top ⋅ [W]) ⊓ loc ⊓ !([Mutex] ⋅ top ⋅ [top] ⊔ [top] ⋅ top ⋅ [Mutex]).
Definition dr := ext ⊓ (cnf ⊓ !hb ⊓ !hb° ⊓ !([A] ⋅ top ⋅ [A])).
Definition ur := int ⊓ (([W] ⋅ top ⋅ [M] ⊔ [M] ⋅ top ⋅ [W]) ⊓ (loc ⊓ (!id ⊓ (!sb^+ ⊓ !(sb^+)°)))).
Definition bl := toid LS ⋅ ((sb ⊓ lo) ⋅ toid LK) ⊓ !(lo ⋅ (toid UL ⋅ lo)).
Definition losbwoul := sb ⊓ (lo ⊓ !(lo ⋅ (toid UL ⋅ lo))).
Definition lu := toid UL ⊓ !(toid UL ⋅ (losbwoul° ⋅ (toid LS ⋅ (losbwoul ⋅ toid UL)))).
Definition witness_conditions := generate_orders (W ⊓ (A ⊔ I)) mobase mo /\ generate_orders LS po loLL.
Definition model_conditions := Hb /\ (Coh /\ (Rf /\ (NaRf /\ (NaRf_0 /\ (Rmw /\ (Lo1 /\ Lo2)))))).
End Model.

Hint Unfold events R W IW FW B RMW F rf po int ext loc addr data ctrl amo unknown_set unknown_relation M emptyset classes_loc A ACQ ACQ_REL CON I LK LS REL SC UL coi tag2events emptyset_0 partition tag2instrs po_loc rfe rfi co0 toid fencerel ctrlcfence imply nodetour singlestep LKW generate_orders generate_cos mobase moi moe co coe coi_0 fr fri fre crit loLU loUL lo asw sb mo_0 cacq crel ccon fr_0 dd fsb sbf rs_prime rs swra swul pp_asw sw cad dob ithbr ithb hb Hb hbl Coh vis Rf NaRf NaRf_0 Rmw Lo1 Lo2 Mutex cnf dr ur bl losbwoul lu witness_conditions model_conditions : cat.

Definition valid (c : candidate) :=
  exists mo loLL : relation (events c),
    witness_conditions c mo loLL /\
    model_conditions c mo loLL.

(* End of translation of model C++11 *)
