(* Translation of model SC *)
From Coq Require Import Relations String.
Require Import Cat.
Section Model.
Variable c : candidate.
Definition events := events c.
Instance SetLike_set_events : SetLike (set events) := SetLike_set events.
Instance SetLike_relation_events : SetLike (relation events) := SetLike_relation events.
Definition W := W c.
Definition IW := IW c.
Definition FW := FW c.
Definition rf := rf c.
Definition po := po c.
Definition loc := loc c.
Definition classes_loc : set events -> set (set events) := fun S Si => forall x y, Si x -> Si y -> loc x y.
Definition partition := classes_loc.
Definition co0 := intersection loc (union (cartesian IW (diff W IW)) (cartesian (diff W FW) FW)).
(* Definition of co_locs already included in the prelude *)
(* Definition of cross already included in the prelude *)
Definition generate_orders s pco := cross (co_locs pco (partition s)).
Definition generate_cos pco := generate_orders W pco.
Definition invrf := rel_inv rf.
Definition cobase := co0.
Variable co : relation events.
Definition fr := diff (rel_seq invrf co) id.
Definition sc := acyclic (union po (union fr (union rf co))).
Definition witness_conditions := generate_cos cobase co.
Definition model_conditions := sc.
(* Informations on the translation from cat to coq:


 *)
End Model.

Hint Unfold SetLike_set_events SetLike_relation_events events W IW FW rf po loc classes_loc partition co0 generate_orders generate_cos invrf cobase fr sc witness_conditions model_conditions : cat.

Definition valid (c : candidate) := 
  exists co : relation (events c),
    witness_conditions c co /\
    model_conditions c co.

(* End of translation of model SC *)
