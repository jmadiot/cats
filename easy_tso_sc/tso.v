(* Translation of model TSO *)
From Coq Require Import Relations String.
Require Import Cat.
Section Model.
Variable c : candidate.
Definition events := events c.
Instance SetLike_set_events : SetLike (set events) := SetLike_set events.
Instance SetLike_relation_events : SetLike (relation events) := SetLike_relation events.
Definition R := R c.
Definition W := W c.
Definition IW := IW c.
Definition FW := FW c.
Definition rf := rf c.
Definition po := po c.
Definition ext := ext c.
Definition loc := loc c.
Definition unknown_set := unknown_set c.
Definition M := union R W.
Definition classes_loc : set events -> set (set events) := fun S Si => forall x y, Si x -> Si y -> loc x y.
Definition MFENCE := unknown_set "MFENCE".
Definition partition := classes_loc.
Definition po_loc := intersection po loc.
Definition rfe := intersection rf ext.
Definition co0 := intersection loc (union (cartesian IW (diff W IW)) (cartesian (diff W FW) FW)).
Definition A := union ((*failed: try X with empty : (set _)*) empty : (set _)) ((*failed: try A with empty : (set _)*) empty : (set _)).
(* Definition of co_locs already included in the prelude *)
(* Definition of cross already included in the prelude *)
Definition generate_orders s pco := cross (co_locs pco (partition s)).
Definition generate_cos pco := generate_orders W pco.
Definition invrf_0 := rel_inv rf.
Definition cobase := co0.
Variable co : relation events.
Definition fr := diff (rel_seq invrf_0 co) id.
Definition test := acyclic (union po_loc (union rf (union fr co))).
Definition poWR := rel_seq (diagonal W) (rel_seq po (diagonal R)).
Definition i1 := rel_seq poWR (diagonal A).
Definition i2 := rel_seq (diagonal A) poWR.
Definition implied := union i1 i2.
Definition ppo := union (rel_seq (diagonal R) (rel_seq po (diagonal R))) (union (rel_seq (diagonal M) (rel_seq po (diagonal W))) (union (rel_seq (diagonal M) (rel_seq po (rel_seq (diagonal MFENCE) (rel_seq po (diagonal M))))) implied)).
Definition ghb := union ppo (union rfe (union fr co)).
Definition tso := acyclic ghb.
Definition witness_conditions := generate_cos cobase co.
Definition model_conditions := test /\ tso.
(* Informations on the translation from cat to coq:

The following set of variables is only used inside try/with's before
any definition:
  A, X
the corresponding try/with's failed. Use the option -defined
id1,id2,... to make the corresponding ones succeed instead.

The following set of variables is used but is neither defined in the
prelude nor provided by the candidate:
  MFENCE

The following renamings occurred:
  invrf -> invrf_0
 *)
End Model.

Hint Unfold SetLike_set_events SetLike_relation_events events R W IW FW rf po ext loc unknown_set M classes_loc MFENCE partition po_loc rfe co0 A generate_orders generate_cos invrf_0 cobase fr test poWR i1 i2 implied ppo ghb tso witness_conditions model_conditions : cat.

Definition valid (c : candidate) := 
  exists co : relation (events c),
    witness_conditions c co /\
    model_conditions c co.

(* End of translation of model TSO *)
