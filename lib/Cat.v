(** Start of prelude for coq translation of .cat files, using
    definitions from RelationAlgebra *)
From Coq Require Import Ensembles List String Relations RelationClasses Classical.
From RelationAlgebra Require Import lattice kat.
From Catincoq Require Import proprel.

Definition set := dpset.
Definition relation A := hrel A A.

Definition union `{lattice.ops} := cup.
Definition intersection `{lattice.ops} := cap.
Definition complement `{lattice.ops} := neg.
Definition diff `{lattice.ops} x y := cap x (neg y).
Definition incl `{lattice.ops} := leq.

Definition empty `{lattice.ops} := bot.
Definition is_empty `{ops : lattice.ops} (x : car ops) := x ≦ bot.
Definition rel_seq {A} : relation A -> relation A -> relation A := dot A A A.
Definition rel_inv {A} : relation A -> relation A := cnv A A.
Definition cartesian {A} : dpset A -> dpset A -> relation A :=
  fun X Y x y => proj1_sig (X x) /\ proj1_sig (Y y).
Definition id {A} : relation A := 1.

Definition dprop_of_prop (P : Prop) : dprop := exist _ P (classic P).
Definition domain {A} : relation A -> dpset A := fun R x => dprop_of_prop (exists y, R x y).
Definition range  {A} : relation A -> dpset A := fun R y => dprop_of_prop (exists x, R x y).

Definition irreflexive {A} (R : relation A) := cap R 1 ≦ bot.

Notation refl_clos := (fun R => cap R 1) (only parsing).
Notation trans_clos := (hrel_itr _) (only parsing).
Notation refl_trans_clos := (hrel_str _) (only parsing).

Definition Ensemble_of_dpset {A} (X : dpset A) : Ensemble A := fun a => proj1_sig (X a).

Definition acyclic {A} (R : relation A) := leq (cap (itr _ R) 1) bot.

Class StrictTotalOrder {A} (R : relation A) :=
  { StrictTotalOrder_Strict :> StrictOrder R;
    StrictTotalOrder_Total : forall a b, a <> b -> (R a b \/ R b a) }.

Definition linearisations {A} (X : dpset A) (R : relation A) : Ensemble (relation A) :=
  fun S => StrictTotalOrder S /\ incl R S.

Definition linearisations_for_co_locs {A} (X : Ensemble A) (R : relation A) : Ensemble (relation A) :=
  fun S => StrictTotalOrder S /\ incl R S.

Definition set_flatten {A} : Ensemble (Ensemble A) -> Ensemble A := fun xss x => exists xs, xss xs /\ xs x.

Definition map {A B} (f : A -> B) (X : Ensemble A) : Ensemble B := fun y => exists x, X x /\ y = f x.

Definition co_locs {A} (pco : relation A) (wss : Ensemble (Ensemble A)) : Ensemble (Ensemble (relation A)) :=
  map (fun ws => linearisations_for_co_locs ws pco) wss.

Definition cross {A} (Si : Ensemble (Ensemble (relation A))) : Ensemble (relation A) :=
  fun ei : relation A => exists (l : list (relation A)) (L : list (Ensemble (relation A))),
      (forall x y, ei x y <-> exists e, In e l /\ e x y) /\
      (forall X, Si X <-> In X L) /\
      Forall2 (fun ei Si => Si ei) l L.

Definition diagonal {A} : dpset A -> relation A := fun X => [X].

(* Execution given as an argument to the model *)

Record candidate :=
  {
    (* Documentation for names:
       http://diy.inria.fr/doc/herd.html#language:identifier *)
    events : Set;
    W   : set events; (* read events *)
    R   : set events; (* write events *)
    IW  : set events; (* initial writes *)
    FW  : set events; (* final writes *)
    B   : set events; (* branch events *)
    RMW : set events; (* read-modify-write events *)
    F   : set events; (* fence events *)

    po  : relation events; (* program order *)
    addr: relation events; (* address dependency *)
    data: relation events; (* data dependency *)
    ctrl: relation events; (* control dependency *)
    rmw : relation events; (* read-exclusive write-exclusive pair *)
    amo : relation events; (* atomic modify *)

    rf  : relation events; (* read-from *)
    loc : relation events; (* same location *)
    ext : relation events; (* external *)
    int : relation events; (* internal *)

    (* Two functions for unknown sets or relations that are found in
    .cat files. cat2coq uses [unknown_set "ACQ"] when translating
    some parts of cat files about C11 *)
    unknown_set : string -> set events;
    unknown_relation : string -> relation events;
  }.

Hint Unfold events W R IW FW B RMW F po addr data ctrl rmw amo rf loc ext int unknown_set unknown_relation : cat_record.
Hint Unfold union intersection diff incl rel_seq rel_inv : cat_defs.
