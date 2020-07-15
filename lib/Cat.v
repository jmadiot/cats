(** Start of prelude for coq translation of .cat files, using
    definitions from RelationAlgebra *)
From Coq Require Import Ensembles List String Relations RelationClasses Classical.
From RelationAlgebra Require Import lattice kat.
From Catincoq Require Import proprel.

Notation set := dpset.
Definition relation A := dprop_hrel A A.

Definition union `{lattice.ops} := cup.
Definition intersection `{lattice.ops} := cap.
Definition complement `{lattice.ops} := neg.
Definition diff `{lattice.ops} := fun x y => cap x (neg y).
Definition incl `{lattice.ops} := leq.

Definition empty `{lattice.ops} := bot.
Definition is_empty `{lattice.ops} (x : car _) := x ≦ bot.
Definition rel_seq {A} : relation A -> relation A -> relation A := dot A A A.
Definition rel_inv {A} : relation A -> relation A := cnv A A.
Definition cartesian {A} (X Y : dpset A) : relation A := [X] ⋅ top ⋅ [Y].
Definition id {A} : relation A := 1.

Definition dprop_of_prop (P : Prop) : dprop := exist _ P (classic P).
Definition domain {A} : relation A -> dpset A := fun R x => dprop_of_prop (exists y, R x y).
Definition range  {A} : relation A -> dpset A := fun R y => dprop_of_prop (exists x, R x y).

Definition irreflexive {A} (R : relation A) := cap R 1 ≦ bot.

Notation refl_clos := (fun R => cap R 1) (only parsing).
Notation trans_clos := (dprop_hrel_itr _) (only parsing).
Notation refl_trans_clos := (dprop_hrel_str _) (only parsing).

Definition Ensemble_of_dpset {A} (X : dpset A) : Ensemble A := fun a => proj1_sig (X a).

Definition acyclic {A} (R : relation A) := leq (cap (itr _ R) 1) bot.

Class StrictTotalOrder {A} (R : relation A) :=
  { StrictTotalOrder_Strict :> StrictOrder R;
    StrictTotalOrder_Total : forall a b, a <> b -> (R a b \/ R b a) }.

Class StrictTotalOrder_on {A} (E : Ensemble A) (R : relation A) :=
  { StrictTotalOrder_on_Strict :> StrictOrder R;
    StrictTotalOrder_on_Total : forall a b, a <> b -> (E a /\ E b) <-> (R a b \/ R b a) }.

Definition strict_total_order_on {A}  (E : dpset A) (R : relation A) :=
  R ⊓ 1 ≦ 0 /\
  R ⋅ R ≦ R /\
  R ≦ [E] ⋅ R ⋅ [E] /\
  [E] ⋅ !1 ⋅ [E] ≦ R ⊔ R°.

Definition linearisations {A} (E : dpset A) (R : relation A) : Ensemble (relation A) :=
  fun S => strict_total_order_on E S /\ [E] ⋅ R ⋅ [E] ≦ S.

Definition linearisations_for_co_locs {A} (X : Ensemble A) (R : relation A) : Ensemble (relation A) :=
  fun S => StrictTotalOrder S /\ incl R S.

Definition set_flatten {A} : Ensemble (Ensemble A) -> Ensemble A := fun xss x => exists xs, xss xs /\ xs x.

Definition subset_image {A B} (f : A -> B) (X : Ensemble A) : Ensemble B := fun y => exists x, X x /\ y = f x.

Definition co_locs {A} (pco : relation A) (wss : Ensemble (Ensemble A)) : Ensemble (Ensemble (relation A)) :=
  subset_image (fun ws => linearisations_for_co_locs ws pco) wss.

Definition cross {A} (Si : Ensemble (Ensemble (relation A))) : Ensemble (relation A) :=
  fun ei : relation A => exists (l : list (relation A)) (L : list (Ensemble (relation A))),
      (forall x y, ei x y <-> exists e, In e l /\ e x y) /\
      (forall X, Si X <-> In X L) /\
      Forall2 (fun ei Si => Si ei) l L.

Definition diagonal {A} : dpset A -> relation A := fun X => [X].

(* Execution given as an argument to the model *)

Definition finite (X : Type) := exists l : list X, forall x : X, List.In x l.

Record candidate :=
  {
    (* Documentation for names:
       http://diy.inria.fr/doc/herd.html#language:identifier *)
    events : Type;
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

    finite_events : finite events;
    rf_wr : rf ≦ [W] ⋅ rf ⋅ [R];
    po_iw : po ≦ [!IW] ⋅ po ⋅ [!IW];
    iw_w : IW ≦ W;
    iw_uniq : [IW] ⋅ loc ⋅ [IW] ≦ 1;
    r_iw : R ⊓ IW ≦ bot;
    fw_w : FW ≦ W;
    iw_fw : [IW ⊓ FW] ⋅ loc ⋅ [W] ≦ top ⋅ [IW ⊓ FW];
    rf_loc : rf ≦ loc;
    r_rf : [R] ≦ top ⋅ rf;
    rf_uniq : rf ⋅ rf° ≦ 1;
    loc_refl : Reflexive loc;
    loc_sym : Symmetric loc;
    loc_trans : Transitive loc;
  }.

Hint Unfold events W R IW FW B RMW F
     po addr data ctrl rmw amo rf loc ext int
     unknown_set unknown_relation
     finite_events
     rf_wr (* TODO can we remove those hints *)
     po_iw
     iw_w
     iw_uniq
     rf_loc
     r_rf
     rf_uniq
  : cat_record.

Hint Unfold union intersection diff incl rel_seq rel_inv : cat_defs.
