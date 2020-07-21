(** Start of prelude for coq translation of .cat files, using
    definitions from RelationAlgebra *)
From Coq Require Import Ensembles List String Relations RelationClasses Classical.
From RelationAlgebra Require Import lattice kat.
From Catincoq Require Import proprel.
From Catincoq Require Export defs.

Definition union `{lattice.ops} := cup.
Definition intersection `{lattice.ops} := cap.
Definition complement `{lattice.ops} := neg.
Definition diff `{lattice.ops} := fun x y => cap x (neg y).
Definition incl `{lattice.ops} := leq.

Definition empty `{lattice.ops} := bot.
Definition is_empty `{lattice.ops} (x : car _) := x ≦ bot.
Definition rel_seq {A} : relation A -> relation A -> relation A := dot A A A.
Definition rel_inv {A} : relation A -> relation A := cnv A A.
Definition cartesian {A} (X Y : set A) : relation A := [X] ⋅ top ⋅ [Y].
Definition id {A} : relation A := 1.

Definition domain {A} : relation A -> set A := fun R x => exists y, R x y.
Definition range  {A} : relation A -> set A := fun R y => exists x, R x y.

Notation refl_clos := (fun R => cap R 1) (only parsing).
Notation trans_clos := (hrel_itr _) (only parsing).
Notation refl_trans_clos := (hrel_str _) (only parsing).

Class StrictTotalOrder {A} (R : relation A) :=
  { StrictTotalOrder_Strict :> StrictOrder R;
    StrictTotalOrder_Total : forall a b, a <> b -> (R a b \/ R b a) }.

Class StrictTotalOrder_on {A} (E : set A) (R : relation A) :=
  { StrictTotalOrder_on_Strict :> StrictOrder R;
    StrictTotalOrder_on_Total : forall a b, a <> b -> (E a /\ E b) <-> (R a b \/ R b a) }.

Definition linearisations {A} := @linear_extension_on A.

(** [partition equiv X] splits [X] into the set of sets [Xi] that are
each included in an equivalence class of the relation [equiv]. It also
filters out empty sets, which we implement below with Inhabited *)

Definition partition {A} (equiv : relation A) (E F : Ensemble A) : Prop :=
  Inhabited _ F /\
  exists C, equivalence_classes equiv C /\ F = Intersection _ E C.

Definition co_locs {A} (pco : relation A) (wss : Ensemble (set A)) : Ensemble (set (relation A)) :=
  subset_image (fun ws => linear_extension_on ws pco) wss.

Definition cross {A} (S : Ensemble (set (relation A)))
  : Ensemble (relation A)
  := subset_image union_of_relations (one_of_each S).

(* Definition cross {A} (Si : Ensemble (set (relation A))) : set (relation A) :=
  fun ei : relation A => exists (l : list (relation A)) (L : list (set (relation A))),
      (forall x y, ei x y <-> exists e, In e l /\ e x y) /\
      (forall X, Si X <-> In X L) /\
      Forall2 (fun ei Si => Si ei) l L. *)

Definition diagonal {A} : set A -> relation A := fun X => [X].

(* Execution given as an argument to the model *)

Definition finite (X : Type) := exists l : list X, forall x : X, List.In x l.

(* TODO: replace Set with Type below when CoLoR has merged the PR *)

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

    (* Two functions for unknown sets or rels that are found in
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

(* for backward compat, TODO remove when ok to do so *)
Definition Ensemble_of_dpset {A} (E : set A) : Ensemble A := E.
