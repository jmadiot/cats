(** Start of prelude for coq translation of .cat files *)
From Coq Require Import Ensembles List String RelationClasses.
(** This prelude uses definitions from RelationAlgebra *)
From RelationAlgebra Require Import all.

Definition set := Ensemble.
Definition relation A := hrel A A.

Class SetLike A :=
  { union : A -> A -> A;
    intersection : A -> A -> A;
    diff : A -> A -> A;
    universal : A;
    incl : A -> A -> Prop }.

Instance SetLike_set (A : Type) : SetLike (set A) :=
  {| union := Union A;
     intersection := Intersection A;
     diff := Setminus A;
     universal := Full_set A;
     incl := Included A |}.

Instance SetLike_relation (A : Type) : SetLike (relation A) :=
  {| union := cup;
     intersection := cap;
     diff := fun R S => cap R (neg S);
     universal := top;
     incl := leq |}.

Definition complement {A} `{SetLike A} (x : A) := diff universal x.

Definition empty {A} `{SetLike A} : A := diff universal universal.

Definition is_empty {A} `{SetLike A} (x : A) : Prop := incl x (diff universal universal).

Definition rel_seq {A} : relation A -> relation A -> relation A := dot A A A.

Definition rel_inv {A} : relation A -> relation A := cnv A A.

Definition cartesian {A} : set A -> set A -> relation A := fun X Y x y => X x /\ Y y.

Definition id {A} : relation A := eq.

Definition domain {A} : relation A -> set A := fun R x => exists y, R x y.

Definition range {A} : relation A -> set A := fun R y => exists x, R x y.

Definition irreflexive {A} (R : relation A) := forall x, ~R x x.

Notation refl_clos := (fun R => union R id) (only parsing).

Notation trans_clos := (hrel_str _) (only parsing).

Notation refl_trans_clos := (hrel_itr _) (only parsing).

Definition acyclic {A} (R : relation A) := incl (intersection (trans_clos R) id) empty.

Class StrictTotalOrder {A} (R : relation A) :=
  { StrictTotalOrder_Strict :> StrictOrder R;
    StrictTotalOrder_Total : forall a b, a <> b -> (R a b \/ R b a) }.

Definition linearisations {A} (X : set A) (R : relation A) : set (relation A) :=
  fun S => StrictTotalOrder S /\ incl R S.

Definition set_flatten {A} : set (set A) -> set A := fun xss x => exists xs, xss xs /\ xs x.

Definition map {A B} (f : A -> B) (X : set A) : set B := fun y => exists x, X x /\ y = f x.

Definition co_locs {A} (pco : relation A) (wss : set (set A)) : set (set (relation A)) :=
  map (fun ws => linearisations ws pco) wss.

Definition cross {A} (Si : set (set (relation A))) : set (relation A) :=
  fun ei : relation A => exists (l : list (relation A)) (L : list (set (relation A))),
      (forall x y, ei x y <-> exists e, In e l /\ e x y) /\
      (forall X, Si X <-> In X L) /\
      Forall2 (fun ei Si => Si ei) l L.

Definition diagonal {A} : set A -> relation A := fun X x y => X x /\ x = y.

Declare Scope cat_scope.
Notation " [ x ] " := (diagonal x) : cat_scope.

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
Hint Unfold union intersection diff universal incl SetLike_set SetLike_relation rel_seq rel_inv : cat_defs.

(** End of prelude *)
