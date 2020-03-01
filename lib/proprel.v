(** * Decidable propositions as a bounded distributive lattice *)

From RelationAlgebra Require Import lattice kat.
From RelationAlgebra Require Export prop.

Definition dprop := { P : Prop | P \/ ~P }.

Definition dprop_impl : dprop -> dprop -> Prop :=
  fun P Q => proj1_sig P -> proj1_sig Q.

Definition dprop_iff : dprop -> dprop -> Prop :=
  fun P Q => proj1_sig P <-> proj1_sig Q.

Program Definition dprop_or : dprop -> dprop -> dprop :=
  fun P Q => exist _ (proj1_sig P \/ proj1_sig Q) ltac:(destruct P, Q; simpl; intuition eauto).

Program Definition dprop_and : dprop -> dprop -> dprop :=
  fun P Q => exist _ (proj1_sig P /\ proj1_sig Q) ltac:(destruct P, Q; simpl; intuition eauto).

Program Definition dprop_not : dprop -> dprop :=
  fun P => exist _ (~proj1_sig P) ltac:(destruct P; simpl; intuition eauto).

Program Definition dprop_False : dprop :=
  exist _ False ltac:(intuition).

Program Definition dprop_True : dprop :=
  exist _ True ltac:(intuition).

(** Lattice operations *)

Canonical Structure dprop_lattice_ops: lattice.ops := {|
  leq := dprop_impl;
  weq := dprop_iff;
  cup := dprop_or;
  cap := dprop_and;
  neg := dprop_not;
  bot := dprop_False;
  top := dprop_True
|}.

Instance dprop_lattice_laws: lattice.laws (BDL+STR+CNV+DIV) dprop_lattice_ops.
Proof.
  constructor; [ constructor | .. ].
  all: repeat intros []; compute in *; try tauto.
Qed.

(** * rel: the main model of heterogeneous binary relations *)

Set Printing Universes.

(** We fix a type universe U and show that heterogeneous relations
between types in this universe form a kleene algebra.  *)

Universe U.
Definition hrel (n m: Type@{U}) := n -> m -> Prop.

(** * Relations as a (bounded, distributive) lattice *)

(** lattice operations and laws are obtained for free, by two
   successive pointwise liftings of the [Prop] lattice *)

Canonical Structure hrel_lattice_ops n m :=
  lattice.mk_ops (hrel n m) leq weq cup cap neg bot top.

Global Instance hrel_lattice_laws n m:
  lattice.laws (BDL+STR+CNV+DIV) (hrel_lattice_ops n m) := pw_laws _.

(** * Relations as a residuated Kleene allegory *)

Section RepOps.
  Implicit Types n m p : Type@{U}.

(** relational composition *)
Definition hrel_dot n m p (x: hrel n m) (y: hrel m p): hrel n p :=
  fun i j => exists2 k, x i k & y k j.

(** converse (or transpose) *)
Definition hrel_cnv n m (x: hrel n m): hrel m n :=
  fun i j => x j i.

(** left / right divisions *)
Definition hrel_ldv n m p (x: hrel n m) (y: hrel n p): hrel m p :=
  fun i j => forall k, x k i -> y k j.

Definition hrel_rdv n m p (x: hrel m n) (y: hrel p n): hrel p m :=
  fun j i => forall k, x i k -> y j k.

Section i.
  Variable n: Type@{U}.
  Variable x: hrel n n.
  (** finite iterations of a relation *)
  Fixpoint iter u := match u with O => @eq _ | S u => hrel_dot _ _ _ x (iter u) end.
  (** Kleene star (reflexive transitive closure) *)
  Definition hrel_str: hrel n n := fun i j => exists u, iter u i j.
  (** strict iteration (transitive closure) *)
  Definition hrel_itr: hrel n n := hrel_dot n n n x hrel_str.
End i.

End RepOps.

(** packing all operations into a monoid; note that the unit on [n] is
   just the equality on [n], i.e., the identity relation on [n] *)

(** We need to eta-expand @eq here. This generates the universe
constraint [U <= Coq.Init.Logic.8] (where the latter is the universe of
the type argument to [eq]). Without the eta-expansion, the definition
would yield the constraint [U = Coq.Init.Logig.8], which is too strong
and leads to universe inconsistencies later on. *)

Canonical Structure hrel_monoid_ops :=
  monoid.mk_ops Type@{U} hrel_lattice_ops hrel_dot (fun n => @eq n) hrel_itr hrel_str hrel_cnv hrel_ldv hrel_rdv.

(** binary relations form a residuated Kleene allegory *)
Instance hrel_monoid_laws: monoid.laws (BDL+STR+CNV+DIV) hrel_monoid_ops.
Proof.
  assert (dot_leq: forall n m p : Type@{U},
   Proper (leq ==> leq ==> leq) (hrel_dot n m p)).
   intros n m p x y H x' y' H' i k [j Hij Hjk]. exists j. apply H, Hij. apply H', Hjk.
  constructor; (try now left); intros.
   apply hrel_lattice_laws.
   intros i j. firstorder.
   intros i j. firstorder congruence.
   intros i j. firstorder.
   intros i j. reflexivity.
   intros x y E i j. apply E.
   intros i j E. exists O. exact E.
   intros i k [j Hij [u Hjk]]. exists (S u). firstorder.
   assert (E: forall i, (iter n x i: hrel n n) ⋅ z ≦ z).
    induction i. simpl. firstorder now subst.
    rewrite <-H0 at 2. transitivity (x⋅((iter n x i: hrel n n)⋅z)).
     simpl. firstorder congruence. now apply dot_leq.
    intros i j [? [? ?] ?]. eapply E. repeat eexists; eauto.
   reflexivity.
   intros i k [[j Hij Hjk] Hik]. exists j; trivial. split; firstorder.
   split. intros E i j [k Hik Hkj]. apply E in Hkj. now apply Hkj.
    intros E i j Hij k Hki. apply E. firstorder.
   split. intros E i j [k Hik Hkj]. apply E in Hik. now apply Hik.
    intros E i j Hij k Hki. apply E. firstorder.
Qed.


(** * Relations as a Kleene algebra with decidable prop tests *)

(** "decidable" sets or predicates: functions to decidable prop *)

Definition dpset: ob hrel_monoid_ops -> lattice.ops := fun Y => pw_ops dprop_lattice_ops Y.

(** injection of decidable prop predicates into relations, as sub-identities *)
Definition hrel_dpset_inj n (x: dpset n): hrel n n := fun i j => i=j /\ proj1_sig (x i).

(** packing relations and decidable prop sets as a Kleene algebra with tests *)

Canonical Structure hrel_dpset_kat_ops :=
  kat.mk_ops hrel_monoid_ops dpset hrel_dpset_inj.


Lemma iter_S {n} {x : hrel_dpset_kat_ops n n} {i} :
  forall a c,
    iter n x (S i) a c -> exists b, iter n x i a b /\ x b c.
Proof.
  induction i; intros a c it.
  - exists a. compute. destruct it as [x0 H <-]; auto.
  - destruct it as [d ad dc]. apply IHi in dc. firstorder.
Qed.

Constraint U < pw.
Instance hrel_dpset_kat_laws: kat.laws hrel_dpset_kat_ops.
Proof.
  constructor.
  - constructor.
    1: now apply lower_laws.
    all: try solve [compute; firstorder].
    + intros n m x a b. split. intros [c <- H]; auto. intros H. exists a; firstorder.
    + right. intros n m x a b. split. intros [c H <-]; auto. intros H. exists b; firstorder.
    + intros _ n x a a_ <-. exists O. reflexivity.
    + intros _ n x a c [b ab [i bc]]. exists (S i), b; auto.
    + intros H n m x z e a c [b [i ab] bc]. revert a ab. induction i; intros a ab.
      * rewrite ab; auto.
      * apply e. destruct ab as [a' aa' a'b]. exists a'; eauto.
    + intros _; right; right.
      intros n m x z e a c [b ab [i bc]].
      revert a b c ab bc. induction i; intros a b c ab bc.
      * rewrite <-bc; auto.
      * apply e. destruct (iter_S _ _ bc) as (b' & bb' & b'c). exists b'; eauto.
  - intros A; constructor; try firstorder.
    intros _ x a; split; compute; auto. destruct (x a); tauto.
  - intros A. constructor; repeat intro; compute in *; discriminate || firstorder.
  - intros A. constructor; repeat intro; compute in *; discriminate || firstorder.
  - intros A x y a b; split.
    + intros [<- ?]; exists a; firstorder.
    + intros [c [<- ?] [<- ?]]. firstorder.
Qed.

(** * Functional relations  *)

Definition frel {A B: Set} (f: A -> B): hrel A B := fun x y => y = f x.

Lemma frel_comp {A B C: Set} (f: A -> B) (g: B -> C): frel f ⋅ frel g ≡ frel (fun x => g (f x)).
Proof.
  apply antisym. intros x z [y -> ->]. reflexivity.
  simpl. intros x z ->. eexists; reflexivity.
Qed.

Instance frel_weq {A B}: Proper (pwr eq ==> weq) (@frel A B).
Proof. unfold frel; split; intros ->; simpl. apply H. apply eq_sym, H. Qed.
