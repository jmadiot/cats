From Coq Require Import Init.Wf Relations.
From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From Catincoq.lib Require Import proprel defs tactics wf.

(** Relation difference *)

Definition diff {A} (r s : relation A) : relation A := fun x y => r x y /\ ~ s x y.
Infix " \ " := diff (at level 50).

Lemma diff_split {A} (r s : relation A) : r ≡ r \ s ⊔ r ⊓ s.
Proof.
  intros x y. destruct (Classical_Prop.classic (s x y));
  compute; intuition.
Qed.

Instance diff_leq {A} : Proper (leq ==> flip leq ==> leq) (@diff A) := ltac:(firstorder).

(** If a relation [r] is well-founded in both directions, then the
    relation [inside], which can go either way, is, too. We could add
    the fact that [r^+ b c], which would make [inside r] well-founded
    for more relations [r], for example [Z.lt] which is not
    well-founded in either direction *)

Inductive inside {A} (r : relation A) : relation (A * A) :=
  | inside_l  a b c   : r a b ->          inside r (b, c) (a, c)
  | inside_r    b c d :          r c d -> inside r (b, c) (b, d).

Instance inside_leq {A} : Proper (leq ==> leq) (@inside A).
Proof.
  intros r s i p q []; [constructor 1 | constructor 2]; apply i; auto.
Qed.

Instance inside_weq {A} : Proper (weq ==> weq) (@inside A).
Proof.
  intros r s e. apply antisym; apply inside_leq; now rewrite e.
Qed.

Lemma inside_wf {A} (r : relation A) :
  well_founded r -> well_founded r° -> well_founded (inside r).
Proof.
  intros wf fw (a, d). revert a d.
  refine (well_founded_induction fw _ _); intros d IHd.
  refine (well_founded_induction wf _ _); intros a IHa.
  constructor. intros (b, c). inversion 1; subst; eauto.
Qed.

Lemma going_inside_terminates {A} (r : relation A) :
  well_founded (inside r) -> r ≦ (r \ r ⋅ r)^+.
Proof.
  intros wf x y.
  change x with (fst (x, y)).
  change y with (snd (x, y)) at 2 4.
  generalize (x, y) as p; clear x y.
  refine (well_founded_induction wf _ _); intros (a, d) IH.
  simpl fst; simpl snd.
  intros ad; rewrite (diff_split _ (r⋅r)) in ad.
  destruct ad as [ad | (ad & [b ab bd])].
  - rel rewrite <-itr_ext. intuition.
  - rel rewrite <-itr_trans. exists b.
    + refine (IH (a, b) _ ab). now apply inside_r.
    + refine (IH (b, d) _ bd). now apply inside_l.
Qed.

(* It is possible to decompose a relation into the transitive closure
   of its "anti-transitive closure" [r'], where [r'] is [r] from which
   we remove all the steps that can be done in two or more [r] steps.
   It can be thought of as an induction in the following way: to prove
   [r x y -> P x y], it is enough to prove [P x y] only when there are
   no extra [r] steps between [x] and [y] (and also that [P] is
   transitive). We require [r] to be well-founded in both directions,
   otherwise one could split [r] into [r⋅r] infinitely many times, for
   example if [r] is the order defined on [option nat] by [None < Some
   i] and [Some i < Some j] whenever [i < j]. This [r] is well-founded
   but its mirror relation is not. *)

Lemma anti_transitive_induction {A} (r : relation A) :
  well_founded r ->
  well_founded r° ->
  r ≦ (r \ r^+ ⋅ r^+)^+.
Proof.
  intros wf fw.
  apply wf_itr in wf.
  apply wf_itr in fw. rewrite <-cnvitr in fw.
  pose proof inside_wf _ wf fw as wfi.
  pose proof going_inside_terminates _ wfi as i.
  transitivity (r^+). kat.
  rewrite i at 1.
  apply itr_leq.
  assert (r^+ ≡ r ⊔ r^+ ⋅ r^+) as E by kat. rewrite E at 1.
  intros x y; compute; intuition.
Qed.

(** Slightly more general *)

Lemma inside_itr {A} (r : relation A) : inside r^+ ≦ (inside r)^+.
Proof.
  rewrite 2itr_clos_trans, 2clos_trans__1n.
  intros p q i.
  induction i as [a b c ab | b c d cd].
  - induction ab as [a b ab | a a' b aa' a'b IH].
    + constructor 1. constructor 1. auto.
    + apply clos_trans_1n_n1.
      econstructor 2. constructor 1. eauto.
      apply clos_trans_1n_n1, IH.
  - induction cd as [c d cd | c c' d cc' c'd IH].
    + constructor 1. constructor 2. auto.
    + econstructor 2. constructor 2. eauto. auto.
Qed.

Lemma wellfounded_inside_itr {A} (r : relation A) :
  well_founded (inside r) ->
  well_founded (inside r^+).
Proof.
  intros w.
  apply wf_itr in w.
  revert w.
  apply wf_leq, inside_itr.
Qed.

Lemma anti_transitive_induction_inside {A} (r : relation A) :
  well_founded (inside r) ->
  r ≦ (r \ r^+ ⋅ r^+)^+.
Proof.
  intros wfi.
  apply wellfounded_inside_itr in wfi.
  apply going_inside_terminates in wfi.
  transitivity (r^+). kat.
  rewrite wfi at 1.
  apply itr_leq.
  assert (r^+ ≡ r ⊔ r^+ ⋅ r^+) as E by kat. rewrite E at 1.
  intros x y; compute; intuition.
Qed.
