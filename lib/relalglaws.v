From Coq Require Import String Ensembles Sorted Mergesort Permutation Classical_Prop.
From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From Catincoq.lib Require Import defs proprel tactics.

Lemma dotcap1l (l : level) (X : ops) {H : laws l X} {Hl : AL ≪ l} :
  forall (n : ob X) (x y z : X n n),
    x ≦ 1 -> x⋅(y ⊓ z) ≡ x⋅y ⊓ z.
Proof.
  intros n x y z Hx.
  apply antisym.
  - rewrite dotxcap. rewrite Hx at 2. ra.
  - rewrite capdotx. rewrite Hx at 2. ra.
Qed.

Lemma dotcap1r (l : level) (X : ops) {H : laws l X} {Hl : AL ≪ l} :
  forall (n : ob X) (x y z : X n n),
    x ≦ 1 -> (y ⊓ z) ⋅ x ≡ y ⋅ x ⊓ z.
Proof.
  intros n x y z Hx.
  apply antisym.
  - rewrite dotcapx. rewrite Hx at 2. ra.
  - rewrite capxdot. rewrite Hx at 1. ra.
Qed.

Lemma dotcap1 (l : level) (X : ops) {H : laws l X} {Hl : AL ≪ l} :
  forall (n : ob X) (u1 u2 x y : X n n),
    u1 ≦ 1 -> u2 ≦ 1 -> u1 ⋅ (x ⊓ y) ⋅ u2 ≡ u1 ⋅ x ⋅ u2 ⊓ y.
Proof.
  intros n u1 u2 x y H1 H2.
  rewrite dotcap1l, dotcap1r; eauto.
Qed.

Lemma cnv_inj (l : level) (X : kat.ops) {_ : kat.laws X} {_ : laws l X} {_ : CNV ≪ l} :
  forall (n : ob X) (a : tst n), [a]° ≡ [a].
Proof.
Abort (* not provable? *).

(** Below is specific to relations *)

Lemma cnv_inj {X} (a : set X) : [a]° ≡ [a].
Proof.
  compute.
  intros x y. split; intros [? ?]; subst y; firstorder.
Qed.

Lemma dotcap1l_rel {X} (x y z : relation X) :
  x ≦ 1 -> x⋅(y ⊓ z) ≡ x⋅y ⊓ z.
Proof.
  eapply dotcap1l. 2:reflexivity. apply lower_laws.
Qed.

Lemma dotcap1r_rel {X} (x y z : relation X) :
  x ≦ 1 -> (y ⊓ z) ⋅ x ≡ y ⋅ x ⊓ z.
Proof.
  eapply dotcap1r. 2:reflexivity. apply lower_laws.
Qed.

Lemma dotcap1_rel {X} (u1 u2 x y : relation X) :
  u1 ≦ 1 -> u2 ≦ 1 -> u1 ⋅ (x ⊓ y) ⋅ u2 ≡ u1 ⋅ x ⋅ u2 ⊓ y.
Proof.
  eapply dotcap1. 2:reflexivity. apply lower_laws.
Qed.

Lemma cnvtst {A} {E : set A} : [E]° ≡ [E].
Proof.
  intros a b; split; intros [-> Ha]; constructor; auto.
Qed.

Lemma tst_dot {A} (R : relation A) E x y : ([E] ⋅ R) x y <-> E x /\ R x y.
Proof.
  split.
  - intros [x_ [<- e] r]. intuition.
  - exists x; firstorder.
Qed.

Lemma dot_tst {A} (R : relation A) E x y : (R ⋅ [E]) x y <-> R x y /\ E y.
  split.
  - intros [y_ r [<- e]]. intuition.
  - exists y; firstorder.
Qed.

Lemma tst_dot_tst {A} (R : relation A) E E' x y :
  ([E] ⋅ R ⋅ [E']) x y <-> E x /\ R x y /\ E' y.
Proof.
  now rewrite dot_tst, tst_dot.
Qed.

Lemma leq_tst_1 {X} (a : set X) : [a] ≦ (1 : relation X).
Proof.
  compute; intuition eauto.
Qed.

Lemma tst_cap_1 {X} (a : set X) : [a] ≡ [a] ⊓ (1 : relation X).
Proof.
  compute; intuition eauto.
Qed.

Lemma cap_cartes {X} (R : relation X) (a b : set X) : R ⊓ ([a] ⋅ top ⋅ [b]) ≡ [a] ⋅ R ⋅ [b].
Proof.
  destruct_rel.
  exists y; hnf; auto. exists x; hnf; auto.
  split; auto. exists y; hnf; auto. exists x; split; auto.
Qed.

Lemma cap_cartes_l {X} (R : relation X) (a b : set X) : ([a] ⋅ top ⋅ [b]) ⊓ R ≡ [a] ⋅ R ⋅ [b].
Proof.
  destruct_rel.
  exists y; hnf; auto. exists x; hnf; auto.
  split; auto. exists y; hnf; auto. exists x; split; auto.
Qed.

(* TODO unify X/A *)

Lemma dom_rng_char {X} (R : relation X) (a b : set X) : R ≦ [a] ⋅ R ⋅ [b] <-> R ≦ [a] ⋅ top ⋅ [b].
Proof.
  split; intros e x y xy; specialize (e x y xy);
    rewrite tst_dot_tst in *; firstorder.
  constructor.
Qed.
