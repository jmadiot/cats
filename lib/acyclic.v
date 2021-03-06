From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From Catincoq.lib Require Import proprel defs Cat tactics relalglaws.

Instance is_empty_leq A : Proper (leq --> impl) (is_empty : relation A -> _).
Proof.
  intros R S H. unfold is_empty.
  compute in *. firstorder. eauto.
Qed.

Instance is_empty_weq A : Proper (weq --> iff) (is_empty : relation A -> _).
Proof.
  intros R S H. split; apply is_empty_leq; compute in *; apply H.
Qed.

Lemma irreflexive_leq A (R S : relation A) : R ≦ S -> irreflexive S -> irreflexive R.
Proof.
  intros H. unfold irreflexive. compute in *; firstorder.
Qed.

Lemma irreflexive_weq A (R S : relation A) : R ≡ S -> irreflexive S <-> irreflexive R.
Proof.
  intros H; split; apply irreflexive_leq; rewrite H; auto.
Qed.

Instance irreflexive_leq_ A : Proper (leq --> impl) (@irreflexive A).
Proof.
  intros x y i a. eapply irreflexive_leq; eauto.
Qed.

Instance irreflexive_weq_ A : Proper (weq --> iff) (@irreflexive A).
Proof.
  intros x y i. split; apply irreflexive_leq; rewrite i; auto.
Qed.

Lemma acyclic_leq A (R S : relation A): R ≦ S -> acyclic S -> acyclic R.
Proof.
  intros H. unfold acyclic. now rewrite H.
Qed.

Instance acyclic_leq_ A : Proper (leq --> impl) (@acyclic A).
Proof.
  intros R S H AC. eapply acyclic_leq; eauto.
Qed.

Lemma acyclic_weq A (R S : relation A): R ≡ S -> acyclic S -> acyclic R.
Proof.
  intros H. unfold acyclic; now rewrite H.
Qed.

Instance acyclic_weq_ A : Proper (weq --> iff) (@acyclic A).
Proof.
  intros R S H. split; apply acyclic_leq; compute in *; apply H.
Qed.

Lemma irreflexive_spec {X} (R : relation X) : irreflexive R <-> forall x, ~ R x x.
Proof.
  compute.
  firstorder.
  subst; eauto.
Qed.

Lemma irreflexive_compose {X} (R S : relation X) : irreflexive (R⋅S) <-> irreflexive (S⋅R).
Proof.
  rewrite 2irreflexive_spec.
  split; intros H x [y xy yx]; apply (H y); exists x; eauto.
Qed.

Lemma acyclic_irreflexive {X} (R : relation X) : acyclic R <-> irreflexive (R^+).
Proof.
  reflexivity.
Qed.

Lemma acyclic_compose {X} (R S : relation X) : acyclic (R⋅S) -> acyclic (S⋅R).
Proof.
  rewrite 2acyclic_irreflexive.
  assert (E : (R⋅S)^+ ≡ R⋅(S⋅R)^*⋅S) by ka. rewrite E.
  rewrite irreflexive_compose.
  apply irreflexive_weq.
  ka.
Qed.

Lemma irreflexive_union {X} (R S : relation X) :
  irreflexive (R ⊔ S) <-> irreflexive R /\ irreflexive S.
Proof.
  unfold irreflexive.
  compute; intuition eauto.
Qed.

Lemma cycle_break {X} (R S : relation X) :
  is_transitive R ->
  is_transitive S ->
  (acyclic (R ⊔ S) <->
   irreflexive R /\
   irreflexive S /\
   acyclic (R ⋅ S)).
Proof.
  intros TR TS.
  split.
  - (* easy direction *)
    rewrite !acyclic_irreflexive.
    intros A; repeat split; revert A; apply irreflexive_leq; ka.
  - intros (r & s & rs).
    rewrite acyclic_irreflexive.
    assert (E : (R ⊔ S)^+ ≡ R^+ ⊔ S^+
                       ⊔ (R^+⋅S^+)^+ ⊔ S^+⋅(R^+⋅S^+)^*⋅R^+
                       ⊔ (R^+⋅S^+)^+⋅R^+ ⊔ S^+⋅(R^+⋅S^+)^+)
      by ka.
    rewrite E.
    rewrite (itr_transitive TR), (itr_transitive TS).
    repeat rewrite irreflexive_union; repeat split; auto.
    + rewrite irreflexive_compose.
      ra_normalise.
      apply rs.
    + rewrite irreflexive_compose.
      apply irreflexive_leq with ((R⋅S)^+); auto.
      rewrite <-(itr_transitive TR).
      ka.
    + rewrite irreflexive_compose.
      apply irreflexive_leq with ((R⋅S)^+); auto.
      rewrite <-(itr_transitive TS).
      ka.
Qed.

Lemma acyclic_itr {X} (R : relation X) : acyclic (R^+) <-> acyclic R.
Proof.
  apply irreflexive_weq. ra.
Qed.

Lemma acyclic_cnv {X} (R : relation X) : acyclic R <-> acyclic R°.
Proof.
  unfold acyclic. rewrite <-cnvitr.
  compute; split; intros a x y; specialize (a y x); intuition.
Qed.

Lemma transitive_irreflexive_acyclic {X} (R : relation X) : is_transitive R -> irreflexive R -> acyclic R.
Proof.
  intros t. apply irreflexive_weq. symmetry. apply itr_transitive. auto.
Qed.

Lemma acyclic_cup_itr_l {X} (R S : relation X) : acyclic (R^+ ⊔ S) <-> acyclic (R ⊔ S).
Proof.
  apply irreflexive_weq. ra.
Qed.

Lemma acyclic_cup_itr_r {X} (R S : relation X) : acyclic (R ⊔ S^+) <-> acyclic (R ⊔ S).
Proof.
  apply irreflexive_weq. ra.
Qed.

Lemma acyclic_bot {A} : acyclic (bot : relation A).
Proof.
  apply leq_capx. left. ra.
Qed.

Lemma empty_acyclic {A} (R : relation A) :
  is_empty R -> acyclic R.
Proof.
  unfold is_empty.
  intros ->.
  apply acyclic_bot.
Qed.

Lemma acyclic_cup {X} (R S : relation X) :
  acyclic (R ⊔ S) <-> acyclic R /\ acyclic S /\ acyclic (R^+ ⋅ S^+).
Proof.
  rewrite <-acyclic_cup_itr_l, <-acyclic_cup_itr_r.
  split.
  - intros A. rewrite <-acyclic_itr in A.
    split; [ | split ]; revert A; apply acyclic_leq; ka.
  - intros (r & s & rs).
    apply cycle_break.
    + unfold is_transitive; ka.
    + unfold is_transitive; ka.
    + split; [ | split]; auto.
Qed.

Lemma acyclic_tst {X} (R S : relation X) (Dom Rng : set X) :
  S ≦ [Dom] ⋅ S ⋅ [Rng] ->
  acyclic (R ⊔ S) <-> acyclic R /\ acyclic ([Rng] ⋅ R^+ ⋅ [Dom] ⊔ S).
Proof.
  intros HS'.
  assert (HS : S ≡ [Dom] ⋅ S ⋅ [Rng]) by (apply antisym; auto; kat).
  split.
  - intros H; split; revert H.
    + apply acyclic_leq. ka.
    + rewrite <-acyclic_itr. apply acyclic_leq. kat.
  - intros (r & rs). apply acyclic_cup.
    split; auto. split. revert rs. apply acyclic_leq. ka.
    assert (S^+ ≡ S⋅S^*) as -> by ka. rewrite HS at 1.
    assert ([Rng] ≦ 1) as -> by kat. ra_normalise. rewrite <-dotA.
    assert (S⋅S^* ≡ S^*⋅S) as -> by ka. rewrite dotA.
    apply acyclic_compose.
    rewrite HS at 1.
    assert (E:[Dom] ≦ 1) by kat. rewrite E at 1; clear E. ra_normalise. rewrite <-!dotA.
    apply acyclic_compose.
    rewrite <-acyclic_itr in rs. revert rs. apply acyclic_leq. ka.
Qed.

Lemma acyclic_incompatible_domain_range {A} (R : relation A) X Y :
  X ⊓ Y ≦ bot -> acyclic ([X] ⋅ R ⋅ [Y]).
Proof.
  intros E.
  apply transitive_irreflexive_acyclic;
    intros a b; destruct_rel; firstorder.
Qed.

Lemma acyclic_cup_excl_l {X} (R S : relation X) :
  R ⋅ S ≦ 0 ->
  acyclic (R ⊔ S) <-> acyclic R /\ acyclic S.
Proof.
  intros RS.
  rewrite acyclic_cup.
  intuition.
  assert (R^+⋅S^+ ≡ R^*⋅(R⋅S)⋅S^*) as -> by ka.
  rewrite RS.
  ra.
Qed.

Lemma acyclic_cup_excl2_l {X} (R S : relation X) :
  R ⋅ S ≦ 0 ->
  S ⋅ S ≦ 0 ->
  acyclic (R ⊔ S) <-> acyclic R.
Proof.
  intros RS SS.
  rewrite acyclic_cup_excl_l; auto.
  intuition.
  unfold acyclic.
  assert (S^+ ≡ S ⊔ (S⋅S)⋅S^*) as -> by ka.
  rewrite SS. ra_normalise.
  intros x x_ [xx <-]. apply SS. exists x; auto.
Qed.
