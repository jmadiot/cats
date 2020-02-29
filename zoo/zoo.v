From Coq Require Import String Ensembles.
From RelationAlgebra Require Import all.
From Catincoq Require Import Cat.

Instance is_empty_leq A : Proper (leq --> impl) (is_empty : relation A -> _).
Proof.
  intros R S H. unfold is_empty. now rewrite H.
Qed.

Instance is_empty_weq A : Proper (weq --> iff) (is_empty : relation A -> _).
Proof.
  intros R S H. split; apply is_empty_leq; compute in *; apply H.
Qed.

Lemma irreflexive_leq A (R S : relation A): R ≦ S -> irreflexive S -> irreflexive R.
Proof.
  intros H. unfold irreflexive. compute in *; intuition eauto.
Qed.

Lemma irreflexive_weq A (R S : relation A): R ≡ S -> irreflexive S <-> irreflexive R.
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

Ltac destruct_rel :=
  repeat
    match goal with
    | |- _ ≡ _ => intros x y; split; intro
    | |- _ ≦ _ => intros x y; intro
    | H : ?R° ?x ?y |- _ => change (R° x y) with (R y x) in H
    | H : (_ ⊓ _) _ _ |- _ => destruct H as [? ?]
    | H : (_ ⊔ _) _ _ |- _ => destruct H
    | H : ([_] ⋅ _) _ _ |- _ => destruct H as [? [<- ?] ?]
    | H : (1 ⋅ _) _ _ |- _ => destruct H as [? <- ?]
    | H : (_ ⋅ [_]) _ _ |- _ => destruct H as [? ? [-> ?]]
    | H : (_ ⋅ 1) _ _ |- _ => destruct H as [? ? ->]
    | H : (_ ⋅ _) _ _ |- _ => destruct H
    | H : [_] _ _ |- _ => destruct H as [->]
    | H : 1 _ _ |- _ => destruct H as [->]
    end.

Lemma cap_cartes {X} (R : relation X) a b : R ⊓ ([a] ⋅ top ⋅ [b]) ≡ [a] ⋅ R ⋅ [b].
Proof.
  destruct_rel.
  exists y; hnf; auto. exists x; hnf; auto.
  split; auto. exists y; hnf; auto. exists x; split; auto.
Qed.

Lemma leq_tst_1 {X} (a : tst X) : [a] ≦ (1 : relation X).
Proof.
  compute; intuition eauto.
Qed.

Lemma tst_cap_1 {X} (a : tst X) : [a] ≡ [a] ⊓ (1 : relation X).
Proof.
  compute; intuition eauto.
Qed.


Require sc_nosm x86tso tso_nosm.

Open Scope cat_scope.

Lemma sc_nosm_stronger_than_x86tso c : is_transitive (po c) -> sc_nosm.valid c -> x86tso.valid c.
Proof.
  intros Hpo.
  unfold sc_nosm.valid, x86tso.valid.
  intros (co & Hco & Hatom & Hsc). exists co. split. apply Hco. clear Hco.

  destruct c as
      [events W R IW FW B RMW F po addr data ctrl rmw amo
              rf loc ext int unknown_set unknown_relation];
    repeat autounfold with * in *.

  split; [ | split ].
  - (* sc => uniproc *)
    revert Hsc.
    apply acyclic_leq.
    lattice.
  - (* atomics *)
    auto.
  - (* sc => tso *)
    revert Hsc.
    apply acyclic_leq.
    rewrite !cap_cartes.
    assert (E0 : [empty] ≡ (0 : relation events)) by kat.
    assert (E1 : [top] ≡ (1 : relation events)) by kat.
    rewrite E0, E1.
    rewrite !leq_tst_1.
    ra_normalise.
    unfold is_transitive in Hpo. rewrite Hpo.
    lattice.
Qed.

Lemma sc_nosm_stronger_than_tso_nosm c : is_transitive (po c) -> sc_nosm.valid c -> tso_nosm.valid c.
Proof.
  intros Hpo.
  unfold sc_nosm.valid, tso_nosm.valid.
  intros (co & Hco & Hatom & Hsc). exists co. split. apply Hco. clear Hco.

  destruct c as
      [events W R IW FW B RMW F po addr data ctrl rmw amo
              rf loc ext int unknown_set unknown_relation];
    repeat autounfold with * in *.

  split; [ | split ].
  - (* sc => uniproc *)
    revert Hsc.
    apply acyclic_leq.
    lattice.
  - (* atomics *)
    auto.
  - (* sc => tso *)
    revert Hsc.
    apply acyclic_leq.
    ra_normalise.
    rewrite !leq_tst_1.
    unfold is_transitive in Hpo. ra_normalise. rewrite Hpo.
    lattice.
Qed.

Ltac destr :=
  match goal with
  | c : candidate |- _ =>
    destruct c as
      [events W R IW FW B RMW F po addr data ctrl rmw amo
              rf loc ext int uset urel]
  end.

Ltac destrunfold := destr; repeat autounfold with * in *.

Lemma x86tso_stronger_than_tso_nosm c :
  is_transitive (po c) ->
  x86tso.valid c -> tso_nosm.valid c.
Proof.
  intros Hpo.
  unfold x86tso.valid, tso_nosm.valid.

  intros (co & Hco & Huniproc & Hatom & Hghb). exists co; split; [ apply Hco | ].
  split; [ | split ].
  - (* uniproc *)
    destrunfold.
    revert Huniproc; apply acyclic_leq.
    kat.
  - (* atomic *)
    auto.
  - (* main *)
    destrunfold.
    revert Hghb; apply acyclic_leq.
    rewrite !cap_cartes.
    kat.
Qed.

Definition domain {X} (R : relation X) := (R ⋅ R°) ⊓ 1.
Definition range {X} (R : relation X) := (R° ⋅ R) ⊓ 1.

Lemma irreflexive_spec {X} (R : relation X) : irreflexive R <-> forall x, ~ R x x.
Proof.
  reflexivity.
Qed.

Lemma irreflexive_compose {X} (R S : relation X) : irreflexive (R⋅S) <-> irreflexive (S⋅R).
Proof.
  rewrite 2irreflexive_spec.
  split; intros H x [y xy yx]; apply (H y); exists x; eauto.
Qed.

Lemma acyclic_irreflexive {X} (R : relation X) : acyclic R <-> irreflexive (R^+).
Proof.
  (* tautology once we settle on definitions of acyclic/irreflexive/etc *)
Admitted.

Lemma acyclic_compose {X} (R S : relation X) : acyclic (R⋅S) -> acyclic (S⋅R).
Proof.
  rewrite 2acyclic_irreflexive.
  assert (E : (R⋅S)^+ ≡ R⋅(S⋅R)^*⋅S) by ka. rewrite E.
  rewrite irreflexive_compose.
  apply irreflexive_weq.
  kat.
Qed.

Lemma range_spec {X} (R : relation X) : R ⋅ range R ≡ R.
Proof.
  unfold range.
  destruct_rel; auto.
  compute; eauto.
Qed.

Lemma range_spec2 {X} (R : relation X) : range R ≡ (fun y y_ => y = y_ /\ exists x, R x y). Admitted.
Lemma domain_spec2 {X} (R : relation X) : domain R ≡ (fun x x_ => x = x_ /\ exists y, R x y). Admitted.

Lemma domain_spec {X} (R : relation X) : domain R ⋅ R ≡ R.
Proof.
  unfold domain.
  destruct_rel; auto.
  compute; eauto.
Qed.

Ltac intuitiond :=
  repeat (
      split ||
       match goal with
       | H : ex _ |- _ => destruct H
       | H : _ = _ |- _ => subst
       end ||
      intuition eauto; destruct_rel
    ).

Lemma range_cup {X} (R S : relation X) : range (R ⊔ S) ≡ range R ⊔ range S.
Proof.
  rewrite !range_spec2; split; intuitiond; compute; eauto.
Qed.

Lemma range_cap {X} (R S : relation X) : range (R ⊓ S) ≦ range R ⊓ range S.
Proof.
  rewrite !range_spec2; split; intuitiond; compute; eauto.
Qed.

Lemma range_tst {X} a (R : relation X) : range (R ⋅ [a]) ≡ [a] ⋅ range R.
Proof.
  rewrite !range_spec2; split; intuitiond; compute; eauto.
Qed.

Lemma range_cnv {X} (R : relation X) : range (R°) ≡ domain R.
Proof.
  rewrite range_spec2, domain_spec2; split; intuitiond; compute; eauto.
Qed.

Hint Rewrite @range_cup @range_cap @range_tst @range_cnv : range_domain.

Lemma range_dot {X} (R S : relation X) : irreflexive S -> range (R ⋅ S) ≦ range S.
Proof.
  intros H. rewrite !range_spec2; split; intuitiond; compute; eauto.
Qed.

Lemma range_1 {X} (R : relation X) : range R ≦ 1.
Proof.
  rewrite !range_spec2; intuitiond.
Qed.

Lemma domain_cup {X} (R S : relation X) : domain (R ⊔ S) ≡ domain R ⊔ domain S.
Proof.
  rewrite !domain_spec2; split; intuitiond; compute; eauto.
Qed.

Lemma domain_cap {X} (R S : relation X) : domain (R ⊓ S) ≦ domain R ⊓ domain S.
Proof.
  rewrite !domain_spec2; split; intuitiond; compute; eauto.
Qed.

Lemma domain_tst {X} a (R : relation X) : domain ([a] ⋅ R) ≡ [a] ⋅ domain R.
Proof.
  rewrite !domain_spec2; split; intuitiond; compute; eauto.
Qed.

Lemma domain_tst2 {X} a (R S : relation X) : domain ([a] ⋅ R ⋅ S) ≡ [a] ⋅ domain (R ⋅ S).
Proof.
  rewrite !domain_spec2; split; intuitiond; compute; eauto.
  eexists; eauto.
Qed.

Lemma domain_cnv {X} (R : relation X) : domain (R°) ≡ range R.
Proof.
  rewrite !domain_spec2, range_spec2; split; intuitiond; compute; eauto.
Qed.

Hint Rewrite @domain_cup @domain_cap @domain_tst @domain_tst2 @domain_cnv : range_domain.

Lemma domain_dot {X} (R S : relation X) : irreflexive R -> domain (R ⋅ S) ≦ domain R.
Proof.
  intros H. rewrite !domain_spec2; split; intuitiond; compute; eauto.
Qed.

Lemma domain_1 {X} (R : relation X) : domain R ≦ 1.
Proof.
  rewrite !domain_spec2; intuitiond.
Qed.

Lemma acyclic_bound_left {X} (R : relation X) : acyclic (range R ⋅ R) -> acyclic R.
Proof.
  intros A. apply acyclic_compose in A. rewrite range_spec in A.
  auto.
Qed.

Lemma acyclic_bound_right {X} (R : relation X) : acyclic (R ⋅ domain R) -> acyclic R.
Proof.
  intros A. apply acyclic_compose in A. rewrite domain_spec in A.
  auto.
Qed.

Lemma cycle_break {X} (R S : relation X) :
  is_transitive R ->
  is_transitive S ->
  (acyclic (R ⊔ S) <->
   irreflexive R /\
   irreflexive S /\
   acyclic (R ⋅ S)).
Admitted.

Definition is_irreflexive {X} (R : relation X) := R ⊓ 1 ≦ 0.

Lemma is_irreflexive_spec {X} (R : relation X) : irreflexive R <-> is_irreflexive R.
Proof.
Admitted.

Definition is_acyclic {X} (R : relation X) := R^+ ⊓ 1 ≦ 0.

Lemma is_acyclic_spec {X} (R : relation X) : acyclic R <-> is_acyclic R.
Proof.
  split; intros A x y; specialize (A x y); rewrite A; compute; tauto.
Qed.

Lemma irreflexive_acyclic {X} (R : relation X) : acyclic R <-> irreflexive (R^+).
Proof.
  rewrite is_acyclic_spec, is_irreflexive_spec.
  compute; auto.
Qed.

Lemma acyclic_itr {X} (R : relation X) : acyclic (R^+) <-> acyclic R.
Proof.
  rewrite 2is_acyclic_spec. unfold is_acyclic.
  cut (R^+^+ ≡ R^+). now intros ->. ra.
Qed.

Lemma acyclic_cup_itr_l {X} (R S : relation X) : acyclic (R^+ ⊔ S) <-> acyclic (R ⊔ S).
Proof.
  rewrite 2is_acyclic_spec. unfold is_acyclic.
  cut ((R ⊔ S)^+ ≡ (R^+ ⊔ S)^+). now intros ->. ra.
Qed.

Lemma acyclic_cup_itr_r {X} (R S : relation X) : acyclic (R ⊔ S^+) <-> acyclic (R ⊔ S).
Proof.
  rewrite 2is_acyclic_spec. unfold is_acyclic.
  cut ((R ⊔ S)^+ ≡ (R ⊔ S^+)^+). now intros ->. ra.
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
      * revert r; rewrite is_irreflexive_spec, is_acyclic_spec; auto.
      * revert s; rewrite is_irreflexive_spec, is_acyclic_spec; auto.
Qed.

Lemma acyclic_range_domain {X} (R S : relation X) :
  acyclic (R ⊔ S) <-> acyclic R /\ acyclic (range S ⋅ R^+ ⋅ domain S ⊔ S).
Proof.
  rewrite acyclic_cup.
  split.
  - intros (r & s & rs). split; auto.
    apply acyclic_cup. split; auto.
    + rewrite range_1, domain_1. revert r. rewrite <-acyclic_itr. apply acyclic_leq. kat.
    + split; auto. rewrite range_1, domain_1. revert rs. apply acyclic_leq. kat.
  - intros (r & rs). split; auto. split. revert rs. apply acyclic_leq. kat.
    assert (E : R^+⋅S^+ ≡ R^+⋅S^*⋅S). kat. rewrite E.
    apply acyclic_bound_left. rewrite range_dot.
    2: { revert rs. rewrite acyclic_irreflexive. apply irreflexive_leq. kat. }
    apply acyclic_compose.
    assert (E' : R^+⋅S^*⋅S ≡ R^+⋅S⋅S^*). kat. rewrite E'.
    rewrite <-(domain_spec S) at 1. apply acyclic_compose.
    revert rs. rewrite 2acyclic_irreflexive. apply irreflexive_leq. kat.
Qed.

Lemma tso_nosm_stronger_than_x86tso c :
  [W c] ⋅ [R c] ≦ 0 ->
  rf c ≦ [W c] ⋅ rf c ⋅ [R c] ->
  irreflexive (po c) ->
  is_transitive (po c) ->
  tso_nosm.valid c -> x86tso.valid c.
Proof.
  intros wr rf_wr po_irr po_trans.
  unfold x86tso.valid, tso_nosm.valid.

  intros (co & Hco & Huniproc & Hatom & Hghb). exists co; split; [ apply Hco | ].
  split; [ | split ].
  - (* uniproc *)
    destrunfold.
    revert Huniproc; apply acyclic_leq.
    kat.
  - (* atomic *)
    auto.
  - (* main *)
    destrunfold.
    set (MF := uset _). fold MF in Hghb.
    rewrite !cap_cartes.

    (* all of the complexity below is due to the fact that po[mf]po is surrounded by [R+W] in tso_nosm
     but not in x86tso. This does not matter in principle, because a cycle can escape po only through
     a com. This intuition is formalized in [acyclic_range_domain], which allows us to conclude,
     painfully, since range(rel) is not a test *)
    assert (E0 : [empty] ≡ (0 : relation events)) by kat.
    assert (E1 : [top] ≡ (1 : relation events)) by kat.
    (* simplication inside acyclic *)
    eapply acyclic_weq.
    { rewrite E0, E1. ra_normalise. reflexivity. }
    (* some simplification in Hgb *)
    eapply acyclic_weq in Hghb; swap 1 2.
    { rewrite E0. ra_normalise. reflexivity. }
    cut (acyclic (po⋅[MF]⋅po + (co + rf ∩ ext + rf°⋅co ∩ !id + [W]⋅po⋅[W] + [R]⋅po⋅[R ⊔ W]))).
    { apply acyclic_weq. ra. }
    apply acyclic_range_domain.
    split.
    { rewrite leq_tst_1.
      apply acyclic_leq with po; ra_normalise; auto. apply acyclic_irreflexive.
      cut (po^+ ≡ po). intros ->; auto. apply itr_transitive; auto. }
    assert (Hpo : (po⋅[MF]⋅po)^+ ≦ po⋅[MF]⋅po).
    { transitivity (po^+⋅[MF]⋅po^+). kat. rewrite itr_transitive; auto. }
    rewrite Hpo.

    revert Hghb; apply acyclic_leq.
    autorewrite with range_domain.
    assert (co_ww : co ≦ [W] ⋅ co ⋅ [W]) by admit (* property of co *).
    rewrite !range_dot, !domain_dot; auto.
    2: { intros x xx. specialize (rf_wr x x xx). clear -wr rf_wr. destruct_rel.
         apply (wr x x). exists x; compute; auto. }
    assert (range_co : range co ≦ [W]) by shelve.
    assert (range_rf : range rf ≦ [R]) by shelve.
    assert (domain_co : domain co ≦ [W]) by shelve.
    assert (domain_rf : domain rf ≦ [W]) by shelve.
    rewrite !range_co, !range_rf, !domain_co, !domain_rf.
    rewrite !range_1, !domain_1.
    rewrite !(leq_cap_l [_] 1).
    ra_normalise.
    kat.
    admit (* property on cross *).

    Unshelve.
    all: unfold range, domain.
    + rewrite co_ww. destruct_rel. split; auto.
    + rewrite rf_wr. destruct_rel. split; auto.
    + rewrite co_ww. destruct_rel. split; auto.
    + rewrite rf_wr. destruct_rel. split; auto.
Admitted (* properties on cross *).

Require rc11.

Lemma sc_nosm_stronger_than_rc11 c :
  is_transitive (po c) ->
  sc_nosm.valid c -> rc11.valid c.
Proof.
  intros Hpo.
  unfold sc_nosm.valid, rc11.valid.

  intros (co & Hco & Hatom & Hsc). exists co; split; [ apply Hco | ].

  split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
  - destrunfold.
    admit.
  - destrunfold.
    admit.
  - destrunfold.
    admit.
  - destrunfold.
    revert Hatom.
    apply is_empty_leq. unfold flip.
    assert (complement' : forall A (R : relation A), complement R ≡ !R).
    { intros; unfold complement, diff, universal. lattice. }
    Fail pourquoi ça marche pas ça rewrite complement'.
    Fail fail rewrite complement'.
    Fail fail rewrite complement'.
    ra_normalise.
(* c'est ça en fait ?
 (⟦ RMW ⟧ ⊔ rmw ⊓ (fr ⊓ complement id) ⋅ co
         ≦ rmw ⊓ (fre ⊓ complement id) ⋅ coe *)
    admit.
  - destrunfold.
    repeat rewrite diag_inter.
    repeat rewrite diag_union.
    Open Scope string_scope.
    set (RLX := uset "RLX").
    set (ACQ := uset "ACQ").
    set (REL := uset "REL").
    set (SC := uset "SC").
    set (AR := uset "ACQ_REL").
    Fail fail ra_normalise. (* bad idea: 8000 lines or so *)
    set (ALL := ([ RLX ] ⊔ ([ REL ] ⊔ ([ AR ] ⊔ ([ ACQ ] ⊔ [ SC ]))))).
    admit.
  - destrunfold.
    revert Hsc. apply acyclic_leq. unfold flip.
    now lattice.
Admitted.

Class Decidable (P : Prop) := { decide : P + ~P }.
Definition bool_of_decidable_Prop (P : Prop) `{Decidable P} : bool := if decide then true else false.
Definition dset_of_decidable_set {A} (X : set A) `{forall a : A, Decidable (X a)} : dset A :=
  fun a => bool_of_decidable_Prop (X a).
  (* fun a => if @dec (X a) _ then true else false. *)

Section playingwithcat.
Variable A : Type.
Variable X : dset A.
Variable Y : set A.
Definition dset' A := { X : A -> Prop | forall a, X a \/ ~X a }.
Variable Z : dset' A.

(* Definition dd := dset A.
Definition ss := set A.
Definition da := @dset_of_decidable_set A.
Coercion da : ss >-> dd.
Variable Ydec : forall a, Decidable (Y a).
Instance Ydecidable a : Decidable (Y a) := Ydec a.
Instance Decidable_Xprop a : Decidable (Xprop a).
*)

Variable R S T : relation A.

Goal exists x : dset A, x = x.
  unfold dset in *.
  unfold bool_lattice_ops in *.
simpl in *.
unfold pw_ops in *.
simpl in *.
Abort.

Goal R ⊔ (R ⋅ S) ⋅ S ⊔ T ⊔ bot ≦ R ⊔ T ⊔ R ⋅ (S ⋅ S) ⊔ [X] (* ⊔ [Z] *).
ra_normalise.
kat.
Qed.

End playingwithcat.
