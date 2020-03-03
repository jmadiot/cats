From RelationAlgebra Require Import lattice prop monoid rel all.
From Coq Require Import Relations String.

(* proof of irrefl(po;com+) <-> acyclic(poloc+com) *)

Definition relation X := hrel X X.
Definition irreflexive {X} (R : relation X) := R ⊓ 1 ≦ 0.
Definition acyclic {X} (R : relation X) := irreflexive (R^+).

Lemma irreflexive_incl {X} (R S : relation X) : R ≦ S -> irreflexive S -> irreflexive R.
Proof.
  unfold irreflexive.
  intros ->; auto.
Qed.

Lemma irreflexive_union {X} (R S : relation X) :
  irreflexive (R ⊔ S) <-> irreflexive R /\ irreflexive S.
Proof.
  unfold irreflexive.
  compute; intuition eauto.
Qed.

Lemma irreflexive_spec {X} (R : relation X) : irreflexive R <-> forall x, ~ R x x.
Proof.
  compute; intuition eauto; subst; eauto.
Qed.

Lemma irreflexive_compose {X} (R S : relation X) : irreflexive (R⋅S) <-> irreflexive (S⋅R).
Proof.
  rewrite 2irreflexive_spec.
  split; intros H x [y xy yx]; apply (H y); exists x; eauto.
Qed.

Instance leq_irreflexive A : Proper (@leq (hrel_lattice_ops A A) ==> flip impl) irreflexive.
Proof.
  unfold irreflexive.
  intros R S -> e. auto.
Qed.

Instance leq_acyclic A : Proper (@leq (hrel_lattice_ops A A) ==> flip impl) acyclic.
Proof.
  intros R S e.
  apply leq_irreflexive.
  rewrite e; auto.
Qed.

Lemma is_transitive_ {X} (R : relation X) `{TR : Transitive _ R} : is_transitive R.
Proof.
  intros a b [c ? ?].
  eapply TR with c; auto.
Qed.

Lemma is_transitive_cap {X} (R S : relation X) : is_transitive R -> is_transitive S -> is_transitive (R ⊓ S).
Proof.
  unfold is_transitive.
  intros e f.
  transitivity (R⋅R ⊓ S⋅S).
  - apply leq_xcap.
    + rewrite !dotcapx, !dotxcap. lattice.
    + rewrite !dotcapx, !dotxcap. lattice.
  - lattice.
Qed.

Instance weq_acyclic A : Proper (@weq (hrel_lattice_ops A A) ==> iff) irreflexive.
Proof.
  intros R S; unfold irreflexive; intros ->; intuition auto.
Qed.

Instance same_relation_irreflexive A : Proper (@weq (hrel_lattice_ops A A) ==> iff) irreflexive.
Proof.
  intros R S; unfold irreflexive; intros ->; intuition auto.
Qed.

Lemma induction_uniproc {X} (R S : relation X) :
  R ⋅ S ⋅ R ≦ R^+ ->
  R^+ ⋅ (S ⋅ R^+)^+ ≦ R^+.
Proof.
  intros H.
  apply itr_ind_r.
  - transitivity (R^*⋅(R⋅S⋅R)⋅R^*).
    + ka.
    + rewrite H. ka.
  - transitivity (R^*⋅(R⋅S⋅R)⋅R^*).
    + ka.
    + rewrite H. ka.
Qed.

Lemma leq_spec {X} (R S : relation X) : R ≦ S -> forall x y, R x y -> S x y.
Proof.
  compute; auto.
Qed.

(* the proof below has been moved in lib/aycyclic *)
Lemma cycle_break {X} (R S : relation X) :
  is_transitive R ->
  is_transitive S ->
  (acyclic (R ⊔ S) <->
   irreflexive R /\
   irreflexive S /\
   acyclic (R ⋅ S)).
Proof.
  intros TR TS. unfold acyclic.
  split.
  - (* easy direction *)
    intros A; repeat split; revert A; apply irreflexive_incl; ka.
  - intros (r & s & rs).
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
      apply irreflexive_incl with ((R⋅S)^+); auto.
      rewrite <-(itr_transitive TR).
      ka.
    + rewrite irreflexive_compose.
      apply irreflexive_incl with ((R⋅S)^+); auto.
      rewrite <-(itr_transitive TS).
      ka.
Qed.

Section uniproc.
Variable events : Type.
Variables po rf co loc : relation events.

Definition fr := rf° ⋅ co.
Definition com := co ⊔ rf ⊔ fr.
Definition poloc := po ⊓ loc.

Variable R W : dset events.
Variable rw_0 : [R] ⋅ [W] ≦ 0.
Variable rf_wr : rf ≦ [W] ⋅ rf ⋅ [R].
Variable co_ww : co ≦ [W] ⋅ co ⋅ [W].
Variable rf_loc : rf ≦ loc.
Variable co_loc : co ≦ loc.
Variable co_total : [W] ⋅ loc ⋅ [W]  ≦ 1 ⊔ co ⊔ co°.
Variable R_rf : [R] ≦ rf° ⋅ [W] ⋅ rf.
Variable rf_unique : rf ⋅ rf° ≦ 1.
Variable loc_refl : 1 ≦ loc.
Variable loc_sym : loc° ≦ loc.
Variable loc_trans : loc ⋅ loc ≦ loc.
Variable po_trans : po ⋅ po ≦ po.
(* Variable po_trans : is_transitive po. *)

Lemma rf_wr' : rf ≡ [W] ⋅ rf ⋅ [R].
Proof.
  apply antisym.
  - assumption.
  - kat.
Qed.

Lemma co_ww' : co ≡ [W] ⋅ co ⋅ [W].
Proof.
  apply antisym.
  - assumption.
  - kat.
Qed.

Lemma injcnv {X} (a : dset X) : [a]° ≡ [a].
Proof.
  compute; intuition congruence.
Qed.

Lemma fr_wr' : fr ≡ [R] ⋅ fr ⋅ [W].
Proof.
  unfold fr. rewrite co_ww', rf_wr'.
  ra_normalise.
  rewrite !injcnv.
  kat.
Qed.

Lemma com_mm : com ≡ [R ⊔ W] ⋅ com ⋅ [R ⊔ W].
Proof.
  unfold com, fr, M.
  rewrite rf_wr', co_ww'.
  ra_normalise.
  rewrite !injcnv.
  kat.
Qed.

Lemma com_loc : com ≦ loc.
Proof.
  unfold com, fr. rewrite rf_loc, co_loc.
  rewrite loc_sym, loc_trans.
  ka.
Qed.

Lemma R_rf' : [R] ≡ [R] ⊓ (rf° ⋅ [W] ⋅ rf).
Proof.
  lattice.
Qed.

Lemma rf_unique' w1 w2 r : rf w1 r -> rf w2 r -> w1 = w2.
Proof.
  intros H1 H2.
  change ((1 : relation events) w1 w2).
  apply rf_unique.
  exists r; eauto.
Qed.

Lemma com_read_r x r : R r -> com x r -> rf x r.
Proof.
  intros Hr Hcom.
  assert (A : (com ⋅ [R]) x r). exists r; auto. constructor; auto.
  revert A. apply leq_spec.
  unfold com.
  rewrite rf_wr', co_ww', fr_wr'.
  ra_normalise.
  rewrite <-!dotA.
  rewrite rmov_inj.
  rewrite rw_0.
  kat.
Qed.

Lemma com_read_l x r : R r -> com r x -> fr r x.
Proof.
  intros Hr Hcom.
  assert (A : ([R] ⋅ com) r x). exists r; auto. constructor; auto.
  revert A. apply leq_spec.
  unfold com.
  rewrite rf_wr', co_ww', fr_wr'.
  ra_normalise.
  rewrite rw_0.
  kat.
Qed.

Lemma co_total' w1 w2 : W w1 -> W w2 -> loc w1 w2 -> w1 = w2 \/ co w1 w2 \/ co w2 w1.
Proof.
  intros ? ? ?.
  assert (H12 : ([W] ⋅ loc ⋅ [W]) w1 w2) by (compute; eauto).
  apply co_total in H12.
  compute in *; intuition.
Qed.

Open Scope string_scope.
Definition tag (s : string) (X : Type) := X.
Lemma tag_ s X : X = tag s X. reflexivity. Qed.
Ltac tag s x := let ty := type of x in change ty with (tag s ty) in x.
Ltac untag x := unfold tag in x.
Ltac introtag s := let x := fresh "__" in intros x; tag s x.

Ltac step :=
  match goal with
  | |- _ ≦ _ => introtag "nameme"; introtag "nameme"; introtag "destructme"
  | H : tag "destructme" ((_ ⋅ _) _ _) |- _ =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    let x := fresh "ev" in
    destruct H as [x H1 H2];
    tag "nameme" x;
    tag "destructme" H1;
    tag "destructme" H2
  | H : tag "destructme" ((_ ⊓ _) _ _) |- _ =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    destruct H as [H1 H2];
    tag "destructme" H1;
    tag "destructme" H2
  | H : tag "destructme" ([R] ?x _) |- _ =>
    let H1 := fresh "isread" in
    let x' := fresh "r" in
    destruct H as [<- H1];
    clear H;
    rename x into x'; untag x'
  | H : tag "destructme" ([W] ?x _) |- _ =>
    let H1 := fresh "iswrite" in
    let x' := fresh "w" in
    destruct H as [<- H1];
    clear H;
    rename x into x'; untag x'
  | H1 : com ?x ?y, H2 : R ?y |- _ => apply com_read_r in H1; auto
  | H2 : is_true (R ?y), H1 : tag _ (com ?x ?y)  |- _ => apply com_read_r in H1; auto
  | H2 : is_true (R ?y), H1 :        com ?x ?y   |- _ => apply com_read_r in H1; auto
  | H2 : is_true (R ?x), H1 : tag _ (com ?x ?y)  |- _ => apply com_read_l in H1; auto
  | H2 : is_true (R ?x), H1 :        com ?x ?y   |- _ => apply com_read_l in H1; auto
  | H : tag _ (?R° ?x ?y) |- _ => change (R° x y) with (R y x) in H
  | H : ?R° ?x ?y |- _ => change (R° x y) with (R y x) in H
  | H : ?A ?B ?C, H' : ?A ?B ?C |- _ => clear H'
  | H1 : tag _ (rf ?w1 ?r), H2 :        rf ?w2 ?r  |- _ => apply (rf_unique' _ _ _ H1) in H2; subst w2
  | H1 : tag _ (rf ?w1 ?r), H2 : tag _ (rf ?w2 ?r) |- _ => apply (rf_unique' _ _ _ H1) in H2; subst w2
  | H1 :        rf ?w1 ?r , H2 : tag _ (rf ?w2 ?r) |- _ => apply (rf_unique' _ _ _ H1) in H2; subst w2
  | H1 :        rf ?w1 ?r , H2 :        rf ?w2 ?r  |- _ => apply (rf_unique' _ _ _ H1) in H2; subst w2
  | x : tag "nameme" events |- _ =>
    let x' := fresh "x" in rename x into x'; untag x'
  | H : tag "destructme" _ |- _ =>
    let H' := fresh in rename H into H'; untag H'
  end.

Lemma cases_uniproc :
  irreflexive (poloc ⋅ com^+) ->
  com ⋅ poloc ⋅ com ≦ com^+.
Proof.
  assert (loc_eq : Equivalence loc) by (split; intros x; compute in *; eauto).
  intros U.
  transitivity (com ⋅ [R ⊔ W] ⋅ poloc ⋅ [R ⊔ W] ⋅ com).
  now rewrite com_mm; kat. rewrite kat.inj_cup. ra_normalise.
  ra_normalise. (* second time, because identifiers are reversed *)
  repeat apply join_leq.
  - (* R R *)
    transitivity (com⋅([R]⋅poloc⋅[R])⋅com); [ ka | ].
    rewrite R_rf'.
    repeat step.
    assert (ww0 : loc w w0).
    { transitivity r. apply rf_loc; auto.
      transitivity r0. symmetry. apply H1.
      symmetry; apply rf_loc; auto. } apply symmetry in ww0.
    destruct (co_total' w0 w ltac:(auto) ltac:(auto) ltac:(auto)) as [<- | [? | ?]].
    + apply leq_spec with (rf ⋅ fr). now unfold com; ka. now compute; eauto.
    + apply leq_spec with (co ⋅ rf ⋅ fr). now unfold com; ka. now compute; eauto.
    + exfalso.
      assert (Hr0 : (poloc ⋅ (fr ⋅ rf)) r0 r0).
      now (exists r; try solve [compute; eauto]).
      apply (U r0 r0). split; [ | compute; auto].
      eapply leq_spec; [ | apply Hr0 ].
      unfold com; ka.
  - (* R W *)
    rewrite R_rf'.
    repeat step.
    assert (ww0 : loc w w0).
    { symmetry. transitivity r. apply rf_loc; auto. apply H0. }
    symmetry in ww0.
    destruct (co_total' w0 w ltac:(auto) ltac:(auto) ltac:(auto)) as [<- | [? | ?]].
    + eapply leq_spec with com; auto. ka.
    + apply leq_spec with (co ⋅ com). now unfold com; ka. now compute; eauto.
    + exfalso.
      assert (Hr : (poloc ⋅ (co ⋅ rf)) r r). exists w. auto. exists w0; auto.
      apply (U r r). split; [ | compute; auto ]. eapply leq_spec; [ | apply Hr ].
      unfold com; ka.
  - (* W R *)
    rewrite R_rf'.
    repeat step.
    assert (ww0 : loc w0 w).
    { transitivity r. apply H2. symmetry. apply rf_loc; auto. }
    destruct (co_total' w0 w ltac:(auto) ltac:(auto) ltac:(auto)) as [<- | [? | ?]].
    + apply leq_spec with (com ⋅ (rf ⋅ fr)). now unfold com; ka. exists w0. auto. exists r; auto.
    + apply leq_spec with (com ⋅ (co ⋅ (rf ⋅ fr))). now unfold com; ka. exists w0; compute; eauto.
    + exfalso.
      assert (Hw0 : (poloc ⋅ fr) w0 w0). exists r; auto. exists w; auto.
      apply (U w0 w0). split; [ | compute; auto ]. eapply leq_spec; [ | apply Hw0 ].
      unfold com; ka.
  - (* W W *)
    repeat step.
    destruct (co_total' w0 w) as [<- | [? | ?]]; auto. apply H0.
    + apply leq_spec with (com ⋅ com). now unfold com; ka. exists w0; auto.
    + apply leq_spec with (com ⋅ (com ⋅ com)). now unfold com; ka. exists w0; auto. exists w; eauto.
      left; left; auto.
    + exfalso.
      apply (U w0 w0). split; [ | reflexivity ]. exists w; auto.
      eapply leq_spec with co. unfold com; ka. auto.
Qed.

Theorem uniproc :
  irreflexive po ->
  acyclic com ->
  (acyclic (poloc ⊔ com) <-> irreflexive (po ⋅ com^+)).
Proof.
  intros Hpo Hcom.
  transitivity (irreflexive (poloc⋅com^+)).
  - split.
    (* main part *)
    + (* easy direction *)
      unfold acyclic, irreflexive.
      assert (E : poloc ⋅ com^+ ≦ (poloc ⊔ com)^+) by ka.
      rewrite E.
      easy.
    + (* direction involving contracting a cycle *)
      intros Hirr.
      cut (acyclic (poloc ⊔ com^+)). apply leq_acyclic. ka.
      apply cycle_break.
      { apply is_transitive_cap; auto. }
      { apply transitive_itr. }
      repeat split.
      { intros x; rewrite <-(Hpo x); unfold poloc. lattice. }
      { apply Hcom. }
      change (poloc⋅com^+⋅(poloc⋅com^+)^* ⊓ 1 ≦ 0).
      rewrite str_itr, dotxpls, capcup'. ra_normalise.
      apply join_leq.
      * apply Hirr.
      * unfold irreflexive in Hirr. rewrite <-Hirr.
        cut (poloc⋅com^+⋅(poloc⋅com^+)^+ ≦ poloc⋅com^+). intros ->; auto.
        rewrite <-dotA. apply dot_leq. reflexivity.
        apply induction_uniproc.
        apply cases_uniproc. auto.
  - (* irrefl(poloc;com+) <-> irrefl(po;com+) *)
    split.
    + intros H x x_ [[y xy yx] <-]; apply H; split. 2:reflexivity. exists y; auto.
      split; auto.
      Fail rewrite com_loc in yx.
      (* TODO: why can't we do: rewrite com_loc in yx. *)
      apply loc_sym. change (loc y x). clear xy. revert y x yx.
      change (com^+ ≦ loc). rewrite com_loc.
      apply itr_ind_l1; auto.
    + apply leq_irreflexive. unfold poloc. rewrite leq_cap_l; auto.
Qed.

End uniproc.
