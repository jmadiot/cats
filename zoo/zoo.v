From Coq Require Import String Ensembles.
From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From AAC_tactics Require Import AAC.
From Catincoq Require Import Cat proprel acyclic co.
From Catincoq Require aac_ra.
Open Scope string_scope.

(*
From AAC_tactics Require Export AAC.
Section lattice.
  Context `{lattice.laws}.
  Global Instance aac_cupA `{CUP ≪ l} : Associative weq cup := cupA.
  Global Instance aac_cupC `{CUP ≪ l} : Commutative weq cup := cupC.
  Global Instance aac_cupU `{BOT+CUP ≪ l} : Unit weq cup bot := Build_Unit _ _ _ cupbx cupxb.
  Global Instance aac_capA `{CAP ≪ l} : Associative weq cap := capA.
  Global Instance aac_capC `{CAP ≪ l} : Commutative weq cap := capC.
  Global Instance aac_capU `{TOP+CAP ≪ l} : Unit weq cap top := Build_Unit _ _ _ captx capxt.
  Global Instance aac_lift_leq_weq : AAC_lift leq weq.
  Proof. constructor; eauto with typeclass_instances. Qed.
End lattice.
Section monoid.
  Context `{monoid.laws} {n: ob X}.
  Global Instance aac_dotA: Associative weq (dot n n n) := (@dotA _ _ _ n n n n).
  Global Instance aac_dotU: Unit weq (dot n n n) (one n).
  Proof. constructor; intro. apply dot1x. apply dotx1. Qed.
End monoid.

Section test.
  Variable X : Type.
  Variables a: dpset X.
  Variables R S : relation X.
  Goal (R ⊔ S ≡ R) -> ((S ⊔ S) ⊔ R ≡ R).
  Proof.
    intros E.
    Set Printing All.
    aac_rewrite E.
    aac_rewrite E.
    aac_reflexivity.
  Qed.

  Goal (R ⊔ S ≡ R) -> ((S ⊔ S) ⊔ R ≡ R).
  Proof.
    intros E.
    aac_rewrite E.
  Abort.

  Goal (R ⊔ [a] ≡ R) -> (([a] ⊔ [a]) ⊔ R ≡ R).
  Proof.
    intros E.
    Fail aac_rewrite E.
  Abort.

  Goal ([a] ⊔ R ≡ R) -> (([a] ⊔ [a]) ⊔ R ≡ R).
  Proof.
    intros E.
    aac_rewrite E.
  Abort.

  Goal ([a] ⋅ R ≡ R) -> (([a] ⋅ [a]) ⋅ R ≡ R).
  Proof.
    intros E.
    aac_rewrite E.
  Abort.

End test.
*)

Require sc_nosm x86tso tso_nosm lamport.

Ltac destr :=
  match goal with
  | c : candidate |- _ =>
    destruct c as
      [events W R IW FW B RMW F po addr data ctrl rmw amo
              rf loc ext int uset urel]
  end.

Ltac destrunfold := destr; repeat autounfold with * in *.

Lemma sc_nosm_lamport c : sc_nosm.valid c <-> lamport.valid c.
Proof.
  unfold sc_nosm.valid, lamport.valid.
  destrunfold.
Abort.

Lemma sc_nosm_stronger_than_x86tso c : is_transitive (po c) -> sc_nosm.valid c -> x86tso.valid c.
Proof.
  intros Hpo.
  unfold sc_nosm.valid, x86tso.valid.
  intros (co & Hco & Hatom & Hsc). exists co. split. apply Hco. clear Hco.

  destr; repeat autounfold with * in *.

  split; [ | split ].
  - (* sc => uniproc *)
    revert Hsc.
    apply acyclic_leq.
    (* note: goal solvable by lattice *)
    assert (po ⊓ loc ≦ po) as -> by lattice.
    ka.
  - (* atomics *)
    auto.
  - (* sc => tso *)
    revert Hsc.
    apply acyclic_leq.
    rewrite !cap_cartes.
    assert (E0 : [empty ⊔ empty : dpset _] ≡ (0 : relation events)) by kat.
    assert (E1 : [top : dpset _] ≡ (1 : relation events)) by kat.
    rewrite E0, E1.
    rewrite !leq_tst_1.
    ra_normalise.
    unfold is_transitive in Hpo. rewrite Hpo.
    (* note: goal solvable by lattice *)
    assert (rf ⊓ ext ≦ rf) as -> by lattice.
    ka.
Qed.

Lemma sc_nosm_stronger_than_tso_nosm c : is_transitive (po c) -> sc_nosm.valid c -> tso_nosm.valid c.
Proof.
  intros Hpo.
  unfold sc_nosm.valid, tso_nosm.valid.
  intros (co & Hco & Hatom & Hsc). exists co. split. apply Hco. clear Hco.

  destr.
  repeat autounfold with * in *.

  split; [ | split ].
  - (* sc => uniproc *)
    revert Hsc.
    apply acyclic_leq.
    assert (po ⊓ loc ≦ po) as -> by lattice.
    ka.
  - (* atomics *)
    auto.
  - (* sc => tso *)
    revert Hsc.
    apply acyclic_leq.
    ra_normalise.
    rewrite !leq_tst_1.
    unfold is_transitive in Hpo. ra_normalise. rewrite Hpo.
    (* note: goal solvable by lattice *)
    assert (rf ⊓ ext ≦ rf) as -> by lattice.
    ka.
Qed.

(*
can sometimes be replaced with assert _ as -> by _.
Tactic Notation "rew" constr(e) :=
  let E := fresh in assert (E : e); [ | rewrite E; clear E].
Tactic Notation "rew" constr(e) "by" tactic(t) :=
  let E := fresh in assert (E : e) by t; rewrite E; clear E.
Tactic Notation "rew" constr(e) "in" hyp(H) :=
  let E := fresh in assert (E : e); [ | rewrite E in H; clear E].
Tactic Notation "rew" constr(e) "in" hyp(H) "by" tactic(t) :=
  let E := fresh in assert (E : e) by t; rewrite E in H; clear E.
/*)

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
    ka.
  - (* atomic *)
    auto.
  - (* main *)
    destrunfold.
    revert Hghb; apply acyclic_leq.
    rewrite !cap_cartes.
    kat.
Qed.



Lemma cnv_inj (l : level) (X : kat.ops) :
  kat.laws X -> laws l X -> CNV ≪ l -> forall (n : ob X) (a : tst n), [a]° ≡ [a].
Proof.
Abort (* not provable? *).

Lemma cnv_inj {X} (a : dpset X) : [a]° ≡ [a].
Proof.
  compute.
  intros x y. split; intros [? ?]; subst y; destruct (a x); firstorder.
Qed.

Lemma dotcap1l (l : level) (X : ops) :
  laws l X -> AL ≪ l ->
  forall (n : ob X) (x y z : X n n),
    x ≦ 1 -> x⋅(y ⊓ z) ≡ x⋅y ⊓ z.
Proof.
  intros H Hl n x y z Hx.
  apply antisym.
  - rewrite dotxcap. rewrite Hx at 2. ra.
  - rewrite capdotx. rewrite Hx at 2. ra.
Qed.

Lemma dotcap1r (l : level) (X : ops) :
  laws l X -> AL ≪ l ->
  forall (n : ob X) (x y z : X n n),
    x ≦ 1 -> (y ⊓ z) ⋅ x ≡ y ⋅ x ⊓ z.
Proof.
  intros H Hl n x y z Hx.
  apply antisym.
  - rewrite dotcapx. rewrite Hx at 2. ra.
  - rewrite capxdot. rewrite Hx at 1. ra.
Qed.

Lemma dotcap1l_rel {X} (x y z : relation X) :
  x ≦ 1 -> x⋅(y ⊓ z) ≡ x⋅y ⊓ z.
Proof.
  eapply dotcap1l. 2:reflexivity. apply lower_laws.
Qed.

Lemma dotcap1r_rel  {X} (x y z : relation X) :
  x ≦ 1 -> (y ⊓ z) ⋅ x ≡ y ⋅ x ⊓ z.
Proof.
  eapply dotcap1r. 2:reflexivity. apply lower_laws.
Qed.


(* Lemma dotcaplr (l : level) (X : ops) : *)
(*   laws l X -> CAP + AL ≪ l -> *)
(*   forall (n : ob X) (x y z t : X n n), *)
(*     x ≦ 1 -> t ≦ 1 -> x⋅(y ⊓ z)⋅t ≡ x⋅y⋅t ⊓ z. *)

(* Lemma dot1capl {X} (R S T : relation X) : R ≦ 1 -> R ⋅ (S ⊓ T) (R ⋅ S) ⊓ T ≡ . *)
(* Proof. *)
(*   intros r x z; split. *)
(*   - intros [[y xy yz] t]. exists y; firstorder. rewrite <-(r x y xy). auto. *)
(*   - intros [y xy [s t]]. split. exists y; auto. rewrite (r x y xy). auto. *)
(* Qed. *)

(* Lemma capdot_1l {X} (R S T : relation X) : R ≦ 1 -> (S ⋅ R) ⊓ T ≡ (S ⊓ T) ⋅ R. *)
(* Proof. *)
(*   intros r x z; split. *)
(*   - intros [[y xy yz] t]. exists y; firstorder. rewrite <-(r x y xy). auto. *)
(*   - intros [y xy [s t]]. split. exists y; auto. rewrite (r x y xy). auto. *)
(* Qed. *)

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
    ka.
  - (* atomic *)
    auto.
  - (* main *)
    destrunfold.
    set (MF := (uset _ : dpset _)). fold MF in Hghb.
    rewrite !cap_cartes.

    (* all of the complexity below is due to the fact that po[mf]po is
     surrounded by [R+W] in tso_nosm but not in x86tso. This does not
     matter in principle, because a cycle can escape po only through a
     com. This intuition is formalized in [acyclic_range_domain],
     which allows us to conclude, painfully, since range(rel) is not a
     test *)
    assert (E0 : [empty : dpset _] ≡ (0 : relation events)) by kat.
    assert (E1 : [top : dpset _] ≡ (1 : relation events)) by kat.
    (* simplication inside acyclic *)
    eapply acyclic_weq.
    { rewrite ?kat.inj_cup, E0, E1. ra_normalise. reflexivity. }
    (* some simplification in Hgb *)
    eapply acyclic_weq in Hghb; swap 1 2.
    { rewrite ?kat.inj_cup, E0. ra_normalise. reflexivity. }
    cut (acyclic (po⋅[MF]⋅po + (co + rf ∩ ext + rf°⋅co ∩ !id + [W]⋅po⋅[W] + [R]⋅po⋅[R ⊔ W]))).
    { rewrite ?kat.inj_cup. apply acyclic_weq. ra. }
    rewrite acyclic_tst with (Dom := (R ⊔ W)) (Rng := (R ⊔ W)).
    + (* apply acyclic_range_domain. *)
      split.
      { rewrite leq_tst_1.
        apply acyclic_leq with po; ra_normalise; auto. apply acyclic_irreflexive.
        cut (po^+ ≡ po). intros ->; auto. apply itr_transitive; auto. }
      assert (Hpo : (po⋅[MF]⋅po)^+ ≦ po⋅[MF]⋅po).
      { transitivity (po^+⋅[MF]⋅po^+). kat. rewrite itr_transitive; auto. }
      rewrite Hpo.
      revert Hghb; apply acyclic_leq.
      assert ([!W] ⋅ rf ≦ 0) by (rewrite rf_wr; kat).
      assert (rf ⋅ [!R] ≦ 0) by (rewrite rf_wr; kat).
      hkat.
    + set (frd :=  rf°⋅co ⊓ !id).
      assert (co_ww : co ≦ [W] ⋅ co ⋅ [W]) by eapply generate_orders_bounds, Hco.
      assert (frd_rw : frd ≦ [R] ⋅ frd ⋅ [W]). {
        unfold frd. rewrite co_ww, rf_wr at 1.
        clear.
        ra_normalise. rewrite !cnv_inj.
        rewrite (leq_tst_1 W) at 1 2. ra_normalise.
        rewrite dotcap1l_rel, dotcap1r_rel; kat || ra.
      }
      (* assert (cow : co ⋅ [!W] ≦ 0). rewrite co_ww. kat.
      assert (woc : [@neg (@tst dprop_hrel_dpset_kat_ops events) W] ⋅ co ≦ 0).
      rewrite co_ww. kat.
      assert (frw : rf°⋅co ⋅ [!W] ≦ 0). aac_rewrite cow. ra.
      assert (rfr : [!R] ⋅ rf°⋅co ≦ 0). rewrite rf_wr, cnvdot, cnv_inj. kat.
      assert (rfrd : [!R] ⋅ frd ≦ 0). unfold frd. rewrite dotxcap.
      clear -rfr. (* Fail aac_rewrite rfr. *) rewrite dotA, rfr. ra.
      assert ([!R] ⋅ frd ≦ 0) as _. (* Fail hkat. *) assumption.
      assert (frdw : frd ⋅ [!W] ≦ 0). unfold frd. rewrite capxdot, <-dotA, cow. ra.
      (* assert ([!R] ⋅ frd ≦ 0) by admit. *)
      (* assert (frd ⋅ [!W] ≦ 0) by admit. *)
      (* Fail hkat. *)
      *)
      assert (rfe_wr : (rf ⊓ ext) ≦ [W] ⋅ (rf ⊓ ext) ⋅ [R]). {
        rewrite dotcap1l_rel, dotcap1r_rel. rewrite rf_wr at 1. auto. kat. kat.
      }
      rewrite rfe_wr, co_ww, frd_rw at 1.
      kat.
Qed.

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
    { reflexivity || (intros; unfold complement, diff, universal; lattice). }
    (* Fail fail rewrite complement'. *)
    ra_normalise.
(* c'est ça en fait ? c'est pas vrai a priori
 (⟦ RMW ⟧ ⊔ rmw ⊓ (fr ⊓ !id) ⋅ co
         ≦ rmw ⊓ (fre ⊓ !id) ⋅ coe *)
    admit.
  - destrunfold.
    repeat rewrite diag_inter.
    repeat rewrite diag_union.
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
Abort.
