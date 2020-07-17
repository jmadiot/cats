From Coq Require Import String Ensembles Sorted Mergesort Permutation.
From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From Catincoq.lib Require Import defs proprel tactics relalglaws.
From CoLoR Require Util.Relation.Total. Arguments exist [A] _ _ _. Arguments existT [A] _ _ _.

Lemma partial_order_of_strict_order {A} (R : relation A) : strict_order R -> partial_order (R ⊔ 1).
Proof.
  intros [tr irr].
  split. ka. split. ra_normalise. rewrite tr. ka. rewrite cnvpls, cnv1, <-cupcap'.
  destruct_rel. destruct (irr x x). split. apply tr; exists y; auto. constructor. constructor.
Qed.

Lemma strict_order_of_partial_order {A} (R : relation A) : partial_order R -> strict_order (R ⊓ !1).
Proof.
  intros (r & t & a); split.
  - destruct_rel.
    split.
    + apply t; eexists; eauto.
    + intros <-. firstorder.
  - firstorder.
    (* TODO understand why firstorder fails if we don't Require CoLoR.Util.Relation.Total *)
Qed.

(* Instead of finiteness, it is also possible to use the axiom of
choice (or the weaker axiom "boolean ideal prime theorem")
https://proofwiki.org/wiki/Order-Extension_Principle *)

Lemma every_strict_order_can_be_total_on_aux {A} (E : set A) (R : relation A) :
  (forall x y : A, R x y \/ ~R x y) ->
  (forall x y : A, x = y \/ x <> y) ->
  finite_set E ->
  strict_order R ->
  exists S,
    strict_order S /\
    total_on E S /\
    [E] ⋅ R ⋅ [E] ≦ S.
Proof.
  intros Rdec Edec [l Fin] Ro.
  destruct (@Total.linearly_extendable A R Rdec) as [lin _].
  spec lin.
  { split. assumption. intros x xx. eapply Ro with x x.
    split. 2: reflexivity. apply RelUtil.trans_tc; auto.
    clear -Ro. intros x y z xy yz. eapply Ro. firstorder. }
  spec lin l. destruct lin as (S & RS & _).
  exists S.
  destruct RS as (U&I&Tr&Ir&Tot).
  repeat apply conj.
  - intros x z [y xy yz]. eapply Tr; eauto.
  - intros x y [xy <-]; eapply Ir, xy.
  - intros x y. destruct_rel. destruct (Tot x y) as [xy | [<- | xy]].
    firstorder. firstorder. left; auto. firstorder. right; auto.
  - intros x y. destruct_rel. apply I. firstorder.
Qed.

Lemma every_strict_order_can_be_total_on {A} (E : set A) (R : relation A) :
  (forall x y : A, R x y \/ ~R x y) ->
  (forall x y : A, x = y \/ x <> y) ->
  finite_set E ->
  strict_order R ->
  exists S,
    strict_order S /\
    S ≦ [E] ⋅ top ⋅ [E] /\
    total_on E S /\
    [E] ⋅ R ⋅ [E] ≦ S.
Proof.
  intros r e f o. destruct (every_strict_order_can_be_total_on_aux _ _ r e f o) as (S & (T&I) & t & RS).
  exists ([E] ⋅ S ⋅ [E]); repeat split.
  - rewrite <-T at 3. kat.
  - rewrite <-I, leq_tst_1. ra.
  - ra.
  - unfold total_on in *.
    assert ([E]⋅!1⋅[E] ≡ [E]⋅([E]⋅!1⋅[E])⋅[E]) as -> by kat.
    rewrite t. elim_cnv. kat.
  - rewrite <-RS. kat.
Qed.

Lemma every_order_can_be_total_on {A} (E : set A) (R : relation A) :
  partial_order R ->
  finite_set E ->
  (forall x y, R x y \/ ~R x y) ->
  exists S,
    partial_order S /\
    total_on E S /\
    [E] ⋅ R ⋅ [E] ≦ S.
Proof.
  intros Rpo Efin Rdec.
  assert (eqdec : forall x y : A, x = y \/ x <> y). {
    intros x y; destruct (Rdec x y) as [|n]; destruct (Rdec y x) as [|n'].
    - left. apply Rpo. firstorder.
    - right; intros <-; tauto.
    - right; intros <-; tauto.
    - right. intros <-. apply n. destruct Rpo as [r]. eapply r. reflexivity.
  }
  pose proof (every_strict_order_can_be_total_on E (R ⊓ !1)) as T.
  spec T.
  { clear T.
    intros x y. destruct (eqdec x y), (Rdec x y).
    right. firstorder.
    right. firstorder.
    left. firstorder.
    right. firstorder. }
  spec T by auto.
  spec T by auto.
  spec T by apply strict_order_of_partial_order.
  destruct T as (S & So & SE & St & RS).
  exists (S ⊔ 1). split; [ | split ].
  - apply partial_order_of_strict_order, So.
  - unfold total_on in *. rewrite St. ra.
  - rewrite <-RS. destruct_rel. destruct (eqdec x y). right; auto. left.
    exists y. exists x; firstorder. firstorder.
Qed.
