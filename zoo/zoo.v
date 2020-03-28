From Coq Require Import String Ensembles Sorted Mergesort Permutation.
From Coq Require Import Classical_Prop.

From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From AAC_tactics Require Import AAC.
From CoLoR Require Util.Relation.Total.

From Catincoq.lib Require Import Cat proprel acyclic co.
From Catincoq.lib Require aac_ra.

Open Scope string_scope.
From Catincoq.zoo (* NOT the one in models/, since we need MFENCE to be defined *) Require x86tso.
From Catincoq.models Require rc11.
(* From Catincoq_Models Require x86tso rc11. *)
From Catincoq.zoo Require sc_nosm tso_nosm lamport.

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

Ltac destr :=
  match goal with
  | c : candidate |- _ =>
    destruct c as
     [events W R IW FW B RMW F po addr data ctrl rmw amo
              rf loc ext int uset urel fin]
  end.

Ltac destrunfold := destr; repeat autounfold with * in *.

Definition partial_order {A} (R : relation A) := 1 ≦ R /\ R ⋅ R ≦ R /\ R ⊓ R° ≦ 1.

Definition strict_order {A} (R : relation A) := R ⋅ R ≦ R /\ R ⊓ 1 ≦ 0.

Definition total_on {A} (E : dpset A) (R : relation A) := [E] ⋅ !1 ⋅ [E] ≦ R ⊔ R°.

Definition total {A} (R : relation A) := !1 ≦ R ⊔ R°.

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
Qed.

Definition finite {A} (E : dpset A) :=
  exists (l : list A), forall a, proj1_sig (E a) -> List.In a l.

Definition in_at {A} (l : list A) : nat -> A -> Prop :=
  fun n x => List.nth_error l n = Some x.

Definition in_before {A} (l : list A) : A -> A -> Prop :=
  fun x y => x = y \/ exists n, exists m, n <= m /\ in_at l n x /\ in_at l m y.

(* Instead of finiteness, it is also possible to use the axiom of
choice (or the weaker axiom "boolean ideal prime theorem")
https://proofwiki.org/wiki/Order-Extension_Principle *)

Lemma every_strict_order_can_be_total_on {A} (E : dpset A) (R : relation A) :
  (forall x y : A, R x y \/ ~R x y) ->
  (forall x y : A, x = y \/ x <> y) ->
  finite E ->
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

Lemma every_order_can_be_total_on {A} (E : dpset A) (R : relation A) :
  partial_order R ->
  finite E ->
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
  destruct T as (S & So & St & RS).
  exists (S ⊔ 1). split; [ | split ].
  - apply partial_order_of_strict_order, So.
  - unfold total_on in *. rewrite St. ra.
  - rewrite <-RS. destruct_rel. destruct (eqdec x y). right; auto. left.
    exists y. exists x; firstorder. firstorder.
Qed.

Lemma cnvtst {A} {E : dpset A} : [E]° ≡ [E].
Proof.
  intros a b; split; intros [-> Ha]; constructor; auto.
Qed.

Ltac elim_cnv :=
  repeat (rewrite ?cnvtst, ?cnv1, ?cnv0, ?cnvstr, ?cnvitr,
          ?cnvtop, ?cnvcap, ?cnvdot, ?cnvpls, ?cnvneg).
(* Hint Rewrite would leave a bunch of subgoals about typeclasses *)

(** Cat idiom for inclusion *)
Lemma is_empty_included {A} (R S : relation A) : is_empty (R ⊓ !S) <-> R ≦ S.
Proof.
  symmetry.
  unfold is_empty.
  split; destruct_rel. firstorder.
  destruct (classic (S x y)); firstorder.
Qed.

Instance linearisations_weq_ A : Proper (weq --> weq --> weq --> iff) (Cat.linearisations : dpset A -> _).
Proof.
  unfold Cat.linearisations, Cat.strict_total_order_on, Proper, respectful, flip.
  intros ? ? e1 ? ? e2 ? ? e3.
  rewrite ?e1, ?e2, ?e3; tauto.
Qed.

Lemma linearisations_weq {A} (E1 E2 : dpset A) (R1 R2 S1 S2 : relation A) :
  E1 ≡ E2 ->
  R1 ≡ R2 ->
  S1 ≡ S2 ->
  Cat.linearisations E1 R1 S1 ->
  Cat.linearisations E2 R2 S2.
Proof.
  intros -> -> ->; auto.
Qed.

Notation " x :: X " := (proj1_sig (X x)).

Ltac hkat_help :=
  repeat
    match goal with
    | H : ?r ≦ [?a] ⋅ ?r ⋅ [?b] |- _ =>
      let H1 := fresh H in
      let H2 := fresh H in
      assert (H1 : [!a] ⋅ r ≦ 0) by (rewrite H; kat);
      assert (H2 : r ⋅ [!b] ≦ 0) by (rewrite H; kat);
      clear H
    end.

Lemma transitive_dot_tst_l {X} (R : relation X) (E : dpset X) :
  is_transitive R -> is_transitive (R ⋅ [E]).
Proof.
  unfold is_transitive.
  assert (R⋅[E]⋅(R⋅[E]) ≦ R⋅R⋅[E]) as -> by kat.
  intros ->; auto.
Qed.

Lemma transitive_dot_tst_r {X} (R : relation X) (E : dpset X) :
  is_transitive R -> is_transitive ([E] ⋅ R).
Proof.
  unfold is_transitive.
  assert ([E]⋅R⋅([E]⋅R) ≦ [E]⋅(R⋅R)) as -> by kat.
  intros ->; auto.
Qed.

Lemma transitive_cap {X} (R S : relation X) :
  is_transitive R -> is_transitive S -> is_transitive (R ⊓ S).
Proof.
  unfold is_transitive.
  rewrite dotxcap, 2dotcapx.
  intros -> ->.
  lattice.
Qed.

Tactic Notation "type" :=
  repeat
    match goal with
    | Hx : ?x :: ?X |- ?x :: ?X => assumption
    | Hx : ?x :: _ ⊓ _ |- _ => destruct Hx
    | Hx : ?x :: ?X, Hy : ?x :: ?Y, XY : ?X ⊓ ?Y ≦ bot |- _ =>
      eapply XY; split; eauto
    | H : (?r ⋅ [?Y]) ?x ?v |- ?v :: ?Y => destruct_rel; assumption
    | H : ([?X] ⋅ ?r ⋅ [?Y]) ?x ?v |- ?v :: ?Y => destruct_rel; assumption
    | H : ([?X] ⋅ ?r ⋅ [?Y]) ?v ?y |- ?v :: ?X => destruct_rel; assumption
    | H : ?r ?x ?v, H2 : ?r ≦ [?X] ⋅ ?r ⋅ [?Y] |- ?v :: ?Y =>
      assert (([X] ⋅ r ⋅ [Y]) x v) by apply H2, H;
      destruct_rel; assumption
    | H : ?r ?v ?y, H2 : ?r ≦ [?X] ⋅ ?r ⋅ [?Y] |- ?v :: ?X =>
      assert (([X] ⋅ r ⋅ [Y]) v y) by apply H2, H;
      destruct_rel; assumption
    | |- _ :: _ ⊓ _ => split
    end.

Tactic Notation "type" var(v) :=
  match goal with
  | H : ?r ?x v, H2 : ?r ≦ [?X] ⋅ ?r ⋅ [?Y] |- _ =>
    assert (v :: Y) by type
  | H : ?r v ?y, H2 : ?r ≦ [?X] ⋅ ?r ⋅ [?Y] |- _ =>
    assert (v :: X) by type
  end.

Ltac t :=
  repeat
    (match goal with
     | |- (_ ⋅ [_]) ?x ?y => exists y; [ | split; auto ]
     | |- ([_] ⋅ _) ?x ?y => exists x; [ split; auto | ]
     | |- (_ ⊓ _) ?x ?y => split; auto
     | |- [_] ?x ?y => split; [ reflexivity | ]
     | |- 1 ?x ?y => reflexivity
     | |- top ?x ?y => constructor
     end; type; try assumption).

Lemma ranging_spec {A} (R : relation A) (X : set A) :
  R ≦ R ⋅ [X] <-> (forall x y, R x y -> y :: X).
Proof.
  split; intros r x y xy.
  - apply r in xy. type.
  - t. eauto.
Qed.

Lemma ranging_itr {A} (R : relation A) (X : set A) :
  (forall x y, R x y -> y :: X) ->
  (forall x y, (R^+) x y -> y :: X).
Proof.
  rewrite <-!ranging_spec.
  intros e; rewrite e at 1. kat.
Qed.

Lemma ranging_cup {A} (R S : relation A) (X : set A) :
  (forall x y, R x y -> y :: X) ->
  (forall x y, S x y -> y :: X) ->
  (forall x y, (R ⊔ S) x y -> y :: X).
Proof.
  rewrite <-!ranging_spec.
  intros e f; rewrite e, f at 1. kat.
Qed.

Lemma ranging_capl {A} (R S : relation A) (X : set A) :
  (forall x y, R x y -> y :: X) ->
  (forall x y, (R ⊓ S) x y -> y :: X).
Proof.
  rewrite <-!ranging_spec.
  intros e; rewrite e at 1. destruct_rel. t.
Qed.

Lemma ranging_capr {A} (R S : relation A) (X : set A) :
  (forall x y, S x y -> y :: X) ->
  (forall x y, (R ⊓ S) x y -> y :: X).
Proof.
  rewrite <-!ranging_spec.
  intros e; rewrite e at 1. destruct_rel. t.
Qed.

Lemma domrng_char {A} (R : relation A) (X Y : set A) :
  R ≦ [X] ⋅  R  ⋅ [Y] <->
  R ≦ [X] ⋅ top ⋅ [Y].
Proof.
  split. intros ->. ra. intros r x y xy. spec r x y xy. t; type.
Qed.

Lemma sc_nosm_lamport c : sc_nosm.valid c <-> lamport.valid c.
Proof.
  unfold sc_nosm.valid, lamport.valid.
  destrunfold.
  assert (rw_disj : R ⊓ W ≦ bot) by admit.
  split.

  - (** Suppose we have a "sc.cat" execution, with a generated co *)
    intros (co & Hco & atomic & sc).
    apply generate_orders_spec_2 in Hco.
    destruct Hco as (iwfw & co_order (* TODO USELESS? *) & co_total).
    assert (co_loc : co ≦ loc).
    { transitivity ([W]⋅loc⋅[W]). rewrite co_total; ka. kat. }
    assert (co_final : [W ⊓ !FW]⋅loc⋅[FW] ≦ co).
    { rewrite <-iwfw. rewrite capcup, 2cap_cartes. kat. }
    assert (co_total' : [W] ⋅ (!1 ⊓ loc) ⋅ [W] ≦ co ⊔ co°).
    { rewrite capC, dotcap1_rel, co_total; try kat.
      destruct_rel. now left. now right. firstorder. }
    assert (co_ww : co ≦ [W] ⋅ co ⋅ [W]).
    { apply domrng_char. transitivity ([W]⋅loc⋅[W]). rewrite co_total; ka. ra. }
    assert (co_iw : co ⋅ [IW] ≦ 0).
    { intros w1 w2.
      assert (([IW] ⊔ [!IW]) w1 w1).
      { assert (a: 1 ≦ [IW] ⊔ [!IW]) by kat. now apply a. }
      destruct_rel.
      - (* w1 and w2 related through IW;co;IW? no contradiction? *)
        assert (w1 = w2) as <-. apply iw_uniq. t. now apply co_loc.
        apply co_order. t.
      - (* w1 is not initial: then, cycle in co *)
        exfalso.
        assert (co w2 w1).
        { apply iwfw. split. now apply loc_sym, co_loc. left. t. }
        assert (c : co w1 w1) by now apply co_order; exists w2; auto.
        exfalso.
        eapply co_order. t. eauto.
    }
    remember (rf° ⋅ co ⊓ !id) as fr.
    set (com := fr ⊔ (rf ⊔ co)).
    set (M := R ⊔ W).
    set (M' := M ⊓ !IW).
    (** We know po+com is acyclic, so we can extend it a total order *)
    destruct (every_strict_order_can_be_total_on top (po ⊔ com)^+)
      as (S & (St & Sirr) & Stot & Sincl).
    { intros; apply classic. }
    { intros; apply classic. }
    { destruct fin as [l]. exists l. intuition. }
    { split. kat. revert sc. apply irreflexive_leq. unfold com. kat. }
    assert (poS : po ≦ S) by (rewrite <-Sincl; kat).
    assert (coS : co ≦ S) by (rewrite <-Sincl; unfold com; kat).
    assert (frS : fr ≦ S). now rewrite <-Sincl; unfold com; kat.
    (** This total order is the "S" of the Lamport-style definition,
     with some subtlety about initial writes *)
    set (S' := [!IW] ⋅ S ⋅ [!IW]).
    exists S'.
    repeat apply conj; try rewrite is_empty_included.
    (** S is indeed a "linearisation" *)
    + (* irreflexive *)
      unfold S'. destruct_rel. apply Sirr. split. auto. reflexivity.
    + (* transitive *)
      unfold S'. transitivity ([!IW] ⋅ (S ⋅ S) ⋅ [!IW]).
      kat. rewrite St. auto.
    + (* domain/range *)
      unfold S'. kat.
    + (* totality *) unfold S'. rewrite 2cnvdot, cnvtst, dotA.
      transitivity ([!IW] ⋅ (S ⊔ S°) ⋅ [!IW]). 2:ka. unfold total_on in Stot.
      rewrite <-Stot.
      kat.
    + (* extends [w]loc[fw] *)
      rewrite cap_cartes.
      cut ([W ⊓ !FW]⋅loc⋅[FW] ≦ S). now intros ->; auto.
      rewrite co_final. auto.
    + (** S extends po *)
      unfold S'. rewrite <-poS.
      rewrite po_iw at 1.
      kat.
    + (** rf can be expressed in terms of S: inclusion 1 *)
      rewrite cap_cartes.
      rewrite cap_cartes_l.
      set (S'' := S' ⊔ [IW]⋅loc⋅[M']).
      set (WRS := [W]⋅(S'' ⊓ loc)⋅[R]).
      change (rf ≦ WRS ⊓ !(S''⋅WRS)).
      apply leq_xcap.
      * (* r <= WRS *)
        unfold WRS, S'', S'. rewrite capC, capcup.
        assert (rf ≦ (([IW] ⊔ [W ⊓ !IW]) ⋅ rf ⋅ [R])) as ->.
        { hkat_help. (* Fail hkat. *) clear -rf_wr0 rf_wr1. hkat. }
        ra_normalise.
        apply cup_leq.
        -- Fail hlattice. rewrite <-iw_w, rf_loc.
           (* tactique pour pousser les [IW] au fond ? *)
           rewrite dotcap1_rel; try kat.
           apply leq_xcap; try kat. unfold M', M. rewrite iw_w at 3.
           clear -rw_disj.
           hkat.
        -- rewrite dotcap1_rel; try kat.
           apply leq_xcap. rewrite rf_loc. now kat.
           assert (rf ≦ S) as <-. rewrite <-Sincl. unfold com. now kat.
           hkat_help.
           (* Fail hkat. *)
           clear -rf_wr0 rf_wr1 rw_disj iw_w.
           hkat.
      * (* r <= !(S'' WRS) *)
        intros w1 r w1r [w2 w1w2 w2r].
        assert (w1 <> w2).
        { intros <-. unfold S'', S' in w1w2. destruct_rel.
          eapply Sirr; split; eauto; reflexivity.
          firstorder. }
        type r.
        type w1.
        assert (w2 :: W) by (unfold WRS in *; type).
        assert (loc w1 w2). { apply loc_trans with r. now apply rf_loc.
          apply loc_sym. subst WRS. destruct_rel. firstorder. }
        destruct (co_total' w1 w2) as [D|D]. now t.
        -- assert (fr r w2).
           { rewrite Heqfr. split. exists w1. apply w1r. apply D. intros ->. type. }
           subst WRS S'' S'. clear w1w2.
           destruct_rel.
           ++ (* left component of WRS : S *)
              assert (S r w2). now apply frS.
              assert (S r r). now eapply St; exists w2; auto.
              eapply Sirr with r r. t.
           ++ (* right component of WRS: IW loc M' *)
              apply co_iw with w1 w2. exists w2; auto; t.
        -- subst WRS S'' S'. clear w2r.
           destruct_rel.
           ++ (* left component of WRS : S *)
              assert (S w2 w1). now apply coS.
              assert (S w1 w1). eapply St; exists w2; auto.
              eapply Sirr with w1 w1. t.
           ++ (* right component of WRS: IW loc M' *)
              apply co_iw with w2 w1. exists w1; auto. t.
    + (** Inclusion 2 *)
      rewrite cap_cartes, cap_cartes_l.
      subst S'.
      intros w1 r [w1r short].
      assert (r :: R). type.
      destruct (r_rf r r ltac:(split; auto)) as [w2 _ qw].
      type w2.
      destruct (classic (w1 = w2)). congruence.
      destruct (co_total' w1 w2) as [D|D].
      { t. type. apply loc_trans with r. now destruct_rel.
        apply loc_sym. now apply rf_loc. }
      * (* w1 -co-> w2 -rf-> r, which should contradict the "short" hypothesis *)
        destruct short. exists w2.
        -- (* w1 to w2 *)
           destruct (proj2_sig (IW w1)).
           ++ (* w1 is initial *)
              right. exists w2. exists w1. now split; auto. now apply co_loc.
              split; auto. split. unfold M. right; auto.
              intro. apply co_iw with w1 w2. firstorder.
           ++ (* w1 is not initial *)
              left. exists w2. exists w1. now split; auto. now apply coS.
              split; auto. intro. apply co_iw with w1 w2. firstorder.
        -- (* w2 to r *)
           exists r. 2: now split; auto. exists w2. now split; auto.
           split. 2: now apply rf_loc.
           assert (r :: !IW). intro riw. apply iw_w in riw. type.
           destruct (proj2_sig (IW w2)).
           ++ (* w2 is initial *)
              right. exists r. exists w2. now split; auto. now apply rf_loc.
              split; auto. split. unfold M. left; auto. auto.
           ++ (* w2 is not initial *)
              left. exists r. exists w2. now split; auto.
              assert (a: rf ≦ S). rewrite <-Sincl. unfold com. kat. now apply a.
              split; auto.
      * (* w1 <-co- w2 -rf-> r, so r-fr->w1, and so r-WRS->w1 *)
        exfalso.
        change (co w2 w1) in D.
        assert (fr r w1). { subst. split. now exists w2; auto.
          unfold id. simpl. type r. type w1. intros ->. type. }
        clear short. destruct_rel.
        -- (* in S *) apply Sirr with r r. split. apply St. exists w1.
           now apply frS. assumption. reflexivity.
        -- (* in IW loc M', but w1 cannot be in IW since w2 -co->w1 *)
           eapply co_iw. exists w1. eauto. now split.

  - (** Now suppose we have an execution with a Lamport-style "S"
    total relation, we build a sc.cat execution, and in particular the
    co between writes, which is S restricted to pairs of writes on the
    same variable, with some detail accounting to initial variables *)
    intros (S & [(Sirr & St & Sdom & Stot) Sincl] & Spo & Srf & rfS).
    rewrite is_empty_included in Srf, rfS, Spo.
    pose proof antisym _ _ Srf rfS as S_rf. clear Srf rfS.
    rewrite cap_cartes in S_rf.
    rewrite cap_cartes_l in S_rf.
    (** S doesn't touch any IW, so we add IW->W\IW and ^+ *)
    set (S_ := (S ⊔ [IW]⋅loc⋅[(R ⊔ W) ⊓ !IW])^+).
    (* set (S_ := ([IW]⋅loc⋅[(R ⊔ W) ⊓ !IW] ⊔ 1) ⋅ S). *)
    fold S_ in S_rf.
    (* set (co_init := loc ⊓ [IW]⋅top⋅[(R ⊔ W) ⊓ !IW]). *)
    set (co := [W] ⋅ (S_ ⊓ loc) ⋅ [W]).  (* ⊔ co_init). *)
    exists co.
    repeat apply conj.
    + (** Properties of co *)
      apply generate_orders_spec.
      repeat apply conj.
      * unfold co. now kat.
      * unfold co, S_.
        destruct_rel.
        cut (acyclic (S ⊔ [IW]⋅loc⋅[(R ⊔ W) ⊓ !IW])). now intros a; apply a.
        apply acyclic_cup_excl2_l.
        -- now rewrite Sdom; kat.
        -- now kat.
        -- now apply transitive_irreflexive_acyclic; auto.
      * apply transitive_dot_tst_l.
        apply transitive_dot_tst_r.
        apply transitive_cap.
        now apply transitive_itr.
        intros x y [z ? ?]. eapply loc_trans; eauto.
      * subst co. rewrite leq_cap_r. kat.
      * assert (co1 : loc ⊓ ([IW]⋅top⋅[W ⊓ !IW] ⊔ [W ⊓ !FW]⋅top⋅[FW]) ≦ co).
        { subst co S_.
          rewrite <-Sincl, <-itr_ext.
          rewrite <-(capI loc) at 1; rewrite <-capA.
          rewrite capcup, !dotcap1_rel, !cap_cartes; try kat.
          rewrite capC. apply cap_leq; auto.
          Fail kat.
         (* assert (iwfw : IW ⊓ FW ≦ bot) by admit. (* et non... *)
          clear -iw_w fw_w iwfw.
          hkat. *)
          apply join_leq.
          - clear -iw_w fw_w.
            hkat.
          - clear -iw_w fw_w rw_disj.
            transitivity ([W ⊓ !FW]⋅loc⋅[FW]⋅([IW] ⊔ [!IW])).
            now kat.
            ra_normalise.
            apply join_leq.
            now hkat.
            assert (E : [W]⋅loc⋅[FW]⋅[IW] ≦ [FW]⋅[IW]⋅loc⋅[FW]⋅[IW])
              by admit (* @luc ? *).
            rewrite capC, inj_cap.
            mrewrite E.
            kat.
        }
        assert (co2 : [W] ⋅ (!1 ⊓ loc) ⋅ [W] ≦ co ⊔ co°) by admit.
        intros w1 w2 w1w2 Ww1 Ww2; split. apply co1.
        intros d; apply co2.
        t.
    + (** atomic. *)
      unfold is_empty.
      admit.
    + (** Main acyclicity requirement, on po+com *)
      apply acyclic_leq with S_.
      * repeat apply join_leq.
        -- (** po *) unfold S_. rewrite <-Spo. ka.
        -- (** fr *)
           intros r w2 ([w1 rw1 w1w2] & rw2). destruct_rel.
           (** We use the totality of S *)
           destruct (Stot r w2) as [T|T].
           { (* Checking it's the right domain *)
             t.
             - rewrite S_rf in rw1.
               destruct_rel.
               assert (([!IW]⋅S⋅[!IW]) w1 r) by now apply Sdom.
               + type.
               + type.
             - subst co S_.
               destruct_rel.
               eapply ranging_itr; eauto.
               apply ranging_cup.
               + intros x y xy. apply Sdom in xy. type.
               + intros x y xy. destruct_rel. type.
           }
           ++ (** first case: S r w2. Then, S_ r w2 *)
              assert (a : forall S : relation events, S ≦ S^+) by (intro;ka). apply a.
              left; auto.
           ++ (** first case: S w2 r. Then rf w1 r can be shortcut
                through w2, contradiction. *)
              exfalso.
              change (S w2 r) in T.
              rewrite S_rf in rw1. destruct rw1 as [rw1 rw1']. apply rw1'.
              exists w2.
              ** (** First part of the path: co w1 w2 *)
                 destruct (proj2_sig (IW w1)) as [w1i | w1ni].
                 (* w1 initial *)
                 { subst co. right. t. now destruct_rel. type. right; type. }
                 (* w1 not initial *)
                 assert (a: ([!IW] ⋅ co) w1 w2) by t.
                 left. cut ([!IW]⋅co ≦ S). intros H; now apply H.
                 subst co S_.
                 assert (S^+ ≡ S) as <- by now apply itr_transitive.
                 rewrite Sdom at 1.
                 rewrite leq_cap_l.
                 kat.
              ** (** Second part: we know S w2 r *)
                 subst co.
                 t.
                 now left.
                 now apply loc_trans with w1; destruct_rel; auto; symmetry.
        -- (** rf*) subst S_.
           rewrite S_rf, 2leq_cap_l, <-itr_ext. kat.
        -- (** co *)
           unfold co. rewrite leq_cap_l. kat.
      * (** S_ is indeed acyclic *)
        unfold S_. rewrite acyclic_itr.
        apply acyclic_cup. repeat apply conj.
        -- apply transitive_irreflexive_acyclic; auto.
        -- apply acyclic_incompatible_domain_range. now firstorder.
        -- apply empty_acyclic. unfold is_empty.
           rewrite itr_str_r.
           rewrite itr_str_l.
           hkat.
Admitted.

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
Abort. (*
    rewrite E0, E1.
    rewrite !leq_tst_1.
    ra_normalise.
    unfold is_transitive in Hpo. rewrite Hpo.
    (* note: goal solvable by lattice *)
    assert (rf ⊓ ext ≦ rf) as -> by lattice.
    ka.
Qed.
*)
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
    unfold empty.
    hkat.
Qed.

Lemma cnv_inj (l : level) (X : kat.ops) {_ : kat.laws X} {_ : laws l X} {_ : CNV ≪ l} :
  forall (n : ob X) (a : tst n), [a]° ≡ [a].
Proof.
Abort (* not provable? *).

Lemma cnv_inj {X} (a : dpset X) : [a]° ≡ [a].
Proof.
  compute.
  intros x y. split; intros [? ?]; subst y; destruct (a x); firstorder.
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
    ka.
  - (* atomic *)
    auto.
  - (* main *)
    destrunfold.
    set (MF := (uset _ : dpset _)) in Hghb. fold MF in Hghb.
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
    { rewrite ?kat.inj_cup. ra_normalise. reflexivity. }
    (* some simplification in Hgb *)
    eapply acyclic_weq in Hghb; swap 1 2.
    { rewrite ?kat.inj_cup, E0. ra_normalise. reflexivity. }
    cut (acyclic (po⋅[MF]⋅po + (co + rf ∩ ext + rf°⋅co ∩ !id + [W]⋅po⋅[W] + [R]⋅po⋅[R ⊔ W]))).
    { rewrite ?kat.inj_cup. apply acyclic_weq. hkat. }
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
