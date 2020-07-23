Ltac split_ n :=
  match constr:(n) with
  | O => fail
  | 1%nat => idtac
  | Datatypes.S ?x => split; [ | split_ x ]
  end.

Tactic Notation "split" := split.
Tactic Notation "split" constr(n) := split_ n.
Tactic Notation "split!" := repeat apply conj.

Tactic Notation "spec" hyp(H) :=
  match type of H with
    forall _ : ?a, _ =>
    let Ha := fresh in
    assert (Ha : a); [ | specialize (H Ha); clear Ha ]
  end.

Tactic Notation "spec" hyp(H) constr(t1) := specialize (H t1).
Tactic Notation "spec" hyp(H) constr(t1) constr(t2) := specialize (H t1 t2).
Tactic Notation "spec" hyp(H) constr(t1) constr(t2) constr(t3) := specialize (H t1 t2 t3).

Tactic Notation "spec" hyp(H) "by" tactic(t) :=
  spec H; [ now t | ].

Tactic Notation "apply" "!" constr(t) := repeat apply t.

Tactic Notation "apply" "?" constr(t) := try apply t.

From RelationAlgebra Require Import prop monoid kat relalg kat_tac.

Ltac destruct_rel :=
  repeat
    match goal with
    | |- _ ≡ _ => intros x y; split; intro
    | |- _ ≦ _ => intros x y ? || intros ? ? || intro
    | |- _ -> _ => intro
    | |- (!_) _ _ => intro
    | H : ?R° ?x ?y |- _ => change (R° x y) with (R y x) in H
    | H : (_ ⊓ _) _ _ |- _ => destruct H as [? ?]
    | H : (_ ⊓ _) _ |- _ => destruct H as [? ?]
    | H : (_ ⊔ _) _ _ |- _ => destruct H
    | H : (_ ⊔ _) _ |- _ => destruct H
    | H : ([_] ⋅ _) _ _ |- _ => destruct H as [? [<- ?] ?]
    | H : (1 ⋅ _) _ _ |- _ => destruct H as [? <- ?]
    | H : (_ ⋅ [_]) _ _ |- _ => destruct H as [? ? [-> ?]]
    | H : (_ ⋅ 1) _ _ |- _ => destruct H as [? ? ->]
    | H : (_ ⋅ _) _ _ |- _ => destruct H
    | H : [_] ?x ?x |- _ => destruct H as [_ H]
    | H : [_] _ _ |- _ => destruct H as [->]
    | H : 1 _ _ |- _ => destruct H
    end.

Tactic Notation "elim_trans" constr(r) :=
  let Heq := fresh "Heq" in
  assert (Heq : r ≡ r^+) by (now symmetry; apply itr_transitive);
  rewrite Heq in *;
  clear Heq.

Tactic Notation "elim_trans" :=
  match goal with
  | H : is_transitive ?r |- _ => elim_trans r; clear H
  | H : ?r ⋅ ?r ≦ ?r |- _ => elim_trans r; clear H
  end.

From Catincoq.lib Require Import proprel.

Lemma cnvtst {A} {E : set A} : [E]° ≡ [E].
Proof.
  intros a b; split; intros [-> Ha]; constructor; auto.
Qed.

Tactic Notation "elim_cnv" :=
  repeat (rewrite ?cnvtst, ?cnv1, ?cnv0, ?cnvstr, ?cnvitr,
          ?cnvtop, ?cnvcap, ?cnvdot, ?cnvpls, ?cnvneg).

Tactic Notation "elim_cnv" "in" hyp(H) :=
  repeat (rewrite ?cnvtst, ?cnv1, ?cnv0, ?cnvstr, ?cnvitr,
          ?cnvtop, ?cnvcap, ?cnvdot, ?cnvpls, ?cnvneg in H).


(** Help solve goals and generate constraints based on the "type" of
    some events i.e. the set to which it belongs, such as R, W, !W,
    etc. *)

Ltac type_ :=
  repeat
    match goal with
    | Hx : ?X |- ?X => assumption
    | Hx : (_ ⊓ _) _ |- _ => destruct Hx
    | Hx : ?X ?x, Hy : ?Y ?x, XY : ?X ⊓ ?Y ≦ bot |- _ =>
      eapply XY; split; eauto
    | H : (?r ⋅ [?Y]) ?x ?v |- ?Y ?v => destruct_rel; assumption
    | H : ([?X] ⋅ ?r ⋅ [?Y]) ?x ?v |- ?Y ?v => destruct_rel; assumption
    | H : ([?X] ⋅ ?r ⋅ [?Y]) ?v ?y |- ?X ?v => destruct_rel; assumption
    | H : ?r ?x ?v, H2 : ?r ≦ [?X] ⋅ ?r ⋅ [?Y] |- ?Y ?v =>
      assert (([X] ⋅ r ⋅ [Y]) x v) by apply H2, H;
      destruct_rel; assumption
    | H : ?r ?v ?y, H2 : ?r ≦ [?X] ⋅ ?r ⋅ [?Y] |- ?X ?v =>
      assert (([X] ⋅ r ⋅ [Y]) v y) by apply H2, H;
      destruct_rel; assumption
    | |- (_ ⊓ _) _ => split
    | |- (!_) _ => try solve [intro; type_]
    | H : ?X ≦ ?Y, H' : ?X ?x |- ?Y ?x => apply H, H'
    | H : ?X ≦ ?Y |- ?Y ?x => try solve [apply H; type_]
    | |- top _ => constructor
    end.

Tactic Notation "type" := type_.

Tactic Notation "type" var(v) :=
  match goal with
  | H : ?r ?x v, H2 : ?r ≦ [?X] ⋅ ?r ⋅ [?Y] |- _ =>
    assert (Y v) by type
  | H : ?r v ?y, H2 : ?r ≦ [?X] ⋅ ?r ⋅ [?Y] |- _ =>
    assert (X v) by type
  end.


(** Somewhat dual to destruct_rel: helps solve goals of the form
    [(some relation) x y] *)

Ltac relate :=
  repeat
    (match goal with
     | |- (_ ⋅ [_]) ?x ?y => exists y; [ | split; auto ]
     | |- ([_] ⋅ [_] ⋅ _) ?x ?y => exists x
     | |- ([_] ⋅ [_] ⋅ [_] ⋅ _) ?x ?y => exists x
     | |- ([_] ⋅ _) ?x ?y => exists x; [ split; auto | ]
     | |- (_ ⊓ _) ?x ?y => split; auto
     | |- [_] ?x ?y => split; [ reflexivity | ]
     | |- 1 ?x ?y => reflexivity
     | |- top ?x ?y => constructor
     | |- ?R° ?x ?y => change (R y x)
     | |- _ => idtac
     end; type; try assumption).
