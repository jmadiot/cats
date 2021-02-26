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

Ltac types_ :=
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
    | |- (!_) _ => try solve [intro; types_]
    | H : ?X ≦ ?Y, H' : ?X ?x |- ?Y ?x => apply H, H'
    | H : ?X ≦ ?Y |- ?Y ?x => try solve [apply H; types_]
    | |- top _ => constructor
    end.

Tactic Notation "types" := types_.

Tactic Notation "types" var(v) :=
  match goal with
  | H : ?r ?x v, H2 : ?r ≦ [?X] ⋅ ?r ⋅ [?Y] |- _ =>
    assert (Y v) by types
  | H : ?r v ?y, H2 : ?r ≦ [?X] ⋅ ?r ⋅ [?Y] |- _ =>
    assert (X v) by types
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
     end; types; try assumption).

(** [rel t], on a goal of the form [r x y], applies tactic [t] on
    relation [r], in a way that allows rewriting. [t] is typically of
    the form [rewrite e] (if e is of the form [_ ≡ _]) or of the form
    [rewrite <-e] (if e is of the form [_ ≦ _]) *)

Tactic Notation "rel" tactic(t) :=
  match goal with
    x : ?A, y : ?A |- ?r ?x ?y =>
    let s := fresh "s" in
    let H := fresh "H" in
    evar (s : relation A);
    assert (H : s ≦ r);
    [ t; unfold s; reflexivity
    | apply H; unfold s; clear s H ]
  end.

Example rel_example {A} (r : relation A) a b c : r a b -> r b c -> r^+ a c.
Proof.
  intros ab bc.
  rel rewrite <-itr_trans.
  rel rewrite <-itr_ext.
  eexists; eauto.
Qed.

(** [in H rel t] is similar to [rel t] but applies [t] on the relation
    [r] where [H] is an hypothesis of the form [r x y] *)

Tactic Notation "in" hyp(H) "rel" tactic(t) :=
  match type of H with
  | ?r ?x ?y =>
    let A := type of x in
    let s := fresh "s" in
    let L := fresh "L" in
    evar (s : relation A);
    assert (L : r ≦ s);
    [ unfold s; t; reflexivity
    | subst s; try (apply L in H; clear L) ];
    idtac
  end.

(* alternative syntax [rel t in H]: better indentation, but requires
   parentheses in [t] when [t] is e.g. [rewrite _] *)

Tactic Notation "rel" tactic(t) "in" hyp(H) := in H rel t. 

Example in_rel_example {A} (r : relation A) a b c : r a b -> r b c -> r^+ a c.
Proof.
  intros ab bc.
  in ab rel rewrite (itr_ext r).
  rel (rewrite (itr_ext r)) in bc. (* alternative syntax *)
  rel rewrite <-itr_trans.
  eexists; eauto.
Qed.
