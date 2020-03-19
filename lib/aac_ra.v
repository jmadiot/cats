From RelationAlgebra Require Import monoid.
From AAC_tactics Require Export AAC.

(* Section lattice. *)
(*   Context `{lattice.laws}. *)
(*   Global Instance aac_cupA `{CUP ≪ l} : Associative weq cup := cupA. *)
(*   Global Instance aac_cupC `{CUP ≪ l} : Commutative weq cup := cupC. *)
(*   Global Instance aac_cupU `{BOT+CUP ≪ l} : Unit weq cup bot := Build_Unit _ _ _ cupbx cupxb. *)
(*   Global Instance aac_capA `{CAP ≪ l} : Associative weq cap := capA. *)
(*   Global Instance aac_capC `{CAP ≪ l} : Commutative weq cap := capC. *)
(*   Global Instance aac_capU `{TOP+CAP ≪ l} : Unit weq cap top := Build_Unit _ _ _ captx capxt. *)
(*   Global Instance aac_lift_leq_weq : AAC_lift leq weq. *)
(*   Proof. constructor; eauto with typeclass_instances. Qed. *)
(* End lattice. *)
(* Section monoid. *)
(*   Context `{monoid.laws} {n: ob X}. *)
(*   Global Instance aac_dotA: Associative weq (dot n n n) := (@dotA _ _ _ n n n n). *)
(*   Global Instance aac_dotU: Unit weq (dot n n n) (one n). *)
(*   Proof. constructor; intro. apply dot1x. apply dotx1. Qed. *)
(* End monoid. *)


(*

Module RelationAlegra_AAC_Instance.
  Section defs.
    Variable X : Type.
    Definition relation X := hrel X X.
    Variables R S : relation X.
    Definition cap : relation X := R ⊓ S.
    Definition dot : relation X := R ⋅ S.
    Definition neg : relation X := !R.
    Definition cup : relation X := R ⊔ S.
    Definition cnv : relation X := R°.
    Definition bot : relation X := bot.
    Definition top : relation X := top.
    Definition eq  : relation X := 1.
    Definition weq : relation X -> relation X -> Prop := weq.
    Definition leq : relation X -> relation X -> Prop := leq.
  End defs.

  Instance eq_weq X : Equivalence (weq X). apply weq_Equivalence. Qed.

  Instance aac_cup_Comm X : Commutative (weq X) (cup X). firstorder. Qed.
  Instance aac_cup_Assoc X : Associative (weq X) (cup X). firstorder. Qed.
  Instance aac_bot X : Unit (weq X) (cup X) (bot X). firstorder. Qed.

  Instance aac_cap_Comm X : Commutative (weq X) (cap X). firstorder. Qed.
  Instance aac_cap_Assoc X : Associative (weq X) (cap X). firstorder. Qed.
  Instance aac_top X : Unit (weq X) (cap X) (top X). firstorder. Qed.

  Instance aac_dot_Assoc X : Associative (weq X) (dot X). firstorder. Qed.
  Instance aac_1 X : Unit (weq X) (dot X) (eq X).
  Proof. constructor; compute; firstorder; subst; firstorder. Qed.

  Instance neg_weq X : Proper (weq X ==> weq X) (neg X). firstorder. Qed.
  Instance cnv_weq X : Proper (weq X ==> weq X) (cnv X). firstorder. Qed.
  Instance neg_leq X : Proper (leq X ==> flip (leq X)) (neg X). firstorder. Qed.
  Instance cnv_leq X : Proper (leq X ==> leq X) (cnv X). firstorder. Qed.

  Instance itr_weq X : Proper (weq X ==> weq X) (itr X). intros x y ->; reflexivity. Qed.
  Instance str_weq X : Proper (weq X ==> weq X) (str X). intros x y ->; reflexivity. Qed.
  Instance itr_leq X : Proper (leq X ==> leq X) (itr X). intros x y ->; reflexivity. Qed.
  Instance str_leq X : Proper (leq X ==> leq X) (str X). intros x y ->; reflexivity. Qed.

  Instance preorder_leq X : PreOrder (leq X).
  Proof. constructor. firstorder. compute; firstorder. Qed.

  Program Instance lift_inclusion_weq X : AAC_lift (leq X) (weq X) := Build_AAC_lift (eq_weq X) _.

End RelationAlegra_AAC_Instance.

Example example {X} (A: dset X) (R S : relation X) :
  (R ⊔ S ≦ R) ->
  ((S ⊔ [A] ⊔ S) ⊔ R ≦ R ⊔ [A]).
Proof.
  intros e.
  Set Printing All.
  do 2 aac_rewrite e. reflexivity.
Qed.
*)


(*
From RelationAlgebra Require Import kat_tac relalg kat.


From Catincoq Require Export Cat proprel.

Module RelationAlegra_AAC_Instance.
  Section defs.
    Variable X : Type.
    Variables R S: relation X.
    Definition cap : relation X := R ⊓ S.
    Definition dot : relation X := R ⋅ S.
    Definition neg : relation X := !R.
    Definition cup : relation X := R ⊔ S.
    Definition cnv : relation X := R°.
    Definition bot : relation X := bot.
    Definition top : relation X := top.
    Definition eq  : relation X := 1.
    Definition weq : relation X -> relation X -> Prop := weq.
    Definition leq : relation X -> relation X -> Prop := leq.
  End defs.

  Instance eq_weq X : Equivalence (weq X). apply weq_Equivalence. Qed.

  Instance aac_cup_Comm X : Commutative (weq X) (cup X). firstorder. Qed.
  Instance aac_cup_Assoc X : Associative (weq X) (cup X). firstorder. Qed.
  Instance aac_bot X : Unit (weq X) (cup X) (bot X). firstorder. Qed.

  Instance aac_cap_Comm X : Commutative (weq X) (cap X). firstorder. Qed.
  Instance aac_cap_Assoc X : Associative (weq X) (cap X). firstorder. Qed.
  Instance aac_top X : Unit (weq X) (cap X) (top X). firstorder. Qed.

  Instance aac_dot_Assoc X : Associative (weq X) (dot X). firstorder. Qed.
  Instance aac_1 X : Unit (weq X) (dot X) (eq X).
  Proof. constructor; compute; firstorder; subst; firstorder. Qed.

  Instance neg_weq X : Proper (weq X ==> weq X) (neg X). firstorder. Qed.
  Instance cnv_weq X : Proper (weq X ==> weq X) (cnv X). firstorder. Qed.
  Instance neg_leq X : Proper (leq X ==> flip (leq X)) (neg X). firstorder. Qed.
  Instance cnv_leq X : Proper (leq X ==> leq X) (cnv X). firstorder. Qed.

  Instance itr_weq X : Proper (weq X ==> weq X) (itr X). intros x y ->; reflexivity. Qed.
  Instance str_weq X : Proper (weq X ==> weq X) (str X). intros x y ->; reflexivity. Qed.
  Instance itr_leq X : Proper (leq X ==> leq X) (itr X). intros x y ->; reflexivity. Qed.
  Instance str_leq X : Proper (leq X ==> leq X) (str X). intros x y ->; reflexivity. Qed.

  Instance preorder_leq X : PreOrder (leq X).
  Proof. constructor. firstorder. compute; firstorder. Qed.

  Program Instance lift_inclusion_weq X : AAC_lift (leq X) (weq X) := Build_AAC_lift (eq_weq X) _.

End RelationAlegra_AAC_Instance.
(* Import RelationAlegra_AAC_Instance. *)
*)

(* Example example {X} (A:dpset X) (R S : relation X) : *)
(*   (R ⋅ [A] ≦ R) -> *)
(*   ((R ⋅ [A] ⋅ S) ⋅ R ≦ R ⋅ [A]). *)
(* Proof. *)
(*   intros e. *)
(*   Set Printing All. *)
(*   aac_rewrite e. *)
(*   reflexivity. *)
(* Qed. *)

(*
(* TODO do this for any ka(t) instance? (but there are many, maybe
that can be a requirement of every Proper) *)

Module RelationAlegra_AAC_Instance.
  (* TODO remove this section? *)
  (*Section defs.
    Variable T : Type.
    Variables R S: relation T.
    Definition inter : relation T := R ⊓ S.
    Definition compo : relation T := R ⋅ S.
    Definition negr  : relation T := !R.
    Definition union : relation T := R ⊔ S.
    Definition cnv   : relation T := R°.
    Definition dot'   : relation T := R ⋅ S.
    Definition bot'   : relation T := bot.
    Definition top'   : relation T := top.
  End defs.*)

  Context `{lattice.ops} `{lattice.laws}.
  Instance eq_weq : Equivalence weq. Proof. apply weq_Equivalence. Qed.

  Instance aac_cup_Comm : Commutative weq cup. Proof. Admitted.
  Instance aac_cup_Assoc : Associative weq cup. Admitted.
  Instance aac_bot : Unit weq cup bot. Admitted.

  Instance aac_cap_Comm : Commutative weq cap. Admitted.
  Instance aac_cap_Assoc : Associative weq cap. Admitted.
  Instance aac_top : Unit weq cap top. Admitted.

  Instance aac_dot_Assoc {obs} (T : ob obs) : Associative weq (dot T T T). Admitted.
  Instance aac_1 {obs} (T : ob obs) : Unit weq (dot T T T) 1. Admitted.

  Instance neg_compat : Proper (weq ==> weq) neg. Admitted.

  Instance cnv_compat `{monoid.laws} {obs} (T : ob obs) : Proper (weq ==> weq) (cnv T). firstorder. Qed.

  Lemma qq {X} (R S : relation X) : (R ⊔ S ≡ R) -> ((S ⊔ S) ⊔ R ≡ R).
  Proof.
    intros e. aac_rewrite e.
  Qed.

  Instance itr_compat {obs} (T : ob obs) : Proper (weq ==> weq) (itr T). Admitted.
  Instance clos_trans_compat T: Proper (weq ==> weq) (clos_trans T).
  Proof. intros R S H; split; apply clos_trans_incr, H. Qed.

  Instance clos_refl_trans_incr T : Proper (inclusion T ==> inclusion T) (clos_refl_trans T).
  Proof.
    intros R S H x y Hxy. induction Hxy.
      constructor 1. apply H. assumption.
      constructor 2.
      econstructor 3; eauto 3.
  Qed.
  Instance clos_refl_trans_compat T : Proper (weq ==> weq) (clos_refl_trans T).
  Proof. intros R S H; split; apply clos_refl_trans_incr, H. Qed.

  Instance preorder_inclusion T : PreOrder (inclusion T).
  Proof. constructor; unfold Reflexive, Transitive, inclusion; intuition.   Qed.

  Program Instance lift_inclusion_weq: AAC_lift (inclusion T) weq :=
    Build_AAC_lift (eq_weq) _.
  Next Obligation. firstorder. Qed.

End Relations.
*)
