From Coq Require Import List.

(** Some results about [map] *)

Lemma map_nil_iff {A B} (f : A -> B) l :
  List.map f l = nil <-> l = nil.
Proof.
  destruct l; simpl; split; congruence.
Qed.

Lemma nth_error_map {A B} (f : A -> B) (n : nat) (l : list A) (b : B) :
  nth_error (List.map f l) n = Some b ->
  exists a, nth_error l n = Some a /\ b = f a.
Proof.
  revert n; induction l; intros [ | n ] Hb.
  - discriminate.
  - discriminate.
  - injection Hb as <-. exists a; firstorder.
  - firstorder.
Qed.

(** Refinement on in_dec *)

Lemma in_dec_refined {A} (a : A) (l : list A) :
  (forall x, { x = a } + { x <> a }) ->
  {In a l} + {~ In a l}.
Proof.
  induction l; firstorder.
Qed.

(** One result about [list_prod] *)

Lemma list_prod_nil_iff {A B} (xs : list A) (ys : list B) :
  list_prod xs ys = nil <-> xs = nil \/ ys = nil.
Proof.
  revert ys.
  induction xs; intros [ | y ys]; simpl; split; firstorder; congruence.
Qed.

(** Some results about Forall2 *)

Lemma Forall2_length {A B} (R : A -> B -> Prop) l1 l2 :
  Forall2 R l1 l2 ->
  Datatypes.length l1 = Datatypes.length l2.
Proof.
  revert l2; induction l1; intros l2 F; inversion F; subst; simpl; firstorder.
Qed.

Lemma Forall2_swap {A B} (R : A -> B -> Prop) l1 l2 :
  Forall2 R l1 l2 ->
  Forall2 (fun b a => R a b) l2 l1.
Proof.
  revert l2; induction l1; intros l2 F; inversion F; firstorder.
Qed.

Lemma Forall2_swap_iff {A B} (R : A -> B -> Prop) l1 l2 :
  Forall2 R l1 l2 <->
  Forall2 (fun b a => R a b) l2 l1.
Proof.
  split; revert l2; induction l1; intros l2 F; inversion F; firstorder.
Qed.

Lemma In_Forall2 {A B} (R : A -> B -> Prop) l1 l2 :
  Forall2 R l1 l2 ->
  forall a, In a l1 -> exists b, In b l2 /\ R a b.
Proof.
  revert l2; induction l1; intros l2 F; inversion F; simpl; subst; firstorder.
  subst; firstorder.
Qed.

Lemma Forall2_In {A B} (R : A -> B -> Prop) l1 l2 :
  Forall2 R l1 l2 ->
  forall b, In b l2 -> exists a, In a l1 /\ R a b.
Proof.
  revert l2; induction l1; intros l2 F; inversion F; simpl; subst; firstorder.
  subst; firstorder.
Qed.

Lemma nth_Forall2 {A B} (R : A -> B -> Prop) l1 l2 :
  Forall2 R l1 l2 ->
  forall i a, nth_error l1 i = Some a ->
         exists b, nth_error l2 i = Some b /\ R a b.
Proof.
  revert l2; induction l1; intros l2 F i a' Ea; inversion F; subst.
  - destruct i; discriminate.
  - destruct i; simpl in *; firstorder.
    injection Ea as <-; firstorder.
Qed.

Lemma Forall2_nth {A B} (R : A -> B -> Prop) l1 l2 :
  Forall2 R l1 l2 ->
  forall i b, nth_error l2 i = Some b ->
         exists a, nth_error l1 i = Some a /\ R a b.
Proof.
  revert l2; induction l1; intros l2 F i a' Ea; inversion F; subst.
  - destruct i; discriminate.
  - destruct i; simpl in *; firstorder.
    injection Ea as <-; firstorder.
Qed.

Lemma Forall2_cons_l_iff {A B} (R : A -> B -> Prop) l1 l2 a :
  Forall2 R (a :: l1) l2 <->
  exists b l2', l2 = b :: l2' /\ R a b /\ Forall2 R l1 l2'.
Proof.
  destruct l2 as [ | b l2'].
  - split. now inversion 1. now firstorder discriminate.
  - split.
    + inversion 1. subst; firstorder.
    + intros (? & ? & H & ? & ?). injection H as <- <-. constructor; auto.
Qed.

Lemma Forall2_cons_r_iff {A B} (R : A -> B -> Prop) l1 l2 b :
  Forall2 R l1 (b :: l2) <->
  exists a l1', l1 = a :: l1' /\ R a b /\ Forall2 R l1' l2.
Proof.
  destruct l1 as [ | a l1'].
  - split. now inversion 1. now firstorder discriminate.
  - split.
    + inversion 1. subst; firstorder.
    + intros (? & ? & H & ? & ?). injection H as <- <-. constructor; auto.
Qed.

Lemma Forall2_map {A B C} (R : A -> B -> Prop) (S : A -> C -> Prop) (f : B -> C) l1 l2 :
  (forall a b, In a l1 -> R a b -> S a (f b)) ->
  Forall2 R l1 l2 ->
  Forall2 S l1 (List.map f l2).
Proof.
  revert l2; induction l1 as [| a l IHl1]; intros l2 RS H.
  - inversion H; destruct l2; subst. constructor. discriminate.
  - inversion H as [ | a_ b l_ l2' ]. subst. simpl.
    constructor; firstorder; apply IHl1; firstorder.
Qed.

Lemma Forall2_map_inv {A B C} (R : A -> B -> Prop) (S : A -> C -> Prop) (f : C -> B) l1 l2 :
  (forall a c, In c l2 -> R a (f c) -> S a c) ->
  Forall2 R l1 (List.map f l2) ->
  Forall2 S l1 l2.
Proof.
  revert l2; induction l1; intros l2 RS H.
  - inversion H; destruct l2; subst. constructor. discriminate.
  - inversion H as [ |  a_ b l l' ]. subst.
    destruct l2 as [ | c l2 ]. discriminate. simpl in *.
    assert (b = f c) by congruence. subst.
    constructor. now firstorder.
    apply IHl1. now firstorder.
    inversion H; subst. firstorder.
Qed.

(** New function [list_list_prod], which is the iteration of [list_prod] *)

Fixpoint list_list_prod {A} (xss : list (list A)) : list (list A) :=
  match xss with
  | nil => nil :: nil
  | xs :: xss =>
    List.map (fun p => fst p :: snd p) (List.list_prod xs (list_list_prod xss))
  end.

Lemma list_list_prod_nil {A} (xss : list (list A)) :
  List.In nil xss <-> list_list_prod xss = nil.
Proof.
  induction xss as [| xs xss IHxss]; simpl; split.
  - tauto.
  - congruence.
  - intros [-> | Hxss].
    + reflexivity.
    + destruct IHxss as [-> _]; simpl; auto.
      destruct (list_prod_nil_iff xs (@nil (list A))) as [_ ->]; auto.
  - intros H. apply map_nil_iff in H.
    apply list_prod_nil_iff in H. tauto.
Qed.

Lemma list_list_prod_in {A} (xss : list (list A)) i x :
  (exists l, List.In l (list_list_prod xss) /\ nth_error l i = Some x) <->
  (~List.In nil xss /\ exists xs, nth_error xss i = Some xs /\ List.In x xs).
Proof.
  revert i x.
  induction xss as [| xs xss IHxss]; intros [ | i] x;
    (split; [intros (l & Hl & Hx) | intros (Hnil & xs' & Hxs' & Hx)]).
  - destruct l; firstorder; simpl in *; congruence.
  - simpl in *; congruence.
  - destruct l; firstorder; simpl in *; congruence.
  - simpl in *; congruence.
  - simpl list_list_prod in Hl.
    rewrite in_map_iff in Hl. destruct Hl as ((x_, l') & <- & Hi).
    simpl in Hx. injection Hx as ->.
    rewrite in_prod_iff in Hi. split. 2: firstorder.
    intros [ | H ]. subst. tauto.
    apply list_list_prod_nil in H. rewrite H in Hi. tauto.
  - simpl in Hxs'. injection Hxs' as <-.
    simpl list_list_prod.
    destruct (list_list_prod xss) as [ | ys yss] eqn:Eys.
    + rewrite <-list_list_prod_nil in Eys. simpl in *; tauto.
    + exists (x :: ys).
      rewrite in_map_iff. split; auto. exists (x, ys). split; auto.
      rewrite in_prod_iff. split; auto.
      now left.
  - split.
    + intros H. apply list_list_prod_nil in H. rewrite H in Hl. tauto.
    + apply IHxss. simpl in Hl.
      rewrite in_map_iff in Hl. destruct Hl as ((x_, l') & <- & Hi).
      simpl in Hx. rewrite in_prod_iff in Hi. firstorder.
  - destruct (IHxss i x) as (_, IH).
    destruct IH as (l & Hl & Hix). now firstorder.
    destruct xs as [|x'' xs'']. now simpl in Hnil; tauto.
    exists (x'' :: l). split; auto.
    apply in_map_iff.
    eexists (_, _); split; [ reflexivity | ].
    apply in_prod_iff.
    split; firstorder.
Qed.

Lemma list_list_prod_in' {A} (L : list (list A)) (l : list A) :
  In l (list_list_prod L) <->
  Forall2 (fun x l' => In x l') l L.
Proof.
  revert l. induction L as [| m L IHL]; intros l.
  - simpl; split. intros [<- | H]. constructor. tauto.
    inversion 1. tauto.
  - simpl. rewrite in_map_iff. rewrite Forall2_cons_r_iff.
    split.
    + intros ((b, l1') & <- & Hi). simpl.
      rewrite in_prod_iff in Hi. destruct Hi as (Hb, Hl1').
      firstorder.
    + intros (b & l1' & -> & Hb & Hl1').
      exists (b, l1'). rewrite in_prod_iff. firstorder.
Qed.
