From Coq Require Import Arith List Streams Lia.
From RelationAlgebra Require Import lattice kat.
From Catincoq.lib Require Import Cat proprel tactics.

Definition list_max l := fold_right max O l.

Lemma list_max_app : forall l1 l2,
   list_max (l1 ++ l2) = max (list_max l1) (list_max l2).
Proof.
induction l1; intros l2; [ reflexivity | ].
now simpl; rewrite IHl1, Nat.max_assoc.
Qed.

Lemma list_max_le : forall l n,
  list_max l <= n <-> Forall (fun k => k <= n) l.
Proof.
induction l; simpl; intros n; split; intros H; intuition.
- apply Nat.max_lub_iff in H.
  now constructor; [ | apply IHl ].
- inversion_clear H as [ | ? ? Hle HF ].
  apply IHl in HF; apply Nat.max_lub; assumption.
Qed.

Lemma list_max_lt : forall l n, l <> nil ->
  list_max l < n <-> Forall (fun k => k < n) l.
Proof.
induction l; simpl; intros n Hnil; split; intros H; intuition.
- destruct l.
  + repeat constructor.
    now simpl in H; rewrite Nat.max_0_r in H.
  + apply Nat.max_lub_lt_iff in H.
    now constructor; [ | apply IHl ].
- destruct l; inversion_clear H as [ | ? ? Hlt HF ].
  + now simpl; rewrite Nat.max_0_r.
  + apply IHl in HF.
    * now apply Nat.max_lub_lt_iff.
    * intros Heq; inversion Heq.
Qed.

Lemma lt_list_max l n :
  n < list_max l <-> exists k, n < k /\ In k l.
Proof.
  induction l; split; simpl.
  - intros. now destruct Nat.nlt_0_r with n.
  - intros []; tauto.
  - rewrite Nat.max_lt_iff. firstorder.
  - rewrite Nat.max_lt_iff. intros (? & ? & [ -> | ]); firstorder.
Qed.

Lemma le_list_max l n :
  n <= list_max l <-> (n = O \/ exists k, n <= k /\ In k l).
Proof.
  induction l; split; simpl.
  - firstorder; lia.
  - firstorder. subst; constructor.
  - rewrite Nat.max_le_iff. firstorder.
  - rewrite Nat.max_le_iff. intros [-> | (? & ? & [ -> | ? ])]; firstorder.
Qed.

Inductive iotree :=
  | Done
  | Read (x : nat) (k : nat -> iotree)
  | Write (x v : nat) (k : iotree).

Inductive label :=
  | read (x v : nat)
  | write (x v : nat).

Inductive admissible_label : iotree -> label -> Prop :=
  | admissible_label_read x v k : admissible_label (Read x k) (read x v)
  | admissible_label_write x v k : admissible_label (Write x v k) (write x v).

Inductive iotree_po : relation (label * iotree) :=
  | exec_read x v k l :
      admissible_label (k v) l ->
      iotree_po (read x v, Read x k) (l, k v)
  | exec_write x v k l :
      admissible_label k l ->
      iotree_po (write x v, Write x v k) (l, k).

Definition shift {A} : (nat -> A) -> (nat -> A) := fun f n => f (S n).

Fixpoint exec_iotree (inputs : Stream nat) (t : iotree) : list label :=
  match t with
  | Done => nil
  | Read x k => read x (hd inputs) :: exec_iotree (tl inputs) (k (hd inputs))
  | Write x v k => write x v :: exec_iotree inputs k
  end.

Definition program := list iotree.

Section Definition_of_candidat.

Variable program : program.

Variable inputs : list (Stream nat).

Definition map2 {A B C} (f : A -> B -> C) : list A -> list B -> list C :=
  fun xs ys => List.map (fun ab : A * B => let (a, b) := ab in f a b) (combine xs ys).

Definition threads : list (list label) :=
  map2 exec_iotree inputs program.

Definition event : Set := nat * nat + nat.

Definition loc_of_label (l : label) :=
  match l with | read x _ | write x _ => x end.

Definition all_locations : list nat :=
  List.concat (List.map (List.map loc_of_label) threads).

Definition label_of (e : event) : option label :=
  match e with
  | inl (i_th, i_instr) =>
    match nth_error threads i_th with
    | None => None
    | Some thread => nth_error thread i_instr
    end
  | inr x =>
    if in_dec Nat.eq_dec x all_locations
    then Some (write x 0)
    else None
  end.

Definition is_Some {A} (o : option A) := match o with Some _ => True | None => False end.
Definition is_None {A} (o : option A) := match o with None => True | Some _ => False end.

Definition events_ := { event | is_Some (label_of event) }.

Lemma finite_map {A B} (f : A -> B) :
  (forall b : B, exists a : A, b = f a) ->
  finite A ->
  finite B.
Proof.
  intros Img [l Fa].
  exists (List.map f l).
  intros b.
  destruct (Img b) as (a, ->).
  apply in_map, Fa.
Qed.

Fixpoint dec_filter {A} (f : A -> Prop) (D : forall a, {f a} + {~f a}) (l : list A) :
  list (sig f) :=
  match l with
  | nil => nil
  | x :: xs =>
    match D x with
    | left pr => exist _ x pr :: dec_filter f D xs
    | right _ => dec_filter f D xs
    end
  end.

Lemma dec_filter_in {A} (f : A -> Prop) D (l : list A) :
  (forall a (pr pr' : f a), pr = pr') ->
  forall x, In x (dec_filter f D l) <-> In (proj1_sig x) l.
Proof.
  intros PI.
  induction l; intros x; simpl. tauto.
  destruct (D a) as [d|d]; split.
  - intros [ <- | H ]. now auto. now right; eapply IHl.
  - intros [ -> | H ]. left. destruct x; f_equal. now apply PI. now right; eapply IHl.
  - intros H; right. now apply IHl.
  - intros [ -> | H]. destruct x. tauto. now apply IHl.
Qed.

Lemma finite_events_ : finite events_.
Proof.
  pose (maxlen := list_max (List.map (fun l => List.length l) threads)).
  pose (indices := List.list_prod (seq 0 (length threads)) (seq 0 (maxlen))).
  pose (all := List.map inl indices ++ List.map inr all_locations).
  unshelve refine (ex_intro _ (dec_filter _ _ all) _).
  { intros a. destruct (label_of a). left; apply I. eauto. }
  intros e.
  apply dec_filter_in.
  now intros a; destruct (label_of a); intros [] []; reflexivity.
  destruct e as [e He]; simpl.
  unfold label_of in He.
  unfold all.
  destruct e as [(i, j) | x].
  - unfold indices.
    rewrite in_app_iff, in_map_iff. left. exists (i, j); split; auto.
    rewrite in_prod_iff, 2in_seq. simpl.
    destruct (nth_error threads i) eqn:Ei. 2: now inversion He.
    destruct (nth_error l j) eqn:Ej. 2: now inversion He.
    split; split; auto with *.
    + apply nth_error_Some. congruence.
    + apply lt_list_max. exists (length l). split.
      now apply nth_error_Some; congruence.
      rewrite in_map_iff. exists l. split; auto. eapply nth_error_In; eauto.
  - rewrite in_app_iff, 2in_map_iff. right. exists x; split; auto.
    revert He. destruct (in_dec _ _ _). auto. inversion 1.
Qed.


Variable readfrom : event -> event.

Variable readfrom_is_consistent :
  forall e x v,
    label_of e = Some (read x v) ->
    label_of (readfrom e) = Some (write x v).

Variable write_is_final : event -> bool.

Definition is_read (e : event) := exists x v, label_of e = Some (read x v).

Definition is_write (e : event) := exists x v, label_of e = Some (write x v).

Definition is_initial_write (e : event) := is_write e /\ exists x, e = inr x.

Definition is_final_write (e : event) := is_write e /\ write_is_final e = true.

Definition is_at (x : nat) (e : event) :=
  exists l, label_of e = Some l /\ loc_of_label l = x.

Variable write_is_final_is_consistent :
  forall e,
    is_final_write e ->
    is_initial_write e ->
    forall x e', is_write e' -> is_at x e -> is_at x e' -> e' = e.

Definition finevent := { event | is_Some (label_of event) }.

Program Definition loc_ : relation finevent :=
  fun e1 e2 => exists x, is_at x e1 /\ is_at x e2.

Definition internal (e1 e2 : event) :=
  exists ith i1 i2, e1 = inl (ith, i1) /\ e2 = inl (ith, i2).

Lemma finevent_ext (e1 e2 : finevent) : proj1_sig e1 = proj1_sig e2 -> e1 = e2.
Proof.
  destruct e1 as (e1, H1), e2 as (e2, H2). simpl. intros <-. f_equal.
  destruct (label_of e1); simpl in H1, H2.
  destruct H1, H2. reflexivity. tauto.
Qed.

Program Definition R_ : set finevent := fun e => is_read e.

Program Definition W_ : set finevent := fun e => is_write e.

Program Definition IW_ : set finevent := fun e => is_initial_write e.

Program Definition FW_ : set finevent := fun e => is_final_write e.

Program Definition rf_ : relation finevent :=
  fun w r => is_write w /\ is_read r /\ readfrom r = w.

Program Definition po_ : relation finevent := fun e1 e2 =>
  match e1, e2 with
  | inl (t1, i1), inl (t2, i2) => t1 = t2 /\ i1 < i2
  | _, _ => False
  end.

Lemma rf_wr_ : rf_ ≦ [W_] ⋅ rf_ ⋅ [R_].
Proof.
  intros w r (ww & rr & rf).
  exists r. exists w; split; auto. split; auto.
Qed.

Lemma po_iw_ : po_ ≦ [!IW_] ⋅ po_ ⋅ [!IW_].
Proof.
  intros [[e1|x1] H1] [[e2|x2] H2] Hpo.
  - exists (exist _ (inl e2) H2).
    + exists (exist _ (inl e1) H1); auto.
      split; auto. intros (? & ? & ?); discriminate.
    + split; auto. intros (? & ? & ?); discriminate.
  - destruct e1. tauto.
  - destruct e2. tauto.
  - tauto.
Qed.

Lemma rw_disj_ : R_ ⊓ W_ ≦ bot. Abort (* unused *).

Lemma iw_w_ : IW_ ≦ W_.
Proof.
  intros w (ww & _); apply ww.
Qed.

Lemma iw_uniq_ : [IW_] ⋅ loc_ ⋅ [IW_] ≦ 1.
Proof.
  intros w1 w2 [w2_ [w1_ [<- [ww1 (x1, E1)]] [x [xw1 xw2]]] [-> [ww2 (x2, E2)]]].
  enough (x1 = x2) by now subst; apply finevent_ext; congruence.
  rewrite E1, E2 in *.
  unfold is_at in *; simpl in *.
  destruct (in_dec _ _ _), (in_dec _ _ _), xw1 as (?&xw1&?), xw2 as (?&xw2&?).
  all: try congruence.
  injection xw1 as <-.
  injection xw2 as <-.
  simpl in *.
  congruence.
Qed.

Lemma fw_w_ : FW_ ≦ W_.
Proof.
  intros w (ww & _). apply ww.
Qed.

Lemma rf_loc_ : rf_ ≦ loc_.
Proof.
  intros w r ((x & v & ww) & (x_ & v_ & rr) & E).
  enough (x_ = x) as ->. exists x. split; eexists. now rewrite ww. now rewrite rr.
  rewrite <-E in ww.
  erewrite readfrom_is_consistent in ww; eauto.
  congruence.
Qed.

Lemma r_rf_ : [R_] ≦ top ⋅ rf_.
Proof.
  intros r r_ [<- (x & v & Hr)].
  assert (Hr' : is_Some (label_of (readfrom (proj1_sig r)))).
  now rewrite (readfrom_is_consistent (proj1_sig r) _ _ Hr).
  exists (exist _ (readfrom (proj1_sig r)) Hr'). constructor.
  repeat split. eexists _, _; apply readfrom_is_consistent; eauto.
  eexists _, _; apply Hr.
Qed.

Lemma rf_uniq_ : rf_ ⋅ rf_° ≦ 1.
Proof.
  intros w1 w2 [r (ww1 & rr & E1) (ww2 & rr' & E2)].
  apply finevent_ext.
  congruence.
Qed.

Lemma loc_refl_ : Reflexive loc_.
Proof.
  intros [x i].
  unfold loc_, is_at.
  simpl.
  destruct (label_of x). 2: inversion i.
  eexists; split; eauto.
Qed.

Lemma loc_sym_ : Symmetric loc_.
Proof.
  firstorder.
Qed.

Lemma loc_trans_ : Transitive loc_.
Proof.
  intros e1 e2 e3.
  intros (x & (xl1 & ? & ?) & (xm1 & ? & ?)).
  intros (y & (yl1 & ? & ?) & (ym1 & ? & ?)).
  assert (x = y) as <- by congruence.
  firstorder.
Qed.

Definition internal_ (e1 e2 : finevent) :=
  exists ith i1 i2, proj1_sig e1 = inl (ith, i1) /\ proj1_sig e2 = inl (ith, i2).

Lemma iw_fw_ : [IW_ ⊓ FW_] ⋅ loc_ ⋅ [W_] ≦ top ⋅ [IW_ ⊓ FW_].
Proof.
  intros w1 w2.
  destruct_rel.
  match goal with H : loc_ _ _ |- _ => destruct H end.
  exists w2. constructor.
  enough (w2 = w1) by now subst; eauto.
  apply finevent_ext.
  simpl in *.
  eapply write_is_final_is_consistent; intuition eauto.
Qed.

Lemma r_iw_ : R_ ⊓ IW_ ≦ bot.
Proof.
  compute.
  firstorder congruence.
Qed.

Definition candidate_of_program : candidate :=
  {| events := { event | is_Some (label_of event) };
     R := R_;
     W := W_;
     IW := IW_;
     FW := FW_;
     B := lattice.bot;
     RMW := lattice.bot;
     F := lattice.bot;
     po := po_;
     addr := lattice.bot;
     data := lattice.bot;
     ctrl := lattice.bot;
     rmw := lattice.bot;
     amo := lattice.bot;
     rf := rf_;
     loc := loc_;
     int := fun e1 e2 => internal_ e1 e2;
     ext := fun e1 e2 => ~internal_ e1 e2;
     unknown_set := fun _ => lattice.bot;
     unknown_relation := fun _ => lattice.bot;
     finite_events := finite_events_;
     rf_wr := rf_wr_;
     po_iw := po_iw_;
     iw_w := iw_w_;
     iw_fw := iw_fw_;
     iw_uniq := iw_uniq_;
     r_iw := r_iw_;
     fw_w := fw_w_;
     rf_loc := rf_loc_;
     r_rf := r_rf_;
     rf_uniq := rf_uniq_;
     loc_refl := loc_refl_;
     loc_sym := loc_sym_;
     loc_trans := loc_trans_;
  |}.

End Definition_of_candidat.

Definition candidates_of_program (p : program) : candidate -> Prop :=
  fun c =>
    exists
      inputs
      readfrom
      readfrom_is_consistent
      write_is_final
      write_is_final_is_consistent,
      c = candidate_of_program
            p
            inputs
            readfrom
            readfrom_is_consistent
            write_is_final
            write_is_final_is_consistent.
