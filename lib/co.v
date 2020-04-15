From Coq Require Import String Ensembles List Lia.
From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From Catincoq.lib Require Import Cat proprel acyclic list.
Open Scope string_scope.
Open Scope program_scope.

Ltac split_ n :=
  match constr:(n) with
  | O => fail
  | 1%nat => idtac
  | Datatypes.S ?x => split; [ | split_ x ]
  end.
Tactic Notation "split" := split.
Tactic Notation "split" constr(n) := split_ n.
Tactic Notation "split!" := repeat apply conj.

Definition is_strict_order {A} (R : relation A) :=
  is_irreflexive R /\
  is_transitive R.

(* if R is a partial strict order R, then S extends R, is a strict
   order, and is "total along" the equivalence relation ER *)
Definition extends_along {A} (R ER S : relation A) :=
  R ≦ S /\
  is_strict_order S /\
  ER ≡ S ⊔ S° ⊔ 1.

Definition equivalence_class {A} (R : relation A) (C : Ensemble A) :=
  exists x, forall y, R x y <-> C y.

Definition strict_total_order_on {A}  (E : dpset A) (R : relation A) :=
  is_strict_order R /\
  R ≦ [E]⋅top⋅[E] /\
  [E]⋅!1⋅[E] ≦ R ⊔ R°.

Definition linear_extension_on {A} (E : dpset A) (R S : relation A) :=
  R ≦ S /\
  strict_total_order_on E S.

Definition linearisations {A} (E : dpset A) (R : relation A) : Ensemble (relation A) :=
  fun S => strict_total_order_on E S /\ [E] ⋅ R ⋅ [E] ≦ S.

(* à noter que ce n'est pas la même chose que [E] ⋅ R^+ ⋅ [E] *)

Section s.
  Variable A : Type.
  Variable loc : relation A.
  Definition classes_loc : set A -> Ensemble (Ensemble A) :=
    fun S Si => (forall x, Si x -> Ensemble_of_dpset S x) /\ forall x y, Si x -> Si y -> loc x y.
  Definition partition := classes_loc.
  Definition generate_orders s pco := cross (co_locs pco (partition s)).
End s.

Definition spec1 {A} (E : dpset A) (loc R S : relation A) :=
  S ≦ [E] ⋅ S ⋅ [E] /\
  S ⊓ 1 ≦ 0 /\
  S ⋅ S ≦ S /\
  S ≦ loc /\
  forall x y : A,
    loc x y ->
    proj1_sig (E x) ->
    proj1_sig (E y) ->
    (R x y -> S x y) /\ (x <> y -> S x y \/ S y x).

Lemma generate_orders_spec {A} (E : dpset A) (loc R S : relation A) :
  generate_orders A loc E R S <->
  spec1 E loc R S.

Proof.
  unfold generate_orders, cross.
  split.
  - intros (l & L & lS & RL & lL).
    split 5.
    + intros x y. rewrite lS. admit.
    + admit.
    + admit.
    + admit.
    + admit.
Admitted.

Lemma generate_orders_bounds {A} (E : dpset A) (loc R S : relation A) :
  generate_orders A loc E R S -> S ≦ [E] ⋅ S ⋅ [E].
Proof.
  rewrite generate_orders_spec. unfold spec1.
  tauto.
Qed.

Lemma generate_orders_spec_2 {A} (W : dpset A) (loc R S : relation A) :
  generate_orders A loc W R S <->
  extends_along R ([W] ⋅ loc ⋅ [W]) S.
Admitted.

Lemma spec1_spec2 {A} (E : dpset A) (loc R S : relation A) :
  spec1 E loc R S <-> extends_along R ([E]⋅loc⋅[E]) S.
Proof.
  split.
  - intros (Sdom & Sirr & St & Sloc & Stot). split 3.
    + destruct_rel. spec Stot x y. destruct Stot as [RS Stot]; auto.
      admit.
Admitted.

Lemma generate_cos_spec {A} (W IW FW : dpset A) (loc : relation A) :
  let co0 := loc ⊓ ([IW] ⋅ top ⋅ [(W ⊓ !IW)] ⊔ [(W ⊓ !FW)] ⋅ top ⋅ [FW]) in
  let generate_orders s pco := cross (co_locs pco (partition A loc s)) in
  let generate_cos pco := generate_orders W pco in
  forall co,
    generate_cos co0 co ->
    is_strict_order co /\
    [W] ⋅ loc ⋅ [W] ≡ co ⊔ co° ⊔ 1 /\
    [IW] ⋅ loc ⋅ [W ⊓ !IW] ≦ co /\
    [W ⊓ !FW] ⋅ loc ⋅ [FW] ≦ co /\
    True
.
Admitted.

(** idée : pour diminuer le risque d'erreur dans la spec, verifier
qu'un tri topologique ça implémente bien le "linearisations" ? *)

Definition direct_image {A B} (f : A -> B) : Ensemble A -> Ensemble B :=
  fun x b => exists a, x a /\ f a = b.

Definition relational_image {A B} (R : A -> B -> Prop) : Ensemble A -> Ensemble B :=
  fun x b => exists a, x a /\ R a b.

Definition functional_relation_domain {A B} (dom : Ensemble A) (R : A -> B -> Prop) :=
  (forall a, dom a <-> exists b, R a b) /\
  (forall a b b', R a b -> R a b' -> b = b').

Lemma list_fun_rel_dom {A B} (dom : Ensemble A) (R : A -> B -> Prop) :
  functional_relation_domain dom R ->
  forall l : list A, Forall dom l -> exists l' : list B, Forall2 R l l'.
Proof.
  intros [Rdef _] l doml.
  induction l.
  - exists nil. constructor.
  - spec Rdef a. destruct Rdef as [Rdef _].
    spec Rdef by now inversion doml; congruence.
    spec IHl by now inversion doml; congruence.
    destruct Rdef as (b & Hb).
    destruct IHl as (l' & Hl').
    exists (b :: l'). now constructor.
Qed.

Definition one_of_each {X} : Ensemble (Ensemble X) -> Ensemble (Ensemble X) :=
  fun A b => exists f : Ensemble X -> X, Same_set _ b (direct_image f A).

Definition one_of_each' {X} : Ensemble (Ensemble X) -> Ensemble (Ensemble X) :=
  fun A b => exists f : Ensemble X -> X -> Prop,
      (forall e fe, (* (exists x, e x) ->  *)f e fe -> e fe) /\
      functional_relation_domain A f /\
      Same_set _ b (relational_image f A).

Definition finite_set {X} (A : Ensemble X) := exists l, forall x, A x -> List.In x l.

(* Definition list_union {X} (l : list (Ensemble X)) : Ensemble X :=
  fun x => exists xs, List.In xs l /\ xs x.*)

Definition set_of_list {X} : list X -> Ensemble X :=
  fun l x => List.In x l.

Lemma one_of_each_lists {X} (A : Ensemble (Ensemble X)) (b : Ensemble X) :
  finite_set A ->
  (forall a, A a -> finite_set a) ->
  one_of_each' A b <->
  exists l : list ((Ensemble X) * X),
    Same_set _ A (set_of_list (List.map fst l)) /\
    Same_set _ b (set_of_list (List.map snd l)).
Proof.
  intros fA fa.
  split.
  - intros (f & ffun & fb).
    admit.
  - intros (l & lA & lb).
Admitted.

Definition sets_of_lists {X} : list (list X) -> Ensemble (Ensemble X) :=
  fun l => set_of_list (List.map set_of_list l).

Definition inclusion_set_of_set {A} (X Y : Ensemble (Ensemble A)) :=
  forall x, X x -> exists y, Y y /\ Same_set _ x y.

Definition same_set_of_set {A} (X Y : Ensemble (Ensemble A)) :=
  inclusion_set_of_set X Y /\
  inclusion_set_of_set Y X.

Lemma Extensionality_Ensembles' {U} (A B : Ensemble U) :
  Same_set U A B <-> A = B.
Proof.
  split. apply Extensionality_Ensembles. intros ->; firstorder.
Qed.

Lemma Extensionality_Ensembles'' {U} (A : Ensemble U) :
  Same_set U A = eq A.
Proof.
  apply Extensionality_Ensembles'; split; intros B.
  apply Extensionality_Ensembles. intros ->; firstorder.
Qed.

Lemma one_of_each'_spec_list {X} (L : list (list X)) :
  NoDup (List.map set_of_list L) ->
  same_set_of_set
    (one_of_each' (sets_of_lists L))
    (sets_of_lists (list_list_prod L)).
Proof.
  intros Hnodup.
  destruct (in_dec_refined nil L) as [Hnil | Hnil].
  now intros []; firstorder.
  {
    (* case where one of the lists is empty *)
    split.
    - intros image (f & fi & (Hf & WQ) & E).
      exfalso.
      destruct (Hf (set_of_list nil)) as [fnil _].
      spec fnil. {
        unfold sets_of_lists, set_of_list.
        rewrite in_map_iff.
        firstorder.
      }
      destruct fnil as (x, Hx).
      apply fi in Hx.
      tauto.
    - apply list_list_prod_nil in Hnil.
      rewrite Hnil. unfold sets_of_lists at 2. simpl.
      unfold set_of_list. simpl.
      intros x [].
  }
  split.
  - (* suppose we have a choice function f : P(X) -> X. We show that
     the direct image of [[L]] through f is in [[list_list_prod L]] *)
    intros image (f & fi & Hf & E).
    apply Extensionality_Ensembles in E. subst image.
    rewrite Extensionality_Ensembles''.
    exists (relational_image f (sets_of_lists L)). split; auto.
    (* for this, we apply f to the list of [l] where l \in L to get fL,
    the list of images of L through f *)
    epose proof list_fun_rel_dom _ f Hf (List.map set_of_list L).
    spec H by now apply Forall_forall.
    destruct H as [fL HfL].
    unfold sets_of_lists, sets_of_lists, set_of_list at 1.
    rewrite in_map_iff.
    (* this fL is indeed the fL in the image, which is almost a tautology.. *)
    exists fL. split.
    { rewrite <-Extensionality_Ensembles''.
      split.
      - intros fx Hx.
        change (In fx fL) in Hx.
        unfold Ensembles.In.
        edestruct (Forall2_In _ _ _ HfL fx Hx).
        now firstorder.
      - intros fl. unfold Ensembles.In.
        intros (A & AL & Afl).
        change (In A (List.map set_of_list L)) in AL.
        change (In fl fL).
        rewrite in_map_iff in AL. destruct AL as (l & <- & lL).
        epose proof In_Forall2 f _ _ HfL (set_of_list l).
        rewrite in_map_iff in H. spec H by firstorder.
        destruct H as (fl_ & fl_fL & l_fl_).
        enough (fl = fl_) by congruence.
        eapply Hf; eauto.
    }
    (* now that the trivial thing is proved, let's prove fL is in
    list_list_prod *)
    rewrite list_list_prod_in'.
    apply Forall2_swap_iff in HfL.
    eapply Forall2_map_inv; eauto.
    simpl.
    intros a l lL fa.
    apply fi in fa. auto.
  - intros b.
    unfold sets_of_lists at  1.
    unfold set_of_list at 1.
    rewrite in_map_iff.
    intros (l & <- & lL).
    rewrite list_list_prod_in' in lL.
    rewrite Extensionality_Ensembles''.
    exists (set_of_list l). split; auto.
    unfold one_of_each'.
    set (f := fun e x => exists i,
                  nth_error l i = Some x /\
                  set_of_list (nth i L nil) = e).
    exists f.
    split 4.
    + (* f choses an element inside the set *)
      subst f.
      (* intros e fe ne (i & Efe & <-). *)
      intros e fe (i & Efe & <-).
      unfold set_of_list.
      destruct (nth_Forall2 _ _ _ lL i fe Efe) as (m & im & fem).
      erewrite nth_error_nth; eauto.
    + (* f is a functional relation *)
      split.
      * intros e; split.
        -- intros Le.
           unfold sets_of_lists in *.
           unfold set_of_list in *.
           apply In_nth_error in Le.
           destruct Le as (i & Le).
           apply nth_error_map in Le.
           destruct Le as (Li & HLi & ->).
           destruct (Forall2_nth _ _ _ lL _ _ HLi) as (x & m  & xm).
           exists x. exists i. firstorder.
           erewrite nth_error_nth; eauto.
        -- intros (x & i & ix & <-).
           destruct (nth_Forall2 _ _ _ lL _ _ ix) as (m & Lm  & xm).
           erewrite nth_error_nth; eauto.
           hnf.
           rewrite in_map_iff. exists m; firstorder.
           eapply nth_error_In; eauto.
      * (* here, we need the nodup hypothesis: no two lists have the
        same set of elements *)
        intros e x y (i & ix & ei) (j & jy & ej).
        assert (iL : i < Datatypes.length L). {
          erewrite <-Forall2_length; eauto.
          apply nth_error_Some. congruence.
        }
        assert (jL : j < Datatypes.length L). {
          erewrite <-Forall2_length; eauto.
          apply nth_error_Some. congruence.
        }
        enough (i = j) by congruence.
        rewrite NoDup_nth_error in Hnodup.
        spec Hnodup i j.
        spec Hnodup by now rewrite map_length.
        apply Hnodup.
        transitivity (Some e); [ | symmetry ].
        -- rewrite <-ei. eapply map_nth_error. now apply nth_error_nth'.
        -- rewrite <-ej. eapply map_nth_error. now apply nth_error_nth'.
    + (* l is included in f(L) *)
      unfold Included, Ensembles.In, set_of_list.
      intros x Hx.
      hnf.
      apply In_nth_error in Hx.
      destruct Hx as (i, Hi).
      destruct (nth_Forall2 _ _ _ lL _ _ Hi) as (m & im & xm).
      exists (set_of_list m).
      split.
      * unfold sets_of_lists.
        unfold sets_of_lists, set_of_list at 1.
        rewrite in_map_iff.
        exists m.
        firstorder.
        eapply nth_error_In; eauto.
      * exists i. firstorder.
        erewrite nth_error_nth; eauto.
    + hnf.
      intros x (e & eL & i & ix & ie).
      eapply nth_error_In; eauto.
Qed.

