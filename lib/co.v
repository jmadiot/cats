From Coq Require Import String Ensembles List Lia.
From RelationAlgebra Require Import prop monoid kat relalg kat_tac.
From Catincoq.lib Require Import defs Cat proprel tactics oneofeach relalglaws.

(** This file uses fun and prop extensionalities in many places, it's
not sure yet whether we will get rid of them or just add them as
axioms and simplify the proofs everywhere *)

Axiom functional_extensionality : forall {A B} (f g : A -> B), (forall x, f x = g x) -> f = g.
Axiom propositional_extensionality : forall (P Q : Prop), P <-> Q -> P = Q.

Lemma rel_ext : forall {A} (R S : relation A), R ≡ S -> R = S.
Proof.
  intros A R S e.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  apply propositional_extensionality, e.
Qed.

Lemma sig_ext : forall {A} (P : A -> Prop) (x y : sig P), proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros A P [x px] [y py]. simpl. intros <-. f_equal.
  apply Coq.Logic.ClassicalFacts.ext_prop_dep_proof_irrel_cic.
  hnf.
  apply propositional_extensionality.
Qed.

Lemma set_ext {A} (E E' : set A) : E ≡ E' <-> E = E'.
Proof.
  split. 2:intros ->; auto.
  intros e.
  apply functional_extensionality; intros x.
  apply propositional_extensionality, e.
Qed.

Lemma to_set_cap {A} E F : Intersection A E F ≡ E ⊓ F.
Proof.
  intros x; split; intros []; split; auto.
Qed.

Lemma set_weq {A} (E E' : set A) :
  (forall a, E a <-> E' a) -> E ≡ E'.
Proof.
  firstorder.
Qed.

Instance Inhabited_leq A : Proper (flip leq --> impl) (Inhabited A).
Proof.
  compute. firstorder.
Qed.

Instance Inhabited_weq A : Proper (weq --> iff) (Inhabited A).
Proof.
  compute. firstorder.
Qed.

(** TODO remove this def *)
(* if R is a partial strict order R, then S extends R, is a strict
   order, and is "total along" the equivalence relation ER *)
Definition extends_along {A} (R ER S : relation A) :=
  R ≦ S /\
  is_strict_order S /\
  ER ≡ S ⊔ S° ⊔ 1.

(* TODO remove *)
(* Definition equivalence_classes_sig {A} (R : relation A) : Ensemble A -> Type := *)
(*   fun C => { x | C x /\ forall y, R x y <-> C y }. *)

Lemma loc_sym_ {c} (x y : events c) : loc c x y <-> loc c y x.
Proof.
  split; apply loc_sym.
Qed.

Lemma loc_sym__ {c} : (loc c)° ≡ loc c.
Proof.
  split; apply loc_sym.
Qed.

(** below, trying to define [location] as [loc] equivalence classes,
    but that seems convoluted, it's probably better to define
    [location] in Cat.v *)
(** this can be implemented with [equivalence_classes] but it seems
backwards, so maybe we should define [loc] with [location_of] instead *)
Definition location (c : candidate) : Type := sig (equivalence_classes (loc c)).

Program Definition location_of {c} (x : events c) : location c
  := exist _ (fun y => loc _ x y) (ex_intro _ x (conj (loc_refl c _) ltac:(tauto))).

Lemma location_of_spec : forall c x y , location_of x = location_of y <-> loc c x y.
Proof.
  intros c x y; split.
  - intros [=e]. change ((fun y : events c => loc c x y) y). rewrite e. apply loc_refl.
  - intros e. apply sig_ext. simpl.
    apply functional_extensionality; intros z.
    apply propositional_extensionality; split.
    + intros. apply loc_trans with x; auto. now apply loc_sym.
    + intros. apply loc_trans with y; auto.
Qed.

Lemma location_of_surj : forall {c} (l : location c), exists e, location_of e = l.
Proof.
  intros c [C (x & Cx & xC)]. exists x. apply sig_ext; simpl.
  apply functional_extensionality; intros z.
  apply propositional_extensionality; split; apply xC.
Qed.

Definition atloc {c} (l : location c) : set (events c) := fun e => location_of e = l.

(*
(** this can be implemented with [equivalence_classes] but it seems
backwards, so maybe we should define [loc] with [location_of] instead *)
(* Definition location (c : candidate) : Type := equivalence_classes (loc c). *)
Variable location : candidate -> Type.
Variable location_eq_dec : forall {c} (l1 l2 : location c), {l1 = l2} + {l1 <> l2}.
Variable location_of : forall {c}, events c -> location c.
Variable location_of_spec : forall c (e1 e2 : events c),
    location_of e1 = location_of e2 <-> loc c e1 e2.
Variable location_of_surj : forall {c} (l : location c), exists e, location_of e = l.
Program Definition atloc {c} (l : location c) : set (events c) :=
  fun e => exist _ (location_of e = l) _.
Next Obligation. destruct (location_eq_dec (location_of e) l); auto. Defined.
*)

(* TODO eliminate these definitions? *)
Definition strict_total_order_on {A}  (E : set A) (R : relation A) :=
  is_strict_order R /\
  R ≦ [E] ⋅ top ⋅ [E] /\
  total_on E R.

(*
Definition linear_extension_on {A} (E : set A) (R S : relation A) :=
  R ≦ S /\ strict_total_order_on E S.
*)

(** [linearisations E R] is the set of strict total orders that
contain ([R] restricted to [E]). When [R] is not itself transitive, it
is possible that the result is different from [linearisations E (R^+)]
*)

(*
Definition linearisations {A} (E : set A) (R : relation A)
  : Ensemble (relation A)
  := fun S => strict_total_order_on E S /\ [E] ⋅ R ⋅ [E] ≦ S.
*)
(*
Definition linearisations' {A} (E : Ensemble A) (R : relation A)
  : Ensemble (relation A)
  := fun S => strict_total_order_on' E S /\ [E] ⋅ R ⋅ [E] ≦ S.
*)

(* the finite version of this is proved in zoo.v *)

Lemma strict_order_of_acyclic {A} (R : relation A) :
  acyclic R <-> is_strict_order (R^+).
Proof.
  unfold acyclic, is_strict_order, is_transitive, relalg.is_irreflexive. intuition hkat.
Qed.

(*
(* TODO unused? *)
Lemma linearisations_exist {A} (E : set A) (R : relation A) :
  finite_set E ->
  acyclic ([E] ⋅ R ⋅ [E]) -> exists S, linearisations E R S.
Proof.
  intros F OR % strict_order_of_acyclic.
  destruct (every_strict_order_can_be_total_on E (([E]⋅R⋅[E])^+)) as (S & OS & SE & Tot & RS);
    try (intros; apply Classical_Prop.classic).
  assumption.
  now apply is_strict_order_spec.
  exists S. split. split; auto. now apply is_strict_order_spec.
  repeat (easy || split). rewrite <-RS. kat.
Qed.
*)

(** This is the code for classes_loc that is indroduced by the cat2coq
translation. The following lemma is the glue between the two notions
but in fact there are several gaps, [classes_loc E F] implies
[classes_loc E F'] for every F' included in F -- this will be useless
in time since we will replace [classes_loc] with [partition] in
cat2coq *)
Definition classes_loc {c} : set (events c) -> Ensemble (Ensemble (events c)) :=
  fun S Si => (forall x, Si x -> Ensemble_of_dpset S x) /\ forall x y, Si x -> Si y -> loc c x y.
Lemma classes_loc_partition {c} : @classes_loc c = partition (loc c).
Proof.
  apply functional_extensionality; intros E.
  apply functional_extensionality; intros F.
  apply propositional_extensionality; split.
  - admit.
  - intros (i & G & (x & Gx & xG) & ->).
    destruct i as (_ & [y Ey Gy]).
    split.
    + intros _ [z e g]. apply e.
    + intros _ _ [z ez gz] [t et gt].
      apply xG in gz.
      apply xG in gt.
      eapply (loc_trans c). apply loc_sym; eauto. eauto.
Abort.

Lemma partition_spec {c} (E : Ensemble (events c)) (E' : Ensemble (events c)) :
  partition (loc c) E E' <-> Inhabited _ E' /\ exists l, E' ≡ atloc l ⊓ E.
Proof.
  split.
  - intros (i & C & Ceq & ->). split; auto.
    destruct Ceq as (x & Cx & xC).
    exists (location_of x).
    rewrite to_set_cap.
    enough (C ≡ atloc (location_of x)) as ->. now apply capC.
    apply set_weq. simpl. intros y. now rewrite <-xC, <-location_of_spec.
  - intros (i & l & e). split; auto. eexists (atloc l). split.
    + destruct (location_of_surj l) as (x, <-). exists x. split. easy.
      intros y. rewrite <-location_of_spec. easy.
    + apply Extensionality_Ensembles'; split.
      * intros x ex. split; apply e, ex.
      * intros x []. apply e; split; auto.
Qed.

(* Previous definition that included sets that were too small: *)
(* Definition partition {A} (equiv : relation A) (X : Ensemble A) *)
(*   : Ensemble (Ensemble A) *)
(*   := fun Xi => (forall x, Xi x -> X x) /\ forall x y, Xi x -> Xi y -> equiv x y. *)

Lemma union_of_relations_leq {A} Rs (S : relation A) :
  union_of_relations Rs ≦ S <-> forall R, Rs R -> R ≦ S.
Proof.
  split.
  - intros L R r. rewrite <-L. intros x y xy. exists R; auto.
  - intros L x y (R & r & xy). eapply L; eauto.
Qed.

(* All linearisations of [R] along different [sets] *)
Definition co_locs {A} (R : relation A) (sets : Ensemble (Ensemble A))
  : Ensemble (Ensemble (relation A))
  := subset_image (fun E => linearisations E R) sets.

(* TODO remove the definition above -- as long as the lemma below is
proved, the rest of this file (and probably all the repo) will work *)
Lemma co_locs_partition_spec {c} R E S :
  co_locs R (partition (loc c) E) S <->
  exists l, Inhabited _ (E ⊓ atloc l) /\ S = linearisations (E ⊓ atloc l) R.
Proof.
  split.
  - intros (E' & (i & C & (x & Cx & xC) & ->) & ->).
    exists (location_of x).
    enough (Intersection (events c) E C = E ⊓ atloc (location_of x)) as <-; auto.
    apply set_ext.
    rewrite to_set_cap, set_ext. f_equal. apply set_ext.
    intros a. rewrite <-xC, <-location_of_spec. unfold atloc. split; auto.
  - intros (l & i & ->).
    unfold co_locs, subset_image.
    set (x := (E ⊓ atloc l)). exists x. subst x.
    split; auto.
    rewrite partition_spec. split; auto.
    exists l. now rewrite capC.
Qed.

(*
Definition cross {A} (S : Ensemble (Ensemble (relation A)))
  : Ensemble (relation A)
  := subset_image union_of_relations (one_of_each S).
*)

Definition generate_orders A (loc : relation A) (s : set A) (pco : relation A)
  : Ensemble (relation A)
  := cross (co_locs pco (partition loc s)).

(* alternate specification for [generate_orders E R S], that is, [S]
must relate any two [R]-related [E] events at the same location, and
be a linearisation of [E] on each location *)

Lemma co_locs_located {c} R (E : set _) x (Ex : E x) :
  co_locs R (partition (loc c) E) (linearisations (E ⊓ atloc (location_of x)) R).
Proof.
  apply co_locs_partition_spec; eexists; split; [ | easy ].
  exists x; easy.
Qed.

(* TODO when done, maybe remove: *)
Lemma co_locs_colocated {c} R (E : set _) x y (Ey : E y) (xy : loc c x y) :
  co_locs R (partition (loc c) E) (linearisations (E ⊓ atloc (location_of x)) R).
Proof.
  apply co_locs_partition_spec; eexists; split; [ | easy ].
  exists y; split; auto. apply location_of_spec, loc_sym, xy.
Qed.

Lemma co_locs_atloc {c} R (E : set _) l x (Ex : E x) (lx : atloc l x) :
  co_locs R (partition (loc c) E) (linearisations (E ⊓ atloc l) R).
Proof.
  apply co_locs_partition_spec; eexists; split; [ | easy ].
  exists x; easy.
Qed.

Lemma co_locs_inhabited {c} R (E : set _) x :
  Inhabited (events c) (E ⊓ atloc (location_of x)) ->
  co_locs R (partition (loc c) E) (linearisations (E ⊓ atloc (location_of x)) R).
Proof.
  intro i.
  apply co_locs_partition_spec; eauto.
Qed.

Lemma generate_orders_spec_3 {c} E (R S : relation (events c)) :
  generate_orders (events c) (loc c) E R S <->
  (R ⊓ [E] ⋅ loc c ⋅ [E]) ≦ S
  /\ S ≦ loc c
  /\ forall l, strict_total_order_on (E ⊓ atloc l) ([atloc l] ⋅ S ⋅ [atloc l]).
Proof.
  split.
  - (* Let [f] be the function choosing the linearisation for each
    location. [S] is the union of all those linearisations. *)
    intros [rels [(f & f_sound & (f_tot & f_fun) & ->%Extensionality_Ensembles') ->]].
    split; [ | split ].
    + intros x y.
      destruct_rel.
      pose (l := location_of x).
      (* pose (R' := ([E ⊓ atloc l] ⋅ R ⋅ [E ⊓ atloc l])). *)
      specialize (f_tot (linearisations (E ⊓ atloc l) R)). apply proj1 in f_tot.
      destruct f_tot as [S RS]. now apply co_locs_located.
      exists S. split. eexists. split; eauto. now apply co_locs_located.
      apply f_sound in RS. destruct RS as (_ & _ & _ & RS). apply RS.
      * exists y; auto. exists x; auto. repeat (split; auto). repeat (split; auto). simpl.
        subst l. symmetry. now apply location_of_spec.
    + apply union_of_relations_leq.
      intros S (Rl & (l & i & ->) % co_locs_partition_spec & RS). apply f_sound in RS.
      destruct RS as (_ & e & _ & _). rewrite e.
      intros x y.
      rewrite tst_dot_tst.
      intros ((_, ?) & _ & (_, ?)).
      apply location_of_spec.
      congruence.
    + (* Let us prove that this union of relation is a strict total
         order for each location*)
      intros l; split; split.
      * (* irreflexivity *)
        unfold relalg.is_irreflexive. apply antisym; [ | ka ].
        assert ([atloc l] ≦ 1) as -> by kat. ra_normalise.
        intros x y [(S, ((R' & (aa & bb & ->)
                          & ((ST, SI) & Sdom & Stot & RS) % f_sound), xx)) <-].
        apply SI. split; easy.
      * (* transitivity *)
        unfold is_transitive.
        intros x z [y xy yz].
        specialize (f_tot (linearisations (E ⊓ atloc (location_of x)) R)).
        apply proj1 in f_tot.
        rewrite tst_dot_tst in *.
        destruct xy as (lx & xy & ly).
        destruct yz as (_  & yz & lz).
        destruct xy as (T & (R' & (l' & i & ->) % co_locs_partition_spec & fRT) & xy).
        destruct yz as (U & (R' & (l'' & i' & ->) % co_locs_partition_spec & fRU) & yz).
        split; auto. split; auto.
        destruct (f_sound _ _ fRT) as ((TT & TI) & TE & ET & RT).
        destruct (f_sound _ _ fRU) as ((TU & UI) & UE & EU & RU).
        assert (l' = location_of x /\ l' = location_of y) as [].
        { (* TODO automate this *)
          apply TE in xy. destruct xy as [? [? [<- [_ ?]]] [-> [_ ?]]]. easy. }
        assert (l'' = location_of y /\ l'' = location_of z) as [].
        { (* TODO automate this *)
          apply UE in yz. destruct yz as [? [? [<- [_ ?]]] [-> [_ ?]]]. easy. }
        subst l' l''.
        replace (location_of y) with (location_of x) in fRU.
        assert (T = U) by now eapply f_fun; eauto. subst T.
        exists U. split. 2: now apply TU; exists y; auto.
        eexists. split; eauto. now apply co_locs_inhabited.
      * (* domain/range are in [E] *)
        intros x y xy.
        rewrite tst_dot_tst in xy. destruct xy as (lx & xy & ly).
        destruct xy as (S & (qdw & (l' & i & ->) % co_locs_partition_spec
                          & (OS & SE & ES & RS) % f_sound) & xy).
        apply SE in xy.
        rewrite tst_dot_tst in xy. destruct xy as ((Ex, l'x) & _ & (Ey, l'y)).
        assert (l = l') as <- by now rewrite <-lx, <-l'x.
        rewrite tst_dot_tst. easy.
      * (* totality on [E ⊓ atloc l] *)
        unfold total_on.
        elim_cnv. ra_normalise.
        intros x y xy.
        pose proof xy as xy'.
        rewrite tst_dot_tst in xy. destruct xy as ((l'x, Ex) & _ & (l'y, Ey)).
        specialize (f_tot (linearisations (E ⊓ atloc l) R)). apply proj1 in f_tot.
        destruct f_tot as [S fRS]. now eapply co_locs_atloc; eauto.
        destruct (f_sound _ _ fRS) as ((SI & ST) & SE & ES & RS).
        destruct (ES x y) as [xy | yx]. now auto.
        -- left.
           rewrite tst_dot_tst.
           intuition.
           exists S; intuition.
           eexists; split; eauto.
           now eapply co_locs_atloc; eauto.
        -- right.
           rewrite tst_dot_tst.
           intuition.
           exists S; intuition.
           eexists; split; eauto.
           now eapply co_locs_atloc; eauto.
  - (* suppose [S] covers [R ⊓ loc] on [E], that [S ≦ loc] and that it
       is a strict total order on each location. We show it satisfies
       [generate_orders] *)
    intros (RS & Sloc & ES).
    assert (Slocx : forall x y l,
               S x y -> l = location_of x ->
               ([E ⊓ atloc l] ⋅ S ⋅ [E ⊓ atloc l]) x y).
    { intros x y l xy ->. destruct (ES (location_of x)) as (_ & SE & _).
      spec SE x y. hnf in SE. spec SE.
      - rewrite tst_dot_tst; intuition. reflexivity.
        apply location_of_spec, loc_sym, Sloc, xy.
      - rewrite tst_dot_tst in *. tauto. }
    (* [S] is the union of all its restrictions to a location... that
       are not empty (this is necessary since [partition] excludes
       empty sets) *)
    exists (fun Sl : relation _ => exists l, Inhabited _ (E ⊓ atloc l)
                                /\ Sl = [atloc l]⋅S⋅[atloc l]).
    split; swap 1 2.
    + apply rel_ext, antisym; intros x y xy.
      * exists ([atloc (location_of x)]⋅S⋅[atloc (location_of x)]).
        split.
        -- exists (location_of x); split; auto. exists x. split. 2: easy.
           eapply Slocx in xy. rewrite tst_dot_tst in xy. apply xy. reflexivity.
        -- pose proof (Slocx x y _ xy eq_refl).
           destruct_rel. rewrite tst_dot_tst; tauto.
      * destruct xy as (? & (l & i & ->) & xy).
        rewrite tst_dot_tst in xy.
        easy.
    + (* Choice function: for each set of linearisations on a given
         location, we unsurprisingly choose the one restriction of [S]
         to this location. We must also not choose anything when the
         set is empty. *)
      pose (f :=
              fun Rs fRs =>
                exists l, Inhabited _ (E ⊓ atloc l) /\
                  Rs = linearisations (E ⊓ atloc l) R /\
                  fRs = [atloc l] ⋅ S ⋅ [atloc l]).
      exists f. split. 2:split. 2:split.
      * (* f is a _sound_ choice function *)
        intros Rs fRs. subst f. intros (l & i & -> & ->). split!; apply ?(ES l).
        now apply is_irreflexive_spec2, (ES l).
        rewrite <-RS.
        intros x y xy.
        rewrite tst_dot_tst in *.
        destruct xy as ((Ex, lx) & xy & (Ey, ly)). intuition. split; auto.
        rewrite tst_dot_tst. intuition.
        apply location_of_spec. now rewrite lx, ly.
      * (* the domain of f is correct *)
        intros Rs. rewrite co_locs_partition_spec.
        split.
        -- intros (l & i & ->). eexists. exists l. eauto.
        -- intros (R1 & l & i & -> & _). eauto.
      * (* f is a function(al relation) *)
        intros Rs.
        enough (H : forall b b' : relation (events c), f Rs b -> f Rs b' -> b ≦ b').
        { intros b b' e e'. apply rel_ext, antisym; eauto. }
        intros S1 S2 (l1 & i1 & e1 & ->) (l2 & i2 & e2 & ->).
        pose proof ES l1 as Sl1.
        pose proof ES l2 as Sl2.
        assert (HS : linearisations (E ⊓ atloc l1) R ([atloc l1]⋅S⋅[atloc l1])).
        { split!; apply ?(ES l1). apply is_irreflexive_spec2, (ES l1).
          rewrite <-RS.
          intros x y ((ex & x2) & xy & (ey & y2)) % tst_dot_tst.
          rewrite tst_dot_tst. intuition. split; auto.
          rewrite tst_dot_tst. intuition. apply location_of_spec. congruence.
        }
        rewrite <-e1, e2 in HS. destruct HS as (OS & S12 & _ & _).
        intros x y xy.
        pose proof (S12 _ _ xy) as ((_ & x2) & _ & (_ & y2)) % tst_dot_tst.
        rewrite tst_dot_tst in *.
        intuition.
      * (* [fun Sl => ...] is indeed the image through this function *)
        split.
        -- intros R1 (l & i & ->).
           eexists. split. apply co_locs_partition_spec. exists l; auto.
           exists l. auto.
        -- intros R1 (Rs_ & (l & i & ->)%co_locs_partition_spec & (l' & i' & D & ->)).
           exists l'. split; auto.
Qed.

Lemma generate_orders_total {c} E (R S : relation (events c)) :
  generate_orders (events c) (loc c) E R S -> [E] ⋅ loc c ⋅ [E] ≦ S ⊔ S° ⊔ 1.
Proof.
  intros (RS & Sloc & SO) % generate_orders_spec_3.
  intros x y (ex & xy & ey) % tst_dot_tst.
  destruct (SO (location_of x)) as (A & B & C).
  destruct (Classical_Prop.classic (x = y)) as [<- | n]. now right. left.
  unfold total_on in C. elim_cnv in C. rewrite dotA in C.
  destruct (C x y) as [H|H].
  - rewrite tst_dot_tst. repeat split; auto. symmetry. now apply location_of_spec.
  - left. now rewrite tst_dot_tst in H.
  - right. now rewrite tst_dot_tst in H.
Qed.

Lemma loc_location_of {c} S : S ≦ loc c ->
 forall x y, S x y -> ([atloc (location_of x)]⋅S⋅[atloc (location_of x)]) x y.
Proof.
  intros Sloc x y xy. rewrite tst_dot_tst. intuition. easy.
  apply eq_sym, location_of_spec, Sloc, xy.
Qed.

Lemma generate_orders_total' {c} E (R S : relation (events c)) :
  generate_orders (events c) (loc c) E R S -> [E] ⋅ (!1 ⊓ loc c) ⋅ [E] ≡ S ⊔ S°.
Proof.
  intros G. apply antisym.
  - apply generate_orders_total in G.
    intros x y (ex & (n & xy) & ey) % tst_dot_tst.
    destruct (G x y). now rewrite tst_dot_tst. now auto. now destruct n.
  - apply generate_orders_spec_3 in G. destruct G as (_ & Sloc & G).
    rewrite capC, <-cap_cartes. apply leq_xcap. apply leq_xcap.
    + rewrite Sloc. rewrite loc_sym__. ra.
    + intros x y xy e.
      destruct (G (location_of x)) as ((SI & ST) & SE & ES).
      destruct xy as [xy | xy].
      * apply SI with x y. split. 2:easy. now apply loc_location_of.
      * apply SI with y x. split. 2:easy.
        rewrite tst_dot_tst. intuition. 2:easy.
        apply location_of_spec, Sloc, xy.
    + enough (S ≦ [E]⋅top⋅[E]) as ->. now elim_cnv; kat.
      (* factoriser le travail avec loc x ci-dessus *)
      intros x y xy. destruct (G (location_of x)) as ((SI & ST) & SE & ES).
      apply loc_location_of in xy; auto.
      apply SE in xy.
      rewrite tst_dot_tst in *. repeat split; apply xy.
Qed.

Lemma generate_orders_order {c} E (R S : relation (events c)) :
  generate_orders (events c) (loc c) E R S -> is_strict_order S.
Proof.
  intros (RS & Sloc & G)%generate_orders_spec_3.
  split.
  - rewrite is_irreflexive_spec2, <-is_irreflexive_spec3. intros x xx.
    apply loc_location_of in xx; auto.
    destruct (G (location_of x)) as ((SI & _) & _).
    rewrite is_irreflexive_spec2, <-is_irreflexive_spec3 in SI.
    apply (SI x xx).
  - intros x z [y xy yz].
    assert (el : location_of x = location_of y). apply location_of_spec, Sloc, xy.
    apply loc_location_of in xy; auto.
    apply loc_location_of in yz; auto. rewrite <-el in yz.
    destruct (G (location_of x)) as ((_ & ST) & _).
    specialize (ST x z ltac:(exists y; eauto)).
    rewrite tst_dot_tst in ST. tauto.
Qed.

Lemma generate_orders_spec_2 {ev} (W : set ev) (loc pco co : relation ev) :
  is_strict_order pco (* is that right? *) ->
  generate_orders ev loc W pco co <->
  extends_along pco ([W] ⋅ loc ⋅ [W]) co.
Proof.
  unfold generate_orders, cross.
  split.
  - intros (colocs & Hcolocs & Eco).
    subst co.
    hnf.
    unfold extends_along in *.
    split 3.
    + enough (pco ⊓ loc ≦ union_of_relations colocs) by admit.
      (* Extends along means something like that ? *)
      intros x y [xy lxy].
      destruct Hcolocs as (f & faimswell & fisfun & Ecolocs).
      rewrite Extensionality_Ensembles'' in Ecolocs. subst colocs.
      hnf.
      unfold relational_image in *.
      (*
        R doit relier x à y
        R = f(Rs) avec Rs qui est dans [co_locs (partition loc W)]
        pour une certaine fonction de choix f : '' -> relation ev
        peut-être qu'il faudrait simplement un ensemble de locations
        et du coup les fonctions c'est x' y' => if loc(x') = loc(x) then
        ou alors c'est "il existe une complétion de l'ordre"
        mais c'est ce qu'on est en train de prouver.
        rha

        ah hmm mais le R il est complètement déterminé ? non il est déterminé par le Rs?
        R = f(Rs)
       *)
Abort.

Definition spec1 {A} (E : set A) (loc R S : relation A) :=
  S ≦ [E] ⋅ S ⋅ [E] /\
  S ⊓ 1 ≦ 0 /\
  S ⋅ S ≦ S /\
  S ≦ loc /\
  forall x y : A,
    loc x y ->
    E x ->
    E y ->
    (R x y -> S x y) /\ (x <> y -> S x y \/ S y x).

Lemma generate_orders_spec {A} (E : set A) (loc R S : relation A) :
  generate_orders A loc E R S <->
  spec1 E loc R S.

Proof.
  unfold generate_orders, cross.
  split.
  - intros l. (* (l & L & lS & RL & lL). *)
    split 5.
    + intros x y.
Abort.

Lemma generate_orders_bounds {A} (E : set A) (loc R S : relation A) :
  generate_orders A loc E R S -> S ≦ [E] ⋅ S ⋅ [E].
Proof.
  (* rewrite generate_orders_spec_3. unfold spec1. *)
  (* tauto. *)
Abort.

Lemma spec1_spec2 {A} (E : set A) (loc R S : relation A) :
  spec1 E loc R S <-> extends_along R ([E]⋅loc⋅[E]) S.
Proof.
  split.
  - intros (Sdom & Sirr & St & Sloc & Stot). split 3.
    + destruct_rel. spec Stot x y. destruct Stot as [RS Stot]; auto.
Abort.

Lemma generate_cos_spec {A} (W IW FW : set A) (loc : relation A) :
  let co0 := loc ⊓ ([IW] ⋅ top ⋅ [(W ⊓ !IW)] ⊔ [(W ⊓ !FW)] ⋅ top ⋅ [FW]) in
  let generate_orders s pco := cross (co_locs pco (partition loc s)) in
  let generate_cos pco := generate_orders W pco in
  forall co,
    generate_cos co0 co ->
    is_strict_order co /\
    [W] ⋅ loc ⋅ [W] ≡ co ⊔ co° ⊔ 1 /\
    [IW] ⋅ loc ⋅ [W ⊓ !IW] ≦ co /\
    [W ⊓ !FW] ⋅ loc ⋅ [FW] ≦ co /\
    True
.
Abort.
