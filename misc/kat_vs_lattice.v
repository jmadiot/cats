From RelationAlgebra Require Import all.
Goal forall X (A B C D : hrel X X), A ⊔ (B ⊔ (B ⋅ C ⊔ D ⊔ C)) ≦ A ⊔ (B ⋅ C ⊔ D ⊔ (B ⊔ C)).
intros.
Time Fail Fail lattice.
Time Fail Fail kat.
Abort.
