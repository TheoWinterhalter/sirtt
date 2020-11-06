(* Global utility *)

From Coq Require Import Utf8.

Set Primitive Projections.

(* Must be somewhere in the stdlib? Or is there only the Prop version? *)
Inductive clos_refl {A} (R : A → A → Type) (x : A) : A → Type :=
| r_step y : R x y → clos_refl R x y
| r_refl : clos_refl R x x.

Record prod A B := pair {
  π₁ : A ;
  π₂ : B
}.

Arguments pair {_ _} _ _.

Notation "A × B" := (prod A B) (left associativity, at level 10).
Notation "'(' u ',' v ')'" := (pair u v) (left associativity, at level 10).