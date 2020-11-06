(* Global utility *)

From Coq Require Import Utf8.

Set Primitive Projections.

(* Must be somewhere in the stdlib? Or is there only the Prop version? *)
Inductive clos_refl {A} (R : A → A → Type) (x : A) : A → Type :=
| r_step y : R x y → clos_refl R x y
| r_refl : clos_refl R x x.

Inductive clos_refl_trans {A} (R : A → A → Type) (x : A) : A → Type :=
| rt_step y : R x y → clos_refl_trans R x y
| rt_refl : clos_refl_trans R x x
| rt_trans y z :
    clos_refl_trans R x y →
    clos_refl_trans R y z →
    clos_refl_trans R x z.



Record prod A B := pair {
  π₁ : A ;
  π₂ : B
}.

Arguments pair {_ _} _ _.

Notation "A × B" := (prod A B) (right associativity, at level 80).
Notation "( u , v )" := (pair u v).


Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "( x ; y )" := (@existT _ _ x y).
Notation "( x ; y ; z )" := (x ; ( y ; z)).
Notation "( x ; y ; z ; t )" := (x ; ( y ; (z ; t))).
Notation "( x ; y ; z ; t ; u )" := (x ; ( y ; (z ; (t ; u)))).
Notation "( x ; y ; z ; t ; u ; v )" := (x ; ( y ; (z ; (t ; (u ; v))))).