(* Global utility *)

From Coq Require Import Utf8 List Lia.
Import ListNotations.

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
Arguments π₁ {_ _} _.
Arguments π₂ {_ _} _.

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


Lemma nth_error_map :
  ∀ {A B} (f : A → B) n l,
    nth_error (map f l) n = option_map f (nth_error l n).
Proof.
  intros A B f n l.
  induction l in n |- *.
  - cbn. destruct n. all: reflexivity.
  - cbn. destruct n.
    + cbn. reflexivity.
    + cbn. apply IHl.
Qed.


Notation "#| l |" := (length l).

Lemma filter_length :
  ∀ A (l : list A) p,
    #| filter p l | ≤ #|l|.
Proof.
  intros A l p.
  induction l.
  - auto.
  - cbn. destruct p.
    + cbn. lia.
    + lia.
Qed.

Lemma filter_firstn_length :
  ∀ A (l : list A) n p,
    #| filter p (firstn n l) | ≤ #| filter p l |.
Proof.
  intros A l n p.
  induction l in n |- *.
  - cbn. destruct n. all: auto.
  - cbn. destruct n.
    + cbn. lia.
    + cbn. destruct p.
      * cbn. specialize (IHl n). lia.
      * apply IHl.
Qed.