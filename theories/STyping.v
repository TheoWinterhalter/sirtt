(** Typing and conversion in SIRTT

  Conversion is not defined from reduction because reduction only deals with
  relevant terms. We should be able to show however that u ↦ v implies
  that u and v are convertible as relevant terms.
  In fact, because of shape-irrelevant reflection, we need to define conversion
  mutually with typing.
  As such, this file should go away.

  I'm also missing exfalso in the AST, and thus axioms in the target to have
  axiom False.
  More crucially, I'm missing equality it seems.
  I could also be abstract about it, but maybe it's not such a good idea?

  Typing is defined without assumptions on contexts.

  Conversion is not typed, but it could have been.

*)

From Coq Require Import Utf8 List.
Require Import Equations.Prop.DepElim.
Require Import Equations.Prop.Classes.
From Equations Require Import Equations.
Require Import Util Level SAst SSubst SReduction SScoping.

Import ListNotations.

Set Default Goal Selector "!".

Definition arrow A B := Prod R A (lift0 1 B).
Notation "A ⇒ B" := (arrow A B) (at level 70, right associativity).

Reserved Notation "Γ ⊢[ l ] t : A"
  (at level 80, l, t, A at next level, format "Γ  ⊢[  l  ]  t  :  A").
Reserved Notation "Γ ⊢[ l ] u ≡ v"
  (at level 80, l, u, v at next level, format "Γ  ⊢[  l  ]  u  ≡  v").

Inductive typing (Γ : context) : level → term → term → Type :=
| type_var :
    ∀ n ℓ A,
      nth_error Γ n = Some (ℓ, A) →
      Γ ⊢[ ℓ ] var n : A

| type_lam :
    ∀ ℓ ℓ' A B t s,
      Γ ⊢[ ℓ ] A : univ s →
      (ℓ', A) :: Γ ⊢[ ℓ ] t : B →
      Γ ⊢[ ℓ ] lam ℓ' A t : Prod ℓ' A B

| type_app :
    ∀ ℓ ℓ' A B u v,
      Γ ⊢[ ℓ ] u : Prod ℓ' A B →
      Γ ⊢[ ℓ ⊔ ℓ' ] v : A →
      Γ ⊢[ ℓ ] app ℓ' u v : B{ 0 := v }

| type_Prod :
    ∀ ℓ ℓ' A B i j,
      Γ ⊢[ ℓ ] A : univ i →
      (▪ ℓ', A) :: Γ ⊢[ ℓ ] B : univ j →
      Γ ⊢[ ℓ ] Prod ℓ' A B : univ (Peano.max i j)

| type_ex :
    ∀ ℓ A P u p,
      Γ ⊢[ ℓ ] u : A →
      Γ ⊢[ I ] p : P{ 0 := u } →
      Γ ⊢[ ℓ ] ex u p : Sum A P

| type_wit :
    ∀ ℓ A P p,
      Γ ⊢[ ℓ ] p : Sum A P →
      Γ ⊢[ ℓ ] wit p : A

| type_prf :
    ∀ A P p,
      Γ ⊢[ I ] p : Sum A P →
      Γ ⊢[ I ] prf p : P{ 0 := wit p }

| type_Sum :
    ∀ ℓ A P i j,
      Γ ⊢[ ℓ ] A : univ i →
      (R, A) :: Γ ⊢[ S ⊔ ℓ ] P : univ j →
      Γ ⊢[ ℓ ] Sum A P : univ (Peano.max i j)

| type_zero :
    ∀ ℓ,
      Γ ⊢[ ℓ ] zero : Nat

| type_succ :
    ∀ ℓ n,
      Γ ⊢[ ℓ ] n : Nat →
      Γ ⊢[ ℓ ] succ n : Nat

| type_elim_nat :
    ∀ ℓ P z s n i,
      Γ ⊢[ ℓ ] P : Nat ⇒ univ i →
      Γ ⊢[ ℓ ] z : app R P zero →
      Γ ⊢[ ℓ ] s :
        Prod R Nat
          (app R (lift0 1 P) (var 0) ⇒ app R (lift0 1 P) (succ (var 0))) →
      Γ ⊢[ ℓ ] n : Nat →
      Γ ⊢[ ℓ ] elim_nat P z s n : app R P n

| type_Nat :
    ∀ ℓ i,
      Γ ⊢[ ℓ ] Nat : univ i

| type_vnil :
    ∀ ℓ A i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] vnil A : Vec A zero

| type_vcons :
    ∀ ℓ A a n v i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] a : A →
      Γ ⊢[ I ] n : Nat →
      Γ ⊢[ ℓ ] v : Vec A n →
      Γ ⊢[ ℓ ] vcons A a n v : Vec A (succ n)

| type_elim_vec :
    ∀ ℓ A P e c n v i j,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] P : Prod I Nat (Vec (lift0 1 A) (var 0) ⇒ univ j) →
      Γ ⊢[ ℓ ] e : app R (app I P zero) (vnil A) →
      Γ ⊢[ ℓ ] c :
        Prod R A
          (Prod I Nat
            (Prod R (Vec (lift0 2 A) (var 0)) (
              app R (app I (lift0 3 P) (var 1)) (var 0) ⇒
              app R
                (app I (lift0 3 P) (succ (var 1)))
                (vcons (lift0 3 A) (var 2) (var 1) (var 0)
            ))
          )
        ) →
      Γ ⊢[ I ] n : Nat →
      Γ ⊢[ ℓ ] v : Vec A n →
      Γ ⊢[ ℓ ] elim_vec A P e c n v : app R (app I P n) v

| type_Vec :
    ∀ ℓ A n i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ S ⊔ ℓ ] n : Nat →
      Γ ⊢[ ℓ ] Vec A n : univ i

| type_refl :
    ∀ ℓ A u i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] u : A →
      Γ ⊢[ ℓ ] refl A u : Eq A u u

| type_coe :
    ∀ ℓ A P u v e t i j,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] P : A ⇒ univ j →
      Γ ⊢[ ℓ ] u : A →
      Γ ⊢[ ℓ ] v : A →
      Γ ⊢[ ℓ ] e : Eq A u v →
      Γ ⊢[ ℓ ] t : app R P u →
      Γ ⊢[ ℓ ] coe A P u v e t : app R P v

| type_Eq :
    ∀ ℓ A u v i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] u : A →
      Γ ⊢[ ℓ ] v : A →
      Γ ⊢[ ℓ ] Eq A u v : univ i

| type_exfalso :
    ∀ ℓ A p i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ I ] p : Empty →
      Γ ⊢[ ℓ ] exfalso A p : A

| type_Empty :
    ∀ ℓ i,
      Γ ⊢[ ℓ ] Empty : univ i

| type_univ :
    ∀ ℓ i j,
      i < j →
      Γ ⊢[ ℓ ] univ i : univ j

| type_conv :
    ∀ t A B ℓ s,
      Γ ⊢[ ℓ ] t : A →
      Γ ⊢[ R ] A ≡ B →
      Γ ⊢[ ▪ ℓ ] B : univ s →
      Γ ⊢[ ℓ ] t : B

| type_sub :
    ∀ ℓ ℓ' t A,
      Γ ⊢[ ℓ ] t : A →
      ℓ ⊑ ℓ' →
      Γ ⊢[ ℓ' ] t : A

where "Γ ⊢[ l ] t : A" := (typing Γ l t A) : s_scope

with conversion (Γ : context) : level → term → term → Type :=

(* TODO *)

where "Γ ⊢[ l ] u ≡ v" := (conversion Γ l u v) : s_scope.

(* TODO Is this the right def?? *)
Inductive wf_context : context → Type :=
| wf_nil : wf_context []
| wf_cons :
    ∀ Γ A ℓ s,
      wf_context Γ →
      Γ ⊢[ ▪ ℓ ] A : univ s →
      wf_context ((ℓ, A) :: Γ).

Lemma typed_scoped :
  ∀ Γ ℓ t A,
    Γ ⊢[ ℓ ] t : A →
    scoping Γ ℓ t.
Proof.
  intros Γ ℓ t A h.
  induction h.
  all: try assumption.
  all: try solve [ constructor ; eauto ].
  - constructor. unfold context_to_scope. rewrite nth_error_map.
    rewrite e. cbn. reflexivity.
  - eapply scope_sub. all: eauto.
Qed.