(* Scoping in SIRTT *)

From Coq Require Import Utf8 List.
Require Import Util Level SAst SSubst SReduction.

Import ListNotations.

Set Default Goal Selector "!".

Inductive scoping (Γ : scope) : level → term → Type :=
| scope_var :
    ∀ n ℓ,
      nth_error Γ n = Some ℓ →
      scoping Γ ℓ (var n)

| scope_lam :
    ∀ ℓ ℓ' A t,
      scoping Γ ℓ A → (* Should it be something lower maybe? *)
      scoping (ℓ' :: Γ) ℓ t →
      scoping Γ ℓ (lam ℓ' A t)

| scope_app :
    ∀ ℓ ℓ' u v,
      scoping Γ ℓ u →
      scoping Γ (ℓ ⊔ ℓ') v →
      scoping Γ ℓ (app ℓ' u v)

| scope_Prod :
    ∀ ℓ ℓ' A B,
      scoping Γ ℓ A → (* Right level? *)
      scoping (ℓ' :: Γ) ℓ B →
      scoping Γ ℓ (Prod ℓ' A B)

| scope_ex :
    ∀ ℓ u p,
      scoping Γ ℓ u →
      scoping Γ I p →
      scoping Γ ℓ (ex u p)

| scope_wit :
    ∀ ℓ t,
      scoping Γ ℓ t →
      scoping Γ ℓ (wit t)

| scope_prf :
    ∀ t,
      scoping Γ I t →
      scoping Γ I (prf t)

| scope_Sum :
    ∀ ℓ A P,
      scoping Γ ℓ A →
      scoping (R :: Γ) I P →
      scoping Γ ℓ (Sum A P)

| scope_zero :
    ∀ ℓ,
      scoping Γ ℓ zero

| scope_succ :
    ∀ ℓ t,
      scoping Γ ℓ t →
      scoping Γ ℓ (succ t)

| scope_elim_nat :
    ∀ ℓ P z s n,
      scoping Γ ℓ P →
      scoping Γ ℓ z →
      scoping Γ ℓ s →
      scoping Γ ℓ n →
      scoping Γ ℓ (elim_nat P z s n)

| scope_Nat :
    ∀ ℓ,
      scoping Γ ℓ Nat

| scope_vnil :
    ∀ ℓ A,
      scoping Γ ℓ A →
      scoping Γ ℓ (vnil A)

| scope_vcons :
    ∀ ℓ A a n v,
      scoping Γ ℓ A →
      scoping Γ ℓ a →
      scoping Γ I n →
      scoping Γ ℓ v →
      scoping Γ ℓ (vcons A a n v)

| scope_elim_vec :
    ∀ ℓ A P e c n v,
      scoping Γ ℓ A →
      scoping Γ ℓ P →
      scoping Γ ℓ e →
      scoping Γ ℓ c →
      scoping Γ I n →
      scoping Γ ℓ v →
      scoping Γ ℓ (elim_vec A P e c n v)

| scope_Vec :
    ∀ ℓ A n,
      scoping Γ ℓ A →
      scoping Γ S n →
      scoping Γ ℓ (Vec A n)

| scope_univ :
    ∀ ℓ s,
      scoping Γ ℓ (univ s)

| scope_sub :
    ∀ ℓ ℓ' t,
      scoping Γ ℓ t →
      ℓ ⊑ ℓ' → (* Could also be ⊏ *)
      scoping Γ ℓ' t
.