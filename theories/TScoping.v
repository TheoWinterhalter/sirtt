(* Scoping in SIRTT *)

From Coq Require Import Utf8 List.
Require Import Util TAst TSubst TReduction.

Import ListNotations.

Set Default Goal Selector "!".

Inductive scoping (Γ : scope) : term → Type :=
| scope_var :
    ∀ n,
      n < Γ →
      scoping Γ (var n)

| scope_lam :
    ∀ A t,
      scoping Γ A →
      scoping (S Γ) t →
      scoping Γ (lam A t)

| scope_app :
    ∀ u v,
      scoping Γ u →
      scoping Γ v →
      scoping Γ (app u v)

| scope_Prod :
    ∀ A B,
      scoping Γ A →
      scoping (S Γ) B →
      scoping Γ (Prod A B)

| scope_zero :
    scoping Γ zero

| scope_succ :
    ∀ t,
      scoping Γ t →
      scoping Γ (succ t)

| scope_elim_nat :
    ∀ P z s n,
      scoping Γ P →
      scoping Γ z →
      scoping Γ s →
      scoping Γ n →
      scoping Γ (elim_nat P z s n)

| scope_Nat :
    scoping Γ Nat

| scope_lnil :
    ∀ A,
      scoping Γ A →
      scoping Γ (lnil A)

| scope_lcons :
    ∀ A a l,
      scoping Γ A →
      scoping Γ a →
      scoping Γ l →
      scoping Γ (lcons A a l)

| scope_elim_list :
    ∀ A P e c l,
      scoping Γ A →
      scoping Γ P →
      scoping Γ e →
      scoping Γ c →
      scoping Γ l →
      scoping Γ (elim_list A P e c l)

| scope_List :
    ∀ A,
      scoping Γ A →
      scoping Γ (List A)

| scope_univ :
    ∀ s,
      scoping Γ (univ s)
.