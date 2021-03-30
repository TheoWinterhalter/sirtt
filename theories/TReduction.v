(* Reduction for MLTT *)

From Coq Require Import Utf8 List.
Require Import Util TAst TSubst.

Import ListNotations.

Set Default Goal Selector "!".

Open Scope t_scope.


Reserved Notation "u ↦ v" (at level 10).

Inductive red : term → term → Type :=
(* Computation rules *)
| beta :
    ∀ u A t,
      (app (lam A t) u) ↦ (t{ 0 := u })

| elim_nat_zero :
    ∀ P z s,
      (elim_nat P z s zero) ↦ z

| elim_nat_succ :
    ∀ P z s n,
      (elim_nat P z s (succ n)) ↦
      (apps s [ n ; elim_nat P z s n ])

| elim_list_lnil :
    ∀ A P e c B,
      (elim_list A P e c (lnil B)) ↦ e

| elim_list_lcons :
    ∀ A P e c B a l,
      (elim_list A P e c (lcons B a l)) ↦
      (apps c [ a ; l ; elim_list A P e c l ])

| coe_refl :
    ∀ A P u t B v,
      (coe A P u u (refl B v) t) ↦ t

(* Congruence rules *)
| lam_ty : ∀ A t A', A ↦ A' → (lam A t) ↦ (lam A' t)
| lam_tm : ∀ A t t', t ↦ t' → (lam A t) ↦ (lam A t')

| app_l : ∀ u v u', u ↦ u' → (app u v) ↦ (app u' v)
| app_r : ∀ u v v', v ↦ v' → (app u v) ↦ (app u v')

| Prod_l : ∀ A B A', A ↦ A' → (Prod A B) ↦ (Prod A' B)
| Prod_r : ∀ A B B', B ↦ B' → (Prod A B) ↦ (Prod A B')

| succ_arg : ∀ t t', t ↦ t' → (succ t) ↦ (succ t')

| elim_nat_p : ∀ P z s t P', P ↦ P' → (elim_nat P z s t) ↦ (elim_nat P' z s t)
| elim_nat_z : ∀ P z s t z', z ↦ z' → (elim_nat P z s t) ↦ (elim_nat P z' s t)
| elim_nat_s : ∀ P z s t s', s ↦ s' → (elim_nat P z s t) ↦ (elim_nat P z s' t)
| elim_nat_t : ∀ P z s t t', t ↦ t' → (elim_nat P z s t) ↦ (elim_nat P z s t')

| lnil_ty : ∀ A A', A ↦ A' → (lnil A) ↦ (lnil A')

| lcons_ty : ∀ A a l A', A ↦ A' → (lcons A a l) ↦ (lcons A' a l)
| lcons_arg : ∀ A a l a', a ↦ a' → (lcons A a l) ↦ (lcons A a' l)
| lcons_vec : ∀ A a l l', l ↦ l' → (lcons A a l) ↦ (lcons A a l')

| elim_list_ty :
    ∀ A P e c l A',
      A ↦ A' →
      (elim_list A P e c l) ↦ (elim_list A' P e c l)
| elim_list_p :
    ∀ A P e c l P',
      P ↦ P' →
      (elim_list A P e c l) ↦ (elim_list A P' e c l)
| elim_list_e :
    ∀ A P e c l e',
      e ↦ e' →
      (elim_list A P e c l) ↦ (elim_list A P e' c l)
| elim_list_c :
    ∀ A P e c l c',
      c ↦ c' →
      (elim_list A P e c l) ↦ (elim_list A P e c' l)
| elim_list_list :
    ∀ A P e c l l',
      l ↦ l' →
      (elim_list A P e c l) ↦ (elim_list A P e c l')

| List_ty : ∀ A A', A ↦ A' → (List A) ↦ (List A')

| refl_ty : ∀ A A' u, A ↦ A' → (refl A u) ↦ (refl A' u)
| refl_tm : ∀ A u u', u ↦ u' → (refl A u) ↦ (refl A u')

| coe_ty : ∀ A P u v e t A', A ↦ A' → (coe A P u v e t) ↦ (coe A' P u v e t)
| coe_p : ∀ A P u v e t P', P ↦ P' → (coe A P u v e t) ↦ (coe A P' u v e t)
| coe_u : ∀ A P u v e t u', u ↦ u' → (coe A P u v e t) ↦ (coe A P u' v e t)
| coe_v : ∀ A P u v e t v', v ↦ v' → (coe A P u v e t) ↦ (coe A P u v' e t)
| coe_e : ∀ A P u v e t e', e ↦ e' → (coe A P u v e t) ↦ (coe A P u v e' t)
| coe_t : ∀ A P u v e t t', t ↦ t' → (coe A P u v e t) ↦ (coe A P u v e t')

| Eq_ty : ∀ A u v A', A ↦ A' → (Eq A u v) ↦ (Eq A' u v)
| Eq_u : ∀ A u v u', u ↦ u' → (Eq A u v) ↦ (Eq A u' v)
| Eq_v : ∀ A u v v', v ↦ v' → (Eq A u v) ↦ (Eq A u v')

| exfalso_ty : ∀ A p A', A ↦ A' → (exfalso A p) ↦ (exfalso A' p)
| exfalso_tm : ∀ A p p', p ↦ p' → (exfalso A p) ↦ (exfalso A p')

where "u ↦ v" := (red u v) : t_scope.