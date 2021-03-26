(* Reduction for SIRTT *)

From Coq Require Import Utf8 List.
Require Import Util Level SAst SSubst.

Import ListNotations.

Set Default Goal Selector "!".

Open Scope s_scope.

(*
  First we define a notion of "top-level" reduction to reveal relevant terms
  hidden under (shape-)irrelevant operations.

  When computing (shape-)irrelevant β-redexes, we postpone the substitution
  as it doesn't matter for computation.
  It's an important trick to have this operation trivially terminating.
*)

Fixpoint reveal u :=
  match u with
  | app I (lam I A t) u =>
    let '(r, σ) := reveal t in
    (r, u :: σ)
  | app S (lam S A t) u =>
    let '(r, σ) := reveal t in
    (r, u :: σ)
  | wit (ex t p) => reveal t
  | _ => (u, [])
  end.

Fixpoint reveal_scope t :=
  match t with
  | app Level.I (lam Level.I A t) u => reveal_scope t ++ [ Level.I ]
  | app Level.S (lam Level.S A t) u => reveal_scope t ++ [ Level.S ]
  | wit (ex t p) => reveal_scope t
  | _ => []
  end.

(**
  The substitution we define with reveal is not a substitution per se because
  its components typically live in different scopes.
  We thus define a special operation for it.
*)
Fixpoint reveal_subst σ t :=
  match σ with
  | u :: σ => (reveal_subst σ t){ 0 := u }
  | [] => t
  end.

Fixpoint reveal_subst_k σ i t :=
  match σ with
  | u :: σ => (reveal_subst_k σ i t){ i := u }
  | [] => t
  end.

(* We can now define proper reduction ↦ *)
(* Note that we do not reduce in irrelevant positions when it can be safely
  determined.
*)

Reserved Notation "u ↦ v" (at level 10).

Inductive red : term → term → Type :=
(* Computation rules *)
| beta :
    ∀ v u A t σ,
      reveal v = (lam R A t, σ) →
      (app R v u) ↦ ((reveal_subst_k σ 1 t){ 0 := u })

| elim_nat_zero :
    ∀ P z s t σ,
      reveal t = (zero, σ) →
      (elim_nat P z s t) ↦ z

| elim_nat_succ :
    ∀ P z s t n σ,
      reveal t = (succ n, σ) →
      (elim_nat P z s t) ↦
      (appsR s [ reveal_subst σ n ; elim_nat P z s (reveal_subst σ n) ])

| elim_vec_vnil :
    ∀ A P e c n t B σ,
      reveal t = (vnil B, σ) →
      (elim_vec A P e c n t) ↦ e

| elim_vec_vcons :
    ∀ A P e c n t B a m v σ,
      reveal t = (vcons B a m v, σ) →
      (elim_vec A P e c n t) ↦
      (apps c [
        (R, reveal_subst σ a) ;
        (I, reveal_subst σ m) ;
        (R, reveal_subst σ v) ;
        (R, elim_vec A P e c (reveal_subst σ m) (reveal_subst σ v))
      ])

(* Congruence rules *)
| lam_ty : ∀ A t A', A ↦ A' → (lam R A t) ↦ (lam R A' t)
| lam_tm : ∀ l A t t', t ↦ t' → (lam l A t) ↦ (lam l A t')

| app_l : ∀ l u v u', u ↦ u' → (app l u v) ↦ (app l u' v)
| app_r : ∀ u v v', v ↦ v' → (app R u v) ↦ (app R u v')

| Prod_l : ∀ A B A', A ↦ A' → (Prod R A B) ↦ (Prod R A' B)
| Prod_r : ∀ l A B B', B ↦ B' → (Prod l A B) ↦ (Prod l A B')

| ex_wit : ∀ u p u', u ↦ u' → (ex u p) ↦ (ex u' p)

| wit_arg : ∀ t t', t ↦ t' → (wit t) ↦ (wit t')

| Sum_l : ∀ A P A', A ↦ A' → (Sum A P) ↦ (Sum A' P)

| succ_arg : ∀ t t', t ↦ t' → (succ t) ↦ (succ t')

| elim_nat_p : ∀ P z s t P', P ↦ P' → (elim_nat P z s t) ↦ (elim_nat P' z s t)
| elim_nat_z : ∀ P z s t z', z ↦ z' → (elim_nat P z s t) ↦ (elim_nat P z' s t)
| elim_nat_s : ∀ P z s t s', s ↦ s' → (elim_nat P z s t) ↦ (elim_nat P z s' t)
| elim_nat_t : ∀ P z s t t', t ↦ t' → (elim_nat P z s t) ↦ (elim_nat P z s t')

| vnil_ty : ∀ A A', A ↦ A' → (vnil A) ↦ (vnil A')

| vcons_ty : ∀ A a n v A', A ↦ A' → (vcons A a n v) ↦ (vcons A' a n v)
| vcons_arg : ∀ A a n v a', a ↦ a' → (vcons A a n v) ↦ (vcons A a' n v)
| vcons_vec : ∀ A a n v v', v ↦ v' → (vcons A a n v) ↦ (vcons A a n v')

| elim_vec_ty :
    ∀ A P e c m v A',
      A ↦ A' →
      (elim_vec A P e c m v) ↦ (elim_vec A' P e c m v)
| elim_vec_p :
    ∀ A P e c m v P',
      P ↦ P' →
      (elim_vec A P e c m v) ↦ (elim_vec A P' e c m v)
| elim_vec_e :
    ∀ A P e c m v e',
      e ↦ e' →
      (elim_vec A P e c m v) ↦ (elim_vec A P e' c m v)
| elim_vec_c :
    ∀ A P e c m v c',
      c ↦ c' →
      (elim_vec A P e c m v) ↦ (elim_vec A P e c' m v)
| elim_vec_vec :
    ∀ A P e c m v v',
      v ↦ v' →
      (elim_vec A P e c m v) ↦ (elim_vec A P e c m v')

| Vec_ty : ∀ A n A', A ↦ A' → (Vec A n) ↦ (Vec A' n)

where "u ↦ v" := (red u v) : s_scope.