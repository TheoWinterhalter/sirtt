(* Syntax for SIRTT *)

From Coq Require Import List Utf8.
Require Import Util Level.

Import ListNotations.

(* Could be anything really *)
Definition sort := nat.

Inductive term :=
| var (n : nat)
| lam (l : level) (A t : term)
| app (l : level) (u v : term)
| Prod (l : level) (A B : term)
| ex (u p : term)
| wit (t : term)
| prf (t : term)
| Sum (A P : term)
| zero
| succ (n : term)
| elim_nat (P z s n : term)
| Nat
| vnil (A : term)
| vcons (A a n v : term)
| elim_vec (A P e c n v : term)
| Vec (A n : term)
| refl (A u : term)
| coe (A P u v e t : term)
| Eq (A u v : term)
| exfalso (A p : term)
| Empty
| univ (s : sort)
.
(* No equality yet, we'll try to have something abstract,
  maybe that should still go in the syntax somehow.
*)

(* A scope contains only relevance information of the binders *)
Definition scope := list level.

(* A binding comes with a relevance level and a type *)
Definition context := list (level × term).

Definition context_to_scope (Γ : context) : scope :=
  map π₁ Γ.

Coercion context_to_scope : context >-> scope.


Fixpoint appsR (t : term) (l : list term) :=
  match l with
  | u :: l => appsR (app R t u) l
  | [] => t
  end.

Fixpoint apps (t : term) (l : list (level × term)) :=
  match l with
  | (ℓ, u) :: l => apps (app ℓ t u) l
  | [] => t
  end.

Lemma context_to_scope_length :
  ∀ (Γ : context),
    #| context_to_scope Γ | = #| Γ |.
Proof.
  intros Γ.
  induction Γ as [| [[] A] Γ ih]. all: cbn ; eauto.
Qed.

Lemma context_to_scope_nth_error :
  ∀ (Γ : context) n ℓ A,
    nth_error Γ n = Some (ℓ, A) →
    nth_error (context_to_scope Γ) n = Some ℓ.
Proof.
  intros Γ n ℓ A h.
  induction Γ as [| [ℓ' B] Γ ih] in n, ℓ, A, h |- *.
  1:{ destruct n. all: discriminate. }
  destruct n.
  - cbn in h. inversion h. subst. clear h.
    cbn. reflexivity.
  - cbn in h. eapply ih in h.
    cbn. auto.
Qed.