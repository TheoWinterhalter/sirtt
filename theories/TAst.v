(* Syntax for MLTT *)

From Coq Require Import List.
Require Import Util Level.

Import ListNotations.

(* Could be anything really *)
Definition sort := nat.

Inductive term :=
| var (n : nat)
| lam (A t : term)
| app (u v : term)
| Prod (A B : term)
| zero
| succ (n : term)
| elim_nat (P z s n : term)
| Nat
| lnil (A : term)
| lcons (A a l : term)
| elim_list (A P e c l : term)
| List (A : term)
| refl (A u : term)
| coe (A P u v e t : term)
| Eq (A u v : term)
| exfalso (A p : term)
| Empty
| axiom (n : nat) (* Refer to an axiom in a global context *)
| univ (s : sort)
.

Definition scope := nat.

Definition context := list term.

Definition context_to_scope (Γ : context) : scope :=
  #|Γ|.

Coercion context_to_scope : context >-> scope.

Fixpoint apps (t : term) (l : list term) :=
  match l with
  | u :: l => apps (app t u) l
  | [] => t
  end.

Inductive term_head :=
| hvar
| hlam
| hprod
| hzero
| hsucc
| hnat
| hnil
| hcons
| hlist
| hrefl
| heq
| hempty
| haxiom
| huniv
.

Definition head (t : term) : option term_head :=
  match t with
  | var n => Some hvar
  | lam A t => Some hlam
  | Prod A B => Some hprod
  | zero => Some hzero
  | succ n => Some hsucc
  | Nat => Some hnat
  | lnil A => Some hnil
  | lcons A a l => Some hcons
  | List A => Some hlist
  | refl A u => Some hrefl
  | Eq A u v => Some heq
  | Empty => Some hempty
  | axiom n => Some haxiom
  | univ s => Some huniv
  | _ => None
  end.