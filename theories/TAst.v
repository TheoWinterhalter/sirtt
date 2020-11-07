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
| univ (s : sort)
.

Definition context := list term.

Fixpoint apps (t : term) (l : list term) :=
  match l with
  | u :: l => apps (app t u) l
  | [] => t
  end.