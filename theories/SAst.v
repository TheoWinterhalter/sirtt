(* Syntax for SIRTT *)

Require Import Util Level.

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
| vec (A n : term)
| univ (s : sort)
.
(* No equality yet, we'll try to have something abstract,
  maybe that should still go in the syntax somehow.
*)

(* A binding comes with a relevance level and a type *)
Definition context := list (level × term).
