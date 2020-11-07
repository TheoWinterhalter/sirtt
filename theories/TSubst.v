(* MLTT Lifting and substitution *)

From Coq Require Import Utf8 List Nat.
Require Import Util TAst.

Import ListNotations.

Fixpoint lift n k t : term :=
  match t with
  | var i => var (if Nat.leb k i then (n + i) else i)
  | lam A t => lam (lift n k A) (lift n (S k) t)
  | app u v => app (lift n k u) (lift n k v)
  | Prod A B => Prod (lift n k A) (lift n (S k) B)
  | zero => zero
  | succ t => succ (lift n k t)
  | elim_nat P z s t =>
    elim_nat (lift n k P) (lift n k z) (lift n k s) (lift n k t)
  | Nat => Nat
  | lnil A => lnil (lift n k A)
  | lcons A a l => lcons (lift n k A) (lift n k a) (lift n k l)
  | elim_list A P e c l =>
    elim_list (lift n k A) (lift n k P)
              (lift n k e) (lift n k c) (lift n k l)
  | List A => List (lift n k A)
  | univ s => univ s
  end.

Notation lift0 n := (lift n 0).

Fixpoint subst s k u :=
  match u with
  | var n =>
    if Nat.leb k n then
      match nth_error s (n - k) with
      | Some b => lift0 k b
      | None => var (n - List.length s)
      end
    else var n
  | lam A t => lam (subst s k A) (subst s (S k) t)
  | app u v => app (subst s k u) (subst s k v)
  | Prod A B => Prod (subst s k A) (subst s (S k) B)
  | zero => zero
  | succ t => succ (subst s k t)
  | elim_nat P z sc t =>
    elim_nat (subst s k P) (subst s k z) (subst s k sc) (subst s k t)
  | Nat => Nat
  | lnil A => lnil (subst s k A)
  | lcons A a l => lcons (subst s k A) (subst s k a) (subst s k l)
  | elim_list A P e c l =>
    elim_list (subst s k A) (subst s k P)
              (subst s k e) (subst s k c) (subst s k l)
  | List A => List (subst s k A)
  | univ s => univ s
  end.

(** Substitutes [t1 ; .. ; tn] in u for [Rel 0; .. Rel (n-1)] *in parallel* *)
Notation subst0 t := (subst t 0).
Definition subst1 t k u := subst [t] k u.
Notation subst10 t := (subst1 t 0).
Notation "M { j := N }" := (subst1 N j M) (at level 10, right associativity).