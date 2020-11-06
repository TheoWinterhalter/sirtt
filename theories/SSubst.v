(* SIRTT Lifting and substitution *)

From Coq Require Import Utf8 List Nat.
Require Import Util SAst.

Fixpoint lift n k t : term :=
  match t with
  | var i => var (if Nat.leb k i then (n + i) else i)
  | lam l A t => lam l (lift n k A) (lift n (S k) t)
  | app l u v => app l (lift n k u) (lift n k v)
  | Prod l A B => Prod l (lift n k A) (lift n (S k) B)
  | ex u p => ex (lift n k u) (lift n k p)
  | wit t => wit (lift n k t)
  | prf t => prf (lift n k t)
  | Sum A P => Sum (lift n k A) (lift n (S k) P)
  | zero => zero
  | succ t => succ (lift n k t)
  | elim_nat P z s t =>
    elim_nat (lift n k P) (lift n k z) (lift n k s) (lift n k t)
  | Nat => Nat
  | vnil A => vnil (lift n k A)
  | vcons A a m v => vcons (lift n k A) (lift n k a) (lift n k m) (lift n k v)
  | elim_vec A P e c m v =>
    elim_vec (lift n k A) (lift n k P)
             (lift n k e) (lift n k c) (lift n k m) (lift n k v)
  | vec A m => vec (lift n k A) (lift n k m)
  | univ s => univ s
  end.

Notation lift0 n := (lift n 0).