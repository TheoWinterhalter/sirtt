(* Erasure translation from SIRTT to MLTT *)

Require Import Util SIRTT MLTT.

Definition dummy : MLTT.term := MLTT.var 0.

Fixpoint trans (t : SIRTT.term) : MLTT.term :=
  match t with
  | SIRTT.var i => MLTT.var i
  | SIRTT.lam l A t => MLTT.lam (trans A) (trans t)
  | SIRTT.app l u v => MLTT.app (trans u) (trans v)
  | SIRTT.Prod l A B => MLTT.Prod (trans A) (trans B)
  | SIRTT.ex u p => trans u
  | SIRTT.wit t => trans t
  | SIRTT.prf t => dummy
  | SIRTT.Sum A P => trans A
  | SIRTT.zero => MLTT.zero
  | SIRTT.succ t => MLTT.succ (trans t)
  | SIRTT.elim_nat P z s t =>
    MLTT.elim_nat (trans P) (trans z) (trans s) (trans t)
  | SIRTT.Nat => MLTT.Nat
  | SIRTT.vnil A => MLTT.lnil (trans A)
  | SIRTT.vcons A a m v => MLTT.lcons (trans A) (trans a) (trans v)
  | SIRTT.elim_vec A P e c m v =>
    MLTT.elim_list (trans A) (trans P) (trans e) (trans c) (trans v)
  | SIRTT.Vec A m => MLTT.List (trans A)
  | SIRTT.univ s => MLTT.univ s
  end.