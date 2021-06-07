(* SIRTT Lifting and substitution *)

From Coq Require Import Utf8 List Nat Lia.
Require Import Util SAst.

Import ListNotations.

Declare Scope s_scope.
Delimit Scope s_scope with s.

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
    elim_vec
      (lift n k A) (lift n k P)
      (lift n k e) (lift n k c) (lift n k m) (lift n k v)
  | Vec A m => Vec (lift n k A) (lift n k m)
  | refl A u => refl (lift n k A) (lift n k u)
  | coe A P u v e t =>
    coe
      (lift n k A) (lift n k P)
      (lift n k u) (lift n k v) (lift n k e)
      (lift n k t)
  | Eq A u v => Eq (lift n k A) (lift n k u) (lift n k v)
  | exfalso A p => exfalso (lift n k A) (lift n k p)
  | Empty => Empty
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
  | lam l A t => lam l (subst (psub s) k A) (subst s (S k) t)
  | app l u v => app l (subst s k u) (subst s k v)
  | Prod l A B => Prod l (subst s k A) (subst s (S k) B)
  | ex u p => ex (subst s k u) (subst s k p)
  | wit t => wit (subst s k t)
  | prf t => prf (subst s k t)
  | Sum A P => Sum (subst s k A) (subst s (S k) P)
  | zero => zero
  | succ t => succ (subst s k t)
  | elim_nat P z sc t =>
    elim_nat (subst (psub s) k P) (subst s k z) (subst s k sc) (subst s k t)
  | Nat => Nat
  | vnil A => vnil (subst (psub s) k A)
  | vcons A a m v => vcons (subst (psub s) k A) (subst s k a) (subst s k m) (subst s k v)
  | elim_vec A P e c m v =>
    elim_vec (subst (psub s) k A) (subst (psub s) k P)
             (subst s k e) (subst s k c) (subst s k m) (subst s k v)
  | Vec A m => Vec (subst s k A) (subst s k m)
  | refl A u => refl (subst (psub s) k A) (subst s k u)
  | coe A P u v e t =>
    coe
      (subst (psub s) k A) (subst (psub s) k P)
      (subst s k u) (subst s k v) (subst s k e)
      (subst s k t)
  | Eq A u v => Eq (subst s k A) (subst s k u) (subst s k v)
  | exfalso A p => exfalso (subst (psub s) k A) (subst s k p)
  | Empty => Empty
  | univ s => univ s
  end.

(** Substitutes [t1 ; .. ; tn] in u for [Rel 0; .. Rel (n-1)] *in parallel* *)
Notation subst0 t := (subst t 0).
Definition subst1 t k u := subst [t] k u.
Notation subst10 t := (subst1 t 0).
Notation "M { j := N }" :=
  (subst1 N j M) (at level 10, right associativity) : s_scope.

Lemma lift_0 :
  ∀ k t, lift 0 k t = t.
Proof.
  intros k t.
  induction t in k |- *.
  all: try reflexivity.
  all: try solve [ cbn ; f_equal ; intuition eauto ].
  cbn. destruct (k <=? n). all: reflexivity.
Qed.

Lemma lift_lift :
  ∀ k n m t,
    lift n k (lift m k t) = lift (n + m) k t.
Proof.
  intros k p m t.
  induction t in k, p, m |- *.
  all: try reflexivity.
  all: try solve [ cbn ; f_equal ; intuition eauto ].
  cbn. destruct (k <=? n) eqn:e.
  - destruct (k <=? m + n) eqn:e'.
    2:{
      eapply Compare_dec.leb_complete in e.
      eapply Compare_dec.leb_complete_conv in e'.
      lia.
    }
    f_equal. lia.
  - rewrite e. reflexivity.
Qed.

Lemma simpl_lift :
  ∀ t n k p i,
    i ≤ k + n →
    k ≤ i →
    lift p i (lift n k t) = lift (p + n) k t.
Proof.
  intros t m k p i h1 h2.
  induction t in m, k, p, i, h1, h2 |- *.
  all: try solve [ intuition eauto ].
  all: try solve [
    simpl ; f_equal ; intuition eauto
  ].
  - simpl. destruct (PeanoNat.Nat.leb_spec k n).
    + destruct (PeanoNat.Nat.leb_spec i (m + n)). 2: lia.
      f_equal. lia.
    + destruct (PeanoNat.Nat.leb_spec i n). 1: lia.
      reflexivity.
  - simpl. f_equal. 1: eauto.
    eapply IHt2. all: lia.
  - simpl. f_equal. 1: eauto.
    eapply IHt2. all: lia.
  - simpl. f_equal. 1: eauto.
    eapply IHt2. all: lia.
Qed.