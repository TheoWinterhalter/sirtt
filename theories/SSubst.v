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

Fixpoint lift_context n k (Γ : context) : context :=
  match Γ with
  | [] => []
  | (ℓ, A) :: Γ => (ℓ, lift n (k + #|Γ|) A) :: lift_context n k Γ
  end.

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
  all: try solve [
    simpl ; f_equal ; eauto ;
    eapply IHt2 ; lia
  ].
  simpl. destruct (PeanoNat.Nat.leb_spec k n).
  - destruct (PeanoNat.Nat.leb_spec i (m + n)). 2: lia.
    f_equal. lia.
  - destruct (PeanoNat.Nat.leb_spec i n). 1: lia.
    reflexivity.
Qed.

Lemma permute_lift :
  ∀ t n k p i,
    i ≤ k →
    lift p i (lift n k t) = lift n (k + p) (lift p i t).
Proof.
  intros t m k p i h.
  induction t in m, k, p, i, h |- *.
  all: try solve [ intuition eauto ].
  all: try solve [
    simpl ; f_equal ; intuition eauto
  ].
  all: try solve [
    simpl ; f_equal ; eauto ;
    eapply IHt2 ; lia
  ].
  simpl. destruct (PeanoNat.Nat.leb_spec k n).
  - destruct (PeanoNat.Nat.leb_spec i n). 2: lia.
    destruct (PeanoNat.Nat.leb_spec i (m + n)). 2: lia.
    destruct (PeanoNat.Nat.leb_spec (k + p) (p + n)). 2: lia.
    f_equal. lia.
  - destruct (PeanoNat.Nat.leb_spec i n).
    + destruct (PeanoNat.Nat.leb_spec (k + p) (p + n)). 1: lia.
      reflexivity.
    + destruct (PeanoNat.Nat.leb_spec (k + p) n). 1: lia.
      reflexivity.
Qed.

Lemma ptm_lift :
  ∀ n k t,
    ptm (lift n k t) = lift n k (ptm t).
Proof.
  intros m k t.
  induction t in m, k |- *.
  all: try reflexivity.
  all: solve [ simpl ; f_equal ; eauto ].
Qed.

Lemma psub_map_lift :
  ∀ n k σ,
    psub (map (lift n k) σ) = map (lift n k) (psub σ).
Proof.
  intros n k σ.
  unfold psub.
  rewrite !map_map. apply map_ext. intro t.
  apply ptm_lift.
Qed.

Lemma psub_length :
  ∀ σ, #| psub σ | = #|σ|.
Proof.
  apply map_length.
Qed.

#[local] Ltac distr_lift_subst_rec_ih :=
  lazymatch goal with
  | ih : ∀ σ m p k, lift _ _ (subst _ _ ?t) = _ |-
    lift _ _ (subst (psub ?σ) _ ?t) = _ =>
    specialize (ih (psub σ)) ;
    rewrite psub_length in ih ;
    apply ih
  | ih : ∀ σ m p k, lift _ _ (subst _ _ ?t) = _ |-
    lift _ _ (subst ?σ _ ?t) = subst (map (lift ?m ?k) _) ?p _ =>
    specialize (ih σ m p k) ;
    apply ih
  end.

Lemma distr_lift_subst_rec :
  ∀ u σ m p k,
    lift m (p + k) (subst σ p u) =
    subst (map (lift m k) σ) p (lift m (p + #|σ| + k) u).
Proof.
  intros u σ m p k.
  induction u in σ, m, p, k |- *.
  all: try solve [ intuition eauto ].
  all: try solve [
    simpl ; f_equal ; intuition eauto
  ].
  all: try solve [
    simpl ; rewrite ?psub_map_lift ; f_equal ;
    intuition eauto ; distr_lift_subst_rec_ih
  ].
  simpl. rewrite map_length.
  rewrite nth_error_map.
  destruct (PeanoNat.Nat.leb_spec p n).
  - destruct (PeanoNat.Nat.leb_spec (p + #|σ| + k) n).
    + destruct (PeanoNat.Nat.leb_spec p (m + n)). 2: lia.
      destruct nth_error eqn:e.
      1:{ apply nth_error_Some_length in e. lia. }
      clear e.
      destruct nth_error eqn:e.
      1:{ apply nth_error_Some_length in e. lia. }
      clear e. simpl.
      destruct (PeanoNat.Nat.leb_spec (p + k) (n - #|σ|)). 2: lia.
      f_equal. lia.
    + destruct (PeanoNat.Nat.leb_spec p n). 2: lia.
      destruct nth_error eqn:e.
      * simpl. replace (p + k) with (k + p) by lia.
        rewrite <- permute_lift. 2: lia.
        reflexivity.
      * simpl. apply nth_error_None in e as ?.
        destruct (PeanoNat.Nat.leb_spec (p + k) (n - #|σ|)). 1: lia.
        reflexivity.
  - destruct (PeanoNat.Nat.leb_spec (p + #|σ| + k) n). 1: lia.
    destruct (PeanoNat.Nat.leb_spec p n). 1: lia.
    simpl. destruct (PeanoNat.Nat.leb_spec (p + k) n). 1: lia.
    reflexivity.
Qed.

Lemma distr_lift_subst :
  ∀ σ t n k,
    lift n k (subst0 σ t) = subst0 (map (lift n k) σ) (lift n (#|σ| + k) t).
Proof.
  intros σ t n k.
  change k with (0 + k).
  apply distr_lift_subst_rec.
Qed.

Lemma distr_lift_subst10 :
  ∀ u v n k,
    lift n k (subst10 v u) = subst10 (lift n k v) (lift n (S k) u).
Proof.
  intros u v n k.
  change k with (0 + k).
  apply distr_lift_subst_rec.
Qed.

Lemma lift_context_length :
  ∀ Γ n k,
    #| lift_context n k Γ | = #|Γ|.
Proof.
  intros Γ n k.
  induction Γ.
  - reflexivity.
  - simpl. f_equal. auto.
Qed.

Lemma nth_error_lift_context :
  ∀ n k Γ m,
    nth_error (lift_context n k Γ) m =
    option_map
      (λ '(ℓ, A), (ℓ, lift n (k + (#|Γ| - Datatypes.S m)) A))
      (nth_error Γ m).
Proof.
  intros n k Γ m.
  induction Γ as [| [ℓ A] Γ ih] in n, k, m |- *.
  - simpl. destruct m. all: reflexivity.
  - simpl. destruct m.
    + simpl. f_equal. f_equal. f_equal. lia.
    + simpl. apply ih.
Qed.