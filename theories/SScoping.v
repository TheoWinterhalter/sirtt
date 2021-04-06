(* Scoping in SIRTT *)

From Coq Require Import Utf8 List.
Require Import Equations.Prop.DepElim.
Require Import Equations.Prop.Classes.
From Equations Require Import Equations.
Require Import Util Level SAst SSubst SReduction.

Import ListNotations.

Set Default Goal Selector "!".

Definition psc (Γ : scope) : scope :=
  map pred Γ.

Inductive scoping (Γ : scope) : level → term → Type :=
| scope_var :
    ∀ n ℓ,
      nth_error Γ n = Some ℓ →
      scoping Γ ℓ (var n)

| scope_lam :
    ∀ ℓ ℓ' A t,
      scoping (psc Γ) ℓ A →
      scoping (ℓ' :: Γ) ℓ t →
      scoping Γ ℓ (lam ℓ' A t)

| scope_app :
    ∀ ℓ ℓ' u v,
      scoping Γ ℓ u →
      scoping Γ (ℓ ⊔ ℓ') v →
      scoping Γ ℓ (app ℓ' u v)

| scope_Prod :
    ∀ ℓ ℓ' A B,
      scoping Γ ℓ A →
      scoping (▪ℓ' :: Γ) ℓ B →
      scoping Γ ℓ (Prod ℓ' A B)

| scope_ex :
    ∀ ℓ u p,
      scoping Γ ℓ u →
      scoping Γ I p →
      scoping Γ ℓ (ex u p)

| scope_wit :
    ∀ ℓ t,
      scoping Γ ℓ t →
      scoping Γ ℓ (wit t)

| scope_prf :
    ∀ t,
      scoping Γ I t →
      scoping Γ S (prf t)

| scope_Sum :
    ∀ ℓ A P,
      scoping Γ ℓ A →
      scoping (R :: Γ) (S ⊔ ℓ) P →
      scoping Γ ℓ (Sum A P)

| scope_zero :
    ∀ ℓ,
      scoping Γ ℓ zero

| scope_succ :
    ∀ ℓ t,
      scoping Γ ℓ t →
      scoping Γ ℓ (succ t)

| scope_elim_nat :
    ∀ ℓ P z s n,
      scoping (psc Γ) ℓ P →
      scoping Γ ℓ z →
      scoping Γ ℓ s →
      scoping Γ ℓ n →
      scoping Γ ℓ (elim_nat P z s n)

| scope_Nat :
    ∀ ℓ,
      scoping Γ ℓ Nat

| scope_vnil :
    ∀ ℓ A,
      scoping (psc Γ) ℓ A →
      scoping Γ ℓ (vnil A)

| scope_vcons :
    ∀ ℓ A a n v,
      scoping (psc Γ) ℓ A →
      scoping Γ ℓ a →
      scoping Γ I n →
      scoping Γ ℓ v →
      scoping Γ ℓ (vcons A a n v)

| scope_elim_vec :
    ∀ ℓ A P e c n v,
      scoping (psc Γ) ℓ A →
      scoping (psc Γ) ℓ P →
      scoping Γ ℓ e →
      scoping Γ ℓ c →
      scoping Γ I n →
      scoping Γ ℓ v →
      scoping Γ ℓ (elim_vec A P e c n v)

| scope_Vec :
    ∀ ℓ A n,
      scoping Γ ℓ A →
      scoping Γ (S ⊔ ℓ) n →
      scoping Γ ℓ (Vec A n)

| scope_refl :
    ∀ ℓ A u,
      scoping (psc Γ) ℓ A →
      scoping Γ ℓ u →
      scoping Γ ℓ (refl A u)

| scope_coe :
    ∀ ℓ A P u v e t,
      scoping (psc Γ) ℓ A →
      scoping (psc Γ) ℓ P →
      scoping Γ ℓ u →
      scoping Γ ℓ v →
      scoping Γ ℓ e →
      scoping Γ ℓ t →
      scoping Γ ℓ (coe A P u v e t)

| scope_Eq :
    ∀ ℓ A u v,
      scoping Γ ℓ A →
      scoping Γ ℓ u →
      scoping Γ ℓ v →
      scoping Γ ℓ (Eq A u v)

| scope_exfalso :
    ∀ ℓ A p,
      scoping (psc Γ) ℓ A →
      scoping Γ I p →
      scoping Γ ℓ (exfalso A p)

| scope_Empty :
    ∀ ℓ,
      scoping Γ ℓ Empty

| scope_univ :
    ∀ ℓ s,
      scoping Γ ℓ (univ s)

| scope_sub :
    ∀ ℓ ℓ' t,
      scoping Γ ℓ t →
      ℓ ⊑ ℓ' → (* Could also be ⊏ *)
      scoping Γ ℓ' t
.

Inductive scoping_context : context → Type :=
| scope_nil : scoping_context []
| scope_cons :
    ∀ ℓ A Γ,
      scoping_context Γ →
      scoping (psc Γ) R A →
      scoping_context ((ℓ, A) :: Γ).

(* Inversion lemmata for scoping *)

Set Equations With UIP.

Derive Signature for scoping.
Derive NoConfusion NoConfusionHom EqDec for level.
Derive NoConfusion NoConfusionHom EqDec for term.
(* Derive NoConfusionHom for scoping. *)

(* Local Ltac invtac h :=
  dependent induction h ; [
    eexists ; split ; [
      right
    | intuition eauto
    ]
  | match goal with
    | ih : ∑ x : _, _ |- _ =>
      destruct ih as [ℓ₀ [? ?]] ;
      exists ℓ₀ ; split ; [
        etransitivity ; eauto
      | intuition eauto
      ]
    end
  ]. *)

Lemma inversion_scope_var :
  ∀ Γ ℓ n,
    scoping Γ ℓ (var n) →
    ∑ ℓ', ℓ' ⊑ ℓ × nth_error Γ n = Some ℓ'.
Proof.
  intros Γ ℓ n h.
  dependent induction h.
  - eexists. split.
    + right.
    + auto.
  - destruct IHh as [ℓ₀ [? ?]].
    exists ℓ₀. split.
    + etransitivity. all: eauto.
    + auto.
Qed.

Lemma inversion_scope_lam :
  ∀ Γ ℓ ℓ' A t,
    scoping Γ ℓ (lam ℓ' A t) →
    scoping (psc Γ) ℓ A ×
    scoping (ℓ' :: Γ) ℓ t.
Proof.
  intros Γ ℓ ℓ' A t h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    all: eapply scope_sub ; eauto.
Qed.

Lemma inversion_scope_app :
  ∀ Γ ℓ ℓ' u v,
    scoping Γ ℓ (app ℓ' u v) →
    scoping Γ ℓ u ×
    scoping Γ (ℓ ⊔ ℓ') v.
Proof.
  intros Γ ℓ ℓ' u v h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    + eapply scope_sub. all: eauto.
    + eapply scope_sub. 1: eauto.
      eapply max_le_cong_l. auto.
Qed.

Lemma inversion_scope_Prod :
  ∀ Γ ℓ ℓ' A B,
    scoping Γ ℓ (Prod ℓ' A B) →
    scoping Γ ℓ A ×
    scoping (▪ℓ' :: Γ) ℓ B.
Proof.
  intros Γ ℓ ℓ' A B h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    + eapply scope_sub. all: eauto.
    + eapply scope_sub. all: eauto.
Qed.

Lemma inversion_scope_ex :
  ∀ Γ ℓ u p,
    scoping Γ ℓ (ex u p) →
    scoping Γ ℓ u ×
    scoping Γ I p.
Proof.
  intros Γ ℓ u p h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    eapply scope_sub. all: eauto.
Qed.

Lemma inversion_scope_wit :
  ∀ Γ ℓ t,
    scoping Γ ℓ (wit t) →
    scoping Γ ℓ t.
Proof.
  intros Γ ℓ t h.
  dependent induction h.
  - intuition auto.
  - eapply scope_sub. all: eauto.
Qed.

Lemma inversion_scope_prf :
    ∀ Γ ℓ t,
      scoping Γ ℓ (prf t) →
      S ⊑ ℓ ×
      scoping Γ I t.
Proof.
  intros Γ ℓ t h.
  dependent induction h.
  - intuition auto. reflexivity.
  - intuition auto.
    etransitivity. all: eauto.
Qed.

Lemma inversion_scope_Sum :
  ∀ Γ ℓ A P,
    scoping Γ ℓ (Sum A P) →
    scoping Γ ℓ A ×
    scoping (R :: Γ) (S ⊔ ℓ) P.
Proof.
  intros Γ ℓ A P h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    + eapply scope_sub. all: eauto.
    + eapply scope_sub. 1: eauto.
      rewrite max_sym. etransitivity. 1: eapply max_le_cong_l. 1: eauto.
      rewrite max_sym. reflexivity.
Qed.

Lemma inversion_scope_succ :
  ∀ Γ ℓ t,
    scoping Γ ℓ (succ t) →
    scoping Γ ℓ t.
Proof.
  intros Γ ℓ t h.
  dependent induction h.
  - intuition auto.
  - eapply scope_sub. all: eauto.
Qed.

Lemma inversion_scope_elim_nat :
  ∀ Γ ℓ P z s n,
    scoping Γ ℓ (elim_nat P z s n) →
    scoping (psc Γ) ℓ P ×
    scoping Γ ℓ z ×
    scoping Γ ℓ s ×
    scoping Γ ℓ n.
Proof.
  intros Γ ℓ P z s n h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    all: eapply scope_sub. all: eauto.
Qed.

Lemma inversion_scope_vnil :
  ∀ Γ ℓ A,
    scoping Γ ℓ (vnil A) →
    scoping (psc Γ) ℓ A.
Proof.
  intros Γ ℓ A h.
  dependent induction h.
  - intuition auto.
  - eapply scope_sub. all: eauto.
Qed.

Lemma inversion_scope_vcons :
  ∀ Γ ℓ A a n v,
    scoping Γ ℓ (vcons A a n v) →
    scoping (psc Γ) ℓ A ×
    scoping Γ ℓ a ×
    scoping Γ I n ×
    scoping Γ ℓ v.
Proof.
  intros Γ ℓ A a n v h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    all: eapply scope_sub. all: eauto.
Qed.

Lemma inversion_scope_elim_vec :
  ∀ Γ ℓ A P e c n v,
    scoping Γ ℓ (elim_vec A P e c n v) →
    scoping (psc Γ) ℓ A ×
    scoping (psc Γ) ℓ P ×
    scoping Γ ℓ e ×
    scoping Γ ℓ c ×
    scoping Γ I n ×
    scoping Γ ℓ v.
Proof.
  intros Γ ℓ A P e c n v h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    all: eapply scope_sub. all: eauto.
Qed.

Lemma inversion_scope_Vec :
  ∀ Γ ℓ A n,
    scoping Γ ℓ (Vec A n) →
    scoping Γ ℓ A ×
    scoping Γ (S ⊔ ℓ) n.
Proof.
  intros Γ ℓ A n h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    + eapply scope_sub. all: eauto.
    + eapply scope_sub. 1: eauto.
      rewrite max_sym. etransitivity. 1: eapply max_le_cong_l. 1: eauto.
      rewrite max_sym. reflexivity.
Qed.

Lemma inversion_scope_refl :
  ∀ Γ ℓ A u,
    scoping Γ ℓ (refl A u) →
    scoping (psc Γ) ℓ A ×
    scoping Γ ℓ u.
Proof.
  intros Γ ℓ A u h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    all: eapply scope_sub. all: eauto.
Qed.

Lemma inversion_scope_coe :
  ∀ Γ ℓ A P u v e t,
    scoping Γ ℓ (coe A P u v e t) →
    scoping (psc Γ) ℓ A ×
    scoping (psc Γ) ℓ P ×
    scoping Γ ℓ u ×
    scoping Γ ℓ v ×
    scoping Γ ℓ e ×
    scoping Γ ℓ t.
Proof.
  intros Γ ℓ A P u v e t h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    all: eapply scope_sub. all: eauto.
Qed.

Lemma inversion_scope_Eq :
  ∀ Γ ℓ A u v,
    scoping Γ ℓ (Eq A u v) →
    scoping Γ ℓ A ×
    scoping Γ ℓ u ×
    scoping Γ ℓ v.
Proof.
  intros Γ ℓ A u v h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    all: eapply scope_sub. all: eauto.
Qed.

Lemma inversion_scope_exfalso :
  ∀ Γ ℓ A p,
    scoping Γ ℓ (exfalso A p) →
    scoping (psc Γ) ℓ A ×
    scoping Γ I p.
Proof.
  intros Γ ℓ A p h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    eapply scope_sub. all: eauto.
Qed.

Ltac scope_inv h h' :=
  lazymatch type of h with
  | scoping ?Γ ?ℓ ?t =>
    lazymatch t with
    | var ?n => apply inversion_scope_var in h as h'
    | lam ?ℓ' ?A ?t => apply inversion_scope_lam in h as h'
    | app ?ℓ' ?u ?v => apply inversion_scope_app in h as h'
    | Prod ?ℓ' ?A ?B => apply inversion_scope_Prod in h as h'
    | ex ?u ?p => apply inversion_scope_ex in h as h'
    | wit ?t => apply inversion_scope_wit in h as h'
    | prf ?t => apply inversion_scope_prf in h as h'
    | Sum ?A ?P => apply inversion_scope_Sum in h as h'
    | succ ?t => apply inversion_scope_succ in h as h'
    | elim_nat ?P ?z ?s ?n => apply inversion_scope_elim_nat in h as h'
    | vnil ?A => apply inversion_scope_vnil in h as h'
    | vcons ?A ?a ?n ?v => apply inversion_scope_vcons in h as h'
    | elim_vec ?A ?P ?e ?c ?n ?v => apply inversion_scope_elim_vec in h as h'
    | Vec ?A ?n => apply inversion_scope_Vec in h as h'
    | refl ?A ?u => apply inversion_scope_refl in h as h'
    | coe ?A ?P ?u ?v ?e ?t => apply inversion_scope_coe in h as h'
    | Eq ?A ?u ?v => apply inversion_scope_Eq in h as h'
    | exfalso ?A ?p => apply inversion_scope_exfalso in h as h'
    | _ => fail "scope_inv: case not handled"
    end
  | _ => fail "scope_inv only applies to scoping assumptions"
  end.

Lemma scoping_context_nth_error :
  ∀ (Γ : context) n ℓ A,
    scoping_context Γ →
    nth_error Γ n = Some (ℓ, A) →
    scoping (skipn (Datatypes.S n) (psc Γ)) R A.
Proof.
  intros Γ n ℓ A h e.
  induction h in n, ℓ, A, e |- *.
  1:{ destruct n. all: discriminate. }
  destruct n.
  - cbn in e. inversion e. subst. clear e.
    cbn. auto.
  - cbn in e. eapply IHh in e. auto.
Qed.