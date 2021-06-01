(* Scoping in SIRTT *)

From Coq Require Import Utf8 List Lia.
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
      scoping (psc Γ) (▪ (ℓ ⊔ ℓ')) A →
      scoping (ℓ' :: Γ) ℓ t →
      scoping Γ ℓ (lam ℓ' A t)

| scope_app :
    ∀ ℓ ℓ' u v,
      scoping Γ ℓ u →
      scoping Γ (ℓ ⊔ ℓ') v →
      scoping Γ ℓ (app ℓ' u v)

| scope_Prod :
    ∀ ℓ ℓ' A B,
      scoping Γ (ℓ ⊔ ▪ ℓ') A →
      scoping (▪ ℓ' :: Γ) ℓ B →
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
      scoping (psc Γ) (▪ ℓ) P →
      scoping Γ ℓ z →
      scoping Γ ℓ s →
      scoping Γ ℓ n →
      scoping Γ ℓ (elim_nat P z s n)

| scope_Nat :
    ∀ ℓ,
      scoping Γ ℓ Nat

| scope_vnil :
    ∀ ℓ A,
      scoping (psc Γ) (▪ ℓ) A →
      scoping Γ ℓ (vnil A)

| scope_vcons :
    ∀ ℓ A a n v,
      scoping (psc Γ) (▪ ℓ) A →
      scoping Γ ℓ a →
      scoping Γ I n →
      scoping Γ ℓ v →
      scoping Γ ℓ (vcons A a n v)

| scope_elim_vec :
    ∀ ℓ A P e c n v,
      scoping (psc Γ) (▪ ℓ) A →
      scoping (psc Γ) (▪ ℓ) P →
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
      scoping (psc Γ) (▪ ℓ) A →
      scoping Γ ℓ u →
      scoping Γ ℓ (refl A u)

| scope_coe :
    ∀ ℓ A P u v e t,
      scoping (psc Γ) (▪ ℓ) A →
      scoping (psc Γ) (▪ ℓ) P →
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
      scoping (psc Γ) (▪ ℓ) A →
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

Inductive scoping_context ℓ : context → Type :=
| scope_nil : scoping_context ℓ []
| scope_cons :
    ∀ ℓ' A Γ,
      scoping_context ℓ Γ →
      scoping (psc Γ) (ℓ ⊔ ▪ ℓ') A →
      scoping_context ℓ ((ℓ', A) :: Γ).

(* Inversion lemmata for scoping *)

Set Equations With UIP.

Derive Signature for scoping.
Derive NoConfusion NoConfusionHom EqDec for level.
Derive NoConfusion NoConfusionHom EqDec for term.

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
    scoping (psc Γ) (▪ (ℓ ⊔ ℓ')) A ×
    scoping (ℓ' :: Γ) ℓ t.
Proof.
  intros Γ ℓ ℓ' A t h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    + eapply scope_sub. 1: eauto.
      apply pred_pred_le.
      apply max_le_cong_l. auto.
    + eapply scope_sub. all: eauto.
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
    scoping Γ (ℓ ⊔ ▪ ℓ') A ×
    scoping (▪ ℓ' :: Γ) ℓ B.
Proof.
  intros Γ ℓ ℓ' A B h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    + eapply scope_sub. 1: eauto.
      apply max_le_cong_l. auto.
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
    scoping (psc Γ) (▪ ℓ) P ×
    scoping Γ ℓ z ×
    scoping Γ ℓ s ×
    scoping Γ ℓ n.
Proof.
  intros Γ ℓ P z s n h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    all: eapply scope_sub. all: eauto.
    apply pred_pred_le. auto.
Qed.

Lemma inversion_scope_vnil :
  ∀ Γ ℓ A,
    scoping Γ ℓ (vnil A) →
    scoping (psc Γ) (▪ ℓ) A.
Proof.
  intros Γ ℓ A h.
  dependent induction h.
  - intuition auto.
  - eapply scope_sub. 1: eauto.
    apply pred_pred_le. auto.
Qed.

Lemma inversion_scope_vcons :
  ∀ Γ ℓ A a n v,
    scoping Γ ℓ (vcons A a n v) →
    scoping (psc Γ) (▪ ℓ) A ×
    scoping Γ ℓ a ×
    scoping Γ I n ×
    scoping Γ ℓ v.
Proof.
  intros Γ ℓ A a n v h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    all: eapply scope_sub. all: eauto.
    apply pred_pred_le. auto.
Qed.

Lemma inversion_scope_elim_vec :
  ∀ Γ ℓ A P e c n v,
    scoping Γ ℓ (elim_vec A P e c n v) →
    scoping (psc Γ) (▪ ℓ) A ×
    scoping (psc Γ) (▪ ℓ) P ×
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
    all: apply pred_pred_le. all: auto.
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
    scoping (psc Γ) (▪ ℓ) A ×
    scoping Γ ℓ u.
Proof.
  intros Γ ℓ A u h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    all: eapply scope_sub. all: eauto.
    apply pred_pred_le. auto.
Qed.

Lemma inversion_scope_coe :
  ∀ Γ ℓ A P u v e t,
    scoping Γ ℓ (coe A P u v e t) →
    scoping (psc Γ) (▪ ℓ) A ×
    scoping (psc Γ) (▪ ℓ) P ×
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
    all: apply pred_pred_le. all: auto.
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
    scoping (psc Γ) (▪ ℓ) A ×
    scoping Γ I p.
Proof.
  intros Γ ℓ A p h.
  dependent induction h.
  - intuition auto.
  - intuition auto.
    eapply scope_sub. all: eauto.
    apply pred_pred_le. auto.
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
  ∀ (Γ : context) n ℓ ℓ' A,
    scoping_context ℓ Γ →
    nth_error Γ n = Some (ℓ', A) →
    scoping (skipn (Datatypes.S n) (psc Γ)) (ℓ ⊔ ▪ ℓ') A.
Proof.
  intros Γ n ℓ ℓ' A h e.
  induction h in n, ℓ', A, e |- *.
  1:{ destruct n. all: discriminate. }
  destruct n.
  - cbn in e. inversion e. subst. clear e.
    cbn. auto.
  - cbn in e. eapply IHh in e. auto.
Qed.

Lemma firstn_psc :
  ∀ Γ n,
    firstn n (psc Γ) = psc (firstn n Γ).
Proof.
  intros Γ n.
  induction Γ as [| ℓ Γ ih] in n |- *.
  - cbn. rewrite firstn_nil. reflexivity.
  - cbn. destruct n.
    + cbn. reflexivity.
    + cbn. f_equal. eapply ih.
Qed.

Lemma psc_idemp :
  ∀ Γ,
    psc (psc Γ) = psc Γ.
Proof.
  induction Γ as [| ℓ Γ ih].
  - reflexivity.
  - cbn. rewrite pred_idemp. f_equal. auto.
Qed.

Lemma psc_app :
  ∀ Γ Δ,
    psc (Γ ++ Δ) = psc Γ ++ psc Δ.
Proof.
  intros Γ Δ.
  induction Γ in Δ |- *.
  - reflexivity.
  - cbn. f_equal. eapply IHΓ.
Qed.

Lemma psc_length :
  ∀ Γ,
    #| psc Γ | = #| Γ |.
Proof.
  intros Γ. induction Γ.
  - reflexivity.
  - cbn. eauto.
Qed.

Inductive scoping_subst ℓ Γ : scope → list term → Type :=
| scoping_subst_cons :
    ∀ ℓ' Δ u σ,
      scoping Γ (ℓ ⊔ ℓ') u →
      scoping_subst ℓ Γ Δ σ →
      scoping_subst ℓ Γ (ℓ' :: Δ) (u :: σ)

| scoping_subst_nil :
    scoping_subst ℓ Γ [] [].

Lemma scoping_subst_nth_error :
  ∀ Γ Δ σ n ℓ ℓ' u,
    scoping_subst ℓ Γ Δ σ →
    nth_error Δ n = Some ℓ' →
    nth_error σ n = Some u →
    scoping Γ (ℓ ⊔ ℓ') u.
Proof.
  intros Γ Δ σ n ℓ ℓ' u h eΔ eσ.
  induction h in n, ℓ', u, eΔ, eσ |- *.
  2:{ destruct n. all: discriminate. }
  destruct n.
  - cbn in eΔ, eσ. inversion eΔ. inversion eσ. subst. clear eΔ eσ.
    auto.
  - cbn in eΔ, eσ. eapply IHh. all: eauto.
Qed.

(* Alternative where we only care about the relevant bits *)
Inductive relevant_scoping_subst Γ : scope → list term → Type :=
| relevant_scoping_subst_nil :
    relevant_scoping_subst Γ [] []
| relevant_scoping_subst_cons :
    ∀ ℓ Δ u σ,
      (ℓ = Level.R → scoping Γ ℓ u) →
      relevant_scoping_subst Γ Δ σ →
      relevant_scoping_subst Γ (ℓ :: Δ) (u :: σ).

Lemma relevant_scoping_subst_nth_error :
  ∀ Γ Δ σ n u,
    relevant_scoping_subst Γ Δ σ →
    nth_error Δ n = Some Level.R →
    nth_error σ n = Some u →
    scoping Γ Level.R u.
Proof.
  intros Γ Δ σ n u h eΔ eσ.
  induction h in n, u, eΔ, eσ |- *.
  1:{ destruct n. all: discriminate. }
  destruct n.
  - cbn in eΔ, eσ. inversion eΔ. inversion eσ. subst. clear eΔ eσ.
    auto.
  - cbn in eΔ, σ. eapply IHh. all: eauto.
Qed.

Inductive weaker_scope : scope → scope → Type :=
| weaker_nil :
    weaker_scope [] []
| weaker_cons :
    ∀ Γ Δ ℓ ℓ',
      weaker_scope Γ Δ →
      Level.potentially_more_relevant ℓ ℓ' →
      weaker_scope (ℓ :: Γ) (ℓ' :: Δ).

Lemma weaker_scope_nth_error :
  ∀ Γ Δ n ℓ,
    nth_error Δ n = Some ℓ →
    weaker_scope Γ Δ →
    ∑ ℓ', nth_error Γ n = Some ℓ' × Level.potentially_more_relevant ℓ' ℓ.
Proof.
  intros Γ Δ n ℓ e h.
  induction h in n, ℓ, e |- *.
  1:{ destruct n. all: discriminate. }
  destruct n.
  - cbn. cbn in e. inversion e. subst. clear e.
    eexists. intuition eauto.
  - cbn. cbn in e. eapply IHh in e. destruct e as [ℓ'' [e hℓ]].
    eexists. intuition eauto.
Qed.

Lemma weaker_scope_psc :
  ∀ Γ Δ,
    weaker_scope Γ Δ →
    weaker_scope (psc Γ) (psc Δ).
Proof.
  intros Γ Δ h.
  induction h.
  - cbn. constructor.
  - cbn. constructor. 1: auto.
    eapply pred_pred_le. auto.
Qed.

Lemma scoping_weak_level :
  ∀ Γ Δ ℓ t,
    scoping Γ ℓ t →
    weaker_scope Δ Γ →
    scoping Δ ℓ t.
Proof.
  intros Γ Δ ℓ t h hw.
  induction h in Δ, hw |- *.
  all: try solve [ constructor ; eauto ].
  - eapply weaker_scope_nth_error in hw as h. 2: eauto.
    destruct h as [ℓ' [e' hℓ]].
    eapply scope_sub. 2: eauto.
    constructor. auto.
  - constructor.
    + eapply IHh1. eapply weaker_scope_psc. auto.
    + eapply IHh2. constructor. 1: auto.
      right.
  - constructor.
    + eapply IHh1. auto.
    + eapply IHh2. constructor. 1: auto.
      right.
  - constructor. 1: auto.
    eapply IHh2. constructor. 1: auto. right.
  - constructor. all: eauto.
    eapply IHh1. eapply weaker_scope_psc. auto.
  - constructor. eapply IHh. eapply weaker_scope_psc. auto.
  - constructor. all: eauto.
    eapply IHh1. eapply weaker_scope_psc. auto.
  - constructor. all: eauto.
    + eapply IHh1. eapply weaker_scope_psc. auto.
    + eapply IHh2. eapply weaker_scope_psc. auto.
  - constructor. all: eauto.
    eapply IHh1. eapply weaker_scope_psc. auto.
  - constructor. all: eauto.
    + eapply IHh1. eapply weaker_scope_psc. auto.
    + eapply IHh2. eapply weaker_scope_psc. auto.
  - constructor. all: eauto.
    eapply IHh1. eapply weaker_scope_psc. auto.
  - eapply scope_sub. 2: eauto.
    eapply IHh. auto.
Qed.

Lemma weaker_psc :
  ∀ Γ,
    weaker_scope (psc Γ) Γ.
Proof.
  intros Γ. induction Γ as [| ℓ Γ ih].
  - constructor.
  - cbn. constructor.
    + eapply ih.
    + eapply pred_le.
Qed.

Lemma scoping_psc :
  ∀ Γ ℓ t,
    scoping Γ ℓ t →
    scoping (psc Γ) ℓ t.
Proof.
  intros Γ ℓ t h.
  eapply scoping_weak_level.
  - eauto.
  - eapply weaker_psc.
Qed.

Lemma relevant_scoping_subst_psc :
  ∀ Γ Δ σ,
    relevant_scoping_subst Γ Δ σ →
    relevant_scoping_subst (psc Γ) (psc Δ) σ.
Proof.
  intros Γ Δ σ h.
  induction h.
  - cbn. constructor.
  - cbn. constructor. 2: eauto.
    intro e. destruct ℓ. 2-3: discriminate.
    cbn. eapply scoping_psc. eauto.
Qed.

Lemma scoping_ptm :
  ∀ Γ ℓ t,
    scoping Γ ℓ t →
    scoping (psc Γ) (▪ ℓ) (ptm t).
Proof.
  intros Γ ℓ t h.
  induction t in Γ, ℓ, h |- *.
  all: try solve [ constructor ; eauto ].
  all: try solve [ scope_inv h hs ; constructor ; intuition eauto ].
  - scope_inv h hs. destruct hs as [ℓ' [hℓ e]].
    eapply scope_sub.
    + constructor. unfold psc. rewrite nth_error_map. rewrite e. cbn.
      reflexivity.
    + eapply pred_pred_le. auto.
  - cbn. scope_inv h hs.
    constructor.
    + eapply IHt1. rewrite max_pred. intuition eauto.
    + eapply IHt2 with (Γ := _ :: _). intuition eauto.
  - cbn. scope_inv h hs.
    constructor. 1: intuition eauto.
    rewrite max_pred. intuition eauto.
  - cbn. scope_inv h hs.
    constructor.
    + rewrite max_pred. eapply IHt1. intuition eauto.
    + eapply IHt2 with (Γ := _ :: _). intuition eauto.
  - cbn. scope_inv h hs. constructor. 1: intuition eauto.
    eapply scoping_psc. intuition eauto.
  - cbn. scope_inv h hs. destruct hs as [hs ?h].
    eapply scope_sub.
    + constructor. eapply scoping_psc. auto.
    + destruct ℓ. all: cbn. 1: auto.
      all: reflexivity.
  - cbn. scope_inv h hs. constructor. 1: intuition eauto.
    destruct hs as [h1 h2].
    eapply IHt2 in h2 as ih. rewrite <- max_pred in ih.
    auto.
  - cbn. scope_inv h hs. constructor. all: try solve [ intuition eauto ].
    eapply scoping_psc. intuition eauto.
  - cbn. scope_inv h hs. constructor. all: try solve [ intuition eauto ].
    eapply scoping_psc. intuition eauto.
  - cbn. scope_inv h hs. constructor. 1: intuition eauto.
    destruct hs as [h1 h2].
    eapply IHt2 in h2 as ih. rewrite <- max_pred in ih.
    auto.
  - cbn. scope_inv h hs. constructor. 1: intuition eauto.
    eapply scoping_psc. intuition eauto.
Qed.

Lemma relevant_scoping_subst_psub :
  ∀ Γ Δ σ,
    relevant_scoping_subst Γ Δ σ →
    relevant_scoping_subst (psc Γ) (psc Δ) (psub σ).
Proof.
  intros Γ Δ σ h.
  induction h.
  - cbn. constructor.
  - cbn. constructor. 2: eauto.
    intro e. destruct ℓ. 2-3: discriminate.
    eapply scoping_ptm. auto.
Qed.

Lemma reveal_scope_sound :
  ∀ Γ ℓ t,
    scoping Γ ℓ t →
    let '(u, σ) := reveal t in
    scoping (reveal_scope t ++ Γ) ℓ u.
Proof.
  fix aux 3.
  intros Γ ℓ t h.
  destruct t. all: try assumption.
  - cbn. destruct l.
    + cbn. assumption.
    + destruct t1. all: try assumption.
      destruct l. all: try assumption.
      scope_inv h hs. destruct hs as [hs _].
      scope_inv hs hs'. destruct hs' as [_ hs'].
      eapply aux in hs'.
      rewrite <- app_assoc. auto.
    + destruct t1. all: try assumption.
      destruct l. all: try assumption.
      scope_inv h hs. destruct hs as [hs _].
      scope_inv hs hs'. destruct hs' as [_ hs'].
      eapply aux in hs'.
      rewrite <- app_assoc. auto.
  - cbn. destruct t. all: try assumption.
    scope_inv h hs. scope_inv hs h'. destruct h' as [h' _].
    eapply aux. auto.
Qed.

Lemma scoping_subst_app :
  ∀ ℓ Γ Δ Ξ σ θ,
    scoping_subst ℓ Γ Δ σ →
    scoping_subst ℓ Γ Ξ θ →
    scoping_subst ℓ Γ (Δ ++ Ξ) (σ ++ θ).
Proof.
  intros ℓ Γ Δ Ξ σ θ h1 h2.
  induction h1 in Ξ, θ, h2 |- *.
  - cbn. constructor. all: eauto.
  - cbn. auto.
Qed.

Lemma scoping_subst_length :
  ∀ ℓ Γ Δ σ,
    scoping_subst ℓ Γ Δ σ →
    #|σ| = #|Δ|.
Proof.
  intros ℓ Γ Δ σ h.
  induction h. all: cbn ; auto.
Qed.

Lemma lift_scoping :
  ∀ Γ Δ Ξ t ℓ,
    scoping (Ξ ++ Γ) ℓ t →
    scoping (Ξ ++ Δ ++ Γ) ℓ (lift #|Δ| #|Ξ| t).
Proof.
  intros Γ Δ Ξ t ℓ h.
  induction t in Γ, Δ, Ξ, ℓ, h |- *.
  all: try solve [ simpl ; constructor ].
  all: try solve [
    simpl ; scope_inv h hs ; constructor ; intuition eauto
  ].
  all: try solve [
    simpl ; scope_inv h hs ; constructor ; intuition eauto ;
    try lazymatch goal with
    | h : ∀ Γ Δ Ξ ℓ, scoping _ _ ?t → _ |-
      scoping (psc (?Ξ ++ ?Δ ++ ?Γ)) ?ℓ (lift _ _ ?t) =>
      specialize (h (psc Γ) (psc Δ) (psc Ξ) ℓ) ;
      rewrite !psc_app ;
      rewrite !psc_length in h ;
      apply h ;
      rewrite <- !psc_app ;
      intuition eauto
    end ;
    eapply IHt2 with (Ξ := _ :: _) ; intuition eauto
  ].
  - cbn. scope_inv h hs. destruct hs as [ℓ' [hℓ e]].
    destruct (PeanoNat.Nat.leb_spec0 #|Ξ| n) as [h1|h1].
    + eapply scope_sub. 2: eauto.
      constructor.
      rewrite nth_error_app2 in e. 2: auto.
      rewrite nth_error_app2. 2: lia.
      rewrite nth_error_app2. 2: lia.
      rewrite <- e. f_equal. lia.
    + eapply scope_sub. 2: eauto.
      constructor. rewrite nth_error_app1 in e. 2: lia.
      rewrite nth_error_app1. 2: lia.
      auto.
  - simpl. scope_inv h hs. destruct hs as [hℓ ?h].
    eapply scope_sub. 2: eauto.
    constructor. auto.
Qed.

Lemma weaker_scope_refl :
  ∀ Γ,
    weaker_scope Γ Γ.
Proof.
  intro Γ. induction Γ.
  - constructor.
  - constructor. 1: auto.
    reflexivity.
Qed.

Lemma scoping_subst_psub :
  ∀ ℓ Γ Δ σ,
    scoping_subst ℓ Γ Δ σ →
    scoping_subst (▪ ℓ) (psc Γ) (psc Δ) (psub σ).
Proof.
  intros ℓ Γ Δ σ h.
  induction h.
  - cbn. constructor. 2: eauto.
    rewrite max_pred.
    eapply scoping_ptm. auto.
  - cbn. constructor.
Qed.

Lemma scoping_subst_sub :
  ∀ ℓ ℓ' Γ Δ σ,
    scoping_subst ℓ Γ Δ σ →
    ℓ ⊑ ℓ' →
    scoping_subst ℓ' Γ Δ σ.
Proof.
  intros ℓ ℓ' Γ Δ σ h hℓ.
  induction h.
  - constructor. 2: auto.
    eapply scope_sub. 1: eauto.
    apply max_le_cong_l. auto.
  - constructor.
Qed.

#[local] Ltac subst_scoping_ih :=
  lazymatch goal with
  | h : ∀ Γ Δ Ξ ℓ σ, scoping _ _ ?t → _, hσ : scoping_subst _ _ ?Δ ?σ |-
    scoping (psc (?Ξ ++ ?Γ)) ?ℓ (subst (psub ?σ) _ ?t) =>
    specialize (h (psc Γ) (psc Δ) (psc Ξ) ℓ (psub σ)) ;
    rewrite !psc_app ;
    rewrite !psc_length in h ;
    apply h ; [
      rewrite <- !psc_app ; intuition eauto
    | eapply scoping_subst_psub ; eauto ;
      (eapply scoping_subst_sub ; intuition eauto ;
        try apply max_le_l ; try apply le_I ; try apply max_le_r)
    ]
  | h : ∀ Γ Δ Ξ ℓ σ, scoping _ _ ?t → _, hσ : scoping_subst _ _ ?Δ ?σ |-
    scoping (?Ξ ++ ?Γ) ?ℓ (subst ?σ _ ?t) =>
    eapply h ; intuition eauto ;
    (eapply scoping_subst_sub ; intuition eauto ;
      try apply max_le_l ; try apply le_I ; try apply max_le_r)
  end.

Lemma subst_scoping :
  ∀ Γ Δ Ξ ℓ σ t,
    scoping (Ξ ++ Δ ++ Γ) ℓ t →
    scoping_subst ℓ Γ Δ σ →
    scoping (Ξ ++ Γ) ℓ (subst σ #|Ξ| t).
Proof.
  intros Γ Δ Ξ ℓ σ t ht hσ.
  induction t in Γ, Δ, Ξ, ℓ, σ, ht, hσ |- *.
  all: try solve [ simpl ; constructor ].
  all: try solve [
    simpl ; scope_inv ht hs ; constructor ; intuition eauto
  ].
  all: try solve [
    simpl ; scope_inv ht hs ; constructor ; intuition eauto ;
    try solve [ eapply IHt2 with (Ξ := _ :: _) ; intuition eauto ] ;
    subst_scoping_ih
  ].
  - cbn. scope_inv ht hs. destruct hs as [ℓ' [hℓ e]].
    destruct (PeanoNat.Nat.leb_spec0 #|Ξ| n) as [h1|h1].
    + rewrite nth_error_app2 in e. 2: auto.
      destruct (nth_error σ _) eqn:e1.
      * eapply lift_scoping with (Ξ := []). cbn.
        eapply nth_error_Some_length in e1 as h2.
        eapply scoping_subst_length in hσ as eσ.
        rewrite nth_error_app1 in e. 2: lia.
        eapply scoping_subst_nth_error in e1. 2,3: eauto.
        rewrite max_l_le in e1. 2: auto.
        auto.
      * eapply nth_error_None in e1.
        eapply scoping_subst_length in hσ as eσ.
        rewrite nth_error_app2 in e. 2: lia.
        eapply scope_sub. 2: eauto.
        constructor. rewrite nth_error_app2. 2: lia.
        rewrite <- e. f_equal. lia.
    + apply PeanoNat.Nat.nle_gt in h1.
      rewrite nth_error_app1 in e. 2: auto.
      eapply scope_sub. 2: eauto.
      constructor. rewrite nth_error_app1. 2: auto.
      auto.
  - simpl. scope_inv ht hs. eapply scope_sub. 2: intuition eauto.
    constructor. subst_scoping_ih.
  - simpl. scope_inv ht hs. constructor. 1: intuition eauto.
    eapply IHt2 with (Ξ := _ :: _). 1: intuition eauto.
    eapply scoping_subst_sub. 1: eauto.
    apply max_le_r.
Qed.

Lemma scoping_reveal_subst_k :
  ∀ Γ Δ u t ℓ,
    let '(v, σ) := reveal u in
    scoping Γ Level.R u →
    scoping (Δ ++ reveal_scope u ++ Γ) ℓ t →
    scoping (Δ ++ Γ) ℓ (reveal_subst_k σ #|Δ| t).
Proof.
  cbn. fix aux 3. intros Γ Δ u t ℓ hu ht.
  destruct u. all: try assumption.
  - cbn. destruct l.
    + assumption.
    + destruct u1. all: try assumption.
      destruct l. all: try assumption.
      cbn. cbn in ht.
      change (?t{?i := ?u})%s with (subst [u] i t).
      scope_inv hu hs. cbn in hs. destruct hs as [hs1 hs2].
      scope_inv hs1 hs1'.
      eapply subst_scoping.
      2:{
        constructor. 2: constructor.
        eapply scope_sub. 1: eauto.
        apply max_le_r.
      }
      cbn. eapply aux. 1: intuition eauto.
      rewrite <- app_assoc in ht. exact ht.
    + destruct u1. all: try assumption.
      destruct l. all: try assumption.
      cbn. cbn in ht.
      change (?t{?i := ?u})%s with (subst [u] i t).
      scope_inv hu hs. cbn in hs. destruct hs as [hs1 hs2].
      scope_inv hs1 hs1'.
      eapply subst_scoping.
      2:{
        constructor. 2: constructor.
        eapply scope_sub. 1: eauto.
        apply max_le_r.
      }
      cbn. eapply aux. 1: intuition eauto.
      rewrite <- app_assoc in ht. exact ht.
  - cbn. destruct u. all: try assumption.
    scope_inv hu hs. scope_inv hs hs'.
    eapply aux. 1: intuition eauto.
    cbn in ht. auto.
Qed.

Lemma scoping_reveal_subst :
  ∀ Γ u t ℓ,
    let '(v, σ) := reveal u in
    scoping Γ Level.R u →
    scoping (reveal_scope u ++ Γ) ℓ t →
    scoping Γ ℓ (reveal_subst σ t).
Proof.
  cbn. intros Γ u t ℓ hu ht.
  rewrite reveal_subst_0. eapply scoping_reveal_subst_k with (Δ := []).
  all: auto.
Qed.

Lemma skipn_psc :
  ∀ Γ n,
    skipn n (psc Γ) = psc (skipn n Γ).
Proof.
  intros Γ n.
  induction Γ as [| ℓ Γ ih] in n |- *.
  - cbn. rewrite skipn_nil. reflexivity.
  - cbn. destruct n.
    + cbn. reflexivity.
    + cbn. eapply ih.
Qed.