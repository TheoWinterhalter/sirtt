(* Typing in SIRTT *)

From Coq Require Import Utf8 List CRelationClasses CMorphisms.
Require Import Util TAst TSubst TReduction TScoping.

Import ListNotations.

Set Default Goal Selector "!".

Definition arrow A B := Prod A (lift0 1 B).
Notation "A ⇒ B" := (arrow A B) (at level 70, right associativity) : t_scope.

Reserved Notation "Σ ;; Γ ⊢ t : A"
  (at level 80, Γ, t, A at next level, format "Σ  ;;  Γ  ⊢  t  :  A").

Reserved Notation "u ≡ v"
  (at level 80, format "u  ≡  v").

Definition conv :=
  clos_refl_sym_trans red.

Notation "u ≡ v" := (conv u v) : t_scope.

(* Σ is a list of axioms *)
Inductive typing (Σ : list term) (Γ : context) : term → term → Type :=
| type_var :
    ∀ n A,
      nth_error Γ n = Some A →
      Σ ;; Γ ⊢ var n : A

| type_lam :
    ∀ A B t s,
      Σ ;; Γ ⊢ A : univ s →
      Σ ;; A ::  Γ ⊢ t : B →
      Σ ;; Γ ⊢ lam A t : Prod A B

| type_app :
    ∀ A B u v,
      Σ ;; Γ ⊢ u : Prod A B →
      Σ ;; Γ ⊢ v : A →
      Σ ;; Γ ⊢ app u v : B{ 0 := v }

| type_Prod :
    ∀ A B i j,
      Σ ;; Γ ⊢ A : univ i →
      Σ ;; A :: Γ ⊢ B : univ j →
      Σ ;; Γ ⊢ Prod A B : univ (max i j)

| type_zero :
    Σ ;; Γ ⊢ zero : Nat

| type_succ :
    ∀ n,
      Σ ;; Γ ⊢ n : Nat →
      Σ ;; Γ ⊢ succ n : Nat

| type_elim_nat :
    ∀ P z s n i,
      Σ ;; Γ ⊢ P : Nat ⇒ univ i →
      Σ ;; Γ ⊢ z : app P zero →
      Σ ;; Γ ⊢ s :
        Prod Nat
          (app (lift0 1 P) (var 0) ⇒ app (lift0 1 P) (succ (var 0))) →
      Σ ;; Γ ⊢ n : Nat →
      Σ ;; Γ ⊢ elim_nat P z s n : app P n

| type_Nat :
    ∀ i,
      Σ ;; Γ ⊢ Nat : univ i

| type_lnil :
    ∀ A i,
      Σ ;; Γ ⊢ A : univ i →
      Σ ;; Γ ⊢ lnil A : List A

| type_lcons :
    ∀ A a l i,
      Σ ;; Γ ⊢ A : univ i →
      Σ ;; Γ ⊢ a : A →
      Σ ;; Γ ⊢ l : List A →
      Σ ;; Γ ⊢ lcons A a l : List A

| type_elim_list :
    ∀ A P e c l i j,
      Σ ;; Γ ⊢ A : univ i →
      Σ ;; Γ ⊢ P : List A ⇒ univ j →
      Σ ;; Γ ⊢ e : app P (lnil A) →
      Σ ;; Γ ⊢ c :
        Prod A (
          Prod (List (lift0 1 A)) (
            app (lift0 2 P) (var 0) ⇒
            app (lift0 2 P) (lcons (lift0 2 A) (var 1) (var 0))
          )
        ) →
      Σ ;; Γ ⊢ l : List A →
      Σ ;; Γ ⊢ elim_list A P e c l : app P l

| type_List :
    ∀ A i,
      Σ ;; Γ ⊢ A : univ i →
      Σ ;; Γ ⊢ List A : univ i

| type_refl :
    ∀ A u i,
      Σ ;; Γ ⊢ A : univ i →
      Σ ;; Γ ⊢ u : A →
      Σ ;; Γ ⊢ refl A u : Eq A u u

| type_coe :
    ∀ A P u v e t i j,
      Σ ;; Γ ⊢ A : univ i →
      Σ ;; Γ ⊢ P : A ⇒ univ j →
      Σ ;; Γ ⊢ u : A →
      Σ ;; Γ ⊢ v : A →
      Σ ;; Γ ⊢ e : Eq A u v →
      Σ ;; Γ ⊢ t : app P u →
      Σ ;; Γ ⊢ coe A P u v e t : app P v

| type_Eq :
    ∀ A u v i,
      Σ ;; Γ ⊢ A : univ i →
      Σ ;; Γ ⊢ u : A →
      Σ ;; Γ ⊢ v : A →
      Σ ;; Γ ⊢ Eq A u v : univ i

| type_exfalso :
    ∀ A p i,
      Σ ;; Γ ⊢ A : univ i →
      Σ ;; Γ ⊢ p : Empty →
      Σ ;; Γ ⊢ exfalso A p : A

| type_Empty :
    ∀ i,
      Σ ;; Γ ⊢ Empty : univ i

| type_axiom :
    ∀ n A,
      nth_error Σ n = Some A →
      Σ ;; Γ ⊢ axiom n : A

| type_univ :
    ∀ i j,
      i < j →
      Σ ;; Γ ⊢ univ i : univ j

| type_conv :
    ∀ t A B s,
      Σ ;; Γ ⊢ t : A →
      A ≡ B →
      Σ ;; Γ ⊢ B : univ s →
      Σ ;; Γ ⊢ t : B

where "Σ ;; Γ ⊢ t : A" := (typing Σ Γ t A) : t_scope.

Inductive wf_context Σ : context → Type :=
| wf_nil : wf_context Σ []
| wf_cons :
    ∀ Γ A s,
      wf_context Σ Γ →
      Σ ;; Γ ⊢ A : univ s →
      wf_context Σ (A :: Γ).

Lemma typed_scoped :
  ∀ Σ Γ t A,
    Σ ;; Γ ⊢ t : A →
    scoping Γ t.
Proof.
  intros Σ Γ t A h.
  induction h.
  all: try assumption.
  all: try solve [ constructor ; eauto ].
  constructor. eapply nth_error_Some_length in e. auto.
Qed.

(* Showing conversion is a congruence, some bits might move to TReduction *)

(* TODO MOVE to Util *)
(* clos_refl_sym_trans preserves congruences / morphisms *)
(* Instance clos_refl_sym_trans_preserves_Proper'
  (A B : Type) R R' (f : A → B) (p : Proper (R ==> R') f) :
  Proper (R ==> clos_refl_sym_trans R') f.
Proof.
  intros x y h. apply rst_step. eapply p. auto.
Qed. *)

(* clos_refl_sym_trans preserves congruences / morphisms *)
Instance clos_refl_sym_trans_preserves_Proper2
  (A B : Type) R R' (f : A → B) (p : Proper (R ==> R') f)
  `{@Reflexive B R'} `{@Symmetric B R'} `{@Transitive B R'} :
  Proper (clos_refl_sym_trans R ==> R') f.
Proof.
  intros x y h.
  induction h.
  - eapply p. auto.
  - reflexivity.
  - symmetry. auto.
  - etransitivity. all: eauto.
Qed.

Instance relfexive_arrow (A B : Type) (R : crelation A) (R' : crelation B)
  `{@Reflexive B R'} :
  Reflexive (R ==> R')%signature.
Proof.
  intros f x y h.
Abort.

Lemma prove_clos_refl_sym_trans :
  ∀ A B (R : crelation A) (R' : crelation B)
    `{@Reflexive B R'} `{@Symmetric B R'} `{@Transitive B R'} x y f,
    clos_refl_sym_trans R x y →
    (∀ x y, R x y → R' (f x) (f y)) →
    R' (f x) (f y).
Proof.
  intros A B R R' ? ? ? x y f h hp.
  induction h.
  - eapply hp. auto.
  - reflexivity.
  - symmetry. eapply IHh.
  - etransitivity. all: eauto.
Qed.

Instance conv_lam_proper :
  Proper (conv ==> conv ==> conv) lam.
Proof.
  (* eapply clos_refl_sym_trans_preserves_Proper2. *)
  intros A A' hA t t' ht.
  (* eapply prove_clos_refl_sym_trans in hA. *)
  (* eapply clos_refl_sym_trans_preserves_Proper. *)
  (* It seems I'll have to it by hand, sadly.
    Probably with a tactic that does the above...
  *)
Abort.