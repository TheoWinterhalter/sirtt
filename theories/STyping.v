(** Typing and conversion in SIRTT

  Conversion is not defined from reduction because reduction only deals with
  relevant terms. We should be able to show however that u ↦ v implies
  that u and v are convertible as relevant terms.
  In fact, because of shape-irrelevant reflection, we need to define conversion
  mutually with typing.
  As such, this file should go away.

  I'm also missing exfalso in the AST, and thus axioms in the target to have
  axiom False.
  More crucially, I'm missing equality it seems.
  I could also be abstract about it, but maybe it's not such a good idea?

  Typing is defined without assumptions on contexts.

  Conversion is not typed, but it could have been.

*)

From Coq Require Import Utf8 List.
Require Import Equations.Prop.DepElim.
Require Import Equations.Prop.Classes.
From Equations Require Import Equations.
Require Import Util Level SAst SSubst SReduction SScoping.

Import ListNotations.

Set Default Goal Selector "!".

Reserved Notation "Γ ⊢[ l ] t : A"
  (at level 20, l, t, A at next level, format "Γ  ⊢[  l  ]  t  :  A").
Reserved Notation "Γ ⊢[ l ] u ≡ v"
  (at level 20, l, u, v at next level, format "Γ  ⊢[  l  ]  u  ≡  v").

Inductive typing (Γ : context) : level → term → term → Type :=
| type_var :
    ∀ n ℓ A,
      nth_error Γ n = Some (ℓ, A) →
      Γ ⊢[ ℓ ] var n : A

(* TODO Other intro rules *)

| type_conv :
    ∀ t A B ℓ s,
      Γ ⊢[ ℓ ] t : A →
      Γ ⊢[ R ] A ≡ B →
      Γ ⊢[ ▪ ℓ ] B : univ s →
      Γ ⊢[ ℓ ] t : B

| type_sub :
    ∀ ℓ ℓ' t A,
      Γ ⊢[ ℓ ] t : A →
      ℓ ⊑ ℓ' →
      Γ ⊢[ ℓ' ] t : A

where "Γ ⊢[ l ] t : A" := (typing Γ l t A) : s_scope

with conversion (Γ : context) : level → term → term → Type :=

(* TODO *)

where "Γ ⊢[ l ] u ≡ v" := (conversion Γ l u v) : s_scope.

(* TODO Is this the right def?? *)
Inductive wf_context : context → Type :=
| wf_nil : wf_context []
| wf_cons :
    ∀ Γ A ℓ s,
      wf_context Γ →
      Γ ⊢[ ▪ ℓ ] A : univ s →
      wf_context ((ℓ, A) :: Γ).

Lemma typed_scoped :
  ∀ Γ ℓ t A,
    Γ ⊢[ ℓ ] t : A →
    scoping Γ ℓ t.
Proof.
  intros Γ ℓ t A h.
  induction h.
  all: try assumption.
  - constructor. unfold context_to_scope. rewrite nth_error_map.
    rewrite e. cbn. reflexivity.
  - eapply scope_sub. all: eauto.
Qed.