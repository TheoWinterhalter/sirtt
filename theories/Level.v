(* Relevance levels *)

From Coq Require Import Utf8 CRelationClasses.
Require Import Util.

Set Default Goal Selector "!".

Inductive level :=
| R (* Relevant *)
| S (* Shape-irrelevant *)
| I (* Irrelevant *).

Definition relevant l :=
  match l with
  | R => true
  | _ => false
  end.

(* Relation of levels *)
Reserved Notation "u ⊏ v" (at level 20).

Inductive more_relevant : level → level → Type :=
| R_S : R ⊏ S
| R_I : R ⊏ I
| S_I : S ⊏ I

where "u ⊏ v" := (more_relevant u v).

Instance more_relevant_trans :
  Transitive more_relevant.
Proof.
  intros u v w h1 h2.
  destruct h1.
  - inversion h2. constructor.
  - inversion h2.
  - inversion h2.
Qed.

Definition potentially_more_relevant := clos_refl more_relevant.
Notation "u ⊑ v" := (potentially_more_relevant u v) (at level 20).

Instance potentially_more_relevant_refl :
  Reflexive potentially_more_relevant.
Proof.
  intro u.
  eapply r_refl.
Qed.

Instance potentially_more_relevant_trans :
  Transitive potentially_more_relevant.
Proof.
  eapply clos_refl_preserve_trans.
  (* Why doesn't it get inferred? *)
  exact more_relevant_trans.
Qed.

Lemma I_sub :
  ∀ ℓ,
    I ⊑ ℓ →
    ℓ = I.
Proof.
  intros ℓ h.
  destruct h as [ℓ h|].
  - inversion h.
  - reflexivity.
Qed.

(* The idea is that when binding an irrelevant term, the binder can appear
  in the type in shape-irrelevant positions.
  It doesn't work for going from shape-irrelevant to relevant however.
  As such it doesn't really deserve to be called a predecessor but it's not
  clear what the right notion is.
*)
Definition pred ℓ :=
  match ℓ with
  | R => R
  | S => S
  | I => S
  end.

Notation "▪ l" := (pred l) (at level 0).

Definition max u v :=
  match u, v with
  | R, v => v
  | S, R => S
  | S, v => v
  | I, v => I
  end.

Notation "u ⊔ v" := (max u v) (at level 19).

Lemma max_sym :
  ∀ u v,
    max u v = max v u.
Proof.
  intros u v.
  destruct u, v. all: reflexivity.
Qed.

Lemma max_le_l :
  ∀ u v,
    u ⊑ u ⊔ v.
Proof.
  intros u v.
  destruct u, v. all: simpl.
  all: try (left ; constructor).
  all: try (right ; constructor).
Qed.

Lemma max_le_r :
  ∀ u v,
    v ⊑ u ⊔ v.
Proof.
  intros u v.
  destruct u, v. all: simpl.
  all: try (left ; constructor).
  all: try (right ; constructor).
Qed.

Lemma max_le_cong_l :
  ∀ ℓ₀ ℓ₁ ℓ₂,
    ℓ₀ ⊑ ℓ₁ →
    ℓ₀ ⊔ ℓ₂ ⊑ ℓ₁ ⊔ ℓ₂.
Proof.
  intros u v w h.
  destruct h as [v h |].
  - destruct h, w. all: cbn.
    all: try right.
    all: left ; constructor.
  - right.
Qed.

Lemma max_l_R :
  ∀ ℓ, ℓ ⊔ R = ℓ.
Proof.
  intro ℓ.
  destruct ℓ. all: reflexivity.
Qed.

Lemma relevant_pred :
  ∀ ℓ,
    relevant (▪ ℓ) = relevant ℓ.
Proof.
  intros []. all: reflexivity.
Qed.

Lemma pred_idemp :
  ∀ ℓ,
    ▪ (▪ ℓ) = ▪ ℓ.
Proof.
  intro ℓ. destruct ℓ. all: reflexivity.
Qed.

Lemma potentially_more_R :
  ∀ ℓ,
    ℓ ⊑ R →
    ℓ = R.
Proof.
  intros ℓ h. inversion h.
  - inversion H.
  - reflexivity.
Qed.

Lemma pred_le :
  ∀ ℓ,
    ▪ ℓ ⊑ ℓ.
Proof.
  intro ℓ. destruct ℓ. all: cbn.
  - right.
  - right.
  - left. constructor.
Qed.

Lemma pred_pred_le :
  ∀ ℓ ℓ',
    ℓ ⊑ ℓ' →
    ▪ ℓ ⊑ ▪ ℓ'.
Proof.
  intros ℓ ℓ' h.
  destruct h as [ℓ' h|].
  - destruct h. all: cbn.
    + left. constructor.
    + left. constructor.
    + right.
  - right.
Qed.

Lemma max_pred :
  ∀ ℓ₀ ℓ₁,
    (▪ ℓ₀) ⊔ (▪ ℓ₁) = ▪ (ℓ₀ ⊔ ℓ₁).
Proof.
  intros ℓ₀ ℓ₁.
  destruct ℓ₀, ℓ₁. all: reflexivity.
Qed.