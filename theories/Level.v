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

Instance potentially_more_relevant_trans :
  Transitive potentially_more_relevant.
Proof.
  eapply clos_refl_preserve_trans.
  (* Why doesn't it get inferred? *)
  exact more_relevant_trans.
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