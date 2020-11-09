(* Relevance levels *)

From Coq Require Import Utf8.
Require Import Util.

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

Definition potentially_more_relevant := clos_refl more_relevant.
Notation "u ⊑ v" := (potentially_more_relevant u v) (at level 20).

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