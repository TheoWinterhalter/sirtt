(* Relevance levels *)

From Coq Require Import Utf8.
Require Import Util.

Inductive level :=
| R (* Relevant *)
| S (* Shape-irrelevant *)
| I (* Irrelevant *).

(* Relation of levels *)
Reserved Notation "u ⊏ v" (at level 20).

Inductive more_relevant : level → level → Type :=
| R_S : R ⊏ S
| R_I : R ⊏ I
| S_I : S ⊏ I

where "u ⊏ v" := (more_relevant u v).

Definition potentially_more_relevant := clos_refl more_relevant.
Notation "u ⊑ v" := (potentially_more_relevant u v) (at level 20).