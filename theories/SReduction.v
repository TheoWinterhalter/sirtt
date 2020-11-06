(* Reduction for SIRTT *)

From Coq Require Import Utf8 List.
Require Import Util SAst.

Import ListNotations.

(*
  First we define a notion of "top-level" reduction to reveal relevant terms
  hidden under (shape-)irrelevant operations.

  When computing (shape-)irrelevant β-redexes, we postpone the substitution
  as it doesn't matter for computation.
  It's an important trick to have this operation trivially terminating.
*)

Reserved Notation "u ▹ v | σ" (at level 10).

Inductive topred : term → term → list term → Type :=
| ibeta A t u : app Level.I (lam Level.I A t) u ▹ t | [ u ]
| sbeta A t u : app Level.S (lam Level.S A t) u ▹ t | [ u ]
| wit_ex t p : wit (ex t p) ▹ t | []

where "u ▹ v | σ" := (topred u v σ).

Reserved Notation "u ▹* v | σ" (at level 10).

Inductive topreds : term → term → list term → Type :=
| topred_refl : ∀ u, u ▹* u | []
| topred_step : ∀ u v σ, u ▹ v | σ → u ▹* v | σ
| topred_trans :
    ∀ u v w σ θ,
      u ▹* v | σ →
      v ▹* w | θ →
      u ▹* w | (θ ++ σ)

where "u ▹* v | σ" := (topreds u v σ).