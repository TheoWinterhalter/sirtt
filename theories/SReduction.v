(* Reduction for SIRTT *)

From Coq Require Import Utf8 List.
Require Import Util SAst.

Import ListNotations.

Set Default Goal Selector "!".

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

(* We can actually define normalisation for top-level reduction easily *)
Fixpoint topnorm_acc (u : term) (σ : list term) : term × list term :=
  match u with
  | app Level.I (lam Level.I A t) u => topnorm_acc t (u :: σ)
  | app Level.S (lam Level.S A t) u => topnorm_acc t (u :: σ)
  | wit (ex t p) => topnorm_acc t σ
  | _ => (u, σ)
  end.

Definition topnorm u := topnorm_acc u [].

Lemma topnorm_acc_sound :
  ∀ u σ v θ,
    topnorm_acc u σ = (v, θ) →
    ∑ τ, u ▹* v | τ × θ = τ ++ σ.
Proof.
  intros u σ v θ e.
  induction u in v, σ, θ, e |- *.
  all: try solve [
    simpl in e ; inversion e ; subst ;
    exists [] ; intuition constructor
  ].
  (* - lazymatch type of e with
    | topnorm_acc (app ?x ?y ?z)  _= _ =>
      rename x into l, y into v1, z into v2
    end.
    clear IHv1 IHv2.
    induction v1 in l, v2, σ, w, θ, e, u, h |- *.
    all: try solve [
      simpl in e ; destruct l ; inversion e ; subst ; assumption
    ].
    lazymatch type of e with
    | topnorm_acc (app _ (lam ?a ?b ?c) _)  _= _ =>
      rename a into l', b into A, c into t
    end.
    destruct l.
    1:{ simpl in e. inversion e. subst. assumption. }
    + destruct l'.
      1,3: simpl in e ; inversion e ; subst ; assumption.
      (* eapply IHv1_2. 1: eassumption. *) *)
Abort.