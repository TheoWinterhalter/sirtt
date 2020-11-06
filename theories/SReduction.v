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
  fix aux 1.
  intros u σ v θ e.
  destruct u.
  all: try solve [
    simpl in e ; inversion e ; subst ;
    exists [] ; intuition constructor
  ].
  - lazymatch type of e with
    | topnorm_acc (app ?x ?y ?z)  _= _ =>
      rename x into l, y into f, z into u
    end.
    destruct f.
    all: try solve [
      simpl in e ; destruct l ; inversion e ; subst ;
      exists [] ; intuition constructor
    ].
    lazymatch type of e with
    | topnorm_acc (app _ (lam ?a ?b ?c) _)  _= _ =>
      rename a into l', b into A, c into t
    end.
    destruct l.
    1:{
      simpl in e. inversion e. subst.
      exists []. intuition constructor.
    }
    + destruct l'.
      1,3: simpl in e ; inversion e ; subst ; exists [] ; intuition constructor.
      cbn in e. apply aux in e.
      destruct e as [τ [h e]]. subst.
      eexists. split.
      * eapply topred_trans. 2: eassumption.
        constructor. constructor.
      * rewrite <- app_assoc. cbn. reflexivity.
    + destruct l'.
      1,2: simpl in e ; inversion e ; subst ; exists [] ; intuition constructor.
      cbn in e. apply aux in e.
      destruct e as [τ [h e]]. subst.
      eexists. split.
      * eapply topred_trans. 2: eassumption.
        constructor. constructor.
      * rewrite <- app_assoc. cbn. reflexivity.
  - destruct u.
    all: try solve [
      simpl in e ; inversion e ; subst ;
      exists [] ; intuition constructor
    ].
    cbn in e. apply aux in e.
    destruct e as [τ [h e]]. subst.
    eexists. split.
    + eapply topred_trans. 2: eassumption.
      constructor. constructor.
    + rewrite <- app_assoc. cbn. reflexivity.
Qed.

Corollary topnorm_sound :
  ∀ u v σ,
    topnorm u = (v, σ) →
    u ▹* v | σ.
Proof.
  intros u v σ e.
  unfold topnorm in e.
  apply topnorm_acc_sound in e.
  destruct e as [τ [h e]].
  rewrite app_nil_r in e. subst.
  assumption.
Qed.

(* We can now define proper reduction ↦ *)

Reserved Notation "u ↦ v" (at level 10).

(* TODO Define substitution first *)
(* Inductive red : term → term :=
(* Computation rules *)
| beta :
    ∀ v u,
      v ▹* lam Level.R A t | σ →
      app Level.R v u ↦ subs (subs t σ) [u] *)