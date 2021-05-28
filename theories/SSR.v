(* Subject reduction for SIRTT *)

From Coq Require Import Utf8 List Nat Lia.
Require Import Equations.Prop.DepElim.
Require Import Equations.Prop.Classes.
From Equations Require Import Equations.
Require Import Util Level SAst SSubst SReduction SScoping STyping.
Import ListNotations.

Set Default Goal Selector "!".

Lemma scoping_red :
  ∀ Γ u v,
    scoping Γ Level.R u →
    u ↦ v →
    scoping Γ Level.R v.
Proof.
  intros Γ u v hs hr.
  induction hr.
  all: try solve [
    scope_inv hs hs' ; constructor ; intuition eauto
  ].
  - (* NEED the subst_scoping and so on, so first clean Erasure. *)
    admit.
  - (* NEED reveal_scope_sound *)
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - scope_inv hs hs'. constructor. 2: intuition eauto.
    (* NEED scoping_psc *)
    (* TODO Add to all try *)
    admit.
Abort.