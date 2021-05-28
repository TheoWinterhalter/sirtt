(** Meta-theoretical consequences of the erasure *)

From Coq Require Import Utf8 List Nat Lia.
Require Import Equations.Prop.DepElim.
Require Import Equations.Prop.Classes.
From Equations Require Import Equations.
Require Import Util SIRTT MLTT Erasure.
Import ListNotations.

Set Default Goal Selector "!".

(** We lift termination of MLTT to SIRTT *)

Definition MLTT_SN :=
  ∀ Σ Γ t A,
    Σ ;; Γ ⊢ t : A →
    Acc MLTT.scored t.

Definition SIRTT_SN :=
  ∀ Γ t A,
    scoping_context Γ → (* TODO Need scoping above? Maybe would make more sense to ask wf? *)
    Γ ⊢[ Level.R ] t : A →
    Acc SIRTT.scored t.

(* TODO MOVE *)
Lemma erase_cored :
  ∀ Γ u v,
    SIRTT.scoping Γ Level.R u →
    SIRTT.cored v u →
    MLTT.cored (trans Γ v) (trans Γ u).
Proof.
  intros Γ u v hu h.
  induction h.
  - left. eapply erase_red. all: eauto.
  - eapply MLTT.cored_trans.
    + eauto.
    + eapply erase_red. 2: auto.
      (* TODO NEED lemma, maybe in some SSR *)
Admitted.

Lemma relative_SN :
  MLTT_SN → SIRTT_SN.
Proof.
  intros h. intros Γ t A hΓ ht.
  eapply erase_typing in ht as ht'. 2: auto.
  eapply h in ht'.
  eapply SIRTT.typed_scoped in ht.
  remember (trans Γ t) as u eqn:e.
  induction ht' as [? h1 h2] in Γ, t, e, ht |- *. subst.
  constructor. intros u [hu].
  eapply erase_cored in hu. 2: eauto.
  pose proof (sq hu) as hh.
  eapply h2 in hh. 3: reflexivity.
  2: admit.
  auto.
Admitted.

(* Also noconf, maybe with a head construct in MLTT and shape construct in SIRTT? *)