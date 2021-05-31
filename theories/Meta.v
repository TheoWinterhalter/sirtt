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
  eapply erase_cored in hu as hu'. 2: eauto.
  pose proof (sq hu') as hh.
  eapply h2 in hh. 3: reflexivity.
  2:{ eapply scoping_cored. all: eauto. }
  auto.
Qed.

Print Assumptions relative_SN.

(** We also lift non-confusion *)

Definition MLTT_NoConf :=
  ∀ u v hu hv,
    head u = Some hu →
    head v = Some hv →
    u ≡ v →
    hu = hv.

Definition SIRTT_NoConf :=
  ∀ Γ u v hu hv,
    SIRTT.head u = Some hu →
    SIRTT.head v = Some hv →
    Γ ⊢[ Level.R ] u ≡ v →
    SIRTT.scoping Γ Level.R u →
    SIRTT.scoping Γ Level.R v →
    hu = hv.

(* TODO MOVE *)
Definition trans_head (h : SIRTT.term_head) : MLTT.term_head :=
  match h with
  | SIRTT.hvar => MLTT.hvar
  | SIRTT.hlam => MLTT.hlam
  | SIRTT.hprod => MLTT.hprod
  | SIRTT.hzero => MLTT.hzero
  | SIRTT.hsucc => MLTT.hsucc
  | SIRTT.hnat => MLTT.hnat
  | SIRTT.hnil => MLTT.hnil
  | SIRTT.hcons => MLTT.hcons
  | SIRTT.hvec => MLTT.hlist
  | SIRTT.hrefl => MLTT.hrefl
  | SIRTT.heq => MLTT.heq
  | SIRTT.hempty => MLTT.hempty
  | SIRTT.huniv => MLTT.huniv
  end.

Definition trans_head_pinv h :=
  match h with
  | MLTT.hvar => SIRTT.hvar
  | MLTT.hlam => SIRTT.hlam
  | MLTT.hprod => SIRTT.hprod
  | MLTT.hzero => SIRTT.hzero
  | MLTT.hsucc => SIRTT.hsucc
  | MLTT.hnat => SIRTT.hnat
  | MLTT.hnil => SIRTT.hnil
  | MLTT.hcons => SIRTT.hcons
  | MLTT.hlist => SIRTT.hvec
  | MLTT.hrefl => SIRTT.hrefl
  | MLTT.heq => SIRTT.heq
  | MLTT.hempty => SIRTT.hempty
  | MLTT.haxiom => SIRTT.hvar (* Only pseudo inverse here *)
  | MLTT.huniv => SIRTT.huniv
  end.

Lemma trans_head_pinv_cancel :
  ∀ h,
    trans_head_pinv (trans_head h) = h.
Proof.
  intro h. destruct h. all: reflexivity.
Qed.

Lemma trans_head_inj :
  ∀ h₀ h₁,
    trans_head h₀ = trans_head h₁ →
    h₀ = h₁.
Proof.
  intros h₀ h₁ e.
  apply (f_equal trans_head_pinv) in e.
  rewrite !trans_head_pinv_cancel in e.
  assumption.
Qed.

(* TODO MOVE *)
Lemma erasure_head :
  ∀ Γ u hu,
    SIRTT.head u = Some hu →
    MLTT.head (trans Γ u) = Some (trans_head hu).
Proof.
  intros Γ u hu e.
  induction u in Γ, hu, e |- *.
  all: simpl in e. all: noconf e.
  all: try reflexivity.
  - destruct l.
    + noconf e. reflexivity.
    + simpl. eauto.
    + simpl. eauto.
  - destruct l.
    + noconf e. reflexivity.
    + simpl. eauto.
    + simpl. eauto.
  - simpl. eauto.
  - simpl. eauto.
Qed.

Lemma relative_NoConf :
  MLTT_NoConf → SIRTT_NoConf.
Proof.
  intros h Γ u v hu hv eu ev hc hsu hsv.
  eapply erase_conv in hc. 2,3: auto.
  eapply h in hc. 2,3: eapply erasure_head ; eauto.
  apply trans_head_inj in hc.
  assumption.
Qed.