(* Erasure translation from SIRTT to MLTT *)

From Coq Require Import Utf8 List Nat Lia.
Require Import Equations.Prop.DepElim.
Require Import Equations.Prop.Classes.
From Equations Require Import Equations.
Require Import Util SIRTT MLTT.
Import ListNotations.

Set Default Goal Selector "!".

Definition dummy : MLTT.term := MLTT.var 0.

Definition scope_trans Γ :=
  filter Level.relevant Γ.

(* Because the context of the translated term is not the same
  we need to track which variables are removed, hence the need for a scope
  for the term.

  Important note: exfalso is not erased to exfalso because in SIRTT, exfalso
  serves as way to build relevant terms out of an irrelevant proof of
  contradiction, as such erasure will forget the proof information.
  Instead we erase it to an axiom corresponding to Empty in the target.
  Erasure is thus not a way of obtaining consistency.
*)
Fixpoint trans (Γ : SIRTT.scope) (t : SIRTT.term) : MLTT.term :=
  match t with
  | SIRTT.var i => MLTT.var #| scope_trans (firstn i Γ) |
  | SIRTT.lam Level.R A t => MLTT.lam (trans Γ A) (trans (Level.R :: Γ) t)
  | SIRTT.lam l _ t => trans (l :: Γ) t
  | SIRTT.app Level.R u v => MLTT.app (trans Γ u) (trans Γ v)
  | SIRTT.app _ u _ => trans Γ u
  | SIRTT.Prod Level.R A B => MLTT.Prod (trans Γ A) (trans (Level.R :: Γ) B)
  | SIRTT.Prod l _ B => trans (Level.pred l :: Γ) B
  | SIRTT.ex u p => trans Γ u
  | SIRTT.wit t => trans Γ t
  | SIRTT.prf t => dummy
  | SIRTT.Sum A P => trans Γ A
  | SIRTT.zero => MLTT.zero
  | SIRTT.succ t => MLTT.succ (trans Γ t)
  | SIRTT.elim_nat P z s t =>
    MLTT.elim_nat (trans Γ P) (trans Γ z) (trans Γ s) (trans Γ t)
  | SIRTT.Nat => MLTT.Nat
  | SIRTT.vnil A => MLTT.lnil (trans Γ A)
  | SIRTT.vcons A a m v => MLTT.lcons (trans Γ A) (trans Γ a) (trans Γ v)
  | SIRTT.elim_vec A P e c m v =>
    MLTT.elim_list (trans Γ A) (trans Γ P) (trans Γ e) (trans Γ c) (trans Γ v)
  | SIRTT.Vec A m => MLTT.List (trans Γ A)
  | SIRTT.refl A u => MLTT.refl (trans Γ A) (trans Γ u)
  | SIRTT.coe A P u v e t =>
    MLTT.coe
      (trans Γ A) (trans Γ P) (trans Γ u) (trans Γ v) (trans Γ e) (trans Γ t)
  | SIRTT.Eq A u v => MLTT.Eq (trans Γ A) (trans Γ u) (trans Γ v)
  | SIRTT.exfalso A p => MLTT.axiom 0
  | SIRTT.Empty => MLTT.Empty
  | SIRTT.univ s => MLTT.univ s
  end.

(* Some properties about the translation itself *)

Lemma scope_trans_app :
  ∀ Γ Δ,
    scope_trans (Γ ++ Δ) = scope_trans Γ ++ scope_trans Δ.
Proof.
  intros Γ Δ.
  unfold scope_trans. apply filter_app.
Qed.

Lemma scope_trans_length :
  ∀ Γ,
    #| scope_trans Γ | ≤ #|Γ|.
Proof.
  intros Γ. apply filter_length.
Qed.

Lemma scope_trans_firstn_length :
  ∀ Ξ n,
    #| scope_trans (firstn n Ξ) | ≤ #| scope_trans Ξ |.
Proof.
  intros Ξ n.
  apply filter_firstn_length.
Qed.

(* TODO MOVE *)
Lemma relevant_pred :
  ∀ ℓ,
    Level.relevant (Level.pred ℓ) = Level.relevant ℓ.
Proof.
  intros []. all: reflexivity.
Qed.

Lemma scope_trans_psc :
  ∀ Γ,
    scope_trans (psc Γ) = scope_trans Γ.
Proof.
  intro Γ. induction Γ as [| [] Γ ih].
  all: cbn. all: eauto.
  f_equal. eapply ih.
Qed.

Lemma firstn_psc :
  ∀ Γ n,
    firstn n (psc Γ) = psc (firstn n Γ).
Proof.
  intros Γ n.
  induction Γ as [| ℓ Γ ih] in n |- *.
  - cbn. rewrite firstn_nil. reflexivity.
  - cbn. destruct n.
    + cbn. reflexivity.
    + cbn. f_equal. eapply ih.
Qed.

Lemma trans_upto :
  ∀ Γ Δ t,
    psc Γ = psc Δ →
    trans Γ t = trans Δ t.
Proof.
  intros Γ Δ t h.
  induction t in Γ, Δ, h |- *.
  all: try reflexivity.
  all: try solve [ cbn ; eauto ].
  all: try solve [ cbn ; f_equal ; eauto ].
  - cbn. rewrite <- scope_trans_psc. rewrite <- firstn_psc. rewrite h.
    rewrite firstn_psc. rewrite scope_trans_psc. reflexivity.
  - cbn. destruct l.
    + f_equal. 1: eauto.
      eapply IHt2. cbn. f_equal. auto.
    + eapply IHt2. cbn. f_equal. auto.
    + eapply IHt2. cbn. f_equal. auto.
  - cbn. destruct l. 2-3: eauto.
    f_equal. all: eauto.
  - cbn. destruct l.
    + f_equal. 1: eauto.
      eapply IHt2. cbn. f_equal. auto.
    + eapply IHt2. cbn. f_equal. auto.
    + eapply IHt2. cbn. f_equal. auto.
Qed.

(* TODO MOVE *)
Lemma pred_idemp :
  ∀ ℓ,
    Level.pred (Level.pred ℓ) = Level.pred ℓ.
Proof.
  intro ℓ. destruct ℓ. all: reflexivity.
Qed.

(* TODO MOVE *)
Lemma psc_idemp :
  ∀ Γ,
    psc (psc Γ) = psc Γ.
Proof.
  induction Γ as [| ℓ Γ ih].
  - reflexivity.
  - cbn. rewrite pred_idemp. f_equal. auto.
Qed.

Lemma trans_psc :
  ∀ Γ t,
    trans (psc Γ) t = trans Γ t.
Proof.
  intros Γ t.
  eapply trans_upto.
  apply psc_idemp.
Qed.

Set Equations With UIP.

Lemma erase_scoping :
  ∀ Γ t,
    SIRTT.scoping Γ Level.R t →
    MLTT.scoping #|scope_trans Γ| (trans Γ t).
Proof.
  intros Γ t h.
  dependent induction h.
  all: try solve [
    cbn ; auto ; constructor ; auto
  ].
  all: try solve [
    destruct ℓ' ;
    cbn ; auto ; constructor ; auto
  ].
  all: try solve [
    cbn ; auto ; constructor ; auto ;
    rewrite <- scope_trans_psc ; rewrite <- trans_psc ; auto
  ].
  all: try solve [
    destruct ℓ' ;
    cbn ; auto ; constructor ; auto ;
    rewrite <- scope_trans_psc ; rewrite <- trans_psc ; auto
  ].
  - constructor.
    apply nth_error_Some_split in e as h.
    rewrite h. rewrite firstn_app. rewrite firstn_firstn.
    replace (min n n) with n by lia.
    apply nth_error_Some_length in e.
    rewrite 2!scope_trans_app. rewrite 2!app_length.
    match goal with
    | |- ?x + ?y < ?x + ?z =>
      cut (y < z)
    end.
    1:{ intro. lia. }
    rewrite firstn_length. replace (n - min n #|Γ|) with 0 by lia.
    rewrite firstn_O. cbn. lia.
  - destruct ℓ.
    2:{ inversion p. subst. inversion H. }
    2:{ inversion p. subst. inversion H. }
    eapply IHh. reflexivity.
Qed.

(* TODO MOVE? *)
Lemma psc_app :
  ∀ Γ Δ,
    psc (Γ ++ Δ) = psc Γ ++ psc Δ.
Proof.
  intros Γ Δ.
  induction Γ in Δ |- *.
  - reflexivity.
  - cbn. f_equal. eapply IHΓ.
Qed.

(* TODO MOVE? *)
Lemma psc_length :
  ∀ Γ,
    #| psc Γ | = #| Γ |.
Proof.
  intros Γ. induction Γ.
  - reflexivity.
  - cbn. eauto.
Qed.

(* TODO MOVE *)
Lemma potentially_more_R :
  ∀ ℓ,
    Level.potentially_more_relevant ℓ Level.R →
    ℓ = Level.R.
Proof.
  intros ℓ h. inversion h.
  - inversion H.
  - reflexivity.
Qed.

#[local] Ltac erase_lift_ih :=
  lazymatch goal with
  | h : ∀ Γ Δ Ξ, SIRTT.scoping _ _ ?t → _ |-
    context [ trans (?Ξ ++ ?Δ ++ ?Γ) (SIRTT.lift _ _ ?t) ] =>
    first [
      rewrite h by intuition eauto ; clear h
    | specialize (h (psc Γ) (psc Δ) (psc Ξ)) ;
      forward h ; [
        rewrite <- psc_app ; intuition eauto
      | rewrite <- !psc_app, !trans_psc in h ;
        rewrite !scope_trans_psc, !psc_length in h ;
        rewrite h ; clear h
      ]
    ]
  | h : ∀ Γ Δ Ξ, SIRTT.scoping _ _ ?t → _ |-
    context [ trans (?ℓ :: ?Ξ ++ ?Δ ++ ?Γ) (SIRTT.lift _ _ ?t) ] =>
    first [
      specialize (h Γ Δ (ℓ :: Ξ)) ;
      forward h ; [
        intuition eauto
      | cbn in h ; rewrite h ; clear h
      ]
    | specialize (h (psc Γ) (psc Δ) (psc (ℓ :: Ξ))) ;
      forward h ; [
        rewrite <- psc_app ; intuition eauto
      | rewrite <- !psc_app, !trans_psc in h ;
        rewrite !scope_trans_psc, !psc_length in h ;
        rewrite h ; clear h
      ]
    ]
  end.

Lemma erase_lift :
  ∀ Γ Δ Ξ t,
    SIRTT.scoping (Ξ ++ Γ) Level.R t →
    trans (Ξ ++ Δ ++ Γ) (SIRTT.lift #|Δ| #|Ξ| t) =
    MLTT.lift #|scope_trans Δ| #|scope_trans Ξ| (trans (Ξ ++ Γ) t).
Proof.
  intros Γ Δ Ξ t h.
  induction t in Γ, Δ, Ξ, h |- *.
  all: try solve [
    try scope_inv h hs ;
    cbn ; repeat erase_lift_ih ; reflexivity
  ].
  all: try solve [
    try scope_inv h hs ;
    destruct l ;
    cbn ; repeat erase_lift_ih ; reflexivity
  ].
  2:{
    scope_inv h hs. destruct hs as [hs _].
    inversion hs. inversion H.
  }
  scope_inv h hs. destruct hs as [ℓ [hℓ e]].
  eapply potentially_more_R in hℓ. subst.
  cbn. destruct (PeanoNat.Nat.leb_spec #|Ξ| n).
  - rewrite firstn_app. rewrite firstn_all2 by lia.
    rewrite firstn_app. rewrite firstn_all2 by lia.
    replace (#| Δ | + n - #| Ξ | - #| Δ |) with (n - #|Ξ|) by lia.
    rewrite firstn_app. rewrite firstn_all2 with (l := Ξ) by lia.
    rewrite !scope_trans_app. rewrite !app_length.
    lazymatch goal with
    | |- context [ if ?u <=? ?v then _ else _ ] =>
      destruct (PeanoNat.Nat.leb_spec u v)
    end.
    2: lia.
    f_equal. lia.
  - rewrite firstn_app. replace (n - #|Ξ|) with 0 by lia.
    rewrite firstn_O. rewrite app_nil_r.
    rewrite firstn_app. replace (n - #|Ξ|) with 0 by lia.
    rewrite firstn_O. rewrite app_nil_r.
    lazymatch goal with
    | |- context [ if ?u <=? ?v then _ else _ ] =>
      destruct (PeanoNat.Nat.leb_spec u v)
    end.
    1:{
      assert (el : #| scope_trans Ξ | = #| scope_trans (firstn n Ξ) |).
      { pose proof (scope_trans_firstn_length Ξ n). lia. }
      clear H0.
      rewrite nth_error_app1 in e. 2: lia.
      apply nth_error_Some_split in e as h'.
      apply (f_equal scope_trans) in h'.
      rewrite scope_trans_app in h'. cbn - [skipn] in h'.
      rewrite h' in el.
      rewrite app_length in el. cbn - [skipn] in el. lia.
    }
    reflexivity.
Qed.

Corollary erase_lift0 :
  ∀ Γ Δ t,
    SIRTT.scoping Γ Level.R t →
    trans (Δ ++ Γ) (SIRTT.lift0 #|Δ| t) =
    MLTT.lift0 #|scope_trans Δ| (trans Γ t).
Proof.
  intros Γ Δ t h.
  eapply erase_lift with (Ξ := []). auto.
Qed.

Fixpoint trans_subst Γ (Δ : SIRTT.scope) σ :=
  match Δ, σ with
  | Level.R :: Δ, u :: σ =>
    match trans_subst Γ Δ σ with
    | Some θ => Some (trans Γ u :: θ)
    | None => None
    end
  | ℓ :: Δ, u :: σ => trans_subst Γ Δ σ
  | [], [] => Some []
  | _, _ => None
  end.

Lemma trans_subst_length_left :
  ∀ Γ Δ σ θ,
    trans_subst Γ Δ σ = Some θ →
    #|Δ| = #|σ|.
Proof.
  intros Γ Δ σ θ e.
  induction Δ as [| [] Δ ih] in σ, θ, e |- *.
  all: destruct σ ; try discriminate.
  - reflexivity.
  - cbn in e. destruct trans_subst eqn:e1. 2: discriminate.
    inversion e.
    cbn. f_equal. eapply ih. eassumption.
  - cbn in e. cbn. f_equal. eapply ih. eauto.
  - cbn in e. cbn. f_equal. eapply ih. eauto.
Qed.

Lemma trans_subst_length_right :
  ∀ Γ Δ σ θ,
    trans_subst Γ Δ σ = Some θ →
    #|scope_trans Δ| = #|θ|.
Proof.
  intros Γ Δ σ θ e.
  induction Δ as [| [] Δ ih] in σ, θ, e |- *.
  all: destruct σ ; try discriminate.
  - cbn in e. inversion e. reflexivity.
  - cbn in e. destruct trans_subst eqn:e1. 2: discriminate.
    inversion e.
    cbn. f_equal. eapply ih. eassumption.
  - cbn in e. cbn. f_equal. eapply ih. eauto.
  - cbn in e. cbn. f_equal. eapply ih. eauto.
Qed.

Lemma trans_subst_nth_error_R :
  ∀ Γ Δ σ θ n,
    trans_subst Γ Δ σ = Some θ →
    nth_error Δ n = Some Level.R →
    ∑ u,
      nth_error σ n = Some u ×
      nth_error θ #| scope_trans (firstn n Δ) | = Some (trans Γ u).
Proof.
  intros Γ Δ σ θ n hσ hn.
  induction Δ as [| [] Δ ih] in σ, θ, n, hσ, hn |- *.
  all: destruct σ ; try discriminate.
  - destruct n. all: discriminate.
  - cbn in hσ. destruct trans_subst eqn:e1. 2: discriminate.
    inversion hσ. subst. clear hσ.
    destruct n.
    + clear hn. cbn.
      eexists. intuition auto.
    + cbn in hn.
      eapply ih in hn. 2: eauto.
      destruct hn as [u [h1 h2]].
      cbn. eexists. intuition eauto.
  - cbn in hσ. destruct n. 1: discriminate.
    cbn in hn. cbn.
    eapply ih in hn. 2: eauto.
    destruct hn as [u [h1 h2]].
    eexists. intuition eauto.
  - cbn in hσ. destruct n. 1: discriminate.
    cbn in hn. cbn.
    eapply ih in hn. 2: eauto.
    destruct hn as [u [h1 h2]].
    eexists. intuition eauto.
Qed.

Inductive scoping_subst Γ : SIRTT.scope → list SIRTT.term → Type :=
| scoping_subst_cons :
    ∀ ℓ Δ u σ,
      SIRTT.scoping Γ ℓ u →
      scoping_subst Γ Δ σ →
      scoping_subst Γ (ℓ :: Δ) (u :: σ)

| scoping_subst_nil :
    scoping_subst Γ [] [].

Lemma scoping_subst_nth_error :
  ∀ Γ Δ σ n ℓ u,
    scoping_subst Γ Δ σ →
    nth_error Δ n = Some ℓ →
    nth_error σ n = Some u →
    SIRTT.scoping Γ ℓ u.
Proof.
  intros Γ Δ σ n ℓ u h eΔ eσ.
  induction h in n, ℓ, u, eΔ, eσ |- *.
  2:{ destruct n. all: discriminate. }
  destruct n.
  - cbn in eΔ, eσ. inversion eΔ. inversion eσ. subst. clear eΔ eσ.
    auto.
  - cbn in eΔ, eσ. eapply IHh. all: eauto.
Qed.

(* Alternative where we only care about the relevant bits *)
Inductive relevant_scoping_subst Γ : SIRTT.scope → list SIRTT.term → Type :=
| relevant_scoping_subst_nil :
    relevant_scoping_subst Γ [] []
| relevant_scoping_subst_cons :
    ∀ ℓ Δ u σ,
      (ℓ = Level.R → SIRTT.scoping Γ ℓ u) →
      relevant_scoping_subst Γ Δ σ →
      relevant_scoping_subst Γ (ℓ :: Δ) (u :: σ).

Lemma relevant_scoping_subst_nth_error :
  ∀ Γ Δ σ n u,
    relevant_scoping_subst Γ Δ σ →
    nth_error Δ n = Some Level.R →
    nth_error σ n = Some u →
    SIRTT.scoping Γ Level.R u.
Proof.
  intros Γ Δ σ n u h eΔ eσ.
  induction h in n, u, eΔ, eσ |- *.
  1:{ destruct n. all: discriminate. }
  destruct n.
  - cbn in eΔ, eσ. inversion eΔ. inversion eσ. subst. clear eΔ eσ.
    auto.
  - cbn in eΔ, σ. eapply IHh. all: eauto.
Qed.

(* TODO MOVE *)
Lemma pred_le :
  ∀ ℓ,
    Level.potentially_more_relevant (Level.pred ℓ) ℓ.
Proof.
  intro ℓ. destruct ℓ. all: cbn.
  - right.
  - right.
  - left. constructor.
Qed.

(* TODO MOVE *)
Inductive weaker_scope : SIRTT.scope → SIRTT.scope → Type :=
| weaker_nil :
    weaker_scope [] []
| weaker_cons :
    ∀ Γ Δ ℓ ℓ',
      weaker_scope Γ Δ →
      Level.potentially_more_relevant ℓ ℓ' →
      weaker_scope (ℓ :: Γ) (ℓ' :: Δ).

(* TODO MOVE *)
(* Lemma weaker_scope_nth_error :
  ∀ Γ Δ n ℓ,
    nth_error Γ n = Some ℓ →
    weaker_scope Γ Δ →
    ∑ ℓ', nth_error Δ n = Some ℓ' × Level.potentially_more_relevant ℓ ℓ'.
Proof.
  intros Γ Δ n ℓ e h.
  induction h in n, ℓ, e |- *.
  1:{ destruct n. all: discriminate. }
  destruct n.
  - cbn. cbn in e. inversion e. subst. clear e.
    eexists. intuition eauto.
  - cbn. cbn in e. eapply IHh in e. destruct e as [ℓ'' [e hℓ]].
    eexists. intuition eauto.
Qed. *)

Lemma weaker_scope_nth_error :
  ∀ Γ Δ n ℓ,
    nth_error Δ n = Some ℓ →
    weaker_scope Γ Δ →
    ∑ ℓ', nth_error Γ n = Some ℓ' × Level.potentially_more_relevant ℓ' ℓ.
Proof.
  intros Γ Δ n ℓ e h.
  induction h in n, ℓ, e |- *.
  1:{ destruct n. all: discriminate. }
  destruct n.
  - cbn. cbn in e. inversion e. subst. clear e.
    eexists. intuition eauto.
  - cbn. cbn in e. eapply IHh in e. destruct e as [ℓ'' [e hℓ]].
    eexists. intuition eauto.
Qed.

(* TODO MOVE *)
Lemma pred_pred_le :
  ∀ ℓ ℓ',
    Level.potentially_more_relevant ℓ ℓ' →
    Level.potentially_more_relevant (Level.pred ℓ) (Level.pred ℓ').
Proof.
  intros ℓ ℓ' h.
  destruct h as [ℓ' h|].
  - destruct h. all: cbn.
    + left. constructor.
    + left. constructor.
    + right.
  - right.
Qed.

Lemma weaker_scope_psc :
  ∀ Γ Δ,
    weaker_scope Γ Δ →
    weaker_scope (psc Γ) (psc Δ).
Proof.
  intros Γ Δ h.
  induction h.
  - cbn. constructor.
  - cbn. constructor. 1: auto.
    eapply pred_pred_le. auto.
Qed.

(* TODO MOVE *)
Lemma scoping_weak_level :
  ∀ Γ Δ ℓ t,
    SIRTT.scoping Γ ℓ t →
    weaker_scope Δ Γ →
    SIRTT.scoping Δ ℓ t.
Proof.
  intros Γ Δ ℓ t h hw.
  induction h in Δ, hw |- *.
  all: try solve [ constructor ; eauto ].
  - eapply weaker_scope_nth_error in hw as h. 2: eauto.
    destruct h as [ℓ' [e' hℓ]].
    eapply scope_sub. 2: eauto.
    constructor. auto.
  - constructor.
    + eapply IHh1. eapply weaker_scope_psc. auto.
    + eapply IHh2. constructor. 1: auto.
      right.
  - constructor.
    + eapply IHh1. auto.
    + eapply IHh2. constructor. 1: auto.
      right.
  - constructor. 1: auto.
    eapply IHh2. constructor. 1: auto. right.
  - constructor. all: eauto.
    eapply IHh1. eapply weaker_scope_psc. auto.
  - constructor. eapply IHh. eapply weaker_scope_psc. auto.
  - constructor. all: eauto.
    eapply IHh1. eapply weaker_scope_psc. auto.
  - constructor. all: eauto.
    + eapply IHh1. eapply weaker_scope_psc. auto.
    + eapply IHh2. eapply weaker_scope_psc. auto.
  - constructor. all: eauto.
    eapply IHh1. eapply weaker_scope_psc. auto.
  - constructor. all: eauto.
    + eapply IHh1. eapply weaker_scope_psc. auto.
    + eapply IHh2. eapply weaker_scope_psc. auto.
  - constructor. all: eauto.
    eapply IHh1. eapply weaker_scope_psc. auto.
  - eapply scope_sub. 2: eauto.
    eapply IHh. auto.
Qed.

(* TODO MOVE *)
Lemma weaker_psc :
  ∀ Γ,
    weaker_scope (psc Γ) Γ.
Proof.
  intros Γ. induction Γ as [| ℓ Γ ih].
  - constructor.
  - cbn. constructor.
    + eapply ih.
    + eapply pred_le.
Qed.

(* TODO MOVE *)
Lemma scoping_psc :
  ∀ Γ ℓ t,
    SIRTT.scoping Γ ℓ t →
    SIRTT.scoping (psc Γ) ℓ t.
Proof.
  intros Γ ℓ t h.
  eapply scoping_weak_level.
  - eauto.
  - eapply weaker_psc.
Qed.

Lemma relevant_scoping_subst_psc :
  ∀ Γ Δ σ,
    relevant_scoping_subst Γ Δ σ →
    relevant_scoping_subst (psc Γ) (psc Δ) σ.
Proof.
  intros Γ Δ σ h.
  induction h.
  - cbn. constructor.
  - cbn. constructor. 2: eauto.
    intro e. destruct ℓ. 2-3: discriminate.
    cbn. eapply scoping_psc. eauto.
Qed.

Lemma trans_subst_psc :
  ∀ Γ Δ σ θ,
    trans_subst Γ Δ σ = Some θ →
    trans_subst (psc Γ) (psc Δ) σ = Some θ.
Proof.
  intros Γ Δ σ θ e.
  induction Δ as [| [] Δ ih] in σ, θ, e |- *.
  all: destruct σ ; try discriminate.
  - cbn in e. inversion e. reflexivity.
  - cbn in e. destruct trans_subst eqn:e1. 2: discriminate.
    inversion e. subst. clear e.
    eapply ih in e1 as h.
    cbn. fold (psc Δ). rewrite h.
    rewrite trans_psc. reflexivity.
  - cbn in e. cbn. eapply ih. auto.
  - cbn in e. cbn. eapply ih. auto.
Qed.

Lemma trans_ptm :
  ∀ Γ t,
    trans Γ (ptm t) = trans Γ t.
Proof.
  intros Γ t.
  induction t in Γ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; intuition eauto ].
  all: try solve [ cbn ; f_equal ; intuition eauto ].
  - destruct l.
    + cbn. f_equal. all: intuition eauto.
    + cbn. eauto.
    + cbn. rewrite IHt2. eapply trans_upto. reflexivity.
  - destruct l.
    + cbn. f_equal. all: intuition eauto.
    + cbn. eauto.
    + cbn. eauto.
  - destruct l.
    + cbn. f_equal. all: intuition eauto.
    + cbn. eauto.
    + cbn. eauto.
Qed.

Lemma trans_subst_psub :
  ∀ Γ Δ σ θ,
    trans_subst Γ Δ σ = Some θ →
    trans_subst (psc Γ) (psc Δ) (psub σ) = Some θ.
Proof.
  intros Γ Δ σ θ e.
  induction Δ as [| [] Δ ih] in σ, θ, e |- *.
  all: destruct σ ; try discriminate.
  - cbn in e. inversion e. reflexivity.
  - cbn in e. destruct trans_subst eqn:e1. 2: discriminate.
    inversion e. subst. clear e.
    eapply ih in e1 as h.
    cbn. fold (psc Δ). rewrite h.
    rewrite trans_psc. rewrite trans_ptm. reflexivity.
  - cbn in e. cbn. eapply ih. auto.
  - cbn in e. cbn. eapply ih. auto.
Qed.

(* TODO MOVE *)
Lemma max_pred :
  ∀ ℓ₀ ℓ₁,
    Level.max (Level.pred ℓ₀) (Level.pred ℓ₁) = Level.pred (Level.max ℓ₀ ℓ₁).
Proof.
  intros ℓ₀ ℓ₁.
  destruct ℓ₀, ℓ₁. all: reflexivity.
Qed.

(* TODO MOVE *)
Lemma scoping_ptm :
  ∀ Γ ℓ t,
    SIRTT.scoping Γ ℓ t →
    SIRTT.scoping (psc Γ) (Level.pred ℓ) (ptm t).
Proof.
  intros Γ ℓ t h.
  induction t in Γ, ℓ, h |- *.
  all: try solve [ constructor ; eauto ].
  all: try solve [ scope_inv h hs ; constructor ; intuition eauto ].
  (* all: try solve [
    cbn ; try scope_inv h hs ; constructor ; intuition eauto ;
    eapply IHt2 with (Γ := _ :: _) ; intuition eauto
  ]. *)
  - scope_inv h hs. destruct hs as [ℓ' [hℓ e]].
    eapply scope_sub.
    + constructor. unfold psc. rewrite nth_error_map. rewrite e. cbn.
      reflexivity.
    + eapply pred_pred_le. auto.
  - cbn. scope_inv h hs.
    constructor. 1: intuition eauto.
    eapply IHt2 with (Γ := _ :: _). intuition eauto.
  - cbn. scope_inv h hs.
    constructor. 1: intuition eauto.
    rewrite max_pred. intuition eauto.
  - cbn. scope_inv h hs.
    constructor. 1: intuition eauto.
    eapply IHt2 with (Γ := _ :: _). intuition eauto.
  - cbn. scope_inv h hs. constructor. 1: intuition eauto.
    eapply scoping_psc. intuition eauto.
  - cbn. scope_inv h hs. destruct hs as [hs ?h].
    eapply scope_sub.
    + constructor. eapply scoping_psc. auto.
    + destruct ℓ. all: cbn. 1: auto.
      all: reflexivity.
  - cbn. scope_inv h hs. constructor. 1: intuition eauto.
    destruct hs as [h1 h2].
    eapply IHt2 in h2 as ih. rewrite <- max_pred in ih.
    auto.
  - cbn. scope_inv h hs. constructor. all: try solve [ intuition eauto ].
    eapply scoping_psc. intuition eauto.
  - cbn. scope_inv h hs. constructor. all: try solve [ intuition eauto ].
    eapply scoping_psc. intuition eauto.
  - cbn. scope_inv h hs. constructor. 1: intuition eauto.
    destruct hs as [h1 h2].
    eapply IHt2 in h2 as ih. rewrite <- max_pred in ih.
    auto.
  - cbn. scope_inv h hs. constructor. 1: intuition eauto.
    eapply scoping_psc. intuition eauto.
Qed.

Lemma relevant_scoping_subst_psub :
  ∀ Γ Δ σ,
    relevant_scoping_subst Γ Δ σ →
    relevant_scoping_subst (psc Γ) (psc Δ) (psub σ).
Proof.
  intros Γ Δ σ h.
  induction h.
  - cbn. constructor.
  - cbn. constructor. 2: eauto.
    intro e. destruct ℓ. 2-3: discriminate.
    eapply scoping_ptm. auto.
Qed.

#[local] Ltac erase_subst_ih :=
  lazymatch goal with
  | h : ∀ Γ Δ Ξ σ θ, SIRTT.scoping _ _ ?t → _,
    h' : trans_subst _ ?Δ ?σ = Some ?θ |-
    context [ trans (?Ξ ++ ?Γ) (SIRTT.subst ?σ _ ?t) ] =>
      erewrite h by intuition eauto ; clear h
  | h : ∀ Γ Δ Ξ σ θ, SIRTT.scoping _ _ ?t → _,
    h' : trans_subst _ ?Δ ?σ = Some ?θ |-
    context [ trans (?Ξ ++ ?Γ) (SIRTT.subst (psub ?σ) _ ?t) ] =>
      specialize (h (psc Γ) (psc Δ) (psc Ξ) (psub σ) θ) ;
      forward h ; [ rewrite <- !psc_app ; intuition eauto |] ;
      forward h ; [ eapply relevant_scoping_subst_psub ; auto |] ;
      forward h ; [ eapply trans_subst_psub ; auto |] ;
      rewrite <- !psc_app in h ;
      rewrite !trans_psc, !psc_length, !scope_trans_psc in h ;
      rewrite h ; clear h
  | h : ∀ Γ Δ Ξ σ θ, SIRTT.scoping _ _ ?t → _,
    h' : trans_subst _ ?Δ ?σ = Some ?θ |-
    context [ trans (?ℓ :: ?Ξ ++ ?Γ) (SIRTT.subst ?σ _ ?t) ] =>
      specialize (h Γ Δ (ℓ :: Ξ) σ θ) ;
      forward h ; [ intuition eauto |] ;
      forward h ; [ auto |] ;
      forward h ; [ auto |] ;
      cbn in h ; rewrite h ; clear h
  | h : ∀ Γ Δ Ξ σ θ, SIRTT.scoping _ _ ?t → _,
    h' : trans_subst _ ?Δ ?σ = Some ?θ |-
    context [ trans (?ℓ :: ?Ξ ++ ?Γ) (SIRTT.subst (psub ?σ) _ ?t) ] =>
      specialize (h (psc Γ) (psc Δ) (psc (ℓ :: Ξ)) (psub σ) θ) ;
      forward h ; [ rewrite <- !psc_app ; intuition eauto |] ;
      forward h ; [ eapply relevant_scoping_subst_psub ; auto |] ;
      forward h ; [ eapply trans_subst_psub ; auto |] ;
      rewrite <- !psc_app in h ;
      rewrite !trans_psc, !psc_length, !scope_trans_psc in h ;
      rewrite h ; clear h
  end.

Lemma erase_subst :
  ∀ Γ Δ Ξ σ t θ,
    SIRTT.scoping (Ξ ++ Δ ++ Γ) Level.R t →
    relevant_scoping_subst Γ Δ σ →
    trans_subst Γ Δ σ = Some θ →
    trans (Ξ ++ Γ) (SIRTT.subst σ #|Ξ| t) =
    MLTT.subst θ #|scope_trans Ξ| (trans (Ξ ++ Δ ++ Γ) t).
Proof.
  intros Γ Δ Ξ σ t θ h sσ hσ.
  induction t in Γ, Δ, Ξ, σ, θ, h, sσ, hσ |- *.
  all: try solve [
    try scope_inv h hs ;
    cbn ; repeat erase_subst_ih ; reflexivity
  ].
  all: try solve [
    try scope_inv h hs ;
    destruct l ;
    cbn ; repeat erase_subst_ih ; reflexivity
  ].
  2:{
    scope_inv h hs. destruct hs as [hs _].
    inversion hs. inversion H.
  }
  cbn. scope_inv h hs. clear h. destruct hs as [ℓ [hℓ e]].
  eapply potentially_more_R in hℓ. subst.
  destruct (PeanoNat.Nat.leb_spec #|Ξ| n).
  - rewrite firstn_app. rewrite firstn_all2 by lia.
    rewrite scope_trans_app. rewrite app_length.
    lazymatch goal with
    | |- context [ ?x <=? ?y ] =>
      destruct (PeanoNat.Nat.leb_spec x y)
    end.
    2: lia.
    lazymatch goal with
    | |- context [ ?x + ?y - ?x ] =>
      replace (x + y - x) with y by lia
    end.
    rewrite nth_error_app2 in e. 2: auto.
    destruct (PeanoNat.Nat.ltb_spec (n - #|Ξ|) #|Δ|) as [h|h].
    + rewrite nth_error_app1 in e. 2: auto.
      eapply trans_subst_nth_error_R in hσ as hh. 2: eauto.
      destruct hh as [u [h1 h2]].
      rewrite h1.
      eapply nth_error_Some_length in e as el.
      rewrite firstn_app. replace (n - #|Ξ| - #|Δ|) with 0 by lia.
      rewrite firstn_O. rewrite app_nil_r.
      rewrite h2.
      apply erase_lift0.
      eapply relevant_scoping_subst_nth_error in sσ. all: eauto.
    + rewrite nth_error_app2 in e. 2: auto.
      destruct (nth_error σ _) eqn:e1.
      1:{
        eapply nth_error_Some_length in e1.
        eapply trans_subst_length_left in hσ.
        lia.
      }
      destruct (nth_error θ _) eqn:e2.
      1:{
        eapply nth_error_Some_length in e2.
        eapply trans_subst_length_right in hσ.
        rewrite firstn_app in e2.
        rewrite firstn_all2 in e2. 2: lia.
        rewrite scope_trans_app in e2. rewrite app_length in e2.
        lia.
      }
      cbn. f_equal.
      rewrite firstn_app.
      rewrite firstn_all2.
      2:{ eapply trans_subst_length_left in hσ. lia. }
      rewrite scope_trans_app. rewrite app_length.
      rewrite firstn_app. rewrite scope_trans_app. rewrite app_length.
      rewrite (firstn_all2 Δ). 2: lia.
      replace (n - #|σ| - #|Ξ|) with (n - #|Ξ| - #|Δ|).
      2:{ eapply trans_subst_length_left in hσ. lia. }
      eapply trans_subst_length_right in hσ. lia.
  - rewrite firstn_app. replace (n - #|Ξ|) with 0 by lia.
    rewrite firstn_O. rewrite app_nil_r.
    lazymatch goal with
    | |- context [ if ?u <=? ?v then _ else _ ] =>
      destruct (PeanoNat.Nat.leb_spec u v)
    end.
    1:{
      assert (el : #| scope_trans Ξ | = #| scope_trans (firstn n Ξ) |).
      { pose proof (scope_trans_firstn_length Ξ n). lia. }
      clear H0.
      rewrite nth_error_app1 in e. 2: lia.
      apply nth_error_Some_split in e as h.
      apply (f_equal scope_trans) in h.
      rewrite scope_trans_app in h. cbn - [skipn] in h.
      rewrite h in el.
      rewrite app_length in el. cbn - [skipn] in el. lia.
    }
    cbn. f_equal.
    rewrite firstn_app. replace (n - #|Ξ|) with 0 by lia.
    rewrite firstn_O. rewrite app_nil_r.
    reflexivity.
Qed.

Corollary erase_subst0 :
  ∀ Γ Δ σ t θ,
    SIRTT.scoping (Δ ++ Γ) Level.R t →
    relevant_scoping_subst Γ Δ σ →
    trans_subst Γ Δ σ = Some θ →
    trans Γ (SIRTT.subst0 σ t) =
    MLTT.subst0 θ (trans (Δ ++ Γ) t).
Proof.
  intros Γ Δ σ t θ h sσ hσ.
  eapply erase_subst with (Ξ := []). all: eauto.
Qed.

Corollary erase_subst10_relevant :
  ∀ Γ t u,
    SIRTT.scoping (Level.R :: Γ) Level.R t →
    SIRTT.scoping Γ Level.R u →
    trans Γ (t{ 0 := u })%s =
    (trans (Level.R :: Γ) t){ 0 := trans Γ u }.
Proof.
  intros Γ t u ht hu.
  change (?t{0 := ?u})%s with (SIRTT.subst0 [u] t).
  change (?t{0 := ?u}) with (MLTT.subst0 [u] t).
  erewrite erase_subst0 with (Δ := [ _ ]).
  - reflexivity.
  - cbn. auto.
  - constructor. 2: constructor. auto.
  - cbn. reflexivity.
Qed.

Lemma reveal_scope_sound :
  ∀ Γ ℓ t,
    SIRTT.scoping Γ ℓ t →
    let '(u, σ) := reveal t in
    SIRTT.scoping (reveal_scope t ++ Γ) ℓ u.
Proof.
  fix aux 3.
  intros Γ ℓ t h.
  destruct t. all: try assumption.
  - cbn. destruct l.
    + cbn. assumption.
    + destruct t1. all: try assumption.
      destruct l. all: try assumption.
      scope_inv h hs. destruct hs as [hs _].
      scope_inv hs hs'. destruct hs' as [_ hs'].
      eapply aux in hs'.
      rewrite <- app_assoc. auto.
    + destruct t1. all: try assumption.
      destruct l. all: try assumption.
      scope_inv h hs. destruct hs as [hs _].
      scope_inv hs hs'. destruct hs' as [_ hs'].
      eapply aux in hs'.
      rewrite <- app_assoc. auto.
  - cbn. destruct t. all: try assumption.
    scope_inv h hs. scope_inv hs h'. destruct h' as [h' _].
    eapply aux. auto.
Qed.

Lemma erase_reveal :
  ∀ Γ u,
    let '(v, σ) := reveal u in
    trans Γ u = trans (reveal_scope u ++ Γ) v.
Proof.
  fix aux 2.
  intros Γ u.
  destruct u.
  all: try reflexivity.
  - cbn. destruct l.
    + reflexivity.
    + destruct u1. all: try reflexivity.
      destruct l. all: try reflexivity.
      cbn. rewrite aux. rewrite <- app_assoc. reflexivity.
    + destruct u1. all: try reflexivity.
      destruct l. all: try reflexivity.
      cbn. rewrite aux. rewrite <- app_assoc. reflexivity.
  - cbn. destruct u. all: try reflexivity.
    cbn. apply aux.
Qed.

Lemma scoping_subst_app :
  ∀ Γ Δ Ξ σ θ,
    scoping_subst Γ Δ σ →
    scoping_subst Γ Ξ θ →
    scoping_subst Γ (Δ ++ Ξ) (σ ++ θ).
Proof.
  intros Γ Δ Ξ σ θ h1 h2.
  induction h1 in Ξ, θ, h2 |- *.
  - cbn. constructor. all: eauto.
  - cbn. auto.
Qed.

Lemma trans_subst_app :
  ∀ Γ Δ₀ Δ₁ σ₀ σ₁ θ₀ θ₁,
    trans_subst Γ Δ₀ σ₀ = Some θ₀ →
    trans_subst Γ Δ₁ σ₁ = Some θ₁ →
    trans_subst Γ (Δ₀ ++ Δ₁) (σ₀ ++ σ₁) = Some (θ₀ ++ θ₁).
Proof.
  intros Γ Δ₀ Δ₁ σ₀ σ₁ θ₀ θ₁ h₀ h₁.
  induction Δ₀ as [| [] Δ₀ ih ] in Δ₁, σ₀, σ₁, θ₀, θ₁, h₀, h₁ |- *.
  all: destruct σ₀ ; try discriminate.
  - cbn in h₀. inversion h₀. assumption.
  - cbn in h₀. destruct trans_subst eqn:e. 2: discriminate.
    inversion h₀. subst. clear h₀.
    cbn. erewrite ih. 2,3: eauto.
    reflexivity.
  - cbn in h₀. cbn. eapply ih. all: eauto.
  - cbn in h₀. cbn. eapply ih. all: eauto.
Qed.

Lemma scoping_subst_length :
  ∀ Γ Δ σ,
    scoping_subst Γ Δ σ →
    #|σ| = #|Δ|.
Proof.
  intros Γ Δ σ h.
  induction h. all: cbn ; auto.
Qed.

Lemma lift_scoping :
  ∀ Γ Δ Ξ t ℓ,
    SIRTT.scoping (Ξ ++ Γ) ℓ t →
    SIRTT.scoping (Ξ ++ Δ ++ Γ) ℓ (SIRTT.lift #|Δ| #|Ξ| t).
Proof.
  intros Γ Δ Ξ t ℓ h.
  induction t in Γ, Δ, Ξ, ℓ, h |- *.
  all: try solve [ simpl ; constructor ].
  all: try solve [
    simpl ; scope_inv h hs ; constructor ; intuition eauto
  ].
  all: try solve [
    simpl ; scope_inv h hs ; constructor ; intuition eauto ;
    try lazymatch goal with
    | h : ∀ Γ Δ Ξ ℓ, SIRTT.scoping _ _ ?t → _ |-
      SIRTT.scoping (psc (?Ξ ++ ?Δ ++ ?Γ)) ?ℓ (SIRTT.lift _ _ ?t) =>
      specialize (h (psc Γ) (psc Δ) (psc Ξ) ℓ) ;
      rewrite !psc_app ;
      rewrite !psc_length in h ;
      apply h ;
      rewrite <- !psc_app ;
      intuition eauto
    end ;
    eapply IHt2 with (Ξ := _ :: _) ; intuition eauto
  ].
  - cbn. scope_inv h hs. destruct hs as [ℓ' [hℓ e]].
    destruct (PeanoNat.Nat.leb_spec0 #|Ξ| n) as [h1|h1].
    + eapply scope_sub. 2: eauto.
      constructor.
      rewrite nth_error_app2 in e. 2: auto.
      rewrite nth_error_app2. 2: lia.
      rewrite nth_error_app2. 2: lia.
      rewrite <- e. f_equal. lia.
    + eapply scope_sub. 2: eauto.
      constructor. rewrite nth_error_app1 in e. 2: lia.
      rewrite nth_error_app1. 2: lia.
      auto.
  - simpl. scope_inv h hs. destruct hs as [hℓ ?h].
    eapply scope_sub. 2: eauto.
    constructor. auto.
Qed.

(* TODO MOVE *)
Lemma weaker_scope_refl :
  ∀ Γ,
    weaker_scope Γ Γ.
Proof.
  intro Γ. induction Γ.
  - constructor.
  - constructor. 1: auto.
    reflexivity.
Qed.

Lemma scoping_subst_psub :
  ∀ Γ Δ σ,
    scoping_subst Γ Δ σ →
    scoping_subst (psc Γ) (psc Δ) (psub σ).
Proof.
  intros Γ Δ σ h.
  induction h.
  - cbn. constructor. 2: eauto.
    eapply scoping_ptm. auto.
  - cbn. constructor.
Qed.

#[local] Ltac subst_scoping_ih :=
  lazymatch goal with
  | h : ∀ Γ Δ Ξ ℓ σ, SIRTT.scoping _ _ ?t → _, hσ : scoping_subst _ ?Δ ?σ |-
    SIRTT.scoping (psc (?Ξ ++ ?Γ)) ?ℓ (SIRTT.subst (psub ?σ) _ ?t) =>
    specialize (h (psc Γ) (psc Δ) (psc Ξ) ℓ (psub σ)) ;
    rewrite !psc_app ;
    rewrite !psc_length in h ;
    apply h ; [
      rewrite <- !psc_app ; intuition eauto
    | eapply scoping_subst_psub ; eauto
    ]
  end.

Lemma subst_scoping :
  ∀ Γ Δ Ξ ℓ σ t,
    SIRTT.scoping (Ξ ++ Δ ++ Γ) ℓ t →
    scoping_subst Γ Δ σ →
    SIRTT.scoping (Ξ ++ Γ) ℓ (SIRTT.subst σ #|Ξ| t).
Proof.
  intros Γ Δ Ξ ℓ σ t ht hσ.
  induction t in Γ, Δ, Ξ, ℓ, σ, ht, hσ |- *.
  all: try solve [ simpl ; constructor ].
  all: try solve [
    simpl ; scope_inv ht hs ; constructor ; intuition eauto
  ].
  all: try solve [
    simpl ; scope_inv ht hs ; constructor ; intuition eauto ;
    eapply IHt2 with (Ξ := _ :: _) ; intuition eauto
  ].
  all: try solve [
    simpl ; scope_inv ht hs ; constructor ; intuition eauto ;
    try solve [ eapply IHt2 with (Ξ := _ :: _) ; intuition eauto ] ;
    subst_scoping_ih
  ].
  - cbn. scope_inv ht hs. destruct hs as [ℓ' [hℓ e]].
    destruct (PeanoNat.Nat.leb_spec0 #|Ξ| n) as [h1|h1].
    + rewrite nth_error_app2 in e. 2: auto.
      destruct (nth_error σ _) eqn:e1.
      * eapply lift_scoping with (Ξ := []). cbn.
        eapply nth_error_Some_length in e1 as h2.
        eapply scoping_subst_length in hσ as eσ.
        rewrite nth_error_app1 in e. 2: lia.
        eapply scope_sub. 2: eauto.
        eapply scoping_subst_nth_error. all: eauto.
      * eapply nth_error_None in e1.
        eapply scoping_subst_length in hσ as eσ.
        rewrite nth_error_app2 in e. 2: lia.
        eapply scope_sub. 2: eauto.
        constructor. rewrite nth_error_app2. 2: lia.
        rewrite <- e. f_equal. lia.
    + apply PeanoNat.Nat.nle_gt in h1.
      rewrite nth_error_app1 in e. 2: auto.
      eapply scope_sub. 2: eauto.
      constructor. rewrite nth_error_app1. 2: auto.
      auto.
  - simpl. scope_inv ht hs. destruct hs as [hℓ ?h].
    eapply scope_sub.
    + constructor. intuition eauto.
    + auto.
Qed.

Lemma scoping_reveal_subst_k :
  ∀ Γ Δ u t,
    let '(v, σ) := reveal u in
    SIRTT.scoping Γ Level.R u →
    SIRTT.scoping (Δ ++ reveal_scope u ++ Γ) Level.R t →
    SIRTT.scoping (Δ ++ Γ) Level.R (reveal_subst_k σ #|Δ| t).
Proof.
  cbn. fix aux 3. intros Γ Δ u t hu ht.
  destruct u. all: try assumption.
  - cbn. destruct l.
    + assumption.
    + destruct u1. all: try assumption.
      destruct l. all: try assumption.
      cbn. cbn in ht.
      change (?t{?i := ?u})%s with (SIRTT.subst [u] i t).
      scope_inv hu hs. cbn in hs. destruct hs as [hs1 hs2].
      scope_inv hs1 hs1'.
      eapply subst_scoping.
      2: constructor. 3: constructor. 2: eauto.
      cbn. eapply aux. 1: intuition eauto.
      rewrite <- app_assoc in ht. exact ht.
    + destruct u1. all: try assumption.
      destruct l. all: try assumption.
      cbn. cbn in ht.
      change (?t{?i := ?u})%s with (SIRTT.subst [u] i t).
      scope_inv hu hs. cbn in hs. destruct hs as [hs1 hs2].
      scope_inv hs1 hs1'.
      eapply subst_scoping.
      2: constructor. 3: constructor. 2: eauto.
      cbn. eapply aux. 1: intuition eauto.
      rewrite <- app_assoc in ht. exact ht.
  - cbn. destruct u. all: try assumption.
    scope_inv hu hs. scope_inv hs hs'.
    eapply aux. 1: intuition eauto.
    cbn in ht. auto.
Qed.

Lemma scoping_reveal_subst :
  ∀ Γ u t,
    let '(v, σ) := reveal u in
    SIRTT.scoping Γ Level.R u →
    SIRTT.scoping (reveal_scope u ++ Γ) Level.R t →
    SIRTT.scoping Γ Level.R (reveal_subst σ t).
Proof.
  cbn. intros Γ u t hu ht.
  rewrite reveal_subst_0. eapply scoping_reveal_subst_k with (Δ := []).
  all: auto.
Qed.

Lemma erase_reveal_subst_k :
  ∀ Γ Δ u t,
    SIRTT.scoping (Δ ++ reveal_scope u ++ Γ) Level.R t →
    SIRTT.scoping Γ Level.R u →
    let '(v, σ) := reveal u in
    trans (Δ ++ Γ) (reveal_subst_k σ #|Δ| t) =
    trans (Δ ++ reveal_scope u ++ Γ) t.
Proof.
  cbn. fix aux 3. intros Γ Δ u t ht h.
  destruct u. all: try reflexivity.
  - cbn. destruct l.
    + reflexivity.
    + destruct u1. all: try reflexivity.
      destruct l. all: try reflexivity.
      cbn.
      scope_inv h hs. cbn in hs. destruct hs as [hs ?]. scope_inv hs h'.
      change (?t{?i := ?u})%s with (SIRTT.subst [u] i t).
      erewrite erase_subst.
      * rewrite subst_empty. symmetry. rewrite <- app_assoc. rewrite aux.
        1: reflexivity.
        -- cbn in ht. rewrite <- app_assoc in ht. auto.
        -- cbn. intuition auto.
      * cbn. eapply scoping_reveal_subst_k. 1: intuition eauto.
        cbn in ht. rewrite <- app_assoc in ht. auto.
      * constructor. 2: constructor.
        auto.
      * reflexivity.
    + destruct u1. all: try reflexivity.
      destruct l. all: try reflexivity.
      cbn.
      scope_inv h hs. cbn in hs. destruct hs as [hs ?]. scope_inv hs h'.
      change (?t{?i := ?u})%s with (SIRTT.subst [u] i t).
      erewrite erase_subst.
      * rewrite subst_empty. symmetry. rewrite <- app_assoc. rewrite aux.
        1: reflexivity.
        -- cbn in ht. rewrite <- app_assoc in ht. auto.
        -- cbn. intuition auto.
      * cbn. eapply scoping_reveal_subst_k. 1: intuition eauto.
        cbn in ht. rewrite <- app_assoc in ht. auto.
      * constructor. 2: constructor.
        auto.
      * reflexivity.
  - cbn. destruct u. all: try reflexivity.
    scope_inv h hs. scope_inv hs h'.
    apply aux.
    + cbn in ht. auto.
    + intuition auto.
Qed.

Corollary erase_reveal_subst :
  ∀ Γ u t,
    SIRTT.scoping (reveal_scope u ++ Γ) Level.R t →
    SIRTT.scoping Γ Level.R u →
    let '(v, σ) := reveal u in
    trans Γ (reveal_subst σ t) = trans (reveal_scope u ++ Γ) t.
Proof.
  cbn. intros Γ u t ht h.
  rewrite reveal_subst_0. eapply erase_reveal_subst_k with (Δ := []).
  all: auto.
Qed.

Lemma erase_red :
  ∀ Γ u v,
    SIRTT.scoping Γ Level.R u →
    (u ↦ v)%s →
    ((trans Γ u) ↦ (trans Γ v))%t.
Proof.
  intros Γ u v hs h.
  induction h in Γ, hs |- *.
  all: try solve [
    cbn ; try constructor ; apply IHh ;
    scope_inv hs hs' ; intuition auto
  ].
  all: try solve [
    cbn ; try constructor ; specialize (IHh (psc Γ)) ;
    rewrite !trans_psc in IHh ; apply IHh ;
    scope_inv hs hs' ; intuition auto
  ].
  all: try solve [
    destruct l ;
    cbn ; try constructor ; apply IHh ;
    scope_inv hs hs' ; intuition auto
  ].
  - cbn. rewrite erase_reveal.
    rewrite e. cbn.
    match goal with
    | |- _ ↦ ?rr =>
      let T := type of rr in
      evar (rhs : T) ;
      replace rr with rhs ; subst rhs
    end.
    1: constructor.
    scope_inv hs h'. cbn in h'. destruct h' as [h1 h2].
    erewrite erase_subst10_relevant.
    3: auto.
    2:{
      eapply scoping_reveal_subst_k with (Δ := [ Level.R ]) in h1 as h'.
      - cbn in h'. rewrite e in h'. eapply h'.
      - cbn. eapply reveal_scope_sound in h1 as hh.
        rewrite e in hh. cbn in hh.
        scope_inv hh hs'. intuition auto.
    }
    f_equal.
    eapply (f_equal π₂) in e as e'. cbn in e'. rewrite <- e'.
    pose proof (erase_reveal_subst_k) as h.
    specialize (h Γ [ Level.R ]). cbn in h.
    symmetry. apply h.
    + eapply reveal_scope_sound in h1 as hh.
      rewrite e in hh. cbn in hh.
      scope_inv hh hs'. intuition auto.
    + auto.
  - cbn. rewrite (erase_reveal _ t). rewrite e. cbn.
    constructor.
  - cbn. rewrite (erase_reveal _ t). rewrite e. cbn.
    eapply (f_equal π₂) in e as e'. cbn in e'. rewrite <- e'.
    rewrite erase_reveal_subst.
    3:{ scope_inv hs hs'. intuition auto. }
    2:{
      scope_inv hs hs'. destruct hs' as [_ [_ [_ h']]].
      eapply reveal_scope_sound in h'. rewrite e in h'.
      cbn in h'. scope_inv h' h''. auto.
    }
    constructor.
  - cbn. rewrite (erase_reveal _ t). rewrite e0. cbn.
    constructor.
  - cbn. rewrite (erase_reveal _ t). rewrite e0. cbn.
    eapply (f_equal π₂) in e0 as e'. cbn in e'. rewrite <- e'.
    rewrite erase_reveal_subst.
    3:{ scope_inv hs hs'. intuition auto. }
    2:{
      scope_inv hs hs'. destruct hs' as [_ [_ [_ [_ [_ h']]]]].
      eapply reveal_scope_sound in h'. rewrite e0 in h'.
      cbn in h'. scope_inv h' h''. intuition auto.
    }
    rewrite erase_reveal_subst.
    3:{ scope_inv hs hs'. intuition auto. }
    2:{
      scope_inv hs hs'. destruct hs' as [_ [_ [_ [_ [_ h']]]]].
      eapply reveal_scope_sound in h'. rewrite e0 in h'.
      cbn in h'. scope_inv h' h''. intuition auto.
    }
    constructor.
  - cbn. rewrite (erase_reveal _ e). rewrite e0. cbn. constructor.
Qed.

(* TODO MOVE *)
Lemma context_to_scope_pctx :
  ∀ Γ,
    SIRTT.context_to_scope (pctx Γ) = psc Γ.
Proof.
  intro Γ. unfold pctx, psc.
  unfold SIRTT.context_to_scope.
  rewrite !map_map. eapply map_ext.
  intros [ℓ t]. reflexivity.
Qed.

(* Even though typing and conversion are mutual, we can probably still
  conclude on conversion first as we will never need the induction hyothesis
  on typing.
*)
Lemma erase_conv :
  ∀ (Γ : SIRTT.context) u v,
    SIRTT.scoping Γ Level.R u →
    SIRTT.scoping Γ Level.R v →
    (Γ ⊢[ Level.R ] u ≡ v)%s →
    trans Γ u ≡ trans Γ v.
Proof.
  intros Γ u v hu hv h.
  remember Level.R as ℓR eqn:eℓ.
  induction h in eℓ, hu, hv |- *.
  all: try discriminate eℓ.
  all: try solve [
    try scope_inv hu hu' ; try scope_inv hv hv' ; intuition eauto
  ].
  all: try solve [
    try scope_inv hu hu' ; try scope_inv hv hv' ;
    cbn ; econstructor ; intuition eauto
  ].
  all: try solve [ subst ; cbn ; constructor ; constructor ].
  all: try solve [
    subst ; cbn ;
    try scope_inv hu hu' ; try scope_inv hv hv' ;
    t_cong ; intuition eauto ;
    rewrite context_to_scope_pctx in * ; intuition eauto ;
    rewrite !trans_psc in * ; intuition eauto
  ].
  - subst. scope_inv hu hs. cbn in hs. destruct hs as [hl hu'].
    scope_inv hl hl'.
    cbn. destruct ℓ'.
    + erewrite erase_subst10_relevant. 2,3: intuition eauto.
      constructor. constructor.
    + change (?t{0 := ?u})%s with (SIRTT.subst0 [u] t).
      erewrite erase_subst0 with (Δ := [ _ ]).
      2:{ cbn. intuition eauto. }
      3: reflexivity.
      2:{ constructor. 2: constructor. auto. }
      cbn. rewrite subst_empty. reflexivity.
    + change (?t{0 := ?u})%s with (SIRTT.subst0 [u] t).
      erewrite erase_subst0 with (Δ := [ _ ]).
      2:{ cbn. intuition eauto. }
      3: reflexivity.
      2:{ constructor. 2: constructor. auto. }
      cbn. rewrite subst_empty. reflexivity.
  - subst. scope_inv hu hs. destruct hs as [hs _].
    inversion hs. inversion H.
  - subst. cbn.
    scope_inv hu hu'. scope_inv hv hv'.
    destruct ℓ'.
    + t_cong. all: intuition eauto.
      rewrite context_to_scope_pctx in *. intuition eauto.
      rewrite !trans_psc in *. intuition eauto.
    + intuition eauto.
    + intuition eauto.
  - subst. cbn.
    scope_inv hu hu'. scope_inv hv hv'.
    destruct ℓ'.
    + t_cong. all: intuition eauto.
    + intuition eauto.
    + intuition eauto.
  - subst. cbn.
    scope_inv hu hu'. scope_inv hv hv'.
    destruct ℓ'.
    + t_cong. all: intuition eauto.
      all: rewrite context_to_scope_pctx in *. all: intuition eauto.
      all: rewrite !trans_psc in *. all: intuition eauto.
    + intuition eauto.
    + cbn. intuition eauto.
  - subst. inversion p.
    + subst. inversion H.
    + subst. intuition eauto.
Qed.

Fixpoint context_trans (Γ : SIRTT.context) :=
  match Γ with
  | (Level.R, A) :: Γ => trans (SIRTT.context_to_scope Γ) A :: context_trans Γ
  | _ :: Γ => context_trans Γ
  | [] => []
  end.

Lemma context_trans_nth_error :
  ∀ (Γ : SIRTT.context) n A,
    nth_error Γ n = Some (Level.R, A) →
    nth_error (context_trans Γ) #| scope_trans (firstn n (SIRTT.context_to_scope Γ)) | =
    Some (trans (skipn (S n) (SIRTT.context_to_scope Γ)) A).
Proof.
  intros Γ n A h.
  induction Γ as [| [ℓ B] Γ ih] in n, A, h |- *.
  1:{ destruct n. all: discriminate. }
  destruct n.
  - cbn in h. inversion h. subst. clear h. simpl. reflexivity.
  - cbn in h. eapply ih in h as h'.
    destruct ℓ.
    + simpl. rewrite h'. reflexivity.
    + simpl. rewrite h'. reflexivity.
    + simpl. rewrite h'. reflexivity.
Qed.

(* TODO MOVE *)
Lemma skipn_psc :
  ∀ Γ n,
    skipn n (psc Γ) = psc (skipn n Γ).
Proof.
  intros Γ n.
  induction Γ as [| ℓ Γ ih] in n |- *.
  - cbn. rewrite skipn_nil. reflexivity.
  - cbn. destruct n.
    + cbn. reflexivity.
    + cbn. eapply ih.
Qed.

Lemma context_trans_pctx :
  ∀ Γ,
    context_trans (pctx Γ) = context_trans Γ.
Proof.
  intros Γ. induction Γ as [| [[] A] Γ ih].
  - reflexivity.
  - cbn. fold (pctx Γ). rewrite context_to_scope_pctx.
    rewrite trans_psc.
    f_equal. auto.
  - cbn. auto.
  - cbn. auto.
Qed.

Lemma scoping_context_pctx :
  ∀ Γ,
    scoping_context Γ →
    scoping_context (pctx Γ).
Proof.
  intros Γ h.
  induction h.
  - cbn. constructor.
  - cbn. fold (pctx Γ). constructor. 1: auto.
    rewrite context_to_scope_pctx. rewrite psc_idemp. auto.
Qed.

Lemma erase_typing :
  ∀ Γ t A,
    scoping_context Γ →
    Γ ⊢[ Level.R ] t : A →
    [ Empty ] ;; context_trans Γ ⊢ trans Γ t :
    trans (pctx Γ) A.
Proof.
  intros Γ t A hΓ h.
  remember Level.R as ℓR eqn:eℓ.
  induction h in eℓ, hΓ |- *.
  all: try discriminate.
  all: try solve [ subst ; cbn ; intuition eauto ].
  all: try solve [
    subst ; cbn ; constructor ; intuition eauto
  ].
  - cbn. subst.
    eapply meta_conv.
    + constructor. eapply context_trans_nth_error. eauto.
    + pose proof erase_lift as h. specialize h with (Ξ := []).
      cbn in h.
      specialize h with (Δ := firstn n (psc Γ) ++ [ Level.R ]).
      specialize h with (Γ0 := skipn (S n) (psc Γ)).
      specialize (h A).
      rewrite scope_trans_app in h. rewrite !app_length in h.
      cbn - [skipn] in h.
      repeat lazymatch type of h with
      | context [ ?n + 1 ] =>
        replace (n + 1) with (S n) in h by lia
      end.
      rewrite !firstn_psc in h. rewrite !scope_trans_psc in h.
      rewrite skipn_psc in h. rewrite !trans_psc in h.
      rewrite <- h.
      * clear h.
        rewrite <- firstn_psc.
        rewrite firstn_length.
        eapply nth_error_Some_length in e as hn.
        rewrite psc_length.
        rewrite context_to_scope_length.
        replace (min n #|Γ|) with n by lia.
        f_equal.
        rewrite <- app_assoc. cbn - [skipn].
        change (Level.R) with (Level.pred (Level.R)).
        rewrite <- skipn_psc.
        rewrite context_to_scope_pctx.
        symmetry. eapply nth_error_Some_split.
        unfold psc. rewrite nth_error_map.
        eapply context_to_scope_nth_error in e. rewrite e. cbn.
        reflexivity.
      * clear h.
        eapply scoping_context_nth_error in e as h. 2: auto.
        rewrite skipn_psc in h. auto.
  - subst. cbn. destruct ℓ'.
    + rewrite context_to_scope_pctx.
      change (Level.R :: psc Γ)
      with (psc (Level.R :: SIRTT.context_to_scope Γ)).
      rewrite !trans_psc.
      econstructor.
      * rewrite !context_to_scope_pctx in IHh1. rewrite !trans_psc in IHh1.
        rewrite context_trans_pctx in IHh1.
        eapply IHh1. 2: reflexivity.
        eapply scoping_context_pctx. auto.
      * rewrite !context_to_scope_pctx in IHh2. rewrite !trans_psc in IHh2.
        eapply IHh2. 2: reflexivity.
        constructor. 1: auto.
        eapply SIRTT.typed_scoped in h1.
        rewrite context_to_scope_pctx in h1. auto.
    + cbn. cbn in IHh2. eapply IHh2. 2: reflexivity.
      constructor. 1: auto.
      eapply SIRTT.typed_scoped in h1.
      rewrite context_to_scope_pctx in h1. auto.
    + cbn. cbn in IHh2. eapply IHh2. 2: reflexivity.
      constructor. 1: auto.
      eapply SIRTT.typed_scoped in h1.
      rewrite context_to_scope_pctx in h1. auto.
  - subst. cbn. destruct ℓ'.
    + eapply meta_conv.
      * eapply type_app. all: intuition eauto.
      * fold trans.
        erewrite erase_subst10_relevant.
        3:{
          eapply SIRTT.typed_scoped in h2 as hs2. cbn in hs2.
          eapply scoping_ptm in hs2. cbn in hs2.
          rewrite context_to_scope_pctx. auto.
        }
        2:{
          (* Here we're missing some hyps.
            We could also prove validity, but it's a pain, and not worth it.
            Even more so as validity is easier to prove by adding said hyps.
          *)
          admit.
        }
        rewrite trans_ptm. rewrite context_to_scope_pctx. rewrite trans_psc.
        reflexivity.
    + change (?t{0 := ?u})%s with (SIRTT.subst0 [u] t).
      erewrite erase_subst0 with (Δ := [ Level.S ]).
      2:{ cbn. admit. }
      3: reflexivity.
      2:{ constructor. 2: constructor. intro. discriminate. }
      cbn. rewrite subst_empty.
      eapply IHh1. all: auto.
    + change (?t{0 := ?u})%s with (SIRTT.subst0 [u] t).
      erewrite erase_subst0 with (Δ := [ Level.S ]).
      2:{ cbn. admit. }
      3: reflexivity.
      2:{ constructor. 2: constructor. intro. discriminate. }
      cbn. rewrite subst_empty.
      eapply IHh1. all: auto.
  - subst. cbn. destruct ℓ'.
    + constructor.
      * cbn in IHh1. eapply IHh1. all: auto.
      * cbn in IHh2. eapply IHh2. 2: reflexivity.
        constructor. 1: auto.
        eapply scoping_psc. eapply SIRTT.typed_scoped. eauto.
    + cbn. cbn in IHh2.
      forward IHh2.
      { constructor. 1: auto.
        eapply scoping_psc. eapply SIRTT.typed_scoped. eauto.
      }
      forward IHh2 by auto.
      (* Another problem: universes!
          Maybe I should change the universe of Prod I and Prod S
          or add some form of cumulativity in the target.
          The first option sounds better because this way irrelevant
          info doesn't affect the level of relevant data.

          The problem with this approach is probably when translating to MLTT
          with the hope of preserving consistency, a.k.a the checker.
          i.e. if we encode refinement types and irrelevant products as
          regular products.
          Let's cross that bridge when we get there.
      *)
      admit.
    + admit.
  - subst. cbn.
    (* Same universe trouble *)
    admit.
  - subst. cbn. rewrite context_to_scope_pctx. rewrite !trans_psc.
    eapply type_elim_nat. all: try solve [ intuition eauto ].
    + forward IHh1. { eapply scoping_context_pctx. auto. }
      forward IHh1 by auto.
      rewrite !context_to_scope_pctx in IHh1.
      rewrite !trans_psc in IHh1.
      rewrite context_trans_pctx in IHh1. eapply IHh1.
    + forward IHh2. 1: auto.
      forward IHh2 by auto.
      cbn in IHh2. rewrite context_to_scope_pctx in IHh2.
      rewrite trans_psc in IHh2.
      eapply IHh2.
    + forward IHh3. 1: auto.
      forward IHh3 by auto.
      cbn in IHh3. rewrite context_to_scope_pctx in IHh3.
      change (Level.R :: Level.R :: psc Γ)
      with (psc (Level.R :: Level.R :: SIRTT.context_to_scope Γ)) in IHh3.
      change (Level.R :: psc Γ)
      with (psc (Level.R :: SIRTT.context_to_scope Γ)) in IHh3.
      rewrite !trans_psc in IHh3.
      pose proof erase_lift0 as h. specialize h with (Δ := [ Level.R ]).
      cbn in h.
      eapply SIRTT.typed_scoped in h1 as h1'.
      rewrite context_to_scope_pctx in h1'.
      eapply h in h1'.
      change (Level.R :: psc Γ)
      with (psc (Level.R :: SIRTT.context_to_scope Γ)) in h1'.
      rewrite !trans_psc in h1'.
      rewrite !h1' in IHh3.
      (* I should prove some lift_lift lemma
        or use twice a lift0 lemma
      *)
      (* eapply IHh3. *)
      admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - subst. econstructor.
    + eapply IHh1. all: auto.
    + eapply erase_conv.
      * (* From validity or extra requirement? *) admit.
      * eapply SIRTT.typed_scoped. eauto.
      * auto.
    + forward IHh2. { eapply scoping_context_pctx. auto. }
      forward IHh2 by reflexivity.
      rewrite context_trans_pctx in IHh2.
      rewrite !context_to_scope_pctx in IHh2.
      rewrite !context_to_scope_pctx.
      rewrite psc_idemp in IHh2.
      eauto.
  - subst. inversion p.
    1:{ inversion H. }
    subst.
    eapply IHh. all: auto.
Admitted.