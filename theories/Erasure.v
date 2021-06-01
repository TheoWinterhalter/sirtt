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
  | SIRTT.exfalso A p => MLTT.exfalso (trans Γ A) (MLTT.axiom 0)
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

Lemma scope_trans_psc :
  ∀ Γ,
    scope_trans (psc Γ) = scope_trans Γ.
Proof.
  intro Γ. induction Γ as [| [] Γ ih].
  all: cbn. all: eauto.
  f_equal. eapply ih.
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
  - cbn. constructor.
    + simpl in IHh1. specialize IHh1 with (1 := eq_refl).
      rewrite scope_trans_psc in IHh1. rewrite trans_psc in IHh1. auto.
    + constructor.
  - destruct ℓ.
    2:{ inversion p. subst. inversion H. }
    2:{ inversion p. subst. inversion H. }
    eapply IHh. reflexivity.
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
  eapply Level.potentially_more_R in hℓ. subst.
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
  | _ :: Δ, _ :: σ => trans_subst Γ Δ σ
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
  eapply Level.potentially_more_R in hℓ. subst.
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

(** Even though typing and conversion are mutual, we conclude on conversion
    first as we will never need the induction hyothesis on typing.
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
  - subst. cbn.
    scope_inv hu hu'. scope_inv hv hv'.
    t_cong.
    + rewrite !context_to_scope_pctx in IHh. rewrite !trans_psc in IHh.
      intuition eauto.
    + reflexivity.
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

Lemma erase_typing :
  ∀ Γ t A,
    scoping_context Level.R Γ →
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
        eapply scoping_context_nth_error in e as h. 2: eauto.
        rewrite skipn_psc in h. auto.
  - subst. cbn. destruct ℓ'.
    + rewrite context_to_scope_pctx.
      change (Level.R :: psc Γ)
      with (psc (Level.R :: SIRTT.context_to_scope Γ)).
      rewrite !trans_psc.
      econstructor.
      * rewrite !context_to_scope_pctx in IHh1. rewrite !trans_psc in IHh1.
        rewrite context_trans_pctx in IHh1.
        eapply IHh1. 1: reflexivity.
        eapply scoping_context_pctx. auto.
      * rewrite !context_to_scope_pctx in IHh2. rewrite !trans_psc in IHh2.
        eapply IHh2. 1: reflexivity.
        constructor. 1: auto.
        eapply SIRTT.typed_scoped in h1.
        rewrite context_to_scope_pctx in h1. auto.
    + cbn. cbn in IHh2. eapply IHh2. 1: reflexivity.
      constructor. 1: auto.
      rewrite psc_context_to_scope. eapply SIRTT.typed_scoped. eauto.
    + cbn. cbn in IHh2. eapply IHh2. 1: reflexivity.
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
          eapply SIRTT.typed_scoped in h3 as hs3. cbn in hs3.
          auto.
        }
        rewrite trans_ptm. rewrite context_to_scope_pctx. rewrite trans_psc.
        reflexivity.
    + change (?t{0 := ?u})%s with (SIRTT.subst0 [u] t).
      erewrite erase_subst0 with (Δ := [ Level.S ]).
      2:{
        cbn. eapply SIRTT.typed_scoped in h3 as hs3. cbn in hs3.
        auto.
      }
      3: reflexivity.
      2:{ constructor. 2: constructor. intro. discriminate. }
      cbn. rewrite subst_empty.
      eapply IHh1. all: auto.
    + change (?t{0 := ?u})%s with (SIRTT.subst0 [u] t).
      erewrite erase_subst0 with (Δ := [ Level.S ]).
      2:{
        cbn. eapply SIRTT.typed_scoped in h3 as hs3. cbn in hs3.
        auto.
      }
      3: reflexivity.
      2:{ constructor. 2: constructor. intro. discriminate. }
      cbn. rewrite subst_empty.
      eapply IHh1. all: auto.
  - subst. cbn. destruct ℓ'.
    + cbn. constructor.
      * cbn in IHh1. eapply IHh1. all: auto.
      * cbn in IHh2. eapply IHh2. 1: reflexivity.
        constructor. 1: auto.
        eapply scoping_psc. eapply SIRTT.typed_scoped. eauto.
    + cbn. cbn in IHh2.
      forward IHh2 by reflexivity.
      forward IHh2.
      { constructor. 1: auto.
        eapply scoping_psc. eapply SIRTT.typed_scoped. eauto.
      }
      auto.
    + cbn. cbn in IHh2.
      forward IHh2 by reflexivity.
      forward IHh2.
      { constructor. 1: auto.
        eapply scoping_psc. eapply SIRTT.typed_scoped. eauto.
      }
      auto.
  - subst. cbn. rewrite context_to_scope_pctx. rewrite !trans_psc.
    eapply type_elim_nat. all: try solve [ intuition eauto ].
    + forward IHh1 by reflexivity.
      forward IHh1. { eapply scoping_context_pctx. auto. }
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
      rewrite SIRTT.lift_lift in IHh3. simpl in IHh3.
      clear h1' h.
      pose proof erase_lift0 as h.
      specialize h with (Δ := [ Level.R ; Level.R ]).
      cbn in h.
      eapply SIRTT.typed_scoped in h1 as h'.
      rewrite context_to_scope_pctx in h'.
      eapply h in h'.
      change (Level.R :: Level.R :: psc Γ)
      with (psc (Level.R :: Level.R :: SIRTT.context_to_scope Γ)) in h'.
      rewrite trans_psc in h'.
      rewrite h' in IHh3.
      unfold arrow. cbn.
      rewrite lift_lift. simpl.
      rewrite trans_psc in IHh3.
      eapply IHh3.
  - subst. cbn. rewrite context_to_scope_pctx. rewrite trans_psc.
    econstructor.
    forward IHh by reflexivity.
    forward IHh. { eapply scoping_context_pctx. auto. }
    rewrite !context_to_scope_pctx in IHh. rewrite !trans_psc in IHh.
    rewrite context_trans_pctx in IHh.
    eauto.
  - subst. cbn. rewrite context_to_scope_pctx. rewrite trans_psc.
    econstructor.
    + forward IHh1 by reflexivity.
      forward IHh1. { eapply scoping_context_pctx. auto. }
      rewrite !context_to_scope_pctx in IHh1. rewrite !trans_psc in IHh1.
      rewrite context_trans_pctx in IHh1.
      eauto.
    + forward IHh2 by reflexivity.
      forward IHh2 by auto.
      rewrite !context_to_scope_pctx in IHh2. rewrite !trans_psc in IHh2.
      eauto.
    + forward IHh4 by reflexivity.
      forward IHh4 by auto.
      rewrite !context_to_scope_pctx in IHh4. rewrite !trans_psc in IHh4.
      eauto.
  - subst. cbn. rewrite !context_to_scope_pctx. rewrite !trans_psc.
    econstructor.
    + forward IHh1 by reflexivity.
      forward IHh1. { eapply scoping_context_pctx. auto. }
      rewrite !context_to_scope_pctx in IHh1. rewrite !trans_psc in IHh1.
      rewrite context_trans_pctx in IHh1.
      eauto.
    + forward IHh2 by reflexivity.
      forward IHh2. { eapply scoping_context_pctx. auto. }
      rewrite !context_to_scope_pctx in IHh2. rewrite !trans_psc in IHh2.
      rewrite !context_trans_pctx in IHh2.
      cbn in IHh2.
      pose proof erase_lift0 as h. specialize h with (Δ := [ Level.S ]).
      cbn in h.
      eapply SIRTT.typed_scoped in h1 as h1'.
      rewrite context_to_scope_pctx in h1'.
      eapply h in h1'.
      change (Level.S :: psc Γ)
      with (psc (Level.S :: SIRTT.context_to_scope Γ)) in h1'.
      rewrite !trans_psc in h1'.
      rewrite h1' in IHh2.
      rewrite lift_0 in IHh2.
      eauto.
    + forward IHh3 by reflexivity.
      forward IHh3 by auto.
      rewrite context_to_scope_pctx in IHh3. rewrite trans_psc in IHh3.
      eauto.
    + forward IHh4 by reflexivity.
      forward IHh4 by auto.
      rewrite context_to_scope_pctx in IHh4. rewrite trans_psc in IHh4.
      cbn in IHh4.
      (* One erase_lift0 *)
      pose proof erase_lift0 as h.
      specialize h with (Δ := [ Level.S ; Level.R ]).
      cbn in h.
      eapply SIRTT.typed_scoped in h1 as h'.
      rewrite context_to_scope_pctx in h'.
      eapply h in h'.
      change (Level.S :: Level.R :: psc Γ)
      with (psc (Level.S :: Level.R :: SIRTT.context_to_scope Γ)) in h'.
      rewrite !trans_psc in h'.
      rewrite h' in IHh4.
      clear h h'.
      (* One erase_lift0 *)
      pose proof erase_lift0 as h.
      specialize h with (Δ := [ Level.R ; Level.S ; Level.R ]).
      cbn in h.
      eapply SIRTT.typed_scoped in h2 as h'.
      rewrite context_to_scope_pctx in h'.
      eapply h in h'.
      change (Level.R :: Level.S :: Level.R :: psc Γ)
      with (psc (Level.R :: Level.S :: Level.R :: SIRTT.context_to_scope Γ))
      in h'.
      rewrite !trans_psc in h'.
      rewrite h' in IHh4.
      clear h h'.
      (* One erase_lift0 *)
      rewrite !SIRTT.lift_lift in IHh4. simpl in IHh4.
      pose proof erase_lift0 as h.
      specialize h with (Δ := [ Level.R ; Level.R ; Level.S ; Level.R ]).
      cbn in h.
      eapply SIRTT.typed_scoped in h2 as h'.
      rewrite context_to_scope_pctx in h'.
      eapply h in h'.
      change (Level.R :: Level.R :: Level.S :: Level.R :: psc Γ)
      with (psc (Level.R :: Level.R :: Level.S :: Level.R :: SIRTT.context_to_scope Γ))
      in h'.
      rewrite !trans_psc in h'.
      rewrite h' in IHh4.
      clear h h'.
      (* One erase_lift0 *)
      pose proof erase_lift0 as h.
      specialize h with (Δ := [ Level.R ; Level.R ; Level.S ; Level.R ]).
      cbn in h.
      eapply SIRTT.typed_scoped in h1 as h'.
      rewrite context_to_scope_pctx in h'.
      eapply h in h'.
      change (Level.R :: Level.R :: Level.S :: Level.R :: psc Γ)
      with (psc (Level.R :: Level.R :: Level.S :: Level.R :: SIRTT.context_to_scope Γ))
      in h'.
      rewrite !trans_psc in h'.
      rewrite h' in IHh4.
      clear h h'.
      unfold arrow. simpl.
      rewrite !lift_lift. simpl.
      eapply IHh4.
    + forward IHh6 by reflexivity.
      forward IHh6 by auto.
      rewrite context_to_scope_pctx in IHh6. rewrite trans_psc in IHh6.
      eauto.
  - subst. cbn. rewrite !context_to_scope_pctx. rewrite !trans_psc.
    econstructor.
    + forward IHh1 by reflexivity.
      forward IHh1. { eapply scoping_context_pctx. auto. }
      rewrite !context_to_scope_pctx in IHh1. rewrite !trans_psc in IHh1.
      rewrite context_trans_pctx in IHh1.
      eauto.
    + forward IHh2 by reflexivity.
      forward IHh2 by auto.
      rewrite !context_to_scope_pctx in IHh2. rewrite !trans_psc in IHh2.
      eauto.
  - subst. cbn. rewrite !context_to_scope_pctx. rewrite !trans_psc.
    econstructor.
    + forward IHh1 by reflexivity.
      forward IHh1. { eapply scoping_context_pctx. auto. }
      rewrite !context_to_scope_pctx in IHh1. rewrite !trans_psc in IHh1.
      rewrite context_trans_pctx in IHh1.
      eauto.
    + forward IHh2 by reflexivity.
      forward IHh2. { eapply scoping_context_pctx. auto. }
      rewrite !context_to_scope_pctx in IHh2. rewrite !trans_psc in IHh2.
      rewrite context_trans_pctx in IHh2.
      eapply IHh2.
    + forward IHh3 by auto. forward IHh3 by auto.
      rewrite context_to_scope_pctx in IHh3. rewrite trans_psc in IHh3.
      auto.
    + forward IHh4 by auto. forward IHh4 by auto.
      rewrite context_to_scope_pctx in IHh4. rewrite trans_psc in IHh4.
      auto.
    + forward IHh5 by auto. forward IHh5 by auto.
      rewrite context_to_scope_pctx in IHh5. rewrite trans_psc in IHh5.
      auto.
    + forward IHh6 by auto. forward IHh6 by auto.
      rewrite context_to_scope_pctx in IHh6. rewrite trans_psc in IHh6.
      auto.
  - subst. cbn. econstructor.
    + forward IHh1 by reflexivity.
      forward IHh1 by auto.
      rewrite !context_to_scope_pctx in IHh1. rewrite !trans_psc in IHh1.
      auto.
    + forward IHh2 by auto. forward IHh2 by auto.
      rewrite context_to_scope_pctx in IHh2. rewrite trans_psc in IHh2.
      auto.
    + forward IHh3 by auto. forward IHh3 by auto.
      rewrite context_to_scope_pctx in IHh3. rewrite trans_psc in IHh3.
      auto.
  - subst. cbn. rewrite context_to_scope_pctx. rewrite trans_psc.
    econstructor.
    + forward IHh1 by reflexivity.
      forward IHh1. { eapply scoping_context_pctx. auto. }
      rewrite !context_to_scope_pctx in IHh1. rewrite !trans_psc in IHh1.
      rewrite context_trans_pctx in IHh1.
      eauto.
    + constructor. reflexivity.
  - subst. econstructor.
    + eapply IHh1. all: auto.
    + eapply erase_conv.
      * eapply SIRTT.typed_scoped. eauto.
      * eapply SIRTT.typed_scoped. eauto.
      * auto.
    + forward IHh3 by reflexivity.
      forward IHh3. { eapply scoping_context_pctx. auto. }
      rewrite context_trans_pctx in IHh3.
      rewrite !context_to_scope_pctx in IHh3.
      rewrite !context_to_scope_pctx.
      rewrite psc_idemp in IHh3.
      eauto.
  - subst. inversion p.
    1:{ inversion H. }
    subst.
    eapply IHh. all: auto.
Qed.

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
      eapply scoping_cored. all: eauto.
Qed.

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