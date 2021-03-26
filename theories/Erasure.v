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
*)
Fixpoint trans (Γ : SIRTT.scope) (t : SIRTT.term) : MLTT.term :=
  match t with
  | SIRTT.var i => MLTT.var #| scope_trans (firstn i Γ) |
  | SIRTT.lam Level.R A t => MLTT.lam (trans Γ A) (trans (Level.R :: Γ) t)
  | SIRTT.lam l A t => trans (l :: Γ) t
  | SIRTT.app Level.R u v => MLTT.app (trans Γ u) (trans Γ v)
  | SIRTT.app l u v => trans Γ u
  | SIRTT.Prod Level.R A B => MLTT.Prod (trans Γ A) (trans (Level.R :: Γ) B)
  | SIRTT.Prod l A B =>trans (Level.pred l :: Γ) B
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

Lemma erase_lift :
  ∀ Γ Δ Ξ t,
    SIRTT.scoping (Ξ ++ Γ) Level.R t →
    trans (Ξ ++ Δ ++ Γ) (SIRTT.lift #|Δ| #|Ξ| t) =
    MLTT.lift #|scope_trans Δ| #|scope_trans Ξ| (trans (Ξ ++ Γ) t).
Proof.
  intros Γ Δ Ξ t h.
  remember (Ξ ++ Γ) as Θ eqn:eΘ. revert Γ Δ Ξ eΘ.
  dependent induction h.
  all: intros Θ Δ Ξ eΘ.
  all: try solve [
    cbn ; rewrite ?IHh, ?IHh1, ?IHh2, ?IHh3, ?IHh4, ?IHh5, ?IHh6 by auto ;
    reflexivity
  ].
  - subst. cbn. destruct (PeanoNat.Nat.leb_spec #|Ξ| n).
    + rewrite firstn_app. rewrite firstn_all2 by lia.
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
    + rewrite firstn_app. replace (n - #|Ξ|) with 0 by lia.
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
        apply nth_error_Some_split in e as h.
        apply (f_equal scope_trans) in h.
        rewrite scope_trans_app in h. cbn - [skipn] in h.
        rewrite h in el.
        rewrite app_length in el. cbn - [skipn] in el. lia.
      }
      reflexivity.
  - destruct ℓ'.
    + cbn. rewrite IHh1. 2: auto.
      specialize (IHh2 Θ Δ (Level.R :: Ξ)).
      forward IHh2.
      { cbn. f_equal. auto. }
      cbn in IHh2. rewrite IHh2.
      reflexivity.
    + cbn. specialize (IHh2 Θ Δ (Level.S :: Ξ)).
      forward IHh2.
      { cbn. f_equal. auto. }
      cbn in IHh2. rewrite IHh2.
      reflexivity.
    + cbn. specialize (IHh2 Θ Δ (Level.I :: Ξ)).
      forward IHh2.
      { cbn. f_equal. auto. }
      cbn in IHh2. rewrite IHh2.
      reflexivity.
  - destruct ℓ'.
    + cbn. rewrite IHh1. 2: auto.
      cbn in IHh2. specialize IHh2 with (1 := eq_refl).
      rewrite IHh2. 2: auto.
      reflexivity.
    + cbn. rewrite IHh1. 2: auto.
      reflexivity.
    + cbn. rewrite IHh1. 2: auto.
      reflexivity.
  - destruct ℓ'.
    + cbn. rewrite IHh1. 2: auto.
      specialize (IHh2 Θ Δ (Level.R :: Ξ)).
      forward IHh2.
      { cbn. f_equal. auto. }
      cbn in IHh2. rewrite IHh2.
      reflexivity.
    + cbn. specialize (IHh2 Θ Δ (Level.S :: Ξ)).
      forward IHh2.
      { cbn. f_equal. auto. }
      cbn in IHh2. rewrite IHh2.
      reflexivity.
    + cbn. specialize (IHh2 Θ Δ (Level.S :: Ξ)).
      forward IHh2.
      { cbn. f_equal. auto. }
      cbn in IHh2. rewrite IHh2.
      reflexivity.
  - destruct ℓ.
    2:{ inversion p. subst. inversion H. }
    2:{ inversion p. subst. inversion H. }
    eapply IHh.
    + reflexivity.
    + auto.
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

Lemma erase_subst :
  ∀ Γ Δ Ξ σ t θ,
    SIRTT.scoping (Ξ ++ Δ ++ Γ) Level.R t → (* Unclear it's needed *)
    scoping_subst Γ Δ σ → (* Could be weakened to only talk about relevant bits *)
    trans_subst Γ Δ σ = Some θ →
    trans (Ξ ++ Γ) (SIRTT.subst σ #|Ξ| t) =
    MLTT.subst θ #|scope_trans Ξ| (trans (Ξ ++ Δ ++ Γ) t).
Proof.
  intros Γ Δ Ξ σ t θ h sσ hσ.
  remember (Ξ ++ Δ ++ Γ) as Θ eqn:eΘ. revert Γ Δ Ξ σ θ sσ hσ eΘ.
  dependent induction h.
  all: intros Θ Δ Ξ σ θ sσ hσ eΘ.
  all: try solve [
    subst ;
    cbn ; erewrite ?IHh, ?IHh1, ?IHh2, ?IHh3, ?IHh4, ?IHh5, ?IHh6 by eauto ;
    reflexivity
  ].
  - subst. cbn. destruct (PeanoNat.Nat.leb_spec #|Ξ| n).
    + rewrite firstn_app. rewrite firstn_all2 by lia.
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
      * rewrite nth_error_app1 in e. 2: auto.
        eapply trans_subst_nth_error_R in hσ as hh. 2: eauto.
        destruct hh as [u [h1 h2]].
        rewrite h1.
        eapply nth_error_Some_length in e as el.
        rewrite firstn_app. replace (n - #|Ξ| - #|Δ|) with 0 by lia.
        rewrite firstn_O. rewrite app_nil_r.
        rewrite h2.
        apply erase_lift0.
        eapply scoping_subst_nth_error in sσ. all: eauto.
      * rewrite nth_error_app2 in e. 2: auto.
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
    + rewrite firstn_app. replace (n - #|Ξ|) with 0 by lia.
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
  - subst. cbn. destruct ℓ'.
    + cbn. erewrite ?IHh1, ?IHh2 by eauto.
      f_equal. specialize IHh2 with (Ξ0 := Level.R :: Ξ). cbn in IHh2.
      erewrite IHh2. all: eauto.
    + specialize IHh2 with (Ξ0 := Level.S :: Ξ). cbn in IHh2.
      eapply IHh2. all: eauto.
    + specialize IHh2 with (Ξ0 := Level.I :: Ξ). cbn in IHh2.
      eapply IHh2. all: eauto.
  - subst. cbn. destruct ℓ'.
    all: try solve [
      cbn ; erewrite ?IHh, ?IHh1, ?IHh2, ?IHh3, ?IHh4, ?IHh5, ?IHh6 by eauto ;
      reflexivity
    ].
  - subst. cbn. destruct ℓ'.
    + erewrite IHh1 by eauto. cbn. f_equal.
      specialize IHh2 with (Ξ0 := Level.R :: Ξ). cbn in IHh2.
      erewrite IHh2. all: eauto.
    + specialize IHh2 with (Ξ0 := Level.S :: Ξ). cbn in IHh2.
      eapply IHh2. all: eauto.
    + specialize IHh2 with (Ξ0 := Level.S :: Ξ). cbn in IHh2.
      eapply IHh2. all: eauto.
  - subst. eapply IHh. all: eauto.
    inversion p. 1:{ subst. inversion H. }
    subst. reflexivity.
Qed.

Corollary erase_subst0 :
  ∀ Γ Δ σ t θ,
    SIRTT.scoping (Δ ++ Γ) Level.R t →
    scoping_subst Γ Δ σ →
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

(* TODO scoping_reveal is a copy? *)
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

(* TODO Copy of reveal_scope_sound? *)
Lemma scoping_reveal :
  ∀ Γ t,
    SIRTT.scoping Γ Level.R t →
    SIRTT.scoping (reveal_scope t ++ Γ) Level.R (π₁ (reveal t)).
Proof.
  fix aux 2.
  intros Γ t h.
  destruct t.
  all: try solve [ assumption ].
  - cbn. destruct l.
    + assumption.
    + destruct t1. all: try assumption.
      destruct l. all: try assumption.
      cbn.
      scope_inv h h'. destruct h' as [h1 h2].
      scope_inv h1 h'. destruct h' as [? hh].
      eapply aux in hh.
      rewrite <- app_assoc. auto.
    + destruct t1. all: try assumption.
      destruct l. all: try assumption.
      cbn.
      scope_inv h h'. destruct h' as [h1 h2].
      scope_inv h1 h'. destruct h' as [? hh].
      eapply aux in hh.
      rewrite <- app_assoc. auto.
  - cbn. destruct t. all: try assumption.
    scope_inv h h'. scope_inv h' h''.
    destruct h'' as [? ?].
    eapply aux. auto.
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
  - simpl. scope_inv h hs. destruct hs as [e ?]. subst.
    constructor. intuition eauto.
Qed.

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
  - simpl. scope_inv ht hs. destruct hs as [e ?]. subst.
    constructor. intuition eauto.
Qed.

Lemma scoping_reveal_subst :
  ∀ Γ u t,
    let '(v, σ) := reveal u in
    SIRTT.scoping Γ Level.R u →
    SIRTT.scoping (reveal_scope u ++ Γ) Level.R t →
    SIRTT.scoping Γ Level.R (reveal_subst σ t).
Proof.
  cbn. fix aux 2. intros Γ u t hu ht.
  destruct u. all: try assumption.
  - cbn. destruct l.
    + assumption.
    + destruct u1. all: try assumption.
      destruct l. all: try assumption.
      cbn. cbn in ht.
      change (?t{0 := ?u})%s with (SIRTT.subst0 [u] t).
      scope_inv hu hs. cbn in hs. destruct hs as [hs1 hs2].
      scope_inv hs1 hs1'.
      eapply subst_scoping with (Ξ := []).
      2: constructor. 3: constructor. 2: eauto.
      cbn. eapply aux. 1: intuition eauto.
      rewrite <- app_assoc in ht. exact ht.
    + destruct u1. all: try assumption.
      destruct l. all: try assumption.
      cbn. cbn in ht.
      change (?t{0 := ?u})%s with (SIRTT.subst0 [u] t).
      scope_inv hu hs. cbn in hs. destruct hs as [hs1 hs2].
      scope_inv hs1 hs1'.
      eapply subst_scoping with (Ξ := []).
      2: constructor. 3: constructor. 2: eauto.
      cbn. eapply aux. 1: intuition eauto.
      rewrite <- app_assoc in ht. exact ht.
  - cbn. destruct u. all: try assumption.
    scope_inv hu hs. scope_inv hs hs'.
    eapply aux. 1: intuition eauto.
    cbn in ht. auto.
Qed.

Lemma erase_reveal_subst :
  ∀ Γ u t,
    SIRTT.scoping (reveal_scope u ++ Γ) Level.R t →
    SIRTT.scoping Γ Level.R u →
    let '(v, σ) := reveal u in
    trans Γ (reveal_subst σ t) = trans (reveal_scope u ++ Γ) t.
Proof.
  cbn. fix aux 2. intros Γ u t ht h.
  destruct u. all: try reflexivity.
  - cbn. destruct l.
    + reflexivity.
    + destruct u1. all: try reflexivity.
      destruct l. all: try reflexivity.
      cbn.
      scope_inv h hs. destruct hs as [hs ?]. scope_inv hs h'.
      change (?t{0 := ?u})%s with (SIRTT.subst0 [u] t).
      erewrite erase_subst0.
      * rewrite subst_empty. symmetry. rewrite <- app_assoc. rewrite aux.
        1: reflexivity.
        -- cbn in ht. rewrite app_assoc. auto.
        -- cbn. intuition auto.
      * cbn. eapply scoping_reveal_subst. 1: intuition eauto.
        cbn in ht. rewrite <- app_assoc in ht. auto.
      * constructor. 2: constructor.
        auto.
      * reflexivity.
    + destruct u1. all: try reflexivity.
      destruct l. all: try reflexivity.
      cbn.
      scope_inv h hs. destruct hs as [hs ?]. scope_inv hs h'.
      change (?t{0 := ?u})%s with (SIRTT.subst0 [u] t).
      erewrite erase_subst0.
      * rewrite subst_empty. symmetry. rewrite <- app_assoc. rewrite aux.
        1: reflexivity.
        -- cbn in ht. rewrite app_assoc. auto.
        -- cbn. intuition auto.
      * cbn. eapply scoping_reveal_subst. 1: intuition eauto.
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

(* Lemma erase_reveal_subst :
  ∀ Γ u,
    SIRTT.scoping Γ Level.R u →
    let '(v, σ) := reveal u in
    trans Γ u = trans Γ (reveal_subst σ v).
Proof.
  intros Γ u h. cbn.
  rewrite erase_reveal.
  revert Γ u h. fix aux 2. intros Γ u h.
  destruct u. all: try reflexivity.
  - simpl. destruct l.
    + reflexivity.
    + destruct u1. all: try reflexivity.
      destruct l. all: try reflexivity.
      cbn.
      scope_inv h hs. destruct hs as [hs ?]. scope_inv hs h'.
      change (?t{0 := u2})%s with (SIRTT.subst0 [u2] t).
      erewrite erase_subst0.
      * rewrite subst_empty. rewrite <- app_assoc. rewrite aux.
        1: reflexivity.
        cbn. intuition auto.
      * cbn. (* eapply scoping_reveal. *) admit.
      * constructor. 2: constructor.
        auto.
      * reflexivity.
    + admit.
  - simpl. destruct u. all: try reflexivity.
    scope_inv h hs. scope_inv hs h'.
    apply aux. intuition auto.
Admitted. *)

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
    (* 2:{
      cbn. eapply scoping_reveal_subst in h1 as h'.
      2: eapply reveal_scope_sound. 2: auto.
      rewrite e in h'.
      (* Sounds very odd! *)
      admit.
    }
    cbn. f_equal.
    eapply (f_equal π₂) in e as e'. cbn in e'. rewrite <- e'.
    rewrite erase_reveal_subst. *)
    (* Wrong!! *)
    (* Even the above is wrong, so it would suggest something unexpected
      happened, and I should not use erase_subst0 or maybe with different
      arguments?
    *)
    all: give_up.
  - cbn. rewrite (erase_reveal _ t). rewrite e. cbn.
    constructor.
  - cbn. rewrite (erase_reveal _ t). rewrite e. cbn.
    eapply (f_equal π₂) in e as e'. cbn in e'. rewrite <- e'.
    rewrite erase_reveal_subst.
    3:{ scope_inv hs hs'. intuition auto. }
    2:{
      scope_inv hs hs'. destruct hs' as [_ [_ [_ h']]].
      eapply scoping_reveal in h'. rewrite e in h'.
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
      eapply scoping_reveal in h'. rewrite e0 in h'.
      cbn in h'. scope_inv h' h''. intuition auto.
    }
    rewrite erase_reveal_subst.
    3:{ scope_inv hs hs'. intuition auto. }
    2:{
      scope_inv hs hs'. destruct hs' as [_ [_ [_ [_ [_ h']]]]].
      eapply scoping_reveal in h'. rewrite e0 in h'.
      cbn in h'. scope_inv h' h''. intuition auto.
    }
    constructor.
Admitted.
