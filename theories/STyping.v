(** Typing and conversion in SIRTT

  Conversion is not defined from reduction because reduction only deals with
  relevant terms. We should be able to show however that u ↦ v implies
  that u and v are convertible as relevant terms.
  In fact, because of shape-irrelevant reflection, we need to define conversion
  mutually with typing.
  As such, this file should go away.

  I'm also missing exfalso in the AST, and thus axioms in the target to have
  axiom False.
  More crucially, I'm missing equality it seems.
  I could also be abstract about it, but maybe it's not such a good idea?

  Typing is defined without assumptions on contexts.

  Conversion is not typed, but it could have been.

*)

From Coq Require Import Utf8 List Lia.
Require Import Equations.Prop.DepElim.
Require Import Equations.Prop.Classes.
From Equations Require Import Equations.
Require Import Util Level SAst SSubst SReduction SScoping.

Import ListNotations.

Set Default Goal Selector "!".

Definition arrow A B := Prod R A (lift0 1 B).
Notation "A ⇒ B" := (arrow A B) (at level 70, right associativity) : s_scope.

(** When Γ ⊢[ ℓ ] t : A then A doesn't live in Γ, but really
    in Γ where all bindings have been Level.pred-ed, meaning all irrelevant
    bindings become shape-irrelevant.
    This means that types in typing judgments need to live in the
    transformed context.
    We call this operation [pctx] pending a better name.
*)
Definition pctx (Γ : context) : context :=
  map (λ '(ℓ, A), (▪ ℓ, A)) Γ.

Reserved Notation "Γ ⊢[ l ] t : A"
  (at level 80, l, t, A at next level, format "Γ  ⊢[  l  ]  t  :  A").

Reserved Notation "Γ ⊢[ l ] u ≡ v"
  (at level 80, l, u, v at next level, format "Γ  ⊢[  l  ]  u  ≡  v").

Inductive typing (Γ : context) : level → term → term → Type :=
| type_var :
    ∀ n ℓ ℓ' A,
      nth_error Γ n = Some (ℓ, A) →
      ℓ ⊑ ℓ' →
      Γ ⊢[ ℓ' ] var n : (lift0 (Datatypes.S n) A)

| type_lam :
    ∀ ℓ ℓ' A B t s,
      pctx Γ ⊢[ ▪ (ℓ ⊔ ℓ') ] A : univ s →
      (ℓ', A) :: Γ ⊢[ ℓ ] t : B →
      Γ ⊢[ ℓ ] lam ℓ' A t : Prod ℓ' A B

| type_app :
    ∀ ℓ ℓ' A B u v j,
      Γ ⊢[ ℓ ] u : Prod ℓ' A B →
      Γ ⊢[ ℓ ⊔ ℓ' ] v : A →
      (* The following would usually follow from validity and inversion
         but this way, it's simpler to make the proof.
      *)
      (▪ ℓ', A) :: pctx Γ ⊢[ ▪ ℓ ] B : univ j →
      Γ ⊢[ ℓ ] app ℓ' u v : B{ 0 := ptm v }

| type_Prod :
    ∀ ℓ ℓ' A B i j,
      Γ ⊢[ ℓ ⊔ ▪ ℓ' ] A : univ i →
      (▪ ℓ', A) :: Γ ⊢[ ℓ ] B : univ j →
      (* NOTE: Prod ℓ A B lives in the universe of B when the binder
        is (shape-)irrelevant.
      *)
      Γ ⊢[ ℓ ] Prod ℓ' A B : univ (if relevant ℓ' then Peano.max i j else j)

| type_ex :
    ∀ j ℓ A P u p,
      ((R, A) :: pctx Γ) ⊢[ S ⊔ ▪ ℓ ] P : univ j →
      Γ ⊢[ ℓ ] u : A →
      Γ ⊢[ I ] p : P{ 0 := ptm u } →
      Γ ⊢[ ℓ ] ex u p : Sum A P

| type_wit :
    ∀ ℓ A P p,
      Γ ⊢[ ℓ ] p : Sum A P →
      Γ ⊢[ ℓ ] wit p : A

| type_prf :
    ∀ ℓ A P p,
      Γ ⊢[ I ] p : Sum A P →
      S ⊑ ℓ →
      Γ ⊢[ ℓ ] prf p : P{ 0 := ptm (wit p) }

| type_Sum :
    ∀ ℓ A P i j,
      Γ ⊢[ ℓ ] A : univ i →
      (R, A) :: Γ ⊢[ S ⊔ ℓ ] P : univ j →
      (* NOTE: Sum A P lives in the universe of A, regardless of P *)
      Γ ⊢[ ℓ ] Sum A P : univ i

| type_zero :
    ∀ ℓ,
      Γ ⊢[ ℓ ] zero : Nat

| type_succ :
    ∀ ℓ n,
      Γ ⊢[ ℓ ] n : Nat →
      Γ ⊢[ ℓ ] succ n : Nat

| type_elim_nat :
    ∀ ℓ P z s n i,
      pctx Γ ⊢[ ▪ ℓ ] P : Nat ⇒ univ i →
      Γ ⊢[ ℓ ] z : app R P zero →
      Γ ⊢[ ℓ ] s :
        Prod R Nat
          (app R (lift0 1 P) (var 0) ⇒ app R (lift0 1 P) (succ (var 0))) →
      Γ ⊢[ ℓ ] n : Nat →
      Γ ⊢[ ℓ ] elim_nat P z s n : app R P (ptm n)

| type_Nat :
    ∀ ℓ i,
      Γ ⊢[ ℓ ] Nat : univ i

| type_vnil :
    ∀ ℓ A i,
      pctx Γ ⊢[ ▪ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] vnil A : Vec A zero

| type_vcons :
    ∀ ℓ A a n v i,
      pctx Γ ⊢[ ▪ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] a : A →
      Γ ⊢[ I ] n : Nat →
      Γ ⊢[ ℓ ] v : Vec A n →
      Γ ⊢[ ℓ ] vcons A a n v : Vec A (succ (ptm n))

| type_elim_vec :
    ∀ ℓ A P e c n v i j,
      pctx Γ ⊢[ ▪ ℓ ] A : univ i →
      pctx Γ ⊢[ ▪ ℓ ] P : Prod I Nat (Vec (lift0 1 A) (var 0) ⇒ univ j) →
      Γ ⊢[ ℓ ] e : app R (app I P zero) (vnil A) →
      Γ ⊢[ ℓ ] c :
        Prod R A
          (Prod I Nat (
            Prod R (Vec (lift0 2 A) (var 0)) (
              app R (app I (lift0 3 P) (var 1)) (var 0) ⇒
              app R
                (app I (lift0 3 P) (succ (var 1)))
                (vcons (lift0 3 A) (var 2) (var 1) (var 0))
            )
          )
        ) →
      Γ ⊢[ I ] n : Nat →
      Γ ⊢[ ℓ ] v : Vec A n →
      Γ ⊢[ ℓ ] elim_vec A P e c n v : app R (app I P n) (ptm v)

| type_Vec :
    ∀ ℓ A n i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ S ⊔ ℓ ] n : Nat →
      Γ ⊢[ ℓ ] Vec A n : univ i

| type_refl :
    ∀ ℓ A u i,
      pctx Γ ⊢[ ▪ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] u : A →
      Γ ⊢[ ℓ ] refl A u : Eq A (ptm u) (ptm u)

| type_coe :
    ∀ ℓ A P u v e t i j,
      pctx Γ ⊢[ ▪ ℓ ] A : univ i →
      pctx Γ ⊢[ ▪ ℓ ] P : A ⇒ univ j →
      Γ ⊢[ ℓ ] u : A →
      Γ ⊢[ ℓ ] v : A →
      Γ ⊢[ ℓ ] e : Eq A u v →
      Γ ⊢[ ℓ ] t : app R P u →
      Γ ⊢[ ℓ ] coe A P u v e t : app R P (ptm v)

| type_Eq :
    ∀ ℓ A u v i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] u : A →
      Γ ⊢[ ℓ ] v : A →
      Γ ⊢[ ℓ ] Eq A u v : univ i

| type_exfalso :
    ∀ ℓ A p i,
      pctx Γ ⊢[ ▪ ℓ ] A : univ i →
      Γ ⊢[ I ] p : Empty →
      Γ ⊢[ ℓ ] exfalso A p : A

| type_Empty :
    ∀ ℓ i,
      Γ ⊢[ ℓ ] Empty : univ i

| type_univ :
    ∀ ℓ i j,
      i < j →
      Γ ⊢[ ℓ ] univ i : univ j

| type_conv :
    ∀ t A B ℓ i j,
      Γ ⊢[ ℓ ] t : A →
      pctx Γ ⊢[ ▪ ℓ ] A ≡ B →
      pctx Γ ⊢[ ▪ ℓ ] A : univ i → (* Would follow from validity *)
      pctx Γ ⊢[ ▪ ℓ ] B : univ j →
      Γ ⊢[ ℓ ] t : B

where "Γ ⊢[ l ] t : A" := (typing Γ l t A) : s_scope

with conversion (Γ : context) : level → term → term → Type :=

(* Computation rules *)

| conv_beta :
    ∀ ℓ ℓ' A t u,
      Γ ⊢[ ℓ ] app ℓ' (lam ℓ' A t) u ≡ t{ 0 := u }

| comp_wit :
    ∀ ℓ u p,
      Γ ⊢[ ℓ ] wit (ex u p) ≡ u

| comp_prf :
    ∀ ℓ u p,
      Γ ⊢[ ℓ ] prf (ex u p) ≡ p

| comp_elim_nat_zero :
    ∀ ℓ P z s,
      Γ ⊢[ ℓ ] elim_nat P z s zero ≡ z

| comp_elim_nat_succ :
    ∀ ℓ P z s n,
      Γ ⊢[ ℓ ]
        elim_nat P z s (succ n) ≡ apps s [ (R, n) ; (R, elim_nat P z s n) ]

| comp_elim_vec_vnil :
    ∀ ℓ A P e c n,
      Γ ⊢[ ℓ ] elim_vec A P e c n (vnil A) ≡ e

| comp_elim_vec_vcons :
    ∀ ℓ A P e c n a v,
      Γ ⊢[ ℓ ]
        elim_vec A P e c n (vcons A a n v) ≡
        apps c [ (R, a) ; (I, n) ; (R, v) ; (R, elim_vec A P e c n v) ]

| comp_coe_refl :
    ∀ ℓ A P u t,
      Γ ⊢[ ℓ ] coe A P u u (refl A u) t ≡ t

(* Congruence rules *)

| cong_lam :
    ∀ ℓ ℓ' A A' t t',
      pctx Γ ⊢[ ▪ ℓ ] A ≡ A' →
      (ℓ', A) :: Γ ⊢[ ℓ ] t ≡ t' →
      Γ ⊢[ ℓ ] lam ℓ' A t ≡ lam ℓ' A' t'

| cong_app :
    ∀ ℓ ℓ' u u' v v',
      Γ ⊢[ ℓ ] u ≡ u' →
      Γ ⊢[ ℓ ] v ≡ v' →
      Γ ⊢[ ℓ ] app ℓ' u v ≡ app ℓ' u' v'

| cong_Prod :
    ∀ ℓ ℓ' A A' B B',
      Γ ⊢[ ℓ ] A ≡ A' →
      (▪ ℓ', A) :: Γ ⊢[ ℓ ] B ≡ B' →
      Γ ⊢[ ℓ ] Prod ℓ' A B ≡ Prod ℓ' A' B'

| cong_ex :
    ∀ ℓ u u' p p',
      Γ ⊢[ ℓ ] u ≡ u' →
      Γ ⊢[ ℓ ] ex u p ≡ ex u' p'

| cong_wit :
    ∀ ℓ t t',
      Γ ⊢[ ℓ ] t ≡ t' →
      Γ ⊢[ ℓ ] wit t ≡ wit t'

| cong_Sum :
    ∀ ℓ A A' P P',
      Γ ⊢[ ℓ ] A ≡ A' →
      (R, A) :: Γ ⊢[ S ⊔ ℓ ] P ≡ P' →
      Γ ⊢[ ℓ ] Sum A P ≡ Sum A' P'

| cong_succ :
    ∀ ℓ n n',
      Γ ⊢[ ℓ ] n ≡ n' →
      Γ ⊢[ ℓ ] succ n ≡ succ n'

| cong_elim_nat :
    ∀ ℓ P P' z z' s s' n n',
      pctx Γ ⊢[ ▪ ℓ ] P ≡ P' →
      Γ ⊢[ ℓ ] z ≡ z' →
      Γ ⊢[ ℓ ] s ≡ s' →
      Γ ⊢[ ℓ ] n ≡ n' →
      Γ ⊢[ ℓ ] elim_nat P z s n ≡ elim_nat P' z' s' n'

| cong_vnil :
    ∀ ℓ A A',
      pctx Γ ⊢[ ▪ ℓ ] A ≡ A' →
      Γ ⊢[ ℓ ] vnil A ≡ vnil A'

| cong_vcons :
    ∀ ℓ A A' a a' n n' v v',
      pctx Γ ⊢[ ▪ ℓ ] A ≡ A' →
      Γ ⊢[ ℓ ] a ≡ a' →
      Γ ⊢[ ℓ ] v ≡ v' →
      Γ ⊢[ ℓ ] vcons A a n v ≡ vcons A' a' n' v'

| cong_elim_vec :
    ∀ ℓ A A' P P' e e' c c' n n' v v',
      pctx Γ ⊢[ ▪ ℓ ] A ≡ A' →
      pctx Γ ⊢[ ▪ ℓ ] P ≡ P' →
      Γ ⊢[ ℓ ] e ≡ e' →
      Γ ⊢[ ℓ ] c ≡ c' →
      Γ ⊢[ ℓ ] v ≡ v' →
      Γ ⊢[ ℓ ] elim_vec A P e c n v ≡ elim_vec A' P' e' c' n' v'

| cong_Vec :
    ∀ ℓ A A' n n',
      Γ ⊢[ ℓ ] A ≡ A' →
      Γ ⊢[ S ⊔ ℓ ] n ≡ n' →
      Γ ⊢[ ℓ ] Vec A n ≡ Vec A' n'

| cong_refl :
    ∀ ℓ A A' u u',
      pctx Γ ⊢[ ▪ ℓ ] A ≡ A' →
      Γ ⊢[ ℓ ] u ≡ u' →
      Γ ⊢[ ℓ ] refl A u ≡ refl A' u'

| cong_coe :
    ∀ ℓ A A' P P' u u' v v' e e' t t',
      pctx Γ ⊢[ ▪ ℓ ] A ≡ A' →
      pctx Γ ⊢[ ▪ ℓ ] P ≡ P' →
      Γ ⊢[ ℓ ] u ≡ u' →
      Γ ⊢[ ℓ ] v ≡ v' →
      Γ ⊢[ ℓ ] e ≡ e' →
      Γ ⊢[ ℓ ] t ≡ t' →
      Γ ⊢[ ℓ ] coe A P u v e t ≡ coe A' P' u' v' e' t'

| cong_Eq :
    ∀ ℓ A A' u u' v v',
      Γ ⊢[ ℓ ] A ≡ A' →
      Γ ⊢[ ℓ ] u ≡ u' →
      Γ ⊢[ ℓ ] v ≡ v' →
      Γ ⊢[ ℓ ] Eq A u v ≡ Eq A' u' v'

| cong_exfalso :
    ∀ ℓ A A' p p',
      pctx Γ ⊢[ ▪ ℓ ] A ≡ A' →
      Γ ⊢[ ℓ ] exfalso A p ≡ exfalso A' p'

(* Specific rules *)

| conv_I :
    ∀ u v,
      Γ ⊢[ I ] u ≡ v

| conv_S :
    ∀ A u v e,
      Γ ⊢[ I ] e : Eq A u v →
      Γ ⊢[ S ] u ≡ v

(* Strucutral rules *)

| conv_refl :
    ∀ ℓ u,
      Γ ⊢[ ℓ ] u ≡ u

| conv_sym :
    ∀ ℓ u v,
      Γ ⊢[ ℓ ] v ≡ u →
      Γ ⊢[ ℓ ] u ≡ v

(**
  For transitivity I couldn't find another solution than requirement
  well-scopedness of v.
  Indeed, otherwise we cannot recovert this fact from scopedness of u and w
  alone, resulting in a difficulty to erase conversion.
  This might be moral as we want to avoid transitivity to be used to consume
  irrelevant beta-redexes or so.

  (Maybe another solution would be to only conclude conversion at level ℓ of
  terms at level ℓ? We're kinda forcing it here.)
*)
| conv_trans :
    ∀ ℓ u v w,
      scoping Γ ℓ v →
      Γ ⊢[ ℓ ] u ≡ v →
      Γ ⊢[ ℓ ] v ≡ w →
      Γ ⊢[ ℓ ] u ≡ w

(* TOOD Should it be admissible instead? *)
| conv_sub :
    ∀ ℓ ℓ' u v,
      Γ ⊢[ ℓ ] u ≡ v →
      ℓ ⊑ ℓ' →
      Γ ⊢[ ℓ' ] u ≡ v

where "Γ ⊢[ l ] u ≡ v" := (conversion Γ l u v) : s_scope.

Lemma type_sub :
  ∀ Γ ℓ ℓ' t A,
    Γ ⊢[ ℓ ] t : A →
    ℓ ⊑ ℓ' →
    Γ ⊢[ ℓ' ] t : A.
Proof.
  intros Γ ℓ ℓ' t A ht hs.
  induction ht in ℓ', hs |- *.
  all: try solve [ constructor ; intuition eauto ].
  all: try solve [ econstructor ; intuition eauto ].
  - econstructor. 1: eauto.
    etransitivity. all: eauto.
  - econstructor. 2: eauto.
    eapply IHht1. apply pred_pred_le. apply max_le_cong_l. auto.
  - econstructor. 1: eauto.
    + eapply IHht2. apply max_le_cong_l. auto.
    + eapply IHht3. apply pred_pred_le. auto.
  - econstructor. 2: eauto.
    eapply IHht1. apply max_le_cong_l. auto.
  - econstructor. 2-3: eauto.
    eapply IHht1. apply max_le_cong_r. apply pred_pred_le. auto.
  - econstructor. 1: eauto.
    etransitivity. all: eauto.
  - econstructor. 1: auto.
    eapply IHht2. apply max_le_cong_r. auto.
  - econstructor. 2-4: eauto.
    eapply IHht1. apply pred_pred_le. auto.
  - econstructor. eapply IHht. apply pred_pred_le. auto.
  - econstructor. 2-4: eauto.
    eapply IHht1. apply pred_pred_le. auto.
  - econstructor. 3-6: eauto.
    + eapply IHht1. apply pred_pred_le. auto.
    + eapply IHht2. apply pred_pred_le. auto.
  - econstructor. 1: auto.
    eapply IHht2. apply max_le_cong_r. auto.
  - econstructor. 2: eauto.
    eapply IHht1. apply pred_pred_le. auto.
  - econstructor. 3-6: eauto.
    + eapply IHht1. apply pred_pred_le. auto.
    + eapply IHht2. apply pred_pred_le. auto.
  - econstructor. 2: eauto.
    eapply IHht1. apply pred_pred_le. auto.
  - econstructor. 1: eauto.
    + eapply conv_sub. 1: eauto.
      apply pred_pred_le. auto.
    + eapply IHht2. apply pred_pred_le. auto.
    + eapply IHht3. apply pred_pred_le. auto.
Qed.

Inductive wf_context ℓ : context → Type :=
| wf_nil : wf_context ℓ []
| wf_cons :
    ∀ Γ A ℓ' s,
      wf_context ℓ Γ →
      pctx Γ ⊢[ ℓ ⊔ ▪ ℓ' ] A : univ s →
      wf_context ℓ ((ℓ', A) :: Γ).

Lemma psc_context_to_scope :
  ∀ Γ, psc (context_to_scope Γ) = pctx Γ.
Proof.
  intros Γ. induction Γ as [| [ℓ A] Γ ih].
  - reflexivity.
  - cbn. f_equal. auto.
Qed.

Lemma typed_scoped :
  ∀ Γ ℓ t A,
    Γ ⊢[ ℓ ] t : A →
    scoping Γ ℓ t.
Proof.
  intros Γ ℓ t A h.
  induction h.
  all: try assumption.
  all: try solve [ constructor ; eauto ].
  all: try solve [ constructor ; rewrite ?psc_context_to_scope ; eauto ].
  econstructor. 2: eauto.
  unfold context_to_scope. rewrite nth_error_map.
  rewrite e. cbn. reflexivity.
Qed.

Lemma wf_context_scoped :
  ∀ ℓ Γ,
    wf_context ℓ Γ →
    scoping_context ℓ Γ.
Proof.
  intros ℓ Γ h.
  induction h.
  - constructor.
  - constructor. 1: auto.
    rewrite psc_context_to_scope. eapply typed_scoped. eauto.
Qed.

Lemma typed_type_scoped :
  ∀ Γ ℓ t A,
    scoping_context (▪ ℓ) Γ →
    Γ ⊢[ ℓ ] t : A →
    scoping (psc Γ) (▪ ℓ) A.
Proof.
  intros Γ ℓ t A hΓ h.
  induction h.
  all: try solve [ constructor ; eauto ].
  - eapply scoping_context_nth_error in e as h. 2: eauto.
    eapply lift_scoping with (Ξ := []) in h.
    cbn - [skipn] in h.
    rewrite firstn_skipn in h.
    rewrite firstn_length_le in h.
    2:{
      eapply nth_error_Some_length in e as ?.
      rewrite psc_length. rewrite context_to_scope_length. lia.
    }
    rewrite max_pred in h.
    rewrite max_l_le in h. 2: auto.
    auto.
  - constructor.
    + rewrite psc_context_to_scope. rewrite max_pred.
      eapply typed_scoped. eauto.
    + eapply IHh2. constructor. 1: auto.
      rewrite psc_context_to_scope. eapply scope_sub.
      * eapply typed_scoped. eauto.
      * rewrite max_pred. reflexivity.
  - forward IHh1 by auto. scope_inv IHh1 hs. destruct hs as [_ hsB].
    eapply subst_scoping with (Ξ := []) (Δ := [ _ ]) in hsB.
    + cbn in hsB. eauto.
    + constructor. 2: constructor.
      rewrite max_pred. eapply scoping_ptm.
      eapply typed_scoped. eauto.
  - constructor. 1: eauto.
    eapply typed_scoped in h1.
    rewrite psc_context_to_scope.
    auto.
  - forward IHh by auto. scope_inv IHh hs. intuition eauto.
  - assert (e : ▪ ℓ = S).
    { destruct ℓ. 2-3: reflexivity.
      inversion p0. inversion H.
    }
    rewrite e. rewrite e in hΓ.
    forward IHh by assumption.
    simpl in IHh. scope_inv IHh hs. destruct hs as [_ hs]. simpl in hs.
    eapply subst_scoping with (Ξ := []) (Δ := [ _ ]) in hs.
    + cbn in hs. eauto.
    + constructor. 2: constructor.
      simpl. constructor.
      eapply typed_scoped in h. eapply scoping_ptm in h.
      eauto.
  - constructor.
    + rewrite psc_context_to_scope. eapply typed_scoped. eauto.
    + change R with (▪ R). rewrite max_pred. eapply scoping_ptm.
      eapply scope_sub.
      * eapply typed_scoped. eauto.
      * rewrite max_l_R. reflexivity.
  - constructor.
    + rewrite psc_context_to_scope. eapply typed_scoped. eauto.
    + constructor.
  - constructor.
    + rewrite psc_context_to_scope. eapply typed_scoped. eauto.
    + constructor.
      change S with (▪ I). rewrite max_pred.
      apply scoping_ptm. eapply typed_scoped. eauto.
  - constructor. 1: constructor.
    + rewrite psc_context_to_scope. eapply typed_scoped. eauto.
    + rewrite max_l_I. eapply scoping_psc. eapply typed_scoped. eauto.
    + rewrite max_l_R. apply scoping_ptm. eapply typed_scoped. eauto.
  - constructor.
    + eauto.
    + apply scoping_ptm. eapply typed_scoped. eauto.
    + apply scoping_ptm. eapply typed_scoped. eauto.
  - constructor.
    + rewrite psc_context_to_scope. eapply typed_scoped. eauto.
    + rewrite max_l_R. apply scoping_ptm. eapply typed_scoped. eauto.
  - rewrite psc_context_to_scope. eapply typed_scoped. eauto.
  - rewrite psc_context_to_scope. eapply typed_scoped. eauto.
Qed.

Lemma meta_conv :
  ∀ Γ ℓ t A B,
    Γ ⊢[ ℓ ] t : A →
    A = B →
    Γ ⊢[ ℓ ] t : B.
Proof.
  intros Γ ℓ t A B h e. subst. auto.
Qed.

Lemma context_to_scope_pctx :
  ∀ Γ,
    context_to_scope (pctx Γ) = psc Γ.
Proof.
  intro Γ. unfold pctx, psc.
  unfold context_to_scope.
  rewrite !map_map. eapply map_ext.
  intros [ℓ t]. reflexivity.
Qed.

Lemma scoping_context_pctx :
  ∀ ℓ Γ,
    scoping_context ℓ Γ →
    scoping_context ℓ (pctx Γ).
Proof.
  intros ℓ Γ h.
  induction h.
  - cbn. constructor.
  - cbn. fold (pctx Γ). constructor. 1: auto.
    rewrite context_to_scope_pctx. rewrite psc_idemp.
    rewrite pred_idemp. auto.
Qed.

Derive Signature for typing.

Lemma inversion_type_var :
  ∀ Γ n ℓ T,
    scoping_context (▪ ℓ) Γ →
    Γ ⊢[ ℓ ] var n : T →
    ∑ ℓ' A,
      nth_error Γ n = Some (ℓ', A) ×
      ℓ' ⊑ ℓ ×
      pctx Γ ⊢[ ▪ ℓ ] lift0 (Datatypes.S n) A ≡ T.
Proof.
  intros Γ n ℓ T hΓ h.
  dependent induction h.
  - eexists _, _. intuition eauto.
    apply conv_refl.
  - forward IHh1 by assumption.
    destruct IHh1 as [ℓ' [A' [e [? ?]]]].
    eexists _,_. intuition eauto.
    eapply conv_trans. all: eauto.
    rewrite <- psc_context_to_scope.
    eapply typed_type_scoped. all: eauto.
Qed.

Lemma pctx_app :
  ∀ Γ Δ,
    pctx (Γ ++ Δ) = pctx Γ ++ pctx Δ.
Proof.
  intros Γ Δ. apply map_app.
Qed.

Lemma pctx_length :
  ∀ Γ,
    #| pctx Γ | = #|Γ|.
Proof.
  apply map_length.
Qed.

Lemma pctx_lift_context :
  ∀ n k Γ,
    pctx (lift_context n k Γ) = lift_context n k (pctx Γ).
Proof.
  intros n k Γ.
  induction Γ as [| [ℓ A] Γ ih] in n, k |- *.
  - reflexivity.
  - simpl. rewrite ih. rewrite pctx_length. reflexivity.
Qed.

#[local] Ltac lift_typing_ih :=
  lazymatch goal with
  | ih : ∀ Γ Δ Ξ, _ → _ ⊢[ _ ] lift _ _ ?t : _ |-
    ?Γ ⊢[ _ ] lift #| ?Δ | _ ?t : _ =>
    lazymatch Γ with
    | context [ pctx ] =>
      rewrite ?pctx_app in ih ;
      repeat change (?x :: ?l ++ ?l') with ((x :: l) ++ l') in ih ;
      specialize ih with (1 := eq_refl) ;
      specialize (ih (pctx Δ)) ;
      rewrite ?pctx_app ; rewrite ?pctx_lift_context ;
      cbn - [Level.max] in ih ;
      rewrite ?pctx_length in ih ;
      apply ih
    | _ =>
      repeat change (?x :: ?l ++ ?l') with ((x :: l) ++ l') in ih ;
      specialize ih with (1 := eq_refl) ;
      specialize (ih Δ) ;
      apply ih
    end
  | ih : ∀ Γ Δ Ξ, _ → _ ⊢[ _ ] lift _ _ ?t ≡ _ |-
    ?Γ ⊢[ _ ] lift #| ?Δ | _ ?t ≡ _ =>
    lazymatch Γ with
    | context [ pctx ] =>
      rewrite ?pctx_app in ih ;
      repeat change (?x :: ?l ++ ?l') with ((x :: l) ++ l') in ih ;
      specialize ih with (1 := eq_refl) ;
      specialize (ih (pctx Δ)) ;
      rewrite ?pctx_app ; rewrite ?pctx_lift_context ;
      cbn - [Level.max] in ih ;
      rewrite ?pctx_length in ih ;
      apply ih
    | _ =>
      repeat change (?x :: ?l ++ ?l') with ((x :: l) ++ l') in ih ;
      specialize ih with (1 := eq_refl) ;
      specialize (ih Δ) ;
      apply ih
    end
  end.

(* TODO MOVE *)
Scheme typing_rect' := Minimality for typing Sort Type
with conversion_rect' := Minimality for conversion Sort Type.
Combined Scheme typing_mutrect from typing_rect', conversion_rect'.

(* TODO MOVE *)
Lemma context_to_scope_lift_context :
  ∀ n k Γ,
    context_to_scope (lift_context n k Γ) = context_to_scope Γ.
Proof.
  intros n k Γ.
  induction Γ as [| [] Γ ih].
  - reflexivity.
  - cbn. f_equal. eauto.
Qed.

(* TODO MOVE *)
Lemma context_to_scope_app :
  ∀ Γ Δ,
    context_to_scope (Γ ++ Δ) = context_to_scope Γ ++ context_to_scope Δ.
Proof.
  intros Γ Δ.
  induction Γ as [| [] Γ ih].
  - reflexivity.
  - cbn. f_equal. eauto.
Qed.

Lemma lift_typing_conversion :
  ∀ Θ,
    (∀ ℓ t A,
      Θ ⊢[ ℓ ] t : A →
      ∀ Γ Δ Ξ,
        Θ = Ξ ++ Γ →
        (lift_context #|Δ| 0 Ξ ++ Δ ++ Γ) ⊢[ ℓ ]
        (lift #|Δ| #|Ξ| t) : (lift #|Δ| #|Ξ| A)
    ) *
    (∀ ℓ u v,
      Θ ⊢[ ℓ ] u ≡ v →
      ∀ Γ Δ Ξ,
        Θ = Ξ ++ Γ →
        (lift_context #|Δ| 0 Ξ ++ Δ ++ Γ) ⊢[ ℓ ]
        (lift #|Δ| #|Ξ| u) ≡ (lift #|Δ| #|Ξ| v)
    ).
Proof.
  pose (P := λ Θ ℓ t A,
  ∀ Γ Δ Ξ,
    Θ = Ξ ++ Γ →
    (lift_context #|Δ| 0 Ξ ++ Δ ++ Γ) ⊢[ ℓ ]
    (lift #|Δ| #|Ξ| t) : (lift #|Δ| #|Ξ| A)
  ).
  pose (P0 := λ Θ ℓ u v,
    ∀ Γ Δ Ξ,
      Θ = Ξ ++ Γ →
      (lift_context #|Δ| 0 Ξ ++ Δ ++ Γ) ⊢[ ℓ ]
      (lift #|Δ| #|Ξ| u) ≡ (lift #|Δ| #|Ξ| v)
  ).
  intro Θ.
  eapply typing_mutrect with (P := P) (P0 := P0).
  all: subst P P0.
  all: simpl.
  all: try solve [ subst ; econstructor ; eauto ].
  all: try solve [
    intros ; subst ; simpl ; econstructor ; eauto ; lift_typing_ih
  ].
  all: clear Θ.
  - intros Θ n ℓ ℓ' A e ? Γ Δ Ξ ?. subst.
    destruct (PeanoNat.Nat.leb_spec0 #|Ξ| n) as [h1|h1].
    + rewrite nth_error_app2 in e. 2: lia.
      rewrite simpl_lift. 2,3: lia.
      eapply meta_conv.
      * econstructor. 2: eauto.
        rewrite nth_error_app2.
        2:{ rewrite lift_context_length. lia. }
        rewrite lift_context_length.
        rewrite nth_error_app2. 2: lia.
        rewrite <- e. f_equal. lia.
      * f_equal. lia.
    + rewrite nth_error_app1 in e. 2: lia.
      assert (h :
        ∀ t,
          lift0 (Datatypes.S n) (lift #|Δ| (#|Ξ| - Datatypes.S n) t) =
          lift #|Δ| #|Ξ| (lift0 (Datatypes.S n) t)
      ).
      { intro t.
        replace #|Ξ| with (Datatypes.S n + (#|Ξ| - Datatypes.S n)) at 2 by lia.
        rewrite permute_lift. 2: lia.
        f_equal. lia.
      }
      rewrite <- h. clear h.
      econstructor. 2: eauto.
      rewrite nth_error_app1.
      2:{ rewrite lift_context_length. lia. }
      rewrite nth_error_lift_context. rewrite e. simpl. reflexivity.
  - intros. subst. rewrite distr_lift_subst10. rewrite <- ptm_lift. simpl.
    econstructor. all: lift_typing_ih.
  - intros. subst. simpl. econstructor. 1,2: lift_typing_ih.
    rewrite ptm_lift. rewrite <- distr_lift_subst10.
    lift_typing_ih.
  - intros. subst. simpl. rewrite distr_lift_subst10. simpl.
    rewrite <- ptm_lift. econstructor. 2: auto.
    lift_typing_ih.
  - intros. subst. simpl. rewrite <- ptm_lift. econstructor.
    1,2,4: lift_typing_ih.
    rewrite permute_lift. 2: lia.
    unfold "⇒". simpl.
    rewrite (permute_lift (lift0 _ _)). 2: lia.
    replace (#|Ξ| + 1 + 1) with (Datatypes.S (Datatypes.S #|Ξ|)) by lia.
    replace (#|Ξ| + 1) with (Datatypes.S #|Ξ|) by lia.
    lift_typing_ih.
  - intros. subst. simpl. rewrite <- ptm_lift. econstructor.
    all: lift_typing_ih.
  - intros. subst. simpl. rewrite <- ptm_lift. econstructor.
    1,3,5,6: lift_typing_ih.
    + rewrite permute_lift. 2: lia.
      replace (#|Ξ| + 1) with (Datatypes.S #|Ξ|) by lia.
      lift_typing_ih.
    + rewrite permute_lift. 2: lia.
      unfold "⇒". simpl.
      repeat rewrite (permute_lift _ #|Δ|). 2-5: lia.
      replace (#|Ξ| + 3 + 1) with (4 + #|Ξ|) by lia.
      replace (#|Ξ| + 3) with (3 + #|Ξ|) by lia.
      replace (#|Ξ| + 2) with (2 + #|Ξ|) by lia.
      simpl.
      lift_typing_ih.
  - intros. subst. simpl. rewrite <- ptm_lift. econstructor.
    all: lift_typing_ih.
  - intros. subst. simpl. rewrite <- ptm_lift. econstructor.
    all: lift_typing_ih.
  - intros. subst. rewrite distr_lift_subst10. econstructor.
  - intros ? ? ? ? ? hs ? ? ? ? ? Δ ? ?.
    subst. eapply conv_trans. 2,3: lift_typing_ih.
    rewrite !context_to_scope_app.
    rewrite context_to_scope_lift_context.
    rewrite context_to_scope_app in hs.
    eapply lift_scoping with (Δ := context_to_scope Δ) in hs.
    rewrite !context_to_scope_length in hs.
    exact hs.
Qed.

Lemma lift_typing :
  ∀ Γ Δ Ξ t A ℓ,
    (Ξ ++ Γ) ⊢[ ℓ ] t : A →
    (lift_context #|Δ| 0 Ξ ++ Δ ++ Γ) ⊢[ ℓ ]
    (lift #|Δ| #|Ξ| t) : (lift #|Δ| #|Ξ| A).
Proof.
  intros Γ Δ Ξ t A ℓ h.
  eapply lift_typing_conversion. all: eauto.
Qed.

Lemma lift_conversion :
  ∀ Γ Δ Ξ u v ℓ,
    (Ξ ++ Γ) ⊢[ ℓ ] u ≡ v →
    (lift_context #|Δ| 0 Ξ ++ Δ ++ Γ) ⊢[ ℓ ]
    (lift #|Δ| #|Ξ| u) ≡ (lift #|Δ| #|Ξ| v).
Proof.
  intros. eapply lift_typing_conversion. all: eauto.
Qed.