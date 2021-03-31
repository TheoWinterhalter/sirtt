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

From Coq Require Import Utf8 List.
Require Import Equations.Prop.DepElim.
Require Import Equations.Prop.Classes.
From Equations Require Import Equations.
Require Import Util Level SAst SSubst SReduction SScoping.

Import ListNotations.

Set Default Goal Selector "!".

Definition arrow A B := Prod R A (lift0 1 B).
Notation "A ⇒ B" := (arrow A B) (at level 70, right associativity) : s_scope.

Reserved Notation "Γ ⊢[ l ] t : A"
  (at level 80, l, t, A at next level, format "Γ  ⊢[  l  ]  t  :  A").

Reserved Notation "Γ ⊢[ l ] u ≡ v"
  (at level 80, l, u, v at next level, format "Γ  ⊢[  l  ]  u  ≡  v").

Inductive typing (Γ : context) : level → term → term → Type :=
| type_var :
    ∀ n ℓ A,
      nth_error Γ n = Some (ℓ, A) →
      Γ ⊢[ ℓ ] var n : A

| type_lam :
    ∀ ℓ ℓ' A B t s,
      Γ ⊢[ ℓ ] A : univ s →
      (ℓ', A) :: Γ ⊢[ ℓ ] t : B →
      Γ ⊢[ ℓ ] lam ℓ' A t : Prod ℓ' A B

| type_app :
    ∀ ℓ ℓ' A B u v,
      Γ ⊢[ ℓ ] u : Prod ℓ' A B →
      Γ ⊢[ ℓ ⊔ ℓ' ] v : A →
      Γ ⊢[ ℓ ] app ℓ' u v : B{ 0 := v }

| type_Prod :
    ∀ ℓ ℓ' A B i j,
      Γ ⊢[ ℓ ] A : univ i →
      (▪ ℓ', A) :: Γ ⊢[ ℓ ] B : univ j →
      Γ ⊢[ ℓ ] Prod ℓ' A B : univ (Peano.max i j)

| type_ex :
    ∀ ℓ A P u p,
      Γ ⊢[ ℓ ] u : A →
      Γ ⊢[ I ] p : P{ 0 := u } →
      Γ ⊢[ ℓ ] ex u p : Sum A P

| type_wit :
    ∀ ℓ A P p,
      Γ ⊢[ ℓ ] p : Sum A P →
      Γ ⊢[ ℓ ] wit p : A

| type_prf :
    ∀ A P p,
      Γ ⊢[ I ] p : Sum A P →
      Γ ⊢[ I ] prf p : P{ 0 := wit p }

| type_Sum :
    ∀ ℓ A P i j,
      Γ ⊢[ ℓ ] A : univ i →
      (R, A) :: Γ ⊢[ S ⊔ ℓ ] P : univ j →
      Γ ⊢[ ℓ ] Sum A P : univ (Peano.max i j)

| type_zero :
    ∀ ℓ,
      Γ ⊢[ ℓ ] zero : Nat

| type_succ :
    ∀ ℓ n,
      Γ ⊢[ ℓ ] n : Nat →
      Γ ⊢[ ℓ ] succ n : Nat

| type_elim_nat :
    ∀ ℓ P z s n i,
      Γ ⊢[ ℓ ] P : Nat ⇒ univ i →
      Γ ⊢[ ℓ ] z : app R P zero →
      Γ ⊢[ ℓ ] s :
        Prod R Nat
          (app R (lift0 1 P) (var 0) ⇒ app R (lift0 1 P) (succ (var 0))) →
      Γ ⊢[ ℓ ] n : Nat →
      Γ ⊢[ ℓ ] elim_nat P z s n : app R P n

| type_Nat :
    ∀ ℓ i,
      Γ ⊢[ ℓ ] Nat : univ i

| type_vnil :
    ∀ ℓ A i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] vnil A : Vec A zero

| type_vcons :
    ∀ ℓ A a n v i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] a : A →
      Γ ⊢[ I ] n : Nat →
      Γ ⊢[ ℓ ] v : Vec A n →
      Γ ⊢[ ℓ ] vcons A a n v : Vec A (succ n)

| type_elim_vec :
    ∀ ℓ A P e c n v i j,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] P : Prod I Nat (Vec (lift0 1 A) (var 0) ⇒ univ j) →
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
      Γ ⊢[ ℓ ] elim_vec A P e c n v : app R (app I P n) v

| type_Vec :
    ∀ ℓ A n i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ S ⊔ ℓ ] n : Nat →
      Γ ⊢[ ℓ ] Vec A n : univ i

| type_refl :
    ∀ ℓ A u i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] u : A →
      Γ ⊢[ ℓ ] refl A u : Eq A u u

| type_coe :
    ∀ ℓ A P u v e t i j,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] P : A ⇒ univ j →
      Γ ⊢[ ℓ ] u : A →
      Γ ⊢[ ℓ ] v : A →
      Γ ⊢[ ℓ ] e : Eq A u v →
      Γ ⊢[ ℓ ] t : app R P u →
      Γ ⊢[ ℓ ] coe A P u v e t : app R P v

| type_Eq :
    ∀ ℓ A u v i,
      Γ ⊢[ ℓ ] A : univ i →
      Γ ⊢[ ℓ ] u : A →
      Γ ⊢[ ℓ ] v : A →
      Γ ⊢[ ℓ ] Eq A u v : univ i

| type_exfalso :
    ∀ ℓ A p i,
      Γ ⊢[ ℓ ] A : univ i →
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
    ∀ t A B ℓ s,
      Γ ⊢[ ℓ ] t : A →
      Γ ⊢[ R ] A ≡ B →
      Γ ⊢[ ▪ ℓ ] B : univ s →
      Γ ⊢[ ℓ ] t : B

| type_sub :
    ∀ ℓ ℓ' t A,
      Γ ⊢[ ℓ ] t : A →
      ℓ ⊑ ℓ' →
      Γ ⊢[ ℓ' ] t : A

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
      Γ ⊢[ ℓ ] A ≡ A' →
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
      Γ ⊢[ S ⊔ ℓ ] P ≡ P' →
      Γ ⊢[ ℓ ] Sum A P ≡ Sum A' P'

| cong_succ :
    ∀ ℓ n n',
      Γ ⊢[ ℓ ] n ≡ n' →
      Γ ⊢[ ℓ ] succ n ≡ succ n'

| cong_elim_nat :
    ∀ ℓ P P' z z' s s' n n',
      Γ ⊢[ ℓ ] P ≡ P' →
      Γ ⊢[ ℓ ] z ≡ z' →
      Γ ⊢[ ℓ ] s ≡ s' →
      Γ ⊢[ ℓ ] n ≡ n' →
      Γ ⊢[ ℓ ] elim_nat P z s n ≡ elim_nat P' z' s' n'

| cong_vnil :
    ∀ ℓ A A',
      Γ ⊢[ ℓ ] A ≡ A' →
      Γ ⊢[ ℓ ] vnil A ≡ vnil A'

| cong_vcons :
    ∀ ℓ A A' a a' n n' v v',
      Γ ⊢[ ℓ ] A ≡ A' →
      Γ ⊢[ ℓ ] a ≡ a' →
      Γ ⊢[ ℓ ] v ≡ v' →
      Γ ⊢[ ℓ ] vcons A a n v ≡ vcons A' a' n' v'

| cong_elim_vec :
    ∀ ℓ A A' P P' e e' c c' n n' v v',
      Γ ⊢[ ℓ ] A ≡ A' →
      Γ ⊢[ ℓ ] P ≡ P' →
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
      Γ ⊢[ ℓ ] A ≡ A' →
      Γ ⊢[ ℓ ] u ≡ u' →
      Γ ⊢[ ℓ ] refl A u ≡ refl A' u'

| cong_coe :
    ∀ ℓ A A' P P' u u' v v' e e' t t',
      Γ ⊢[ ℓ ] A ≡ A' →
      Γ ⊢[ ℓ ] P ≡ P' →
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
      Γ ⊢[ ℓ ] A ≡ A' →
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

| conv_sub :
    ∀ ℓ ℓ' u v,
      Γ ⊢[ ℓ ] u ≡ v →
      ℓ ⊑ ℓ' →
      Γ ⊢[ ℓ' ] u ≡ v

where "Γ ⊢[ l ] u ≡ v" := (conversion Γ l u v) : s_scope.

Inductive wf_context : context → Type :=
| wf_nil : wf_context []
| wf_cons :
    ∀ Γ A ℓ s,
      wf_context Γ →
      Γ ⊢[ ▪ ℓ ] A : univ s →
      wf_context ((ℓ, A) :: Γ).

Lemma typed_scoped :
  ∀ Γ ℓ t A,
    Γ ⊢[ ℓ ] t : A →
    scoping Γ ℓ t.
Proof.
  intros Γ ℓ t A h.
  induction h.
  all: try assumption.
  all: try solve [ constructor ; eauto ].
  - constructor. unfold context_to_scope. rewrite nth_error_map.
    rewrite e. cbn. reflexivity.
  - eapply scope_sub. all: eauto.
Qed.