(* Reduction for SIRTT *)

From Coq Require Import Utf8 List.
Require Import Util Level SAst SSubst.

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
| ibeta A t u : app I (lam I A t) u ▹ t | [ u ]
| sbeta A t u : app S (lam S A t) u ▹ t | [ u ]
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
  | app I (lam I A t) u => topnorm_acc t (u :: σ)
  | app S (lam S A t) u => topnorm_acc t (u :: σ)
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

(* TODO MOVE *)
Fixpoint appsR (t : term) (l : list term) :=
  match l with
  | u :: l => appsR (app R t u) l
  | [] => t
  end.

Fixpoint apps (t : term) (l : list (level × term)) :=
  match l with
  | (ℓ, u) :: l => apps (app ℓ t u) l
  | [] => t
  end.

(* We can now define proper reduction ↦ *)
(* Note that we do not reduce in irrelevant positions when it can be safely
  determined.
*)

Reserved Notation "u ↦ v" (at level 10).

Inductive red : term → term → Type :=
(* Computation rules *)
| beta :
    ∀ v u A t σ,
      v ▹* lam R A t | σ →
      (app R v u) ↦ ((subst σ 0 t){ 0 := u })

| elim_nat_zero :
    ∀ P z s t σ,
      t ▹* zero | σ →
      (elim_nat P z s t) ↦ z

| elim_nat_succ :
    ∀ P z s t n σ,
      t ▹* succ n | σ →
      (elim_nat P z s t) ↦
      (appsR s [ subst σ 0 n ; elim_nat P z s (subst σ 0 n) ])

| elim_vec_vnil :
    ∀ A P e c n t B σ,
      t ▹* vnil B | σ →
      (elim_vec A P e c n t) ↦ e

| elim_vec_vcons :
    ∀ A P e c n t B a m v σ,
      t ▹* vcons B a m v | σ →
      (elim_vec A P e c n t) ↦
      (apps c [
        (R, subst σ 0 a) ;
        (I, subst σ 0 m) ;
        (R, subst σ 0 v) ;
        (R, elim_vec A P e c (subst σ 0 m) (subst σ 0 v))
      ])

(* Congruence rules *)
| lam_ty : ∀ l A t A', A ↦ A' → (lam l A t) ↦ (lam l A' t)
| lam_tm : ∀ l A t t', t ↦ t' → (lam l A t) ↦ (lam l A t')

| app_l : ∀ l u v u', u ↦ u' → (app l u v) ↦ (app l u' v)
| app_r : ∀ l u v v', v ↦ v' → (app l u v) ↦ (app l u v')

| Prod_l : ∀ l A B A', A ↦ A' → (Prod l A B) ↦ (Prod l A' B)
| Prod_r : ∀ l A B B', B ↦ B' → (Prod l A B) ↦ (Prod l A B')

| ex_wit : ∀ u p u', u ↦ u' → (ex u p) ↦ (ex u' p)

| wit_arg : ∀ t t', t ↦ t' → (wit t) ↦ (wit t')

| Sum_l : ∀ A P A', A ↦ A' → (Sum A P) ↦ (Sum A' P)

| succ_arg : ∀ t t', t ↦ t' → (succ t) ↦ (succ t')

| elim_nat_p : ∀ P z s t P', P ↦ P' → (elim_nat P z s t) ↦ (elim_nat P' z s t)
| elim_nat_z : ∀ P z s t z', z ↦ z' → (elim_nat P z s t) ↦ (elim_nat P z' s t)
| elim_nat_s : ∀ P z s t s', s ↦ s' → (elim_nat P z s t) ↦ (elim_nat P z s' t)
| elim_nat_t : ∀ P z s t t', t ↦ t' → (elim_nat P z s t) ↦ (elim_nat P z s t')

| vnil_ty : ∀ A A', A ↦ A' → (vnil A) ↦ (vnil A')

| vcons_ty : ∀ A a n v A', A ↦ A' → (vcons A a n v) ↦ (vcons A' a n v)
| vcons_arg : ∀ A a n v a', a ↦ a' → (vcons A a n v) ↦ (vcons A a' n v)
| vcons_nat : ∀ A a n v n', n ↦ n' → (vcons A a n v) ↦ (vcons A a n' v)
| vcons_vec : ∀ A a n v v', v ↦ v' → (vcons A a n v) ↦ (vcons A a n v')

| elim_vec_ty :
    ∀ A P e c m v A',
      A ↦ A' →
      (elim_vec A P e c m v) ↦ (elim_vec A' P e c m v)
| elim_vec_p :
    ∀ A P e c m v P',
      P ↦ P' →
      (elim_vec A P e c m v) ↦ (elim_vec A P' e c m v)
| elim_vec_e :
    ∀ A P e c m v e',
      e ↦ e' →
      (elim_vec A P e c m v) ↦ (elim_vec A P e' c m v)
| elim_vec_c :
    ∀ A P e c m v c',
      c ↦ c' →
      (elim_vec A P e c m v) ↦ (elim_vec A P e c' m v)
| elim_vec_nat :
    ∀ A P e c m v m',
      m ↦ m' →
      (elim_vec A P e c m v) ↦ (elim_vec A P e c m' v)
| elim_vec_vec :
    ∀ A P e c m v v',
      v ↦ v' →
      (elim_vec A P e c m v) ↦ (elim_vec A P e c m v')

| vec_ty : ∀ A n A', A ↦ A' → (vec A n) ↦ (vec A' n)
| vec_nat : ∀ A n n', n ↦ n' → (vec A n) ↦ (vec A n')

where "u ↦ v" := (red u v).