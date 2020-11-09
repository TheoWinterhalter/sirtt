(* Erasure translation from SIRTT to MLTT *)

From Coq Require Import Utf8 List Nat Lia.
Require Import Util SIRTT MLTT.

Import ListNotations.

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
  | SIRTT.Prod l A B =>trans (l :: Γ) B
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

Lemma erase_lift :
  ∀ Γ Δ Ξ t,
    trans (Ξ ++ Δ ++ Γ) (SIRTT.lift #|Δ| #|Ξ| t) =
    MLTT.lift #|scope_trans Δ| #|scope_trans Ξ| (trans (Ξ ++ Γ) t).
Proof.
  intros Γ Δ Ξ t.
  induction t in Γ, Δ, Ξ |- *.
  - cbn. destruct (PeanoNat.Nat.leb_spec #|Ξ| n).
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
        (* Here we have a case where the variable should not exist...
          Hence the discrepancy. Maybe we should return dummy in those cases
          as well?
        *)
        pose proof (scope_trans_firstn_length Ξ n).
        give_up.
      }
      reflexivity.
Abort.

(* Need to figure out how to translate substitutions properly *)
(* Lemma erase_subst :
  ∀ σ k t,
    trans Γ (SIRTT.subst σ k t) = MLTT.subst (map trans σ) k (trans Γ t).
Proof.
  intros σ k t.
  induction t in σ, k |- *.
  - cbn. destruct (PeanoNat.Nat.leb_spec k n).
    + rewrite nth_error_map. destruct nth_error eqn:e.
      * cbn. admit.
      * cbn. rewrite map_length. reflexivity.
    + reflexivity.
  - destruct l.
    + cbn. rewrite ?IHt1, ?IHt2. reflexivity.
    (* + cbn. rewrite ?IHt1, ?IHt2. reflexivity.
    + *)
    (* The translation of variables is most likely wrong.
      It is much more complicated because we remove binders.
      The translation operation should probably take (at least) an integer
      to offset things. But it basically has to do strengthening which is not
      that easy… It feels like it should take a list of the forgotten variables.
      This is not so great, an alternative would be welcome.
      It could also just be the scope (R,I,S,...)
    *)
Abort. *)

Fixpoint erase_toplevel_scope t :=
  match t with
  | SIRTT.lam l A t => [ l ]
  | SIRTT.app l u v => erase_toplevel_scope u
  | _ => []
  end.

Lemma erase_topred_term :
  ∀ Γ u v σ,
    u ▹ v | σ →
    trans Γ u = trans (erase_toplevel_scope u ++ Γ) v.
Proof.
  intros Γ u v σ h.
  induction h.
  all: reflexivity.
Qed.