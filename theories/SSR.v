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
  induction hr in Γ, hs |- *.
  all: try solve [
    scope_inv hs hs' ; intuition eauto
  ].
  all: try solve [
    scope_inv hs hs' ; constructor ; intuition eauto
  ].
  - scope_inv hs hs'. simpl in hs'. destruct hs' as [hv hu].
    eapply subst_scoping with (Ξ := []).
    2:{ constructor. 2: constructor. eauto. }
    simpl.
    eapply scoping_reveal_subst_k with (Δ := [ _ ]) in hv as h.
    + erewrite e in h. simpl in h. eapply h.
    + simpl. eapply reveal_scope_sound in hv as h.
      rewrite e in h. scope_inv h h'.
      intuition eauto.
  - scope_inv hs hs'. destruct hs' as [hP [hz [hsc ht]]].
    simpl. constructor. 2: simpl. all: constructor.
    all: intuition eauto. 1: simpl.
    all: eapply reveal_scope_sound in ht as h.
    all: rewrite e in h.
    all: scope_inv h h'.
    all: eapply scoping_reveal_subst in ht as h2. 2,4: eauto.
    all: rewrite e in h2. all: auto.
  - scope_inv hs hs'. destruct hs' as [hA [hP [he [hc [hn ht]]]]].
    simpl. constructor. 2: simpl. all: constructor. 2: simpl.
    1: constructor. 2: simpl. 1: constructor. 2: simpl.
    all: try solve [ intuition eauto ].
    all: eapply reveal_scope_sound in ht as hs'.
    all: rewrite e0 in hs'.
    all: scope_inv hs' hs''. all: intuition auto.
    all: eapply scoping_reveal_subst in ht as h ; [| shelve].
    all: rewrite e0 in h. all: eassumption.
    Unshelve. all: eauto.
Qed.