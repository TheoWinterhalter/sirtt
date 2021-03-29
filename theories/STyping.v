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

*)

From Coq Require Import Utf8 List.
Require Import Equations.Prop.DepElim.
Require Import Equations.Prop.Classes.
From Equations Require Import Equations.
Require Import Util Level SAst SSubst SReduction SScoping.

Import ListNotations.

Set Default Goal Selector "!".