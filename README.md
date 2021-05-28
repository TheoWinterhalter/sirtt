# Shape Irrelevant Reflection in Type Theory

This repo contains a formal definition of SIRTT (shape-irrelevant reflection
type theory) as well as a translation performing erasure of (shape-)irrelevant
information in terms from which we derive strong normalisation and non-confusion
of SIRTT.

## Quick jump

- [Main idea]
- [How to build]
- [File overview]

[Main idea]: #main-idea-of-the-project
[How to build]: #how-to-build
[File overview]: #file-overview

## Main idea of the project

Extensional type theory (ETT) differentiates itself from intensional type
theory (ITT) by featuring the *reflection* rule which turns any proof of
equality into a conversion. This comes at the cost of the loss of decidability
of type checking, but also causes conversion to collapse in an inconsistent
context which in turn undermines the suitability of ETT as a programming
language.

Shape-irrelevant reflection restricts this rule to only apply to
shape-irrelevant arguments. In this formalisation we take two prototypical
examples: vectors and refinement/subset types.
In `vec A n` and `{ x : A | P }`, `n` and `P` are considered shape-irrelevant,
while in `vcons a n v` and `ex t p`, `n` and `p` are irrelevant.
For irrelevant terms, while the reflection rule could apply, we have a stronger
principle that they are simply all convertible.

The main contribution of this repo, besides the definition of the system,
is a notion of erasure to a variant of MLTT with axiom `False`.

```coq
Fixpoint trans (Γ : SIRTT.scope) (t : SIRTT.term) : MLTT.term.
```

It needs to have scoping information to remember which variable is relevant
and must be kept.

The important theorems are
```coq
Lemma erase_red :
  ∀ Γ u v,
    SIRTT.scoping Γ Level.R u →
    (u ↦ v)%s →
    ((trans Γ u) ↦ (trans Γ v))%t.

Lemma erase_conv :
  ∀ (Γ : SIRTT.context) u v,
    SIRTT.scoping Γ Level.R u →
    SIRTT.scoping Γ Level.R v →
    (Γ ⊢[ Level.R ] u ≡ v)%s →
    trans Γ u ≡ trans Γ v.

Lemma erase_typing :
  ∀ Γ t A,
    scoping_context Γ →
    Γ ⊢[ Level.R ] t : A →
    [ Empty ] ;; context_trans Γ ⊢ trans Γ t :
    trans (pctx Γ) A.
```

Assuming that MLTT (even with axiom `False`/`Empty`) is strongly normalising, we
get this property for SIRTT from the third and last theorems above.

```coq
(* From Meta.v *)

Definition MLTT_SN :=
  ∀ Σ Γ t A,
    Σ ;; Γ ⊢ t : A →
    Acc MLTT.scored t.

Definition SIRTT_SN :=
  ∀ Γ t A,
    scoping_context Γ →
    Γ ⊢[ Level.R ] t : A →
    Acc SIRTT.scored t.

Lemma relative_SN :
  MLTT_SN → SIRTT_SN.
```

Assuming that MLTT enjoys non-confusion (for instance that `Nat` is not
convertible to an arrow type) we get this property for SIRTT using the second
one.

Thanks to this, checking in SIRTT can be made to fail when compared types have
different heads, and instead reduce to "a few" equalities to prove, typically
on natural numbers.

## How to build

This project has been tested with Coq 8.13.1 and Equations 1.2.4.
You can install them from `opam`:

```fish
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq.8.13.1 coq-equations.1.2.4+8.13
```

To build the project then, simply run
```fish
make
```

It should output the list of files being compiled and the mention
```coq
Closed under the global context
Closed under the global context
```
corresponding to the fact that the two main theorems of this formalisation
are axiom-free (a fact verified by Coq itself).

## File overview

Relevant files can be found in the `theories` directory.

| File | Description |
|------|-------------|
| `Util.v` | Global utility |
| `Level.v` | Relevance levels |
| `SAst.v` | SIRTT AST |
| `SSubst.v` | SIRTT Lifting and substitution |
| `SReduction.v`| Reduction for SIRTT |
| `SScoping.v`| Scoping in SIRTT |
| `STyping.v`| Typing and conversion in SIRTT |
| `SSR.v`| Subject reduction in SIRTT |
| `SIRTT.v` | All of SIRTT in one module for practicality |
| `TAst.v` | MLTT AST |
| `TSubst.v` | MLTT Lifting and substitution |
| `TReduction.v`| Reduction for MLTT |
| `TScoping.v`| Scoping in MLTT |
| `TTyping.v`| Typing and conversion in MLTT |
| `MLTT.v` | All of MLTT in one module for practicality |
| `Erasure.v` | Erasure translation from SIRTT to MLTT |
| `Meta.v` | Meta-theoretical consequences of the erasure |