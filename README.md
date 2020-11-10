# Shape Irrelevant Reflection in Type Theory

I use coq 8.12.0 and Equations 1.2.3

## File overview

| File | Description |
|------|-------------|
| `Util.v` | Global utility |
| `Level.v` | Relevance levels |
| `SAst.v` | SIRTT AST |
| `SSubst.v` | SIRTT Lifting and substitution |
| `SReduction.v`| Reduction for SIRTT |
| `SScoping.v`| Scoping in SIRTT |
| `SIRTT.v` | All of SIRTT in one module for practicality |
| `TAst.v` | MLTT AST |
| `TSubst.v` | MLTT Lifting and substitution |
| `TReduction.v`| Reduction for MLTT |
| `TScoping.v`| Scoping in MLTT |
| `MLTT.v` | All of MLTT in one module for practicality |
| `Erasure.v` | Erasure translation from SIRTT to MLTT |