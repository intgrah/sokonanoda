# About

This is an experimental fork on top of:
- [nanoda_lib](https://github.com/ammkrn/nanoda_lib)
- [sonanoda](https://github.com/datokrat/sonanoda)

The purpose of this fork is to evaluate some optimizations related to the costly
interning cache access and other engineering perspectives. The changes are not
intended to change the underlying typechecking logic and we may contribute back
once the evaluation stabilizes.

## Current Change Set

1. Local-First Expr Allocation Check: it appears that the imported expressions
   table is huge such that its lookup becomes costly. We adjusted the order
   of checks to look at local interning cache first to reduce global cache visiting.
   We also adjust the default `IndexSet` API to avoid allow holding an entry
   first and then decide the interning position in a second step. If the expr really
   needs to be allocated locally, this remove one extra lookup. In general, this 
   optimization shows 5% speedup in Cedar and Mathlib.

2. Local-only Expression Filtering: another optimization is to do a filtering
   scan of the expression to avoid global cache lookup if the expression to local-only.
   - `Local/Var` are apparently local-only;
   - Nodes tied to `TcCtx` are also local-only.

   This change brings another 10% speedup in Cedar and Mathlib.
