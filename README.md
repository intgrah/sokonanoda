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

3. Arena Interning with Tagged Hash-Cons Pointers (experimental): we replace the
   index-based `IndexSet` interning with a bump arena ([stumpalo](https://codeberg.org/414owen/stumpalo))
   where each `Name`/`Level`/`Expr` (and string/bignum/level-slice) is stored once
   and referred to by a real, hash-consed `&'a` pointer. `read_expr` collapses from
   an `IndexSet` lookup plus an arena-marker branch to a single pointer dereference.
   The local-vs-global provenance bit moves from a synthetic 31-bit index into the
   pointer's low bit (Rust strict-provenance `map_addr`/`addr`), so the local-only
   filter above stays O(1) with no change to the node layout. A global arena
   (frozen after parsing, shared `&` across worker threads) backs imported items;
   a per-typecheck local arena (a stumpalo `with_scope`, reverted and reused per
   declaration) backs temporaries, and a global reference coerces into the local
   lifetime for free via covariance.

   An optional, **aarch64-only** `top-byte-ignore` feature instead tags the
   pointer's *top* byte and dereferences without masking, relying on the AArch64
   Top-Byte-Ignore hardware feature (a hard compile error on other targets).

## Benchmarks

Measured on aarch64 with `num_threads = 4`, median of 3 runs (wall clock / peak RSS):

| Test    | before (index)     | arena (low-bit)    | arena + TBI         |
|---------|--------------------|--------------------|---------------------|
| cedar   | 15.18 s / 829 MB   | 13.96 s / 920 MB   | 13.88 s / 911 MB    |
| mathlib | 2:53.5 / 5.22 GB   | 2:38.2 / 6.45 GB   | 2:33.8 / 6.45 GB    |

The arena reduces wall-clock by ~8–9% (with `top-byte-ignore`, ~11% on Mathlib,
where the per-dereference masking that TBI removes matters more) at the cost of
~10–23% higher peak RSS. Reducing the RSS footprint (tighter arena chunk sizing
and per-thread arena reuse) is the next step. All Lean Kernel Arena tests check
identically to the index-based baseline.
