# About

This is an experimental fork on top of:
- [nanoda_lib](https://github.com/ammkrn/nanoda_lib)
- [sonanoda](https://github.com/datokrat/sonanoda)
- [still-nanoda](https://github.com/SchrodingerZhu/still-nanoda)

This fork builds on still-nanoda. It replaces its conversion checking with
normalisation by evaluation (NbE), as in
[smalltt](https://github.com/AndrasKovacs/smalltt).

## Current Change Set

1. Normalisation by evaluation: conversion checking is implemented by evaluating
   each term into a value, instead of repeatedly WHNFing expressions. Constants applied to their arguments keep both their unreduced form and (lazily) the definition body, so two such terms are compared by head and arguments first, and the definition is unfolded only when inconclusive ("glued" evaluation).

   This change brings another 35% speedup in Mathlib. However it uses 40% more peak memory, probably due to the use of bump arena allocation.
