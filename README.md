# About

This is an experimental fork on top of:
- [nanoda_lib](https://github.com/ammkrn/nanoda_lib)
- [sonanoda](https://github.com/datokrat/sonanoda)
- [still-nanoda](https://github.com/SchrodingerZhu/still-nanoda)

It is essentially a testing bed for high-performance typechecking for Lean.

You shouldn't use this for serious purposes.

Currently, it is about 9x faster than the official kernel, measured on mathlib.

Basically, the core conversion algorithm is entirely replaced by something closure-based. There are also some non-theoretical, purely programming optimisations.
