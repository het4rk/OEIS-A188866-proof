# Verification record

| Item | Value |
|---|---|
| Date | 2026-10-12 |
| Verified commit | `8b0e0356d9ed494ca9b3ca765e8a957cc7e39549` |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc4` |
| Mathlib | `v4.35.0-rc4`, commit `1f414401f69059aa7eead47b53ee40bd38455eeb` |
| Build result | `Build completed successfully` (see [`build-log.txt`](build-log.txt)) |
| Axioms | 4 declarations, all `[propext, Classical.choice, Quot.sound]` (see [`axioms.txt`](axioms.txt)) |
| CI | [![Lean build](https://github.com/het4rk/OEIS-A188866-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/OEIS-A188866-proof/actions/workflows/lean.yml) |

## Reproduce

```bash
git clone https://github.com/het4rk/OEIS-A188866-proof
cd OEIS-A188866-proof
git checkout 8b0e0356d9ed494ca9b3ca765e8a957cc7e39549
cd NovelProof
lake exe cache get
lake build
lake env lean Axioms.lean
grep -rnw sorry NovelProof --include=*.lean   # expect no output
```

## No-sorry check

`grep -rnw sorry NovelProof/NovelProof --include=*.lean` gave no matches (exit code 1), and the build log has no `declaration uses 'sorry'` warnings.

## SHA-256 of the Lean sources (at the verified commit)

```
703a99bd32b3bbe464341f8ae1dee62ad493984a4375f22f823fe17f873c1ffd  ./NovelProof/Axioms.lean
3a08f954368186fc2d3a39bd51f33cfd241491d7fb559bee20737b3efd619756  ./NovelProof/NovelProof.lean
f227c38258838e73721833a5e42b86665ea24adc6c99ab97737cdb956aef0f9b  ./NovelProof/NovelProof/Arrays.lean
bd8dc57459336ed8d120af5f68d72dcfa6ae0b89ff461d377b20373f5e687472  ./NovelProof/NovelProof/Corollaries.lean
02a8520650f609d71352e74ebf903d16c2d2e15e7c64c6a46fc787a262700340  ./NovelProof/NovelProof/Words.lean
```

Commits after the verified one change only `verification/` (and the paper PDF). The Lean sources are unchanged, as the hashes above confirm.
