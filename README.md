# Proof of Hardin's empirical column formulas for OEIS A188866

[![Lean build](https://github.com/het4rk/OEIS-A188866-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/OEIS-A188866-proof/actions/workflows/lean.yml)

**Author:** Hetark Shah, AI-assisted by Grok  
**Date:** October 12, 2026

## Result

Let `T(n,k)` be the number of `n × k` binary arrays without the pattern `0 1` vertically, diagonally or antidiagonally ([A188866](https://oeis.org/A188866), R. H. Hardin, 2011). For all `k ≥ 1` and `n ≥ k − 2` we prove `T(n,k) = 3^(k−1)·(n+1) − R_(k−1)`, where `R_L` is the total range (max − min) of all `3^L` lazy walks of length `L` (`R = 0, 2, 10, 40, 146, 508, 1716, 5682, …`). Substituting `R_0..R_7` gives Hardin's eight column formulas (columns 4–8 are A188861–A188865), each on its stated range. The formulas also follow in principle from Howroyd's bijection with smooth words combined with Knopfmacher–Mansour–Munagi–Prodinger (arXiv:0809.0551). What this repo adds is a direct elementary proof and the first machine-checked verification.

## Status

**Complete proof.** All eight OEIS "Empirical" column formulas (k = 1..8), plus a uniform closed form for every column, are proved and machine-checked.

## Theorems and Lean names

| Lean name | Statement |
|---|---|
| `T_eq_W` | `T n (L+1) = W n L` (arrays ↔ smooth words) |
| `fiber_card` | each step sequence has `M+1−range` starting points (non-empty interval) |
| `W_formula` | `L ≤ M+1 → W M L = 3^L·(M+1) − R L` |
| `T_formula` | `L ≤ n+1 → T n (L+1) = 3^L·(n+1) − R L` |
| `R_values` | `R 0 … R 7` |
| `T_col1` … `T_col8` | Hardin's column formulas, e.g. `6 ≤ n → T n 8 = 2187n − 3495` |

No `sorry`, no `native_decide`, no extra hypotheses.

## Build

Toolchain `leanprover/lean4:v4.35.0-rc4`; Mathlib `v4.35.0-rc4` (commit `1f414401f69059aa7eead47b53ee40bd38455eeb`, pinned in `lake-manifest.json`).

```bash
cd NovelProof
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Axioms output

```
'NovelProof.T_eq_W' depends on axioms: [propext, Classical.choice, Quot.sound]
'NovelProof.T_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'NovelProof.T_col4' depends on axioms: [propext, Classical.choice, Quot.sound]
'NovelProof.T_col8' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Machine-check attestation

- [`verification/`](verification/) holds `build-log.txt` (fresh-clone build), `axioms.txt`, and [`VERIFICATION.md`](verification/VERIFICATION.md) with the commit SHA, toolchain, Mathlib commit, reproduce commands, the no-sorry grep result and SHA-256 hashes of the Lean sources.
- [CI](https://github.com/het4rk/OEIS-A188866-proof/actions/workflows/lean.yml) does a clean build on every push, fails on any `sorry`, and checks an axiom whitelist (`scripts/check_axioms.sh`). It uploads the build log and axiom report as the `lean-attestation` artifact and shows them in the job summary.

## Paper

[`paper/main.tex`](paper/main.tex) and [`paper/paper.pdf`](paper/paper.pdf).


## Citation

See [`CITATION.cff`](CITATION.cff):

> Hetark Shah (AI-assisted by Grok), *Proof of Hardin's empirical column formulas for OEIS A188866*, 2026. https://github.com/het4rk/OEIS-A188866-proof

## License

Apache-2.0 (the same as Mathlib). See [`LICENSE`](LICENSE).
