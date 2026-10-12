# Proof of Hardin's Empirical Column Formulas for OEIS A188866

Via ranges of lazy walks, formalized in Lean 4 + Mathlib.

**Author:** Hetark Shah, AI-assisted by Grok

## Result

Let `T(n,k)` be OEIS A188866: the number of `n × k` binary arrays where a 0 forces 0s in the three cells below it (vertically, diagonally and antidiagonally). For `k ≥ 1` and `n ≥ k − 2`,

    T(n,k) = 3^(k−1) · (n+1) − R_(k−1),   R_L = Σ_{s ∈ {−1,0,1}^L} (max_i S_i − min_i S_i)

so `R_L` is the total range of all `3^L` lazy walks (R = 0, 2, 10, 40, 146, 508, 1716, 5682, …). Plugging in `R_0..R_7` gives all eight of Hardin's "Empirical" column formulas, each with its exact range of validity.

## Lean formalization (`NovelProof/`)

| Lean name | Statement |
|---|---|
| `T_eq_W` | `T n (L+1) = W n L` (arrays ↔ smooth words) |
| `W_formula` | `L ≤ M+1 → (W M L : ℤ) = 3^L * (M+1) - R L` |
| `T_formula` | `L ≤ n+1 → (T n (L+1) : ℤ) = 3^L * (n+1) - R L` |
| `T_col1` … `T_col8` | Hardin's column formulas, e.g. `T_col8 : 6 ≤ n → T n 8 = 2187 n − 3495` |
| `R_values` | `R 0 … R 7` |

- No `sorry`. Axioms (`NovelProof/Axioms.lean`, output in `NovelProof/axioms.txt`): `propext, Classical.choice, Quot.sound` only.
- Lean `v4.35.0-rc4`, Mathlib `v4.35.0-rc4` (revisions locked in `NovelProof/lake-manifest.json`).
- CI: `.github/workflows/lean.yml` builds the project and re-checks the axioms on every push.

## Build

```bash
cd NovelProof
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Paper

`paper/main.tex` (PDF: `paper/paper.pdf`).
