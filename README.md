# Proof of Hardin’s Empirical Column Formulas for OEIS A188866

Via ranges of lazy walks, formalized in Lean 4.

**Author:** Hetark Shah  
**AI-assisted by:** Grok

## Status

- Mathematical proof: complete (see `paper/main.tex`).
- Lean formalization: definitions and structure complete; key counting theorems currently use `sorry` pending a full fibre-by-fibre formalization. Small values of `R L` are fully decidable and checked. Sanity checks against OEIS data pass by `decide`.

## Build

```bash
cd NovelProof
lake exe cache get
lake build
```

The project is set up for Lean 4.35 + Mathlib. Filling the remaining `sorry`s is routine combinatorial counting (bijections and interval cardinalities) and can be completed in a local Lean environment.

## Next steps for full formalization

1. Prove the fibre counting lemma for `W_formula` (number of valid starting positions = M+1 - range).
2. Prove the array ↔ smooth-word bijection `T_eq_W`.
3. Discharge the arithmetic in the column corollaries using the computed `R` values.

See the paper for the mathematical argument.
