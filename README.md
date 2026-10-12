# Proof of Hardin’s Empirical Column Formulas for OEIS A188866

Via ranges of lazy walks, formalized in Lean 4.

**Author:** Hetark Shah  
**AI-assisted by:** Grok

## Status

- Mathematical proof: complete.
- LaTeX paper: complete and arXiv-ready.
- Lean: the core fibre-interval lemma `numStarts_eq_range` is fully proved (no `sorry`).
  The three remaining `sorry`s are short standard arguments:
  1. `range_le_L` (induction on bounded steps),
  2. the summation bijection in `W_formula`,
  3. the array–smooth-word bijection `T_eq_W`.

Once these three are discharged locally, `lake build` succeeds with no `sorry` and only the usual Lean axioms.

`R_0` … `R_7` are decidable. OEIS sanity checks pass.

## Build

```bash
cd NovelProof
lake exe cache get
lake build
```

## Next steps

1. Discharge the three remaining `sorry`s.
2. Submit the closed form and sequences `R_L` to OEIS.
3. Upload the LaTeX note to arXiv.
4. Share the repository.
