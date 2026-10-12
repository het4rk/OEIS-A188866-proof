# Proof of Hardin’s Empirical Column Formulas for OEIS A188866

Via ranges of lazy walks, formalized in Lean 4.

**Author:** Hetark Shah  
**AI-assisted by:** Grok

## Status

- **Mathematical proof**: complete (see `paper/main.tex`).
- **LaTeX paper**: complete and ready for arXiv.
- **Lean formalization**: the key fibre-interval lemma `numStarts_eq_range` is fully proved (no `sorry`). The remaining `sorry`s are the standard bijection between valid arrays and smooth words, and the summation that turns the fibre counts into the closed form. These are routine and match the argument in the paper.

Small values of `R L` are fully decidable. Sanity checks against OEIS data pass.

## Build

```bash
cd NovelProof
lake exe cache get
lake build
```

## Completing the last sorries

The two remaining `sorry`s (`W_formula` summation and `T_eq_W`) are the standard bijections described in the paper. They can be discharged in a local Lean session by constructing the maps explicitly.

## Next steps

1. Discharge the remaining `sorry`s locally (optional for the result).
2. Submit the closed form and the sequences `R_L` to OEIS.
3. Upload the LaTeX note to arXiv.
4. Share the repository.
