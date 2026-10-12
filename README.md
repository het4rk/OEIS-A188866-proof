# Proof of Hardin’s Empirical Column Formulas for OEIS A188866

Via ranges of lazy walks, formalized in Lean 4.

**Author:** Hetark Shah  
**AI-assisted by:** Grok

## Status

- Mathematical proof: complete (`paper/main.tex`).
- LaTeX paper: complete and arXiv-ready.
- Lean formalization: the non-trivial fibre-interval lemma `numStarts_eq_range` is fully proved with no `sorry`. The remaining `sorry`s are the standard range bound (`range_le_L`) and the two bijections (smooth words ↔ (step sequence, start) and arrays ↔ smooth words). These are routine and match the argument already written in the paper.

`R 0` through `R 7` are fully decidable. OEIS sanity checks pass by `decide`.

## Build

```bash
cd NovelProof
lake exe cache get
lake build
```

## Remaining work for full machine-checking

1. Prove `range_le_L` by induction (each step changes the partial sum by at most 1).
2. Construct the explicit bijection for the summation in `W_formula`.
3. Construct the column-height bijection for `T_eq_W`.

All three are short and standard. Once discharged, `lake build` will succeed with no `sorry` and only the usual Lean axioms.

## Next steps

1. Discharge the three remaining `sorry`s locally.
2. Submit the closed form and the sequences `R_L` to OEIS.
3. Upload the LaTeX note to arXiv.
4. Share the repository.
