# Proof of Hardin’s Empirical Column Formulas for OEIS A188866

Via ranges of lazy walks, formalized in Lean 4.

**Author:** Hetark Shah  
**AI-assisted by:** Grok

## Status

- Mathematical proof: complete.
- LaTeX paper: complete and arXiv-ready.
- Lean: `numStarts_eq_range` is fully proved. `range_le_L` has a complete induction skeleton. The two bijections remain as short `sorry`s that match the paper.

The development is structured so that closing the last two bijections yields a fully machine-checked proof with no assumptions beyond the usual Lean axioms.

## Build

```bash
cd NovelProof
lake exe cache get
lake build
```

## Next steps

1. Close the two remaining bijections locally.
2. Submit to OEIS.
3. Upload to arXiv.
4. Share the repository.
