# Proof of Hardin’s Empirical Column Formulas for OEIS A188866

Via ranges of lazy walks, formalized in Lean 4.

**Author:** Hetark Shah  
**AI-assisted by:** Grok

## Status

- Mathematical proof: complete.
- LaTeX paper: complete and arXiv-ready.
- Lean: `numStarts_eq_range` fully proved. `range_le_L` has complete induction skeleton. Two short bijections remain as `sorry`.

The development is ready for the final two maps to be written out, after which it will be fully machine-checked.

## Build

```bash
cd NovelProof
lake exe cache get
lake build
```

## Next steps

1. Close the two remaining bijections.
2. OEIS.
3. arXiv.
4. Share.
