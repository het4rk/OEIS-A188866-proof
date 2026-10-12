# Proof of Hardin’s Empirical Column Formulas for OEIS A188866

Via ranges of lazy walks, formalized in Lean 4.

**Author:** Hetark Shah  
**AI-assisted by:** Grok

## Status

- Mathematical proof: complete.
- LaTeX paper: complete and arXiv-ready.
- Lean: denser formalization. `numStarts_eq_range` fully proved. `range_le_L` has complete induction. Two short bijections remain.

Closing the last two `sorry`s finishes the machine-checked proof.

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
