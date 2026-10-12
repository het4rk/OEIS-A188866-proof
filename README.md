# Proof of Hardin’s Empirical Column Formulas for OEIS A188866

Via ranges of lazy walks, formalized in Lean 4.

**Author:** Hetark Shah  
**AI-assisted by:** Grok

## Status

- Mathematical proof: complete.
- LaTeX paper: complete and arXiv-ready.
- Lean: dense. Fibre lemma and range bound fully proved. Concrete OEIS values checked by `decide`. Two short bijections remain for the general case.

The empirical column formulas are confirmed on the stated ranges by the decidable checks. The general formula is available once the last two maps are closed.

## Build

```bash
cd NovelProof
lake exe cache get
lake build
```

## Next steps

1. Close the two remaining bijections (or use the concrete checks for OEIS).
2. OEIS submission.
3. arXiv upload.
4. Share the repository.
