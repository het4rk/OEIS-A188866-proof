# Proof of Hardin’s Empirical Column Formulas for OEIS A188866

Via ranges of lazy walks, formalized in Lean 4.

**Author:** Hetark Shah  
**AI-assisted by:** Grok

## Status

- Mathematical proof: complete.
- LaTeX paper: complete and arXiv-ready.
- Lean formalization: **complete**. Both bijections are closed; `lake build` succeeds with no `sorry` and only the standard Lean axioms.

The uniform closed form \( T(n,k) = 3^{k-1}(n+1) - R_{k-1} \) (for \( n \ge k-2 \)) is now fully machine-checked.

## Build

```bash
cd NovelProof
lake exe cache get
lake build
```

The project uses Lean v4.35.0-rc4 with Mathlib v4.35.0-rc1. Exact dependency revisions are locked in `NovelProof/lake-manifest.json`.

## Next steps

1. Submit the sequences \( R_L \) and the column formulas to OEIS.
2. arXiv.
3. Share.
