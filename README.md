# Proof of Hardin’s Empirical Column Formulas for OEIS A188866

Via ranges of lazy walks, formalized in Lean 4.

**Author:** Hetark Shah  
**AI-assisted by:** Grok

## Abstract

Let \(T(n, k)\) count the \(n \times k\) binary arrays that avoid the pattern 01 vertically, diagonally and antidiagonally. This is OEIS A188866. R. H. Hardin listed eight empirical column formulas that remained marked “Empirical” on OEIS. We prove the uniform closed form

\[
T(n, k) = 3^{k-1}(n + 1) - R_{k-1}\qquad (n \ge k-2),
\]

where \(R_L\) is the total range of all \(3^L\) lazy walks of length \(L\) with steps in \(\{-1,0,1\}\).

The development is machine-checked in Lean 4 + Mathlib.

## Contents

- `paper/` — LaTeX source of the note
- `NovelProof/` — Lean 4 formalization

## Build

```bash
cd NovelProof
lake exe cache get
lake build
```

## License

MIT (code and paper)
