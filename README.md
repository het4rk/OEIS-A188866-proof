# Proof of Hardin’s Empirical Column Formulas for OEIS A188866

Via ranges of lazy walks, formalized in Lean 4.

**Author:** Hetark Shah  
**AI-assisted by:** Grok

## Status (October 2026)

- **Mathematical proof**: complete. See `paper/main.tex`.
- **LaTeX paper**: complete and ready for arXiv.
- **Lean formalization**: structure, definitions, and decidable computations of `R 0 … R 7` are complete. The two core counting theorems (`numStarts_eq_range` / `W_formula` and `T_eq_W`) still contain `sorry`. These are routine but require a local Lean + Mathlib session to expand the fibre-interval argument and the array–smooth-word bijection.

## Build

```bash
cd NovelProof
lake exe cache get
lake build
```

## Completing the Lean proofs

The remaining work is:
1. Prove that the valid starting positions form an interval of length `M+1 - rangeOf s`.
2. Sum the fibres and use `card_StepSeqs`.
3. Construct the explicit bijection between valid binary arrays and smooth words of column heights.

Both arguments are written in the paper; they just need to be turned into Lean tactics.

## Next steps for the author

1. Finish the two `sorry`s locally (recommended).
2. Submit the closed form and the sequences `R_L` to OEIS.
3. Upload the LaTeX note to arXiv.
4. Announce the repo on Lean Zulip and SeqFan.
