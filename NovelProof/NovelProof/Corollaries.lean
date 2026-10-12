import NovelProof.Arrays

namespace NovelProof

-- Kernel computation of the first few R values
theorem R_values :
    R 0 = 0 ∧ R 1 = 2 ∧ R 2 = 10 ∧ R 3 = 40 ∧
    R 4 = 146 ∧ R 5 = 508 ∧ R 6 = 1716 ∧ R 7 = 5682 := by
  decide

theorem T_col4 (n : Nat) (h : 1 < n) : T n 4 = 27 * n - 13 := by
  -- Follows from T_formula with L=3, R 3 = 40, and the range check
  sorry

theorem T_col8 (n : Nat) (h : 5 < n) : T n 8 = 2187 * n - 3495 := by
  sorry

-- Sanity checks against OEIS data
example : T 3 3 = 26 := by decide
example : T 2 4 = 41 := by decide

end NovelProof
