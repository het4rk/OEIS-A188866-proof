import NovelProof.Arrays

/-!
# All column formulas of OEIS A188866 (conjectured "Empirical" by R. H. Hardin)

`T n k` counts `n × k` binary arrays avoiding `0 1` vertically, diagonally and
antidiagonally.  OEIS A188866 lists *empirical* formulas for `k = 1, …, 8`;
A188861 is the column `k = 4`.  We prove all of them from `T_formula`.
-/

namespace NovelProof

set_option maxRecDepth 100000 in
lemma R_values : R 0 = 0 ∧ R 1 = 2 ∧ R 2 = 10 ∧ R 3 = 40 ∧ R 4 = 146 ∧ R 5 = 508 ∧
    R 6 = 1716 ∧ R 7 = 5682 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem T_col1 (n : ℕ) : (T n 1 : ℤ) = n + 1 := by
  rw [T_formula (by omega), R_values.1]; ring
theorem T_col2 (n : ℕ) : (T n 2 : ℤ) = 3 * n + 1 := by
  rw [T_formula (by omega), R_values.2.1]; ring
theorem T_col3 (n : ℕ) (h : 1 ≤ n) : (T n 3 : ℤ) = 9 * n - 1 := by
  rw [T_formula (by omega), R_values.2.2.1]; ring
/-- OEIS A188861: `a(n) = 27 n - 13` for `n > 1`. -/
theorem T_col4 (n : ℕ) (h : 2 ≤ n) : (T n 4 : ℤ) = 27 * n - 13 := by
  rw [T_formula (by omega), R_values.2.2.2.1]; ring
theorem T_col5 (n : ℕ) (h : 3 ≤ n) : (T n 5 : ℤ) = 81 * n - 65 := by
  rw [T_formula (by omega), R_values.2.2.2.2.1]; ring
theorem T_col6 (n : ℕ) (h : 4 ≤ n) : (T n 6 : ℤ) = 243 * n - 265 := by
  rw [T_formula (by omega), R_values.2.2.2.2.2.1]; ring
theorem T_col7 (n : ℕ) (h : 5 ≤ n) : (T n 7 : ℤ) = 729 * n - 987 := by
  rw [T_formula (by omega), R_values.2.2.2.2.2.2.1]; ring
theorem T_col8 (n : ℕ) (h : 6 ≤ n) : (T n 8 : ℤ) = 2187 * n - 3495 := by
  rw [T_formula (by omega), R_values.2.2.2.2.2.2.2]; ring

end NovelProof

/-! Sanity checks against the OEIS data by brute force over all arrays. -/
example : NovelProof.T 3 3 = 26 := by decide +kernel
example : NovelProof.T 2 4 = 41 := by decide +kernel
