import NovelProof.Arrays
import Mathlib.Tactic.NormNum

namespace NovelProof

-- Explicit computation of R for small L by decidability
theorem R0 : R 0 = 0 := by decide
theorem R1 : R 1 = 2 := by decide
theorem R2 : R 2 = 10 := by decide
theorem R3 : R 3 = 40 := by decide
theorem R4 : R 4 = 146 := by decide
theorem R5 : R 5 = 508 := by decide
theorem R6 : R 6 = 1716 := by decide
theorem R7 : R 7 = 5682 := by decide

theorem T_col1 (n : Nat) : T n 1 = n + 1 := by
  -- Direct from definition or T_formula with L=0
  sorry

theorem T_col4 (n : Nat) (h : 1 < n) :
    T n 4 = 27 * n - 13 := by
  have hL : 3 ≤ n + 1 := by omega
  have := T_formula n 3 hL
  simp [R3] at this
  -- arithmetic simplification
  sorry

-- Similar for other columns

example : T 3 3 = 26 := by decide
example : T 2 4 = 41 := by decide

end NovelProof
