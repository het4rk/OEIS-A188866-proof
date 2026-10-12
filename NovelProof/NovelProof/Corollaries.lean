import NovelProof.Arrays

namespace NovelProof

theorem R_vals :
    R 0 = 0 ∧ R 1 = 2 ∧ R 2 = 10 ∧ R 3 = 40 ∧
    R 4 = 146 ∧ R 5 = 508 ∧ R 6 = 1716 ∧ R 7 = 5682 := by
  decide

example : T 3 3 = 26 := by decide
example : T 2 4 = 41 := by decide

end NovelProof
