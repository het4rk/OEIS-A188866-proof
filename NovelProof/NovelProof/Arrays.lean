import NovelProof.Words

namespace NovelProof

/-- Binary array avoidance condition for A188866. -/
def ValidArray {n k : Nat} (a : Fin n → Fin k → Bool) : Prop :=
  ∀ (i : Fin n) (j : Fin k), a i j = false →
    (∀ i' : Fin n, i.val < i'.val → a i' j = false) ∧
    (∀ i' : Fin n, j' : Fin k, i.val < i'.val → |j'.val - j.val| = 1 → a i' j' = false)

def T (n k : Nat) : Nat :=
  (Finset.univ : Finset (Fin n → Fin k → Bool)).filter ValidArray |>.card

theorem T_eq_W (n L : Nat) : T n (L + 1) = W n L := by
  -- Each valid array has columns that are initial segments of 1s followed by 0s.
  -- The diagonal/antidiagonal conditions are equivalent to adjacent column heights
  -- differing by at most 1. This gives a bijection with smooth words.
  sorry

theorem T_formula (n L : Nat) (h : L ≤ n + 1) :
    (T n (L + 1) : ℤ) = 3 ^ L * (n + 1 : ℤ) - R L := by
  rw [T_eq_W]
  exact W_formula n L h

end NovelProof
