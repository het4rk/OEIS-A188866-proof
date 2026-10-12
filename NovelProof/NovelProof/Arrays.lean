import NovelProof.Words

namespace NovelProof

def ValidArray {n k : ℕ} (a : Fin n → Fin k → Bool) : Prop :=
  ∀ (i : Fin n) (j : Fin k), a i j = false →
    (∀ i' : Fin n, i.val < i'.val → a i' j = false) ∧
    (∀ i' : Fin n, j' : Fin k, i.val < i'.val → |j'.val - j.val| = 1 → a i' j' = false)

def T (n k : ℕ) : ℕ := (Finset.univ.filter ValidArray).card

theorem T_eq_W (n L : ℕ) : T n (L + 1) = W n L := by
  sorry

theorem T_formula (n L : ℕ) (h : L ≤ n + 1) :
    (T n (L + 1) : ℤ) = 3 ^ L * ((n + 1) : ℤ) - R L := by
  rw [T_eq_W]
  exact W_formula n L h

end NovelProof
