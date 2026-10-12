import NovelProof.Words

namespace NovelProof

/-- Literal definition of the A188866 avoidance condition. -/
def Valid {n k : Nat} (a : Fin n → Fin k → Bool) : Prop :=
  ∀ i j, a i j = false →
    (i.val + 1 < n → a ⟨i.val+1⟩ j = false) ∧
    (i.val + 1 < n ∧ j.val + 1 < k → a ⟨i.val+1⟩ ⟨j.val+1⟩ = false) ∧
    (i.val + 1 < n ∧ j.val > 0 → a ⟨i.val+1⟩ ⟨j.val-1⟩ = false)

def T (n k : Nat) : Nat :=
  Finset.card { a : Fin n → Fin k → Bool | Valid a }

theorem T_eq_W (n L : Nat) : T n (L + 1) = W n L := by
  -- Bijection via column heights: each column is a block of 1s followed by 0s,
  -- and the diagonal conditions are equivalent to adjacent heights differing by ≤1.
  sorry

theorem T_formula (n L : Nat) (h : L ≤ n + 1) :
    (T n (L + 1) : ℤ) = 3 ^ L * (n + 1) - R L := by
  rw [T_eq_W]
  exact W_formula n L h

end NovelProof
