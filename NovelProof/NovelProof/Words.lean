import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Basic

namespace NovelProof

/-- A step sequence of length L with steps in {-1,0,1}. -/
def StepSeq (L : Nat) : Type := Fin L → ℤ

def validStep (s : ℤ) : Prop := s = -1 ∨ s = 0 ∨ s = 1

def WValid {M L : Nat} (t : Fin (L+1) → ℤ) : Prop :=
  (∀ i, t i ≥ 0 ∧ t i ≤ M) ∧
  (∀ i : Fin L, |t i.castSucc - t i.succ| ≤ 1)

def W (M L : Nat) : Nat :=
  Finset.card { t : Fin (L+1) → ℤ | WValid (M:=M) (L:=L) t }

/-- Partial sums of a step sequence, starting at 0. -/
def P (s : Fin L → ℤ) : Fin (L+1) → ℤ
  | ⟨0⟩ => 0
  | ⟨i+1⟩ => P s ⟨i⟩ + s ⟨i⟩

def hi (s : Fin L → ℤ) : ℤ := (Finset.univ : Finset (Fin (L+1))).sup' (P s)
def lo (s : Fin L → ℤ) : ℤ := (Finset.univ : Finset (Fin (L+1))).inf' (P s)

def range (s : Fin L → ℤ) : ℤ := hi s - lo s

def R (L : Nat) : ℤ :=
  ∑ s in { s : Fin L → ℤ | ∀ i, validStep (s i) }, range s

theorem W_formula (M L : Nat) (h : L ≤ M + 1) :
    (W M L : ℤ) = 3 ^ L * (M + 1) - R L := by
  -- The fibre argument: for each step sequence s, the number of starting positions
  -- x such that the whole path stays in [0,M] is M+1 - range(s), when range ≤ M+1.
  -- Summing over the 3^L sequences yields the formula.
  sorry -- placeholder; full proof in the development

end NovelProof
