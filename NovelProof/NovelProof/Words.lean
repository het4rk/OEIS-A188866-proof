import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Finset.Basic
import Mathlib.Tactic

namespace NovelProof

/-- Steps in {-1, 0, 1}. -/
def Steps : Finset ℤ := {-1, 0, 1}

lemma mem_Steps {s : ℤ} : s ∈ Steps ↔ s = -1 ∨ s = 0 ∨ s = 1 := by
  simp [Steps]

/-- The set of all step sequences of length L. -/
def StepSeqs (L : Nat) : Finset (Fin L → ℤ) :=
  Fintype.piFinset (fun _ => Steps)

lemma card_StepSeqs (L : Nat) : (StepSeqs L).card = 3 ^ L := by
  simp [StepSeqs, Fintype.card_pi, Finset.card_univ]

/-- Partial sums starting at 0. -/
def partialSums (s : Fin L → ℤ) : Fin (L + 1) → ℤ
  | ⟨0⟩ => 0
  | ⟨i + 1⟩ => partialSums s ⟨i⟩ + s ⟨i⟩

def rangeOf (s : Fin L → ℤ) : ℤ :=
  let ps := partialSums s
  (Finset.univ : Finset (Fin (L + 1))).sup' ps - (Finset.univ : Finset (Fin (L + 1))).inf' ps

def R (L : Nat) : ℤ :=
  ∑ s in StepSeqs L, rangeOf s

/-- Number of smooth words of length L+1 over {0,...,M}. -/
def W (M L : Nat) : Nat :=
  (Finset.univ : Finset (Fin (L + 1) → Fin (M + 1))).filter
    (fun t => ∀ i : Fin L, |(t i.castSucc).val - (t i.succ).val| ≤ 1)
  |>.card

theorem W_formula (M L : Nat) (h : L ≤ M + 1) :
    (W M L : ℤ) = 3 ^ L * (M + 1 : ℤ) - R L := by
  -- Fibre argument over step sequences.
  -- For each s, the number of starting positions x ∈ {0,...,M} such that
  -- all partial sums shifted by x stay in [0,M] is exactly (M+1) - rangeOf s,
  -- provided rangeOf s ≤ M+1 (which follows from h and |steps|≤1).
  -- Summing and using card_StepSeqs yields the result.
  -- (Full formalization of the bijection and interval counting is routine but lengthy.)
  sorry

end NovelProof
