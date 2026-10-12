import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Finset.Basic
import Mathlib.Tactic

namespace NovelProof

def Steps : Finset ℤ := Finset.insert (-1) (Finset.insert 0 {1})

lemma Steps_card : Steps.card = 3 := by decide

def StepSeqs (L : ℕ) : Finset (Fin L → ℤ) :=
  Fintype.piFinset (fun _ => Steps)

lemma card_StepSeqs (L : ℕ) : (StepSeqs L).card = 3 ^ L := by
  simp [StepSeqs, Fintype.card_piFinset, Steps_card]

def partialSums {L : ℕ} (s : Fin L → ℤ) : Fin (L + 1) → ℤ :=
  fun i => ∑ j : Fin i.val, s ⟨j.val, by omega⟩

def rangeOf {L : ℕ} (s : Fin L → ℤ) : ℤ :=
  let vals := Finset.image (partialSums s) Finset.univ
  (vals.max'.getD 0) - (vals.min'.getD 0)

def R (L : ℕ) : ℤ := ∑ s ∈ StepSeqs L, rangeOf s

def isSmooth {M L : ℕ} (t : Fin (L + 1) → Fin (M + 1)) : Prop :=
  ∀ i : Fin L, Int.natAbs ((t i.castSucc).val : ℤ - (t i.succ).val) ≤ 1

def W (M L : ℕ) : ℕ :=
  Finset.card (Finset.filter (isSmooth (M:=M) (L:=L)) Finset.univ)

/-- Number of integer starting positions that keep the whole path inside [0, M]. -/
def numStarts {L : ℕ} (s : Fin L → ℤ) (M : ℕ) : ℕ :=
  (Finset.Icc (0 : ℤ) M).filter
    (fun x => ∀ i : Fin (L + 1), 0 ≤ x + partialSums s i ∧ x + partialSums s i ≤ M)
  |>.card

lemma numStarts_eq_range {L M : ℕ} (s : Fin L → ℤ) (hr : rangeOf s ≤ M + 1) :
    numStarts s M = (M + 1 : ℕ) - rangeOf s := by
  -- The set of valid starting positions x is a contiguous integer interval
  -- of length (M + 1) - rangeOf s.
  -- Proof: let m = min partialSums, M_ = max partialSums; then range = M_ - m.
  -- x is valid iff -m ≤ x ≤ M - M_, so the length is M - M_ + m + 1 = M + 1 - range.
  sorry

theorem W_formula (M L : ℕ) (h : L ≤ M + 1) :
    (W M L : ℤ) = 3 ^ L * ((M + 1) : ℤ) - R L := by
  -- Every smooth word determines a unique step sequence s and a unique starting height.
  -- The number of smooth words is therefore ∑ s, numStarts s M.
  -- Under h, rangeOf s ≤ L ≤ M + 1 for every s, so numStarts s M = M + 1 - rangeOf s.
  -- Summing over StepSeqs L and using card_StepSeqs yields the formula.
  sorry

end NovelProof
