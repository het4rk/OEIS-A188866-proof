import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Finset.Basic
import Mathlib.Tactic

namespace NovelProof

def Steps : Finset ℤ := {-1, 0, 1}
lemma Steps_card : Steps.card = 3 := by decide

def StepSeqs (L : ℕ) : Finset (Fin L → ℤ) := Fintype.piFinset (fun _ => Steps)
lemma card_StepSeqs (L : ℕ) : (StepSeqs L).card = 3 ^ L := by
  simp [StepSeqs, Fintype.card_piFinset, Steps_card]

def partialSums {L : ℕ} (s : Fin L → ℤ) : Fin (L + 1) → ℤ
  | ⟨0, _⟩ => 0
  | ⟨i + 1, h⟩ => partialSums s ⟨i, Nat.lt_of_succ_lt_succ h⟩ + s ⟨i, Nat.lt_of_succ_lt_succ h⟩

def rangeOf {L : ℕ} (s : Fin L → ℤ) : ℤ :=
  let ps := Finset.image (partialSums s) Finset.univ
  ps.max'.getD 0 - ps.min'.getD 0

def R (L : ℕ) : ℤ := ∑ s ∈ StepSeqs L, rangeOf s

def isSmooth {M L : ℕ} (t : Fin (L + 1) → Fin (M + 1)) : Prop :=
  ∀ i : Fin L, |(t i.castSucc).val - (t i.succ).val| ≤ 1

def W (M L : ℕ) : ℕ := (Finset.univ.filter (isSmooth (M:=M) (L:=L))).card

def numStarts {L : ℕ} (s : Fin L → ℤ) (M : ℕ) : ℕ :=
  ((Finset.Icc (0 : ℤ) (M : ℤ)).filter
    (fun x => ∀ i, 0 ≤ x + partialSums s i ∧ x + partialSums s i ≤ (M : ℤ))).card

lemma partialSums_zero {L : ℕ} (s : Fin L → ℤ) : partialSums s ⟨0, by omega⟩ = 0 := rfl

lemma min_le_zero {L : ℕ} (s : Fin L → ℤ) :
    (Finset.image (partialSums s) Finset.univ).min'.getD 0 ≤ 0 := by
  apply Finset.min'_le
  exact ⟨⟨0, by omega⟩, by simp [partialSums]⟩

lemma zero_le_max {L : ℕ} (s : Fin L → ℤ) :
    0 ≤ (Finset.image (partialSums s) Finset.univ).max'.getD 0 := by
  apply Finset.le_max'
  exact ⟨⟨0, by omega⟩, by simp [partialSums]⟩

lemma numStarts_eq_range {L M : ℕ} (s : Fin L → ℤ) (hr : rangeOf s ≤ (M : ℤ) + 1) :
    numStarts s M = (M + 1 : ℕ) - rangeOf s := by
  set ps := Finset.image (partialSums s) Finset.univ
  set m := ps.min'.getD 0
  set Mmax := ps.max'.getD 0
  have hm0 : m ≤ 0 := min_le_zero s
  have hM0 : 0 ≤ Mmax := zero_le_max s
  have hrange : rangeOf s = Mmax - m := rfl
  have hiff (x : ℤ) :
      (∀ i, 0 ≤ x + partialSums s i ∧ x + partialSums s i ≤ (M : ℤ)) ↔
      -m ≤ x ∧ x ≤ (M : ℤ) - Mmax := by
    constructor
    · intro h
      constructor
      · obtain ⟨i, hi⟩ := Finset.min'_mem ps (by simp)
        have := h i
        simp [hi] at this
        omega
      · obtain ⟨i, hi⟩ := Finset.max'_mem ps (by simp)
        have := h i
        simp [hi] at this
        omega
    · intro ⟨h1, h2⟩ i
      have hS : m ≤ partialSums s i ∧ partialSums s i ≤ Mmax := by
        constructor
        · exact Finset.min'_le _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
        · exact Finset.le_max' _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      constructor <;> omega
  have heq : (Finset.Icc (0 : ℤ) (M : ℤ)).filter
      (fun x => ∀ i, 0 ≤ x + partialSums s i ∧ x + partialSums s i ≤ (M : ℤ)) =
      Finset.Icc (-m) ((M : ℤ) - Mmax) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨_, hcond⟩
      exact (hiff x).1 hcond
    · rintro ⟨h1, h2⟩
      have hx : 0 ≤ x ∧ x ≤ (M : ℤ) := by constructor <;> omega
      exact ⟨hx, (hiff x).2 ⟨h1, h2⟩⟩
  have hab : -m ≤ (M : ℤ) - Mmax := by
    have : Mmax - m ≤ (M : ℤ) + 1 := by rwa [← hrange]
    omega
  rw [numStarts, heq, Finset.card_Icc]
  simp [hrange]
  omega

lemma range_le_L {L : ℕ} (s : Fin L → ℤ) (hs : ∀ i, s i ∈ Steps) : rangeOf s ≤ (L : ℤ) := by
  induction L with
  | zero =>
    simp [rangeOf, partialSums]
    omega
  | succ L ih =>
    let s' : Fin L → ℤ := fun i => s ⟨i.val, by omega⟩
    have hs' : ∀ i, s' i ∈ Steps := fun i => hs ⟨i.val, by omega⟩
    have ih' := ih s' hs'
    have hstep : |s ⟨L, by omega⟩| ≤ 1 := by
      have := hs ⟨L, by omega⟩
      simp [Steps] at this
      omega
    have : rangeOf s ≤ rangeOf s' + 1 := by
      simp [rangeOf]
      omega
    omega

theorem W_formula (M L : ℕ) (h : L ≤ M + 1) :
    (W M L : ℤ) = 3 ^ L * ((M + 1) : ℤ) - R L := by
  have hbij : (W M L : ℤ) = ∑ s ∈ StepSeqs L, (numStarts s M : ℤ) := by
    sorry
  rw [hbij]
  have hrange : ∀ s ∈ StepSeqs L, rangeOf s ≤ (M : ℤ) + 1 := by
    intro s hs
    have hsteps : ∀ i, s i ∈ Steps := fun i => (Finset.mem_piFinset.mp hs) i
    have := range_le_L s hsteps
    omega
  calc
    ∑ s ∈ StepSeqs L, (numStarts s M : ℤ) = ∑ s ∈ StepSeqs L, ((M + 1 : ℕ) - rangeOf s : ℤ) := by
      apply Finset.sum_congr rfl
      intro s hs
      simp [numStarts_eq_range s (hrange s hs)]
    _ = ∑ s ∈ StepSeqs L, ((M + 1 : ℤ) - rangeOf s) := by simp
    _ = (StepSeqs L).card * (↑M + 1) - ∑ s ∈ StepSeqs L, rangeOf s := by
      rw [Finset.sum_sub_distrib, Finset.sum_const]
    _ = 3 ^ L * (↑M + 1) - R L := by
      simp [card_StepSeqs, R]

end NovelProof
