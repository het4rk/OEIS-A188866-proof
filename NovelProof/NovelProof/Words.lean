import Mathlib

open Finset

namespace NovelProof

/-- Words of length `L+1` over `{0,…,M}` whose consecutive letters differ by at most 1. -/
def WValid (M L : ℕ) (t : Fin (L+1) → Fin (M+1)) : Prop :=
  ∀ i : Fin L, |((t i.succ : ℕ) : ℤ) - ((t i.castSucc : ℕ) : ℤ)| ≤ 1

instance (M L : ℕ) : DecidablePred (WValid M L) := fun _ => by unfold WValid; infer_instance

/-- Number of such words. -/
def W (M L : ℕ) : ℕ := (univ.filter (WValid M L)).card

/-- Allowed step sequences. -/
def D (L : ℕ) : Finset (Fin L → ℤ) := Fintype.piFinset fun _ => ({-1, 0, 1} : Finset ℤ)

/-- Partial sums of a step sequence. -/
def P {L : ℕ} (d : Fin L → ℤ) : ℕ → ℤ
  | 0 => 0
  | i+1 => P d i + (if h : i < L then d ⟨i, h⟩ else 0)

lemma rne (L : ℕ) : (range (L+1)).Nonempty := ⟨0, by simp⟩

/-- Maximum of the walk. -/
def hi {L : ℕ} (d : Fin L → ℤ) : ℤ := (range (L+1)).sup' (rne L) (P d)
/-- Minus the minimum of the walk. -/
def lo {L : ℕ} (d : Fin L → ℤ) : ℤ := - (range (L+1)).inf' (rne L) (P d)

/-- Total range `∑ (max - min)` over all `3^L` lazy walks of length `L`. -/
def R (L : ℕ) : ℤ := ∑ d ∈ D L, (hi d + lo d)

def steps {M L : ℕ} (t : Fin (L+1) → Fin (M+1)) : Fin L → ℤ :=
  fun i => ((t i.succ : ℕ) : ℤ) - ((t i.castSucc : ℕ) : ℤ)

lemma P_telescope {M L : ℕ} (t : Fin (L+1) → Fin (M+1)) :
    ∀ i (hi : i < L + 1), ((t ⟨i, hi⟩ : ℕ) : ℤ) = ((t 0 : ℕ) : ℤ) + P (steps t) i := by
  intro i
  induction i with
  | zero => intro h; simp [P]
  | succ i ih =>
    intro h
    have h' : i < L := by omega
    rw [P, ← add_assoc, ← ih (by omega)]
    simp only [h', ↓reduceDIte]
    simp only [steps]
    have e1 : (⟨i, h'⟩ : Fin L).succ = ⟨i+1, h⟩ := rfl
    have e2 : (⟨i, h'⟩ : Fin L).castSucc = ⟨i, by omega⟩ := rfl
    rw [e1, e2]; ring

lemma P_lip {L : ℕ} {d : Fin L → ℤ} (hd : d ∈ D L) :
    ∀ a b, a ≤ b → |P d b - P d a| ≤ (b - a : ℕ) := by
  intro a b hab
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction c with
  | zero => simp
  | succ c ih =>
    have := ih (by omega)
    have hstep : |(if h : a + c < L then d ⟨a + c, h⟩ else 0)| ≤ 1 := by
      split_ifs with h
      · have := (Fintype.mem_piFinset.mp hd) ⟨a+c, h⟩
        simp only [mem_insert, mem_singleton] at this
        rcases this with h | h | h <;> simp [h]
      · simp
    rw [show a + (c+1) = (a + c) + 1 by omega, P]
    calc |P d (a + c) + _ - P d a| = |(P d (a+c) - P d a) + (if h : a + c < L then d ⟨a + c, h⟩ else 0)| := by ring_nf
      _ ≤ |P d (a+c) - P d a| + |(if h : a + c < L then d ⟨a + c, h⟩ else 0)| := abs_add_le _ _
      _ ≤ _ := by
          have e : a + c + 1 - a = c + 1 := by omega
          have e2 : a + c - a = c := by omega
          rw [e2] at this; rw [e]; push_cast; linarith

lemma P_zero {L : ℕ} (d : Fin L → ℤ) : P d 0 = 0 := rfl

lemma hi_nonneg {L : ℕ} (d : Fin L → ℤ) : 0 ≤ hi d :=
  (P_zero d).symm ▸ le_sup' (P d) (by simp : 0 ∈ range (L+1))

lemma lo_nonneg {L : ℕ} (d : Fin L → ℤ) : 0 ≤ lo d := by
  have := inf'_le (P d) (by simp : 0 ∈ range (L+1))
  rw [P_zero] at this; unfold lo; linarith

lemma hi_add_lo_le {L : ℕ} {d : Fin L → ℤ} (hd : d ∈ D L) : hi d + lo d ≤ L := by
  obtain ⟨a, ha, ea⟩ := exists_mem_eq_sup' (rne L) (P d)
  obtain ⟨b, hb, eb⟩ := exists_mem_eq_inf' (rne L) (P d)
  simp only [mem_range] at ha hb
  unfold hi lo; rw [ea, eb]
  rcases le_total a b with h | h
  · have := P_lip hd a b h
    have := neg_abs_le (P d b - P d a)
    push_cast [h] at *; omega
  · have := P_lip hd b a h
    have := le_abs_self (P d a - P d b)
    push_cast [h] at *; omega

/-- Fiber count: words with a fixed step sequence are determined by their first letter. -/
lemma fiber_card {M L : ℕ} (hLM : L ≤ M + 1) {d : Fin L → ℤ} (hd : d ∈ D L) :
    (((univ.filter (WValid M L)).filter (fun t => steps t = d)).card : ℤ)
      = (M : ℤ) + 1 - (hi d + lo d) := by
  have hcard : ((Icc (lo d) ((M:ℤ) - hi d)).card : ℤ) = (M : ℤ) + 1 - (hi d + lo d) := by
    rw [Int.card_Icc]; have := hi_add_lo_le hd; rw [Int.toNat_of_nonneg (by omega)]; ring
  rw [← hcard]
  have hPlo : ∀ i, i < L + 1 → -lo d ≤ P d i := fun i hi => by
    unfold lo; rw [neg_neg]; exact inf'_le _ (mem_range.mpr hi)
  have hPhi : ∀ i, i < L + 1 → P d i ≤ hi d := fun i hi => le_sup' _ (mem_range.mpr hi)
  congr 1
  refine card_bij' (fun t _ => ((t 0 : ℕ) : ℤ))
    (fun x hx => fun i => ⟨(x + P d i).toNat, by
      simp only [mem_Icc] at hx; have := hPhi i i.isLt; omega⟩) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    obtain ⟨-, rfl⟩ := ht
    obtain ⟨a, ha, ea⟩ := exists_mem_eq_sup' (rne L) (P (steps t))
    obtain ⟨b, hb, eb⟩ := exists_mem_eq_inf' (rne L) (P (steps t))
    simp only [mem_range] at ha hb
    have ta := P_telescope t a ha
    have tb := P_telescope t b hb
    have := (t ⟨a, ha⟩).isLt
    have : (0:ℤ) ≤ ((t ⟨b, hb⟩ : ℕ) : ℤ) := by positivity
    simp only [mem_Icc, hi, lo]; rw [ea, eb]; constructor <;> omega
  · intro x hx
    simp only [mem_filter, mem_univ, true_and]
    have hx' := mem_Icc.mp hx
    have hval : ∀ i : Fin (L+1), (((⟨(x + P d i).toNat, by
        have := hPhi i i.isLt; omega⟩ : Fin (M+1)) : ℕ) : ℤ) = x + P d i := by
      intro i; simp only; have := hPlo i i.isLt; rw [Int.toNat_of_nonneg (by omega)]
    have hst : steps (fun i : Fin (L+1) => (⟨(x + P d i).toNat, by
        have := hPhi i i.isLt; omega⟩ : Fin (M+1))) = d := by
      funext i
      simp only [steps]; rw [hval, hval]
      simp only [Fin.val_succ, Fin.val_castSucc, P, i.isLt, ↓reduceDIte]; ring
    refine ⟨?_, hst⟩
    intro i
    have h1 := congrFun hst i
    simp only [steps] at h1
    rw [h1]
    have := (Fintype.mem_piFinset.mp hd) i
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h | h <;> simp [h]
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    obtain ⟨-, rfl⟩ := ht
    funext i; ext; simp only
    rw [← P_telescope t i i.isLt]; simp
  · intro x hx
    simp only [P_zero, add_zero, Fin.val_zero]
    exact Int.toNat_of_nonneg (by have := lo_nonneg d; simp only [mem_Icc] at hx; omega)

lemma steps_mem {M L : ℕ} {t : Fin (L+1) → Fin (M+1)} (ht : WValid M L t) : steps t ∈ D L := by
  refine Fintype.mem_piFinset.mpr fun i => ?_
  have := ht i
  simp only [steps, mem_insert, mem_singleton]
  rw [abs_le] at this; omega

lemma card_D (L : ℕ) : (D L).card = 3 ^ L := by
  simp [D, Fintype.card_piFinset]

/-- **Main counting theorem.** For `L ≤ M`, the number of words of length `L+1`
over `{0,…,M}` with adjacent letters differing by at most one equals `3^L (M+1) - R L`. -/
theorem W_formula {M L : ℕ} (hLM : L ≤ M + 1) : (W M L : ℤ) = 3 ^ L * ((M : ℤ) + 1) - R L := by
  unfold W R
  rw [card_eq_sum_card_fiberwise (f := steps) (t := D L) (fun t ht => steps_mem (mem_filter.mp ht).2)]
  push_cast
  rw [sum_congr rfl fun d hd => fiber_card hLM hd, sum_sub_distrib, sum_const, card_D]
  simp

end NovelProof
