import NovelProof.Words

open Finset

namespace NovelProof

/-- An `n × k` binary array (row `i`, column `j`) *avoids the pattern `0 1`
vertically, diagonally and antidiagonally* if a `0` at `(i,j)` forces `0` at
`(i+1,j-1)`, `(i+1,j)`, `(i+1,j+1)` (whenever those cells exist).  Here `false = 0`. -/
def Valid (n k : ℕ) (a : Fin n → Fin k → Bool) : Prop :=
  ∀ (i i' : Fin n) (j j' : Fin k), (i' : ℕ) = i + 1 → (j : ℕ) ≤ j' + 1 → (j' : ℕ) ≤ j + 1 →
    a i j = false → a i' j' = false

instance (n k : ℕ) : DecidablePred (Valid n k) := fun _ => by unfold Valid; infer_instance

/-- `T n k` = OEIS A188866(n,k): number of valid `n × k` arrays. -/
def T (n k : ℕ) : ℕ := (univ.filter (Valid n k)).card

/-- Array determined by the "first zero row" of each column. -/
def toArr {n L : ℕ} (t : Fin (L+1) → Fin (n+1)) : Fin n → Fin (L+1) → Bool :=
  fun i j => decide ((i : ℕ) < t j)

/-- Number of ones in each column. -/
def fromArr {n L : ℕ} (a : Fin n → Fin (L+1) → Bool) : Fin (L+1) → Fin (n+1) :=
  fun j => ⟨(univ.filter fun i => a i j = true).card, by
    have := card_le_univ (univ.filter fun i => a i j = true); simp at this ⊢; omega⟩

lemma card_lt (n m : ℕ) (hm : m ≤ n) : (univ.filter fun i : Fin n => (i : ℕ) < m).card = m := by
  rcases Nat.lt_or_ge m n with h | h
  · have : (univ.filter fun i : Fin n => (i : ℕ) < m) = Iio ⟨m, h⟩ := by
      ext i; simp [Fin.lt_def]
    rw [this, Fin.card_Iio]
  · have hmn : m = n := by omega
    subst hmn
    rw [filter_true_of_mem (fun i _ => i.isLt)]; simp

lemma col_mono {n k : ℕ} {a : Fin n → Fin k → Bool} (ha : Valid n k a) (j : Fin k) :
    ∀ i i' : Fin n, i ≤ i' → a i j = false → a i' j = false := by
  intro i i' hii'
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Fin.le_def.mp hii')
  induction c generalizing i' with
  | zero => intro h; have : i' = i := Fin.ext (by omega); rw [this]; exact h
  | succ c ih =>
    intro h
    have hlt : (i : ℕ) + c < n := by have := i'.isLt; omega
    exact ha ⟨i + c, hlt⟩ i' j j (by simp; omega) (by omega) (by omega)
      (ih ⟨i + c, hlt⟩ (Fin.le_def.mpr (by simp)) rfl h)

lemma toArr_fromArr {n L : ℕ} {a : Fin n → Fin (L+1) → Bool} (ha : Valid n (L+1) a) :
    toArr (fromArr a) = a := by
  funext i j
  show decide ((i : ℕ) < ((fromArr a j : Fin (n+1)) : ℕ)) = a i j
  have hv : ((fromArr a j : Fin (n+1)) : ℕ) = (univ.filter fun i => a i j = true).card := rfl
  by_cases h : a i j = true
  · rw [h]; apply decide_eq_true; rw [hv]
    have : Iic i ⊆ univ.filter fun i => a i j = true := by
      intro i' hi'
      simp only [mem_Iic] at hi'
      simp only [mem_filter, mem_univ, true_and]
      by_contra h'
      simp only [Bool.not_eq_true] at h'
      have := col_mono ha j i' i hi' h'
      simp_all
    have := card_le_card this
    rw [Fin.card_Iic] at this; omega
  · simp only [Bool.not_eq_true] at h
    rw [h]; apply decide_eq_false; rw [hv, not_lt]
    have : (univ.filter fun i => a i j = true) ⊆ Iio i := by
      intro i' hi'
      simp only [mem_filter, mem_univ, true_and] at hi'
      simp only [mem_Iio]
      by_contra h'
      have := col_mono ha j i i' (not_lt.mp h') h
      simp_all
    have := card_le_card this
    rw [Fin.card_Iio] at this; exact this

lemma fromArr_toArr {n L : ℕ} (t : Fin (L+1) → Fin (n+1)) : fromArr (toArr t) = t := by
  funext j; ext
  simp only [fromArr, toArr, decide_eq_true_eq]
  exact card_lt n (t j) (by have := (t j).isLt; omega)

lemma valid_toArr {n L : ℕ} {t : Fin (L+1) → Fin (n+1)} (ht : WValid n L t) :
    Valid n (L+1) (toArr t) := by
  -- consecutive letters differ by at most one, hence so do letters at distance ≤ 1
  have key : ∀ j j' : Fin (L+1), (j : ℕ) ≤ j' + 1 → (j' : ℕ) ≤ j + 1 →
      ((t j' : ℕ) : ℤ) ≤ (t j : ℕ) + 1 := by
    intro j j' h1 h2
    rcases Nat.lt_trichotomy j j' with h | h | h
    · have hj : (j : ℕ) < L := by omega
      have := abs_le.mp (ht ⟨j, hj⟩)
      have e1 : (⟨j, hj⟩ : Fin L).succ = j' := Fin.ext (by simp; omega)
      have e2 : (⟨j, hj⟩ : Fin L).castSucc = j := rfl
      rw [e1, e2] at this; linarith
    · have : j = j' := Fin.ext h
      subst this; linarith
    · have hj : (j' : ℕ) < L := by omega
      have := abs_le.mp (ht ⟨j', hj⟩)
      have e1 : (⟨j', hj⟩ : Fin L).succ = j := Fin.ext (by simp; omega)
      have e2 : (⟨j', hj⟩ : Fin L).castSucc = j' := rfl
      rw [e1, e2] at this; linarith
  intro i i' j j' hi h1 h2 h
  simp only [toArr, decide_eq_false_iff_not, not_lt] at h ⊢
  have := key j j' h1 h2
  omega

lemma wvalid_of_valid_toArr {n L : ℕ} {t : Fin (L+1) → Fin (n+1)}
    (ht : Valid n (L+1) (toArr t)) : WValid n L t := by
  -- if a letter jumps by ≥ 2, the array has a `0` with a `1` below a neighbour
  have key : ∀ j j' : Fin (L+1), (j : ℕ) ≤ j' + 1 → (j' : ℕ) ≤ j + 1 →
      (t j' : ℕ) ≤ (t j : ℕ) + 1 := by
    intro j j' h1 h2
    by_contra hc
    rw [not_le] at hc
    have hj := (t j').isLt
    have hr1 : (t j : ℕ) < n := by omega
    have hr2 : (t j : ℕ) + 1 < n := by omega
    have := ht ⟨t j, hr1⟩ ⟨t j + 1, hr2⟩ j j' rfl h1 h2
      (by simp [toArr])
    simp [toArr] at this; omega
  intro i
  rw [abs_le]
  have a1 := key i.castSucc i.succ (by simp; omega) (by simp)
  have a2 := key i.succ i.castSucc (by simp) (by simp; omega)
  constructor <;> omega

/-- **Bijection theorem.** Valid `n × (L+1)` arrays are equinumerous with words of
length `L+1` over `{0,…,n}` whose adjacent letters differ by at most one. -/
theorem T_eq_W (n L : ℕ) : T n (L+1) = W n L := by
  unfold T W
  symm
  refine card_bij' (fun t _ => toArr t) (fun a _ => fromArr a) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht ⊢
    exact valid_toArr ht
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    apply wvalid_of_valid_toArr
    rw [toArr_fromArr ha]; exact ha
  · intro t _; exact fromArr_toArr t
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    exact toArr_fromArr ha

/-- **Main theorem.** For `n + 1 ≥ k ≥ 1` … precisely for `k = L+1` and `L ≤ n`,
`T(n,k) = 3^(k-1) * (n+1) - R(k-1)`. -/
theorem T_formula {n L : ℕ} (h : L ≤ n + 1) : (T n (L+1) : ℤ) = 3 ^ L * ((n : ℤ) + 1) - R L := by
  rw [T_eq_W]; exact W_formula h

end NovelProof
