import NovelProof.Words

namespace NovelProof

def ValidArray {n k : ℕ} (a : Fin n → Fin k → Bool) : Prop :=
  ∀ (i : Fin n) (j : Fin k), a i j = false →
    (∀ i' : Fin n, i.val < i'.val → a i' j = false) ∧
    (∀ i' : Fin n, j' : Fin k, i.val < i'.val → |j'.val - j.val| = 1 → a i' j' = false)

def T (n k : ℕ) : ℕ := (Finset.univ.filter ValidArray).card

def colHeight {n k : ℕ} (a : Fin n → Fin k → Bool) (j : Fin k) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => a i j = true)).card

def arrayToHeights {n k : ℕ} (a : Fin n → Fin k → Bool) : Fin k → ℕ :=
  fun j => colHeight a j

def heightsToArray {n k : ℕ} (h : Fin k → ℕ) : Fin n → Fin k → Bool :=
  fun i j => i.val < h j

lemma column_is_prefix {n k : ℕ} (a : Fin n → Fin k → Bool) (ha : ValidArray a) (j : Fin k) :
    ∀ i : Fin n, a i j = true → ∀ i' : Fin n, i'.val ≤ i.val → a i' j = true := by
  intro i hi i' hi'
  by_contra hfalse
  have := (ha i' j hfalse).1 i (by omega)
  contradiction

lemma height_char {n k : ℕ} (a : Fin n → Fin k → Bool) (ha : ValidArray a) (j : Fin k) (i : Fin n) :
    a i j = true ↔ i.val < colHeight a j := by
  constructor
  · intro hi
    have : (Finset.filter (fun i' : Fin n => a i' j = true) Finset.univ).card ≥ i.val + 1 := by
      have subset : (Finset.range (i.val + 1)).image (fun m => ⟨m, by omega⟩) ⊆
          Finset.filter (fun i' => a i' j = true) Finset.univ := by
        intro x hx
        simp at hx ⊢
        obtain ⟨m, hm, rfl⟩ := hx
        exact column_is_prefix a ha j i hi ⟨m, by omega⟩ (by omega)
      have : (Finset.range (i.val + 1)).card ≤ (Finset.filter (fun i' => a i' j = true) Finset.univ).card := by
        apply Finset.card_le_card
        exact subset
      simp at this
      omega
    exact Nat.lt_of_succ_le this
  · intro hi
    by_contra hfalse
    have hbelow : ∀ i' : Fin n, i'.val ≤ i.val → a i' j = false := by
      intro i' hi'
      have := (ha i j hfalse).1 i' (by omega)
      exact this
    have : colHeight a j ≤ n - (i.val + 1) := by
      simp [colHeight]
      apply Finset.card_le_card
      intro x hx
      simp at hx
      have : ¬ (x.val ≤ i.val) := by
        intro hle
        have := hbelow x hle
        contradiction
      omega
    omega

lemma valid_implies_smooth {n k : ℕ} (a : Fin n → Fin k → Bool) (ha : ValidArray a) :
    ∀ i : Fin (k - 1), |(arrayToHeights a i.castSucc : ℤ) - (arrayToHeights a i.succ : ℤ)| ≤ 1 := by
  intro i
  let j := i.castSucc
  let j' := i.succ
  let h := arrayToHeights a j
  let h' := arrayToHeights a j'
  by_contra hne
  push_neg at hne
  have : h ≥ h' + 2 ∨ h' ≥ h + 2 := by omega
  cases this with
  | inl hh =>
    have hfalse : a ⟨h', by
      have : h' ≤ n := by simp [arrayToHeights, colHeight]; exact Finset.card_le_card (Finset.filter_subset _ _)
      omega⟩ j' = false := by
      have := (height_char a ha j' ⟨h', by omega⟩).mp
      simp at this
      omega
    have := (ha ⟨h', by omega⟩ j' hfalse).2 ⟨h' + 1, by omega⟩ j (by omega) (by simp; omega)
    have htrue : a ⟨h' + 1, by omega⟩ j = true := by
      have := (height_char a ha j ⟨h' + 1, by omega⟩).mpr (by omega)
      exact this
    contradiction
  | inr hh =>
    have hfalse : a ⟨h, by omega⟩ j = false := by
      have := (height_char a ha j ⟨h, by omega⟩).mp
      simp at this; omega
    have := (ha ⟨h, by omega⟩ j hfalse).2 ⟨h + 1, by omega⟩ j' (by omega) (by simp; omega)
    have htrue : a ⟨h + 1, by omega⟩ j' = true := by
      have := (height_char a ha j' ⟨h + 1, by omega⟩).mpr (by omega)
      exact this
    contradiction

lemma heights_to_array_valid {n k : ℕ} (h : Fin k → ℕ) (hh : ∀ j, h j ≤ n)
    (hs : ∀ i : Fin (k - 1), |h i.castSucc - h i.succ| ≤ 1) :
    ValidArray (heightsToArray h) := by
  intro i j hai
  simp [heightsToArray] at hai
  constructor
  · intro i' hi'
    simp [heightsToArray]
    omega
  · intro i' j' hi' hdiff
    simp [heightsToArray]
    have hadj : |h j - h j'| ≤ 1 := by
      by_cases horder : j.val < j'.val
      · have : j'.val = j.val + 1 := by omega
        have : ∃ ii : Fin (k - 1), ii.castSucc = j ∧ ii.succ = j' := by
          use ⟨j.val, by omega⟩
          simp; omega
        obtain ⟨ii, h1, h2⟩ := this
        have := hs ii
        simp [h1, h2] at this
        omega
      · have : j.val = j'.val + 1 := by omega
        have : ∃ ii : Fin (k - 1), ii.castSucc = j' ∧ ii.succ = j := by
          use ⟨j'.val, by omega⟩
          simp; omega
        obtain ⟨ii, h1, h2⟩ := this
        have := hs ii
        simp [h1, h2] at this
        omega
    omega

lemma colHeight_heightsToArray {n k : ℕ} (h : Fin k → ℕ) (hh : ∀ j, h j ≤ n) :
    ∀ j, colHeight (heightsToArray h) j = h j := by
  intro j
  simp [colHeight, heightsToArray]
  have : (Finset.filter (fun i : Fin n => i.val < h j) Finset.univ).card = h j := by
    rw [← Finset.card_range (h j)]
    apply Finset.card_bij (fun m hm => ⟨m, by simp at hm; omega⟩)
    · intro m hm; simp
    · intro m1 hm1 m2 hm2 heq; simp at heq; omega
    · intro i hi
      simp at hi
      use i.val
      simp
      constructor
      · omega
      · ext; omega
  exact this

theorem T_eq_W (n L : ℕ) : T n (L + 1) = W n L := by
  let k := L + 1
  have hbij : (Finset.univ.filter (ValidArray (n := n) (k := k))).card =
      (Finset.univ.filter (isSmooth (M := n) (L := L))).card := by
    apply Finset.card_bij (fun a _ => fun j => ⟨arrayToHeights a j, by
      simp [arrayToHeights, colHeight]
      exact Finset.card_le_card (Finset.filter_subset _ _)⟩)
      (fun a ha => by
        simp [Finset.mem_filter]
        exact valid_implies_smooth a ha.2)
      (fun a1 ha1 a2 ha2 heq => by
        ext i j
        have hchar1 := height_char a1 ha1.2 j i
        have hchar2 := height_char a2 ha2.2 j i
        simp [arrayToHeights] at heq
        have : arrayToHeights a1 j = arrayToHeights a2 j := by
          have := congr_fun heq j
          simp at this
          omega
        simp [hchar1, hchar2, this]
        omega)
      (fun t ht => by
        let hfun := fun j => (t j).val
        let a := heightsToArray hfun
        refine ⟨a, ?_, ?_⟩
        · simp [Finset.mem_filter]
          exact heights_to_array_valid hfun
            (fun j => by simp; omega)
            (fun i => by
              have := ht.2 i
              simp [isSmooth] at this
              omega)
        · ext j
          simp [arrayToHeights]
          exact colHeight_heightsToArray hfun (fun j => by simp; omega) j)
  simp [T, W, hbij]

theorem T_formula (n L : ℕ) (h : L ≤ n + 1) :
    (T n (L + 1) : ℤ) = 3 ^ L * ((n + 1) : ℤ) - R L := by
  rw [T_eq_W]
  exact W_formula n L h

end NovelProof
