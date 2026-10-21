module

public import KumarNivat.FiniteWordDynamics

@[expose] public section

namespace KumarNivat

-- words record all consecutive values, with either integer or natural starting indices.
def sequenceWord {I A : Type*} [AddCommMonoidWithOne I] (a : I → A) (r : ℕ) (n : I) : Fin r → A :=
  fun i => a (n + (i.val : I))

-- only words actually occurring in the sequence contribute to its complexity.
noncomputable def wordCount {I A : Type*} [AddCommMonoidWithOne I] (a : I → A) (r : ℕ) : ℕ :=
  (Set.range (sequenceWord a r)).ncard

-- finite image of the letters makes every finite-word language finite.
theorem sequenceWord_range_finite {I A : Type*} [AddCommMonoidWithOne I]
    (a : I → A) (ha : (Set.range a).Finite) (r : ℕ) : (Set.range (sequenceWord a r)).Finite := by
  apply (Set.Finite.pi' (fun _ : Fin r => ha)).subset
  rintro _ ⟨n, rfl⟩ i
  exact ⟨n + (i.val : I), rfl⟩

-- prefix restriction maps the longer occurring language onto the shorter one.
def wordPrefix {A : Type*} (m n : ℕ) (hmn : m ≤ n) (w : Fin n → A) : Fin m → A :=
  fun i => w ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩

-- the same starting index witnesses both a word and its prefix.
theorem wordPrefix_range {I A : Type*} [AddCommMonoidWithOne I]
    (a : I → A) (m n : ℕ) (hmn : m ≤ n) :
    wordPrefix m n hmn '' Set.range (sequenceWord a n) = Set.range (sequenceWord a m) := by
  ext w
  constructor
  · rintro ⟨_v, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨sequenceWord a n k, ⟨k, rfl⟩, rfl⟩

-- the unique empty word fixes the starting value of the word count.
theorem wordCount_zero {I A : Type*} [AddCommMonoidWithOne I] (a : I → A) : wordCount a 0 = 1 := by
  have he : Set.range (sequenceWord a 0) = {sequenceWord a 0 0} := by
    ext w
    constructor
    · rintro ⟨n, rfl⟩
      exact Subsingleton.elim _ _
    · rintro rfl
      exact ⟨0, rfl⟩
  simp only [wordCount, he, Set.ncard_singleton]

-- word complexity cannot decrease when the window is lengthened.
theorem wordCount_mono {I A : Type*} [AddCommMonoidWithOne I]
    (a : I → A) (ha : (Set.range a).Finite) : Monotone (wordCount a) := by
  intro m n hmn
  unfold wordCount
  rw [← wordPrefix_range a m n hmn]
  exact Set.ncard_image_le (sequenceWord_range_finite a ha n)

-- a count at most the window length forces one of the preceding increases to vanish.
theorem wordCount_has_plateau {I A : Type*} [AddCommMonoidWithOne I]
    (a : I → A) (ha : (Set.range a).Finite) (r : ℕ) (hbound : wordCount a r ≤ r) :
    ∃ j : ℕ, j < r ∧ wordCount a (j + 1) = wordCount a j := by
  by_contra! hnone
  have hstrict (j : ℕ) (hj : j < r) : wordCount a j < wordCount a (j + 1) :=
    lt_of_le_of_ne (wordCount_mono a ha (by omega)) (Ne.symm (hnone j hj))
  have hlower (j : ℕ) : j ≤ r → j + 1 ≤ wordCount a j := by
    induction j with
    | zero =>
      intro _hj
      simpa only [Nat.zero_add, wordCount_zero] using (le_refl (1 : ℕ))
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hnext := hstrict j (by omega)
      omega
  have hlast := hlower r le_rfl
  omega

-- equal cardinalities make prefix restriction injective on the actual longer language.
theorem word_extension_determined_at_plateau {I A : Type*} [AddCommMonoidWithOne I]
    (a : I → A) (ha : (Set.range a).Finite) (j : ℕ)
    (heq : wordCount a (j + 1) = wordCount a j) :
    ∀ n k : I, sequenceWord a j n = sequenceWord a j k →
      sequenceWord a (j + 1) n = sequenceWord a (j + 1) k := by
  have hcard : (wordPrefix j (j + 1) (by omega) '' Set.range (sequenceWord a (j + 1))).ncard =
      (Set.range (sequenceWord a (j + 1))).ncard := by
    rw [wordPrefix_range]
    exact heq.symm
  have hinj := Set.injOn_of_ncard_image_eq hcard (sequenceWord_range_finite a ha (j + 1))
  intro n k he
  exact hinj ⟨n, rfl⟩ ⟨k, rfl⟩ he

-- recording one extra letter gives determined successor states even at a zero-length plateau.
theorem word_successor_determined_at_plateau {I A : Type*} [AddCommMonoidWithOne I]
    (a : I → A) (ha : (Set.range a).Finite) (j : ℕ)
    (heq : wordCount a (j + 1) = wordCount a j) :
    ∀ n k : I, sequenceWord a (j + 1) n = sequenceWord a (j + 1) k →
      sequenceWord a (j + 1) (n + 1) = sequenceWord a (j + 1) (k + 1) := by
  intro n k he
  apply word_extension_determined_at_plateau a ha j heq
  funext i
  have hi := congrFun he i.succ
  simpa [sequenceWord, add_assoc, add_left_comm, add_comm] using hi

-- the bilateral morse--hedlund bound supplies the paper's period no larger than r.
theorem morse_hedlund_bilateral {A : Type*} (a : ℤ → A) (ha : (Set.range a).Finite)
    (r : ℕ) (hbound : wordCount a r ≤ r) :
    ∃ p : ℕ, 0 < p ∧ p ≤ r ∧ Function.Periodic a (p : ℤ) := by
  obtain ⟨j, hj, heq⟩ := wordCount_has_plateau a ha r hbound
  obtain ⟨p, hp, hcard, hperiod⟩ := bounded_period_of_bilateral_determinism (sequenceWord a (j + 1))
    (sequenceWord_range_finite a ha (j + 1)) (word_successor_determined_at_plateau a ha j heq)
  have hcount : wordCount a (j + 1) ≤ r := (wordCount_mono a ha (by omega)).trans hbound
  refine ⟨p, hp, hcard.trans hcount, ?_⟩
  intro n
  have he := congrFun (hperiod n) (0 : Fin (j + 1))
  simpa only [sequenceWord, Fin.val_zero, Nat.cast_zero, add_zero] using he

-- the one-sided bound gives a periodic tail with both the start and period bounded by r.
theorem morse_hedlund_one_sided {A : Type*} (a : ℕ → A) (ha : (Set.range a).Finite)
    (r : ℕ) (hbound : wordCount a r ≤ r) :
    ∃ b p : ℕ, b < r ∧ 0 < p ∧ p ≤ r ∧ ∀ n : ℕ, b ≤ n → a (n + p) = a n := by
  obtain ⟨j, hj, heq⟩ := wordCount_has_plateau a ha r hbound
  obtain ⟨b, p, hb, hp, hcard, hperiod⟩ := bounded_eventual_period_of_determinism (sequenceWord a (j + 1))
    (sequenceWord_range_finite a ha (j + 1)) (word_successor_determined_at_plateau a ha j heq)
  have hcount : wordCount a (j + 1) ≤ r := (wordCount_mono a ha (by omega)).trans hbound
  refine ⟨b, p, hb.trans_le hcount, hp, hcard.trans hcount, ?_⟩
  intro n hn
  have he := congrFun (hperiod n hn) (0 : Fin (j + 1))
  simpa only [sequenceWord, Fin.val_zero, Nat.cast_zero, add_zero] using he

end KumarNivat
