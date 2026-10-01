import KumarNivat.NewtonCyclicOrder

namespace KumarNivat

-- the second semicircle follows the negatives in the same order as the first.
def doubledFactorDirections (q : ℕ) [NeZero q] (h : Fin q → Site) : ZMod (2 * q) → Site :=
  fun i => if hi : i.val < q then h ⟨i.val, hi⟩
    else -h ⟨i.val - q, by have hv := ZMod.val_lt i; omega⟩

-- adding one half-turn changes only the sign of the actual direction.
theorem doubledFactorDirections_antipodal (q : ℕ) [NeZero q] (h : Fin q → Site)
    (i : ZMod (2 * q)) :
    doubledFactorDirections q h (i + (q : ZMod (2 * q))) = -doubledFactorDirections q h i := by
  have hq : 0 < q := NeZero.pos q
  have hi : i.val < 2 * q := ZMod.val_lt i
  have hqval : (q : ZMod (2 * q)).val = q := ZMod.val_natCast_of_lt (by omega)
  by_cases hfirst : i.val < q
  · have hv : (i + (q : ZMod (2 * q))).val = i.val + q := by
      rw [ZMod.val_add, hqval, Nat.mod_eq_of_lt (by omega)]
    simp only [doubledFactorDirections, hfirst, dite_true, hv,
      show ¬ i.val + q < q by omega, dite_false]
    congr 2
    apply Fin.ext
    simp
  · have hv : (i + (q : ZMod (2 * q))).val = i.val - q := by
      rw [ZMod.val_add_of_le (by rw [hqval]; omega), hqval]
      omega
    simp only [doubledFactorDirections, hfirst, dite_false, hv,
      show i.val - q < q by omega, dite_true, neg_neg]

-- strictly ordered upper directions produce strict turns at every interior half-turn offset.
theorem doubledFactorDirections_positive_offset (q : ℕ) [NeZero q] (h : Fin q → Site)
    (hstrict : ∀ i j : Fin q, i < j → 0 < determinant (h i) (h j))
    (i : ZMod (2 * q)) (d : ℕ) (hd0 : 0 < d) (hdq : d < q) :
    0 < determinant (doubledFactorDirections q h i)
      (doubledFactorDirections q h (i + (d : ZMod (2 * q)))) := by
  have hi : i.val < 2 * q := ZMod.val_lt i
  have hdval : (d : ZMod (2 * q)).val = d := ZMod.val_natCast_of_lt (by omega)
  have hnegleft (p r : Site) : determinant (-p) r = determinant r p := by simp [determinant]; ring
  have hnegright (p r : Site) : determinant p (-r) = determinant r p := by simp [determinant]; ring
  have hnegneg (p r : Site) : determinant (-p) (-r) = determinant p r := by simp [determinant]
  by_cases hfirst : i.val < q
  · have hv : (i + (d : ZMod (2 * q))).val = i.val + d := by
      rw [ZMod.val_add, hdval, Nat.mod_eq_of_lt (by omega)]
    by_cases hremain : i.val + d < q
    · simp only [doubledFactorDirections, hfirst, dite_true, hv, hremain]
      exact hstrict ⟨i.val, hfirst⟩ ⟨i.val + d, hremain⟩ (by change i.val < i.val + d; omega)
    · simp only [doubledFactorDirections, hfirst, dite_true, hv, hremain, dite_false]
      rw [hnegright]
      apply hstrict
      change i.val + d - q < i.val
      omega
  · by_cases hwrap : i.val + d < 2 * q
    · have hv : (i + (d : ZMod (2 * q))).val = i.val + d := by
        rw [ZMod.val_add, hdval, Nat.mod_eq_of_lt hwrap]
      have hsecond : ¬ i.val + d < q := by omega
      simp only [doubledFactorDirections, hfirst, dite_false, hv, hsecond]
      rw [hnegneg]
      apply hstrict
      change i.val - q < i.val + d - q
      omega
    · have hv : (i + (d : ZMod (2 * q))).val = i.val + d - 2 * q := by
        rw [ZMod.val_add_of_le (by rw [hdval]; omega), hdval]
      have hwrapped : i.val + d - 2 * q < q := by omega
      simp only [doubledFactorDirections, hfirst, dite_false, hv, hwrapped, dite_true]
      rw [hnegleft]
      apply hstrict
      change i.val + d - 2 * q < i.val - q
      omega

-- the derived half-turn signs give the complete cyclic direction order, including strict adjacent corners.
theorem doubledFactorDirections_cyclic_order (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (h : Fin q → Site) (hstrict : ∀ i j : Fin q, i < j → 0 < determinant (h i) (h j)) :
    CyclicEdgeOrder (doubledFactorDirections q h) := by
  have hzero (p : Site) : determinant p (-p) = 0 := by simp [determinant]; ring
  have hrightneg (p r : Site) : determinant p (-r) = -determinant p r := by simp [determinant]; ring
  refine ⟨?_, ?_⟩
  · intro i
    have ht := doubledFactorDirections_positive_offset q h hstrict (i - 1) 1 (by omega) (by omega)
    simpa only [Nat.cast_one, sub_add_cancel] using ht
  · intro i
    refine ⟨q + 1, by omega, ?_, ?_⟩
    · intro d hd
      by_cases hd0 : d = 0
      · subst d
        simp only [Nat.cast_zero, add_zero]
        change 0 ≤ directionNormal (doubledFactorDirections q h i) (doubledFactorDirections q h i)
        rw [directionNormal_self]
      · by_cases hdq : d = q
        · subst d
          rw [doubledFactorDirections_antipodal, hzero]
        · exact le_of_lt (doubledFactorDirections_positive_offset q h hstrict i d (by omega) (by omega))
    · intro d hd hdn
      have he : i + (d : ZMod (2 * q)) = (i + ((d - q : ℕ) : ZMod (2 * q))) + (q : ZMod (2 * q)) := by
        rw [add_assoc, ← Nat.cast_add, Nat.sub_add_cancel (by omega : q ≤ d)]
      rw [he, doubledFactorDirections_antipodal, hrightneg]
      have ht := doubledFactorDirections_positive_offset q h hstrict i (d - q) (by omega) (by omega)
      exact neg_nonpos.mpr (le_of_lt ht)

end KumarNivat
