import KumarNivat.NewtonCyclicFactorDouble
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace KumarNivat

-- prefix sums use the actual ordered integer factor vectors.
def factorVertexPrefix {q : ℕ} (h : Fin q → Site) (t : ℕ) : Site :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin q => i.val < t), h i

-- the first prefix is the actual origin.
theorem factorVertexPrefix_zero {q : ℕ} (h : Fin q → Site) : factorVertexPrefix h 0 = 0 := by
  simp [factorVertexPrefix]

-- adding one factor advances its actual prefix vertex by that vector.
theorem factorVertexPrefix_succ {q : ℕ} (h : Fin q → Site) (t : ℕ) (ht : t < q) :
    factorVertexPrefix h (t + 1) = factorVertexPrefix h t + h ⟨t, ht⟩ := by
  classical
  have hset : Finset.univ.filter (fun i : Fin q => i.val < t + 1) =
      insert ⟨t, ht⟩ (Finset.univ.filter (fun i : Fin q => i.val < t)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases he : i.val = t
      · left
        exact Fin.ext he
      · right
        omega
    · rintro (rfl | hi)
      · simp
      · omega
  unfold factorVertexPrefix
  rw [hset, Finset.sum_insert (by simp)]
  exact add_comm _ _

-- the prefix vertices run along the ordered factors and then along their negatives back to the origin.
def doubledFactorVertices (q : ℕ) [NeZero q] (h : Fin q → Site) : ZMod (2 * q) → Site :=
  fun i => if i.val < q then factorVertexPrefix h i.val
    else factorVertexPrefix h q - factorVertexPrefix h (i.val - q)

-- the doubled prefix construction really closes with the prescribed actual edge vectors.
theorem doubledFactorVertices_next (q : ℕ) [NeZero q] (h : Fin q → Site)
    (i : ZMod (2 * q)) :
    doubledFactorVertices q h (i + 1) = doubledFactorVertices q h i + doubledFactorDirections q h i := by
  have hq : 0 < q := NeZero.pos q
  have hi : i.val < 2 * q := ZMod.val_lt i
  have h1 : (1 : ZMod (2 * q)).val = 1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (n := 2 * q) (a := 1) (by omega))
  by_cases hfirst : i.val < q
  · have hv : (i + 1).val = i.val + 1 := by
      rw [ZMod.val_add, h1, Nat.mod_eq_of_lt (by omega)]
    by_cases hstay : i.val + 1 < q
    · simp only [doubledFactorVertices, doubledFactorDirections, hfirst, ite_true, dite_true, hv, hstay]
      exact factorVertexPrefix_succ h i.val hfirst
    · have he : i.val + 1 = q := by omega
      simp only [doubledFactorVertices, doubledFactorDirections, hfirst, ite_true, dite_true, hv, hstay, ite_false]
      have hp := factorVertexPrefix_succ h i.val hfirst
      rw [he] at hp
      simpa only [he, Nat.sub_self, factorVertexPrefix_zero, sub_zero] using hp
  · by_cases hstay : i.val + 1 < 2 * q
    · have hv : (i + 1).val = i.val + 1 := by
        rw [ZMod.val_add, h1, Nat.mod_eq_of_lt hstay]
      have hsecond : ¬ i.val + 1 < q := by omega
      have hcore : i.val - q < q := by omega
      have he : i.val + 1 - q = (i.val - q) + 1 := by omega
      simp only [doubledFactorVertices, doubledFactorDirections, hfirst, ite_false, dite_false, hv, hsecond]
      rw [he, factorVertexPrefix_succ h (i.val - q) hcore]
      abel
    · have hv : (i + 1).val = 0 := by
        rw [ZMod.val_add_of_le (by rw [h1]; omega), h1]
        omega
      have hcore : i.val - q < q := by omega
      have he : i.val - q + 1 = q := by omega
      have hp := factorVertexPrefix_succ h (i.val - q) hcore
      rw [he] at hp
      simp only [doubledFactorVertices, doubledFactorDirections, hfirst, ite_false, dite_false,
        hv, hq, ite_true, factorVertexPrefix_zero]
      rw [hp]
      abel

end KumarNivat
