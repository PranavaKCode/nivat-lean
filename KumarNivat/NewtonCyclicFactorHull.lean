import KumarNivat.NewtonCyclicFactorCoordinates
import KumarNivat.NewtonCyclicFacets

namespace KumarNivat

-- ordered half-fan normals are negative before their edge and nonnegative after it.
theorem ordered_half_factor_normal_signs {q : ℕ} (h : Fin q → Site)
    (hstrict : ∀ i j : Fin q, i < j → 0 < determinant (h i) (h j)) (k : Fin q) :
    (∀ j : Fin q, j.val < k.val → directionNormal (h k) (h j) ≤ 0) ∧
      (∀ j : Fin q, k.val ≤ j.val → 0 ≤ directionNormal (h k) (h j)) := by
  constructor
  · intro j hj
    have hpos := hstrict j k hj
    have he : directionNormal (h k) (h j) = -determinant (h j) (h k) := by
      simp [directionNormal, determinant]
      ring
    rw [he]
    exact neg_nonpos.mpr (le_of_lt hpos)
  · intro j hj
    by_cases he : j = k
    · rw [he, directionNormal_self]
    · have hne : j.val ≠ k.val := fun hz => he (Fin.ext hz)
      exact le_of_lt (hstrict k j (by change k.val < j.val; omega))

-- the smaller endpoint sum is attained at the corresponding actual prefix vertex.
theorem factor_prefix_normal_minimum_sum {q : ℕ} (h : Fin q → Site) (ν : Site →+ ℤ) (t : ℕ)
    (hbefore : ∀ i : Fin q, i.val < t → ν (h i) ≤ 0)
    (hafter : ∀ i : Fin q, t ≤ i.val → 0 ≤ ν (h i)) :
    (∑ i : Fin q, min 0 (ν (h i) : ℝ)) = latticeNormal ν (latticeEmbedding (factorVertexPrefix h t)) := by
  classical
  rw [factorVertexPrefix_embedding, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hit : i.val < t
  · simp only [ite_eq_left hit, latticeNormal_embedding]
    exact min_eq_right (by exact_mod_cast hbefore i hit)
  · simp only [ite_eq_right hit, map_zero]
    exact min_eq_left (by exact_mod_cast hafter i (by omega))

-- opposite normals attain that same endpoint sum on the return half of the actual walk.
theorem factor_complement_normal_minimum_sum {q : ℕ} (h : Fin q → Site) (ν : Site →+ ℤ) (t : ℕ)
    (hbefore : ∀ i : Fin q, i.val < t → 0 ≤ ν (h i))
    (hafter : ∀ i : Fin q, t ≤ i.val → ν (h i) ≤ 0) :
    (∑ i : Fin q, min 0 (ν (h i) : ℝ)) =
      latticeNormal ν (latticeEmbedding (factorVertexPrefix h q - factorVertexPrefix h t)) := by
  classical
  rw [factorVertexComplement_embedding, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hit : i.val < t
  · simp only [ite_eq_left hit, map_zero]
    exact min_eq_left (by exact_mod_cast hbefore i hit)
  · simp only [ite_eq_right hit, latticeNormal_embedding]
    exact min_eq_right (by exact_mod_cast hafter i (by omega))

-- every actual walk vertex attains the full segment sum's lower support level for its edge normal.
theorem ordered_factor_vertex_normal_minimum_sum (q : ℕ) [NeZero q] (h : Fin q → Site)
    (hstrict : ∀ i j : Fin q, i < j → 0 < determinant (h i) (h j)) (i : ZMod (2 * q)) :
    (∑ j : Fin q, min 0 (directionNormal (doubledFactorDirections q h i) (h j) : ℝ)) =
      latticeNormal (directionNormal (doubledFactorDirections q h i))
        (latticeEmbedding (doubledFactorVertices q h i)) := by
  have hneg (p g : Site) : directionNormal (-p) g = -directionNormal p g := by
    simp [directionNormal, determinant]
    ring
  by_cases hi : i.val < q
  · let k : Fin q := ⟨i.val, hi⟩
    obtain ⟨hbefore, hafter⟩ := ordered_half_factor_normal_signs h hstrict k
    simp only [doubledFactorDirections, doubledFactorVertices, hi, dite_true, ite_true]
    exact factor_prefix_normal_minimum_sum h (directionNormal (h k)) i.val hbefore hafter
  · let k : Fin q := ⟨i.val - q, by have hv := ZMod.val_lt i; omega⟩
    obtain ⟨hbefore, hafter⟩ := ordered_half_factor_normal_signs h hstrict k
    simp only [doubledFactorDirections, doubledFactorVertices, hi, dite_false, ite_false]
    apply factor_complement_normal_minimum_sum h (directionNormal (-h k)) (i.val - q)
    · intro j hj
      rw [hneg]
      exact neg_nonneg.mpr (hbefore j hj)
    · intro j hj
      rw [hneg]
      exact neg_nonpos.mpr (hafter j hj)

-- the actual prefix walk's hull is the complete segment zonotope, rather than a supplied polygon identity.
theorem ordered_factor_prefix_hull_eq_zonotope (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (h : Fin q → Site) (hstrict : ∀ i j : Fin q, i < j → 0 < determinant (h i) (h j)) :
    convexHull ℝ (Set.range (fun i => latticeEmbedding (doubledFactorVertices q h i))) =
      differenceZonotope (List.ofFn h) := by
  classical
  have horder := doubledFactorDirections_cyclic_order q hq h hstrict
  have hedge : ∀ i, doubledFactorVertices q h (i + 1) = doubledFactorVertices q h i +
      (1 : ℤ) • doubledFactorDirections q h i := by
    intro i
    simpa only [one_smul] using doubledFactorVertices_next q h i
  apply Set.Subset.antisymm
  · apply convexHull_min ?_ (differenceZonotope_convex (List.ofFn h))
    rintro _ ⟨i, rfl⟩
    change latticeEmbedding (doubledFactorVertices q h i) ∈ differenceZonotope (List.ofFn h)
    by_cases hi : i.val < q
    · simp only [doubledFactorVertices, hi, ite_true]
      exact factorVertexPrefix_mem_zonotope h i.val
    · simp only [doubledFactorVertices, hi, ite_false]
      exact factorVertexComplement_mem_zonotope h (i.val - q)
  · intro z hz
    rw [ordered_cyclic_walk_facet_presentation (doubledFactorDirections q h) horder
      (doubledFactorVertices q h) (fun _ => 1) (fun _ => by norm_num) hedge]
    intro i
    have hb := factorZonotope_normal_lower_bound h (directionNormal (doubledFactorDirections q h i)) z hz
    rw [ordered_factor_vertex_normal_minimum_sum q h hstrict i, latticeNormal_embedding] at hb
    exact hb

end KumarNivat
