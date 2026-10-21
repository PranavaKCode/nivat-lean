module

public import KumarNivat.AnchoredCyclicFaces
public import KumarNivat.AnchoredMaximalCyclic

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- a translated oriented segment cannot be longer than the actual containing facet interval.
theorem translated_segment_length_le_interval (A B v : RealPlane) (hv : v ≠ 0)
    (r s : ℝ) (hstart : B ∈ lineInterval A v 0 s)
    (hend : B + r • v ∈ lineInterval A v 0 s) : r ≤ s := by
  obtain ⟨t, ht, he₀⟩ := hstart
  obtain ⟨u, hu, he₁⟩ := hend
  change A + t • v = B at he₀
  change A + u • v = B + r • v at he₁
  rw [← he₀, add_assoc, ← add_smul] at he₁
  have hparameter : u = t + r := (smul_left_injective ℝ hv) (add_left_cancel he₁)
  linarith [ht.1, hu.2]

-- an attained polygon minimum supplies an actual minimizing residual point without a compactness hypothesis.
theorem cyclic_minkowski_minimizing_residual_point {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (C : Set RealPlane) (hsum : latticeHull F = latticeHull Z + C) (i : ZMod n) :
    ∃ c ∈ C, latticeNormal (directionNormal (e i)) c =
      (directionNormal (e i) (P.vertex i) : ℝ) - (directionNormal (e i) (Q.vertex i) : ℝ) := by
  have hpoint : latticeEmbedding (P.vertex i) ∈ latticeHull F :=
    subset_convexHull ℝ _ ⟨P.vertex i, P.vertex_mem i, rfl⟩
  rw [hsum] at hpoint
  obtain ⟨z, hz, c, hc, he⟩ := Set.mem_add.mp hpoint
  have hQ := ordered_cyclic_real_point_normal_minimum e horder Z Q z hz i
  have hnormal := congrArg (latticeNormal (directionNormal (e i))) he
  rw [map_add, latticeNormal_embedding] at hnormal
  have hqc : latticeEmbedding (Q.vertex i) + c ∈ latticeHull F := by
    rw [hsum]
    exact Set.add_mem_add (subset_convexHull ℝ _ ⟨Q.vertex i, Q.vertex_mem i, rfl⟩) hc
  have hP := ordered_cyclic_real_point_normal_minimum e horder F P _ hqc i
  rw [map_add, latticeNormal_embedding] at hP
  exact ⟨c, hc, by linarith⟩

-- the same attained residual point places the entire original newton edge inside the actual envelope edge.
theorem cyclic_edge_lengths_dominate_of_minkowski_sum {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (C : Set RealPlane) (hsum : latticeHull F = latticeHull Z + C) :
    ∀ i, Q.edgeLength i ≤ P.edgeLength i := by
  intro i
  obtain ⟨c, hc, hnormal⟩ := cyclic_minkowski_minimizing_residual_point e horder Z F Q P C hsum i
  let B : RealPlane := latticeEmbedding (Q.vertex i) + c
  have hstart : B ∈ normalFace (latticeHull F) (latticeNormal (directionNormal (e i)))
      (directionNormal (e i) (P.vertex i) : ℝ) := by
    refine ⟨?_, ?_⟩
    · rw [hsum]
      exact Set.add_mem_add (subset_convexHull ℝ _ ⟨Q.vertex i, Q.vertex_mem i, rfl⟩) hc
    · dsimp [B]
      rw [map_add, latticeNormal_embedding, hnormal]
      ring
  have hlastEq : latticeEmbedding (Q.vertex (i + 1)) + c =
      B + (Q.edgeLength i : ℝ) • latticeEmbedding (e i) := by
    rw [Q.edge_eq, latticeEmbedding_add, latticeEmbedding_zsmul]
    dsimp [B]
    abel
  have hend : B + (Q.edgeLength i : ℝ) • latticeEmbedding (e i) ∈
      normalFace (latticeHull F) (latticeNormal (directionNormal (e i)))
        (directionNormal (e i) (P.vertex i) : ℝ) := by
    refine ⟨?_, ?_⟩
    · rw [← hlastEq, hsum]
      exact Set.add_mem_add (subset_convexHull ℝ _ ⟨Q.vertex (i + 1), Q.vertex_mem _, rfl⟩) hc
    · rw [map_add, map_smul, latticeNormal_embedding, directionNormal_self, Int.cast_zero, smul_zero, add_zero]
      exact hstart.2
  have hene : e i ≠ 0 := by
    intro hzero
    have hdet := horder.adjacent_pos i
    rw [hzero] at hdet
    simp [determinant] at hdet
  have hv : latticeEmbedding (e i) ≠ 0 := by
    intro he
    exact hene (latticeEmbedding_injective (by simpa [latticeEmbedding] using he))
  rw [ordered_cyclic_facet_is_actual_edge e horder F P i] at hstart hend
  have hwidth := translated_segment_length_le_interval (latticeEmbedding (P.vertex i)) B
    (latticeEmbedding (e i)) hv (Q.edgeLength i : ℝ) (P.edgeLength i : ℝ) hstart hend
  exact_mod_cast hwidth

-- the source's compact convex envelope metadata now yields its required integer edge-length inequalities.
theorem anchored_cyclic_envelope_edge_lengths {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (henvelope : AnchoredCyclicEnvelope e (latticeHull Z) F) :
    ∀ i, Q.edgeLength i ≤ P.edgeLength i := by
  obtain ⟨_hpoly, C, _hconvex, _hcompact, _hnonempty, hsum⟩ := henvelope
  exact cyclic_edge_lengths_dominate_of_minkowski_sum e horder Z F Q P C hsum

end KumarNivat
