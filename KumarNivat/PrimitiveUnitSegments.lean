module

public import KumarNivat.SegmentSummandGeometry

@[expose] public section

namespace KumarNivat

-- an actual pair of parallel lattice endpoints contains a unit segment in the prescribed primitive direction.
theorem primitive_unit_anchor_in_convex_set (P : Set RealPlane) (hP : Convex ℝ P)
    (a : Site) (τ : Site →+ ℤ)
    (hker : ∀ g : Site, directionNormal a g = 0 → g = τ g • a)
    (p : Site) (hp : p ≠ 0) (hparallel : directionNormal a p = 0) (q : Site)
    (hq : latticeEmbedding q ∈ P) (hqp : latticeEmbedding (q + p) ∈ P) :
    ∃ E : RealPlane, E ∈ P ∧ E + latticeEmbedding a ∈ P ∧
      latticeNormal (directionNormal a) E = (directionNormal a q : ℝ) := by
  have hrep := hker p hparallel
  have hn : τ p ≠ 0 := by intro hz; apply hp; rw [hrep, hz, zero_smul]
  have hemp : latticeEmbedding p = (τ p : ℝ) • latticeEmbedding a := by
    simpa only [latticeEmbedding_zsmul] using congrArg latticeEmbedding hrep
  by_cases hpos : 0 < τ p
  · have hlen : (1 : ℝ) ≤ (τ p : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ τ p)
    have hspan := lineInterval_subset_convex_set P hP (latticeEmbedding q) (latticeEmbedding a)
      0 (τ p : ℝ) (by linarith)
      (by simpa only [zero_smul, add_zero] using hq)
      (by simpa only [latticeEmbedding_add, hemp] using hqp)
    refine ⟨latticeEmbedding q, hq, ?_, latticeNormal_embedding _ _⟩
    simpa only [one_smul] using hspan ⟨1, ⟨by norm_num, hlen⟩, rfl⟩
  · have hlen : (1 : ℝ) ≤ -(τ p : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ -τ p)
    have hend : latticeEmbedding (q + p) + (-(τ p : ℝ)) • latticeEmbedding a ∈ P := by
      rw [latticeEmbedding_add, hemp, neg_smul]
      simpa only [add_neg_cancel_right] using hq
    have hspan := lineInterval_subset_convex_set P hP (latticeEmbedding (q + p)) (latticeEmbedding a)
      0 (-(τ p : ℝ)) (by linarith)
      (by simpa only [zero_smul, add_zero] using hqp) hend
    refine ⟨latticeEmbedding (q + p), hqp, ?_, ?_⟩
    · simpa only [one_smul] using hspan ⟨1, ⟨by norm_num, hlen⟩, rfl⟩
    · rw [latticeNormal_embedding, map_add, hparallel, add_zero]

end KumarNivat
