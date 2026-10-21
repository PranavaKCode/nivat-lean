module

public import KumarNivat.NewtonCyclicFacets

@[expose] public section

namespace KumarNivat

-- adjacent cramer coordinates identify the actual tangent parameter on a supporting line.
theorem real_tangent_parameter_of_zero_normal (p q : Site) (hdet : determinant p q ≠ 0)
    (z : RealPlane) (hzero : latticeNormal (directionNormal q) z = 0) :
    z = (latticeNormal (directionNormal p) z / (determinant p q : ℝ)) • latticeEmbedding q := by
  have hreal : (determinant p q : ℝ) ≠ 0 := by exact_mod_cast hdet
  have he := real_plane_edge_cramer_identity p q z
  rw [hzero, neg_zero, zero_smul, zero_add] at he
  calc
    z = (determinant p q : ℝ)⁻¹ • ((determinant p q : ℝ) • z) := by
      rw [smul_smul, inv_mul_cancel₀ hreal, one_smul]
    _ = _ := by rw [he, smul_smul, div_eq_inv_mul]

-- zero residual lengths still give all actual supporting inequalities on the convex hull.
theorem ordered_cyclic_nonnegative_real_point_minimum {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (v : ZMod n → Site)
    (r : ZMod n → ℤ) (hr : ∀ k, 0 ≤ r k)
    (hedge : ∀ k, v (k + 1) = v k + r k • e k) (x : RealPlane)
    (hx : x ∈ convexHull ℝ (Set.range (fun k => latticeEmbedding (v k)))) :
    ∀ i, (directionNormal (e i) (v i) : ℝ) ≤ latticeNormal (directionNormal (e i)) x := by
  have hmin := ordered_cyclic_walk_normal_minimum e horder v r hr hedge
  intro i
  have hgen : Set.range (fun k => latticeEmbedding (v k)) ⊆
      {y : RealPlane | (directionNormal (e i) (v i) : ℝ) ≤ latticeNormal (directionNormal (e i)) y} := by
    rintro _ ⟨k, rfl⟩
    change (directionNormal (e i) (v i) : ℝ) ≤ latticeNormal (directionNormal (e i)) (latticeEmbedding (v k))
    rw [latticeNormal_embedding]
    exact_mod_cast hmin i k
  exact convexHull_min hgen
    ((convex_Ici (directionNormal (e i) (v i) : ℝ)).linear_preimage (latticeNormal (directionNormal (e i)))) hx

-- adjacent support bounds give the whole residual face even when its edge has zero length.
theorem ordered_cyclic_nonnegative_walk_face_is_edge {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (v : ZMod n → Site)
    (r : ZMod n → ℤ) (hr : ∀ k, 0 ≤ r k)
    (hedge : ∀ k, v (k + 1) = v k + r k • e k) (i : ZMod n) :
    normalFace (convexHull ℝ (Set.range (fun k => latticeEmbedding (v k))))
        (latticeNormal (directionNormal (e i))) (directionNormal (e i) (v i) : ℝ) =
      lineInterval (latticeEmbedding (v i)) (latticeEmbedding (e i)) 0 (r i : ℝ) := by
  apply Set.Subset.antisymm
  · intro x hx
    let z : RealPlane := x - latticeEmbedding (v i)
    let p := e (i - 1)
    let q := e i
    let D : ℝ := determinant p q
    have hD : 0 < determinant p q := horder.adjacent_pos i
    have hDR : (0 : ℝ) < D := by dsimp [D]; exact_mod_cast hD
    have hnorm := ordered_cyclic_nonnegative_real_point_minimum e horder v r hr hedge x hx.1
    have hprev := congrArg (directionNormal p) (hedge (i - 1))
    simp only [p, sub_add_cancel, map_add, map_zsmul, directionNormal_self, smul_zero, add_zero] at hprev
    have hlower : 0 ≤ latticeNormal (directionNormal p) z := by
      dsimp [z]
      rw [map_sub, latticeNormal_embedding, hprev]
      exact sub_nonneg.mpr (hnorm (i - 1))
    have hzero : latticeNormal (directionNormal q) z = 0 := by
      dsimp [z]
      rw [map_sub, latticeNormal_embedding, hx.2, sub_self]
    let s : ℝ := latticeNormal (directionNormal p) z / D
    have hz : z = s • latticeEmbedding q :=
      real_tangent_parameter_of_zero_normal p q (ne_of_gt hD) z hzero
    have hrep : x = latticeEmbedding (v i) + s • latticeEmbedding (e i) := by
      rw [← hz]
      dsimp [z]
      abel
    have hs₀ : 0 ≤ s := div_nonneg hlower hDR.le
    have hnext := hnorm (i + 1)
    rw [hedge, map_add, map_zsmul, smul_eq_mul] at hnext
    rw [hrep, map_add, map_smul, latticeNormal_embedding, latticeNormal_embedding, smul_eq_mul] at hnext
    push_cast at hnext
    have hnextpos := horder.adjacent_pos (i + 1)
    simp only [add_sub_cancel_right] at hnextpos
    have hnextneg : directionNormal (e (i + 1)) (e i) < 0 := by
      change determinant (e (i + 1)) (e i) < 0
      have he : determinant (e (i + 1)) (e i) = -determinant (e i) (e (i + 1)) := by
        simp only [determinant]
        ring
      rw [he]
      omega
    have hnextnegR : (directionNormal (e (i + 1)) (e i) : ℝ) < 0 := by exact_mod_cast hnextneg
    have hs₁ : s ≤ (r i : ℝ) := by nlinarith
    exact ⟨s, ⟨hs₀, hs₁⟩, hrep.symm⟩
  · intro x hx
    have hstart : latticeEmbedding (v i) ∈ normalFace (convexHull ℝ (Set.range (fun k => latticeEmbedding (v k))))
        (latticeNormal (directionNormal (e i))) (directionNormal (e i) (v i) : ℝ) :=
      ⟨subset_convexHull ℝ _ ⟨i, rfl⟩, latticeNormal_embedding _ _⟩
    have hend : latticeEmbedding (v i) + (r i : ℝ) • latticeEmbedding (e i) ∈
        normalFace (convexHull ℝ (Set.range (fun k => latticeEmbedding (v k)))) (latticeNormal (directionNormal (e i)))
          (directionNormal (e i) (v i) : ℝ) := by
      have he := congrArg latticeEmbedding (hedge i)
      rw [latticeEmbedding_add, latticeEmbedding_zsmul] at he
      rw [← he]
      refine ⟨subset_convexHull ℝ _ ⟨i + 1, rfl⟩, ?_⟩
      rw [latticeNormal_embedding, hedge, map_add, map_zsmul, directionNormal_self, smul_zero, add_zero]
    have hconv : Convex ℝ (normalFace (convexHull ℝ (Set.range (fun k => latticeEmbedding (v k)))) (latticeNormal (directionNormal (e i)))
        (directionNormal (e i) (v i) : ℝ)) :=
      (convex_convexHull ℝ _).inter ((convex_singleton _).linear_preimage _)
    rw [lineInterval_eq_segment _ _ _ _ (by exact_mod_cast hr i)] at hx
    simp only [zero_smul, add_zero] at hx
    exact hconv.segment_subset hstart hend hx

end KumarNivat
