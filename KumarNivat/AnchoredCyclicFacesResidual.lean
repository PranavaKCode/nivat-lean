module

public import KumarNivat.AnchoredEnvelopeLengthsResidual

@[expose] public section

namespace KumarNivat

-- a nonzero geometric dilation carries the exact supporting slice to its scaled level.
theorem normal_face_real_dilation (C : Set RealPlane) (ell : RealPlane →ₗ[ℝ] ℝ)
    (cut a : ℝ) (ha : a ≠ 0) :
    normalFace ((fun x : RealPlane => a • x) '' C) ell (a * cut) =
      (fun x : RealPlane => a • x) '' normalFace C ell cut := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, he⟩
    rw [map_smul, smul_eq_mul] at he
    exact ⟨x, ⟨hx, mul_left_cancel₀ ha he⟩, rfl⟩
  · rintro ⟨x, ⟨hx, he⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [map_smul, smul_eq_mul, he]⟩

-- positive dilation rescales the tangent interval while keeping its primitive direction.
theorem line_interval_positive_dilation (A v : RealPlane) (r a : ℝ) (ha : 0 < a) :
    (fun x : RealPlane => a • x) '' lineInterval A v 0 r =
      lineInterval (a • A) v 0 (a * r) := by
  ext z
  constructor
  · rintro ⟨_x, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨a * s, ⟨mul_nonneg ha.le hs.1, mul_le_mul_of_nonneg_left hs.2 ha.le⟩, ?_⟩
    change a • A + (a * s) • v = a • (A + s • v)
    rw [smul_add, smul_smul]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨A + (s / a) • v, ⟨s / a, ⟨div_nonneg hs.1 ha.le, ?_⟩, rfl⟩, ?_⟩
    · apply (div_le_iff₀ ha).mpr
      nlinarith [hs.2]
    · change a • (A + (s / a) • v) = a • A + s • v
      rw [smul_add, smul_smul, mul_div_cancel₀ _ (ne_of_gt ha)]

-- the actual residual minimum is the difference of the relaxed polygon and original newton supports.
theorem scaled_facet_relaxation_residual_support_level {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) (j : ℤ) :
    directionNormal (e i)
      (scaledFacetRelaxationVertex e F P i j i - cyclicFacetRelaxationScale e i • Q.vertex i) =
        cyclicFacetRelaxationScale e i *
          (cyclicFacetRelaxedCut e F P i j i - directionNormal (e i) (Q.vertex i)) := by
  rw [map_sub, scaled_facet_relaxation_support_levels e horder F P i j i,
    map_zsmul, smul_eq_mul]
  ring

-- the residual supporting inequality is proved from its constructed nonnegative cyclic walk.
theorem cyclic_facet_relaxed_residual_normal_lower {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (hlen : ∀ k, Q.edgeLength k ≤ P.edgeLength k) (i : ZMod n) (j : ℤ)
    (hj₀ : 0 ≤ j) (hjm : j ≤ cyclicFacetRelaxationScale e i)
    (hbuffer : Q.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1 ≤ P.edgeLength i) :
    ∀ x ∈ cyclicFacetRelaxedResidual e Z F Q P i j,
      ((cyclicFacetRelaxedCut e F P i j i - directionNormal (e i) (Q.vertex i) : ℤ) : ℝ) ≤
        latticeNormal (directionNormal (e i)) x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hmin := ordered_cyclic_nonnegative_real_point_minimum e horder
    (fun k => scaledFacetRelaxationVertex e F P i j k - cyclicFacetRelaxationScale e i • Q.vertex k)
    (fun k => scaledFacetRelaxationLength e F P i j k - cyclicFacetRelaxationScale e i * Q.edgeLength k)
    (scaled_facet_relaxation_residual_lengths_nonnegative e horder Z F Q P hlen i j hj₀ hjm hbuffer)
    (scaled_facet_relaxation_residual_edge_equations e horder Z F Q P i j) y hy i
  rw [scaled_facet_relaxation_residual_support_level e horder Z F Q P i j] at hmin
  have hM : (0 : ℝ) < (cyclicFacetRelaxationScale e i : ℝ) := by
    exact_mod_cast cyclic_facet_relaxation_scale_positive e horder i
  rw [map_smul, smul_eq_mul, ← div_eq_inv_mul]
  apply (le_div_iff₀ hM).mpr
  push_cast at hmin ⊢
  nlinarith

-- the whole original-plane residual face is calculated from the actual integer residual walk.
theorem cyclic_facet_relaxed_residual_face {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (hlen : ∀ k, Q.edgeLength k ≤ P.edgeLength k) (i : ZMod n) (j : ℤ)
    (hj₀ : 0 ≤ j) (hjm : j ≤ cyclicFacetRelaxationScale e i)
    (hbuffer : Q.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1 ≤ P.edgeLength i) :
    normalFace (cyclicFacetRelaxedResidual e Z F Q P i j) (latticeNormal (directionNormal (e i)))
        ((cyclicFacetRelaxedCut e F P i j i - directionNormal (e i) (Q.vertex i) : ℤ) : ℝ) =
      lineInterval ((cyclicFacetRelaxationScale e i : ℝ)⁻¹ • latticeEmbedding
        (scaledFacetRelaxationVertex e F P i j i - cyclicFacetRelaxationScale e i • Q.vertex i))
        (latticeEmbedding (e i)) 0
        ((cyclicFacetRelaxationScale e i : ℝ)⁻¹ *
          ((scaledFacetRelaxationLength e F P i j i - cyclicFacetRelaxationScale e i * Q.edgeLength i : ℤ) : ℝ)) := by
  have hM : (0 : ℝ) < (cyclicFacetRelaxationScale e i : ℝ) := by
    exact_mod_cast cyclic_facet_relaxation_scale_positive e horder i
  have hlevel : ((cyclicFacetRelaxedCut e F P i j i - directionNormal (e i) (Q.vertex i) : ℤ) : ℝ) =
      (cyclicFacetRelaxationScale e i : ℝ)⁻¹ *
        (directionNormal (e i)
          (scaledFacetRelaxationVertex e F P i j i - cyclicFacetRelaxationScale e i • Q.vertex i) : ℝ) := by
    rw [scaled_facet_relaxation_residual_support_level e horder Z F Q P i j, Int.cast_mul,
      ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hM), one_mul]
  rw [hlevel]
  unfold cyclicFacetRelaxedResidual
  rw [normal_face_real_dilation _ _ _ _ (inv_ne_zero (ne_of_gt hM)),
    ordered_cyclic_nonnegative_walk_face_is_edge e horder
      (fun k => scaledFacetRelaxationVertex e F P i j k - cyclicFacetRelaxationScale e i • Q.vertex k)
      (fun k => scaledFacetRelaxationLength e F P i j k - cyclicFacetRelaxationScale e i * Q.edgeLength k)
      (scaled_facet_relaxation_residual_lengths_nonnegative e horder Z F Q P hlen i j hj₀ hjm hbuffer)
      (scaled_facet_relaxation_residual_edge_equations e horder Z F Q P i j) i,
    line_interval_positive_dilation _ _ _ _ (inv_pos.mpr hM)]

-- its left endpoint depends only on the original left vertex and the fixed layer number.
theorem cyclic_facet_relaxed_residual_left_endpoint {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) (j : ℤ) :
    (cyclicFacetRelaxationScale e i : ℝ)⁻¹ • latticeEmbedding
        (scaledFacetRelaxationVertex e F P i j i - cyclicFacetRelaxationScale e i • Q.vertex i) =
      latticeEmbedding (P.vertex i) +
        ((j : ℝ) / (determinant (e (i - 1)) (e i) : ℝ)) • latticeEmbedding (e (i - 1)) -
        latticeEmbedding (Q.vertex i) := by
  have hD := horder.adjacent_pos i
  have hN := horder.adjacent_pos (i + 1)
  simp only [add_sub_cancel_right] at hN
  have hDR : (determinant (e (i - 1)) (e i) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  have hNR : (determinant (e i) (e (i + 1)) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hM : (cyclicFacetRelaxationScale e i : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (cyclic_facet_relaxation_scale_positive e horder i)
  have hcoeff : (cyclicFacetRelaxationScale e i : ℝ)⁻¹ *
      ((j * determinant (e i) (e (i + 1)) : ℤ) : ℝ) =
        (j : ℝ) / (determinant (e (i - 1)) (e i) : ℝ) := by
    dsimp [cyclicFacetRelaxationScale]
    push_cast
    field_simp
  simp only [scaledFacetRelaxationVertex, ite_true, latticeEmbedding_sub, latticeEmbedding_add,
    latticeEmbedding_zsmul, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hM,
    one_smul, hcoeff]

end KumarNivat
