import KumarNivat.AnchoredEnvelopeLengthsScaled
import KumarNivat.NewtonCyclicMinkowski

namespace KumarNivat

open scoped Pointwise

-- undoing a nonzero geometric dilation recovers the original real set.
theorem inverse_real_dilation_image (a : ℝ) (ha : a ≠ 0) (S : Set RealPlane) :
    (fun x : RealPlane => a⁻¹ • x) '' ((fun x : RealPlane => a • x) '' S) = S := by
  rw [Set.image_image]
  have he : (fun x : RealPlane => a⁻¹ • (a • x)) = id := by
    funext x
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rfl
  change (fun x : RealPlane => a⁻¹ • (a • x)) '' S = S
  rw [he, Set.image_id]

-- linear geometric dilation distributes over the actual minkowski sum.
theorem real_dilation_image_add (a : ℝ) (S T : Set RealPlane) :
    (fun x : RealPlane => a • x) '' (S + T) =
      (fun x : RealPlane => a • x) '' S + (fun x : RealPlane => a • x) '' T := by
  ext z
  constructor
  · rintro ⟨_x, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    change a • (s + t) ∈ (fun x : RealPlane => a • x) '' S + (fun x : RealPlane => a • x) '' T
    rw [smul_add]
    exact Set.add_mem_add ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro ⟨_s, ⟨s, hs, rfl⟩, _t, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨s + t, Set.add_mem_add hs ht, smul_add a s t⟩

-- scaling the actual integer vertices scales their entire convex hull.
theorem real_dilation_integer_walk_hull {n : ℕ} [NeZero n] (v : ZMod n → Site) (M : ℤ) :
    (fun x : RealPlane => (M : ℝ) • x) '' convexHull ℝ (Set.range (fun k => latticeEmbedding (v k))) =
      convexHull ℝ (Set.range (fun k => latticeEmbedding (M • v k))) := by
  have he := (LinearMap.lsmul ℝ RealPlane (M : ℝ)).image_convexHull
    (Set.range (fun k => latticeEmbedding (v k)))
  change (fun x : RealPlane => (M : ℝ) • x) '' _ = _ at he
  rw [he]
  congr 1
  ext z
  constructor
  · rintro ⟨_x, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, latticeEmbedding_zsmul M (v k)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨latticeEmbedding (v k), ⟨k, rfl⟩, (latticeEmbedding_zsmul M (v k)).symm⟩

-- the residual is constructed from the actual cleared walk, then returned to the original plane.
def cyclicFacetRelaxedResidual {n : ℕ} [NeZero n] (e : ZMod n → Site)
    (Z F : Finset Site) (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (i : ZMod n) (j : ℤ) : Set RealPlane :=
  (fun x : RealPlane => (cyclicFacetRelaxationScale e i : ℝ)⁻¹ • x) ''
    convexHull ℝ (Set.range (fun k => latticeEmbedding
      (scaledFacetRelaxationVertex e F P i j k - cyclicFacetRelaxationScale e i • Q.vertex k)))

-- the actual residual closed walk subtracts the cleared newton edge lengths coordinatewise.
theorem scaled_facet_relaxation_residual_edge_equations {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) (j : ℤ) :
    ∀ k, scaledFacetRelaxationVertex e F P i j (k + 1) - cyclicFacetRelaxationScale e i • Q.vertex (k + 1) =
      (scaledFacetRelaxationVertex e F P i j k - cyclicFacetRelaxationScale e i • Q.vertex k) +
        (scaledFacetRelaxationLength e F P i j k - cyclicFacetRelaxationScale e i * Q.edgeLength k) • e k := by
  intro k
  rw [scaled_facet_relaxation_edge_equations e horder F P i j k, Q.edge_eq,
    smul_add, smul_smul, sub_smul]
  abel

-- the buffer makes the constructed residual walk nonnegative, including possible zero edges.
theorem scaled_facet_relaxation_residual_lengths_nonnegative {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (hlen : ∀ k, Q.edgeLength k ≤ P.edgeLength k) (i : ZMod n) (j : ℤ)
    (hj₀ : 0 ≤ j) (hjm : j ≤ cyclicFacetRelaxationScale e i)
    (hbuffer : Q.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1 ≤ P.edgeLength i) :
    ∀ k, 0 ≤ scaledFacetRelaxationLength e F P i j k - cyclicFacetRelaxationScale e i * Q.edgeLength k := by
  intro k
  exact sub_nonneg.mpr (scaled_facet_relaxation_lengths_dominate e horder Z F Q P hlen i j hj₀ hjm hbuffer k)

-- every buffered layer retains the exact original newton hull as a genuine minkowski summand.
theorem cyclic_facet_relaxed_region_minkowski {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (hlen : ∀ k, Q.edgeLength k ≤ P.edgeLength k) (i : ZMod n) (j : ℤ)
    (hj₀ : 0 ≤ j) (hjm : j ≤ cyclicFacetRelaxationScale e i)
    (hbuffer : Q.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1 ≤ P.edgeLength i) :
    cyclicFacetRelaxedRegion e F P i j = latticeHull Z + cyclicFacetRelaxedResidual e Z F Q P i j := by
  let M := cyclicFacetRelaxationScale e i
  have hM := cyclic_facet_relaxation_scale_positive e horder i
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  let v := fun k => M • Q.vertex k
  let w := fun k => scaledFacetRelaxationVertex e F P i j k - M • Q.vertex k
  let r := fun k => M * Q.edgeLength k
  let d := fun k => scaledFacetRelaxationLength e F P i j k - M * Q.edgeLength k
  have hr : ∀ k, 0 < r k := fun k => mul_pos hM (Q.length_pos k)
  have hd : ∀ k, 0 ≤ d k :=
    scaled_facet_relaxation_residual_lengths_nonnegative e horder Z F Q P hlen i j hj₀ hjm hbuffer
  have hv : ∀ k, v (k + 1) = v k + r k • e k := by
    intro k
    dsimp [v, r]
    rw [Q.edge_eq, smul_add, smul_smul]
  have hw : ∀ k, w (k + 1) = w k + d k • e k :=
    scaled_facet_relaxation_residual_edge_equations e horder Z F Q P i j
  have hsum := ordered_cyclic_walk_minkowski e horder v w r d hr hd hv hw
  have he : (fun k => latticeEmbedding (v k + w k)) =
      (fun k => latticeEmbedding (scaledFacetRelaxationVertex e F P i j k)) := by
    funext k
    congr 1
    dsimp [v, w]
    abel
  rw [he] at hsum
  obtain ⟨A, _hA, R, hRv, _hRr, hHull⟩ :=
    exists_actual_scaled_facet_relaxation e horder Z F Q P hlen i j hj₀ hjm hbuffer
  rw [R.hull_eq, hRv] at hHull
  rw [← real_dilation_integer_walk_hull Q.vertex M, ← Q.hull_eq] at hsum
  calc
    cyclicFacetRelaxedRegion e F P i j =
        (fun x : RealPlane => (M : ℝ)⁻¹ • x) ''
          ((fun x : RealPlane => (M : ℝ) • x) '' cyclicFacetRelaxedRegion e F P i j) :=
      (inverse_real_dilation_image (M : ℝ) hMR _).symm
    _ = (fun x : RealPlane => (M : ℝ)⁻¹ • x) ''
        (((fun x : RealPlane => (M : ℝ) • x) '' latticeHull Z) +
          convexHull ℝ (Set.range (fun k => latticeEmbedding (w k)))) := by rw [← hHull, hsum]
    _ = latticeHull Z + cyclicFacetRelaxedResidual e Z F Q P i j := by
      rw [real_dilation_image_add, inverse_real_dilation_image (M : ℝ) hMR]
      rfl

-- finite residual vertices give compactness, convexity and a real residual point without extra assumptions.
theorem cyclic_facet_relaxed_residual_geometry {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) (j : ℤ) :
    Convex ℝ (cyclicFacetRelaxedResidual e Z F Q P i j) ∧
      IsCompact (cyclicFacetRelaxedResidual e Z F Q P i j) ∧
      (cyclicFacetRelaxedResidual e Z F Q P i j).Nonempty := by
  let w := fun k => scaledFacetRelaxationVertex e F P i j k - cyclicFacetRelaxationScale e i • Q.vertex k
  refine ⟨?_, ?_, ?_⟩
  · exact (convex_convexHull ℝ _).linear_image
      (LinearMap.lsmul ℝ RealPlane (cyclicFacetRelaxationScale e i : ℝ)⁻¹)
  · exact ((Set.finite_range (fun k => latticeEmbedding (w k))).isCompact_convexHull ℝ).image
      (continuous_const_smul _)
  · exact ⟨_, Set.mem_image_of_mem _ (subset_convexHull ℝ _ ⟨0, rfl⟩)⟩

end KumarNivat
