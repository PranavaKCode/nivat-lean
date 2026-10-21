module

public import KumarNivat.AnchoredCyclicFacesRelaxation
public import KumarNivat.NewtonEnvelopeSaturation
public import KumarNivat.PolyhedralLimits

@[expose] public section

namespace KumarNivat

-- saturating the actual integer walk gives a lattice-convex polygon with those same vertices and lengths.
theorem exists_saturated_positive_cyclic_walk {n : ℕ} [NeZero n]
    (e v : ZMod n → Site) (r : ZMod n → ℤ) (hr : ∀ k, 0 < r k)
    (hedge : ∀ k, v (k + 1) = v k + r k • e k) :
    ∃ A : Finset Site, LatticeConvex A ∧ ∃ R : OrderedCyclicLatticePolygon e A,
      R.vertex = v ∧ R.edgeLength = r := by
  classical
  let T : Finset Site := Finset.univ.image v
  have hgen : latticeEmbedding '' (T : Set Site) = Set.range (fun k => latticeEmbedding (v k)) := by
    ext z
    constructor
    · rintro ⟨u, hu, he⟩
      obtain ⟨k, _hk, hku⟩ := Finset.mem_image.mp hu
      exact ⟨k, by change latticeEmbedding (v k) = z; rw [hku]; exact he⟩
    · rintro ⟨k, rfl⟩
      exact ⟨v k, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩, rfl⟩
  have hHull : latticeHull T = convexHull ℝ (Set.range (fun k => latticeEmbedding (v k))) := by
    unfold latticeHull
    rw [hgen]
  obtain ⟨A, hA, hTA, hAHull, _hAmem⟩ := exists_latticeConvex_hull_saturation T
  let R : OrderedCyclicLatticePolygon e A :=
    { vertex := v
      edgeLength := r
      length_pos := hr
      edge_eq := hedge
      vertex_mem := fun k => hTA (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
      hull_eq := hAHull.trans hHull }
  exact ⟨A, hA, R, rfl, rfl⟩

-- each intermediate layer moves precisely its named inward support by j original integer levels.
def cyclicFacetRelaxedCut {n : ℕ} [NeZero n] (e : ZMod n → Site)
    (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) (j : ℤ) (k : ZMod n) : ℤ :=
  directionNormal (e k) (P.vertex k) - if k = i then j else 0

-- the actual rational relaxation is kept in the original real lattice plane.
def cyclicFacetRelaxedRegion {n : ℕ} [NeZero n] (e : ZMod n → Site)
    (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) (j : ℤ) : Set RealPlane :=
  finiteInwardRegion Finset.univ (fun k => directionNormal (e k)) (cyclicFacetRelaxedCut e F P i j)

-- the constructed integer walk has exactly the cleared original support levels.
theorem scaled_facet_relaxation_support_levels {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F : Finset Site)
    (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) (j : ℤ) :
    ∀ k, directionNormal (e k) (scaledFacetRelaxationVertex e F P i j k) =
      cyclicFacetRelaxationScale e i * cyclicFacetRelaxedCut e F P i j k := by
  have hcn := (cyclic_facet_neighbors_distinct e horder i).2.1
  intro k
  by_cases hk : k = i
  · subst k
    have hreverse : directionNormal (e i) (e (i - 1)) = -determinant (e (i - 1)) (e i) := by
      change determinant (e i) (e (i - 1)) = -determinant (e (i - 1)) (e i)
      simp only [determinant]
      ring
    simp only [scaledFacetRelaxationVertex, cyclicFacetRelaxedCut, ite_true,
      map_add, map_zsmul, smul_eq_mul, hreverse]
    dsimp [cyclicFacetRelaxationScale]
    ring
  · by_cases hn : k = i + 1
    · subst k
      simp only [scaledFacetRelaxationVertex, cyclicFacetRelaxedCut, ite_eq_right hcn.symm,
        ite_true, map_sub, map_zsmul, directionNormal_self, smul_eq_mul, mul_zero, sub_zero]
    · simp only [scaledFacetRelaxationVertex, cyclicFacetRelaxedCut, ite_eq_right hk, ite_eq_right hn,
        map_zsmul, sub_zero, smul_eq_mul]

-- a positive integer dilation of the whole inward region clears its support levels exactly.
theorem finite_inward_region_positive_dilation {I : Type*} (J : Finset I)
    (μ : I → Site →+ ℤ) (cut : I → ℤ) (M : ℤ) (hM : 0 < M) :
    (fun x : RealPlane => (M : ℝ) • x) '' finiteInwardRegion J μ cut =
      finiteInwardRegion J μ (fun k => M * cut k) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩ k hk
    change ((M * cut k : ℤ) : ℝ) ≤ latticeNormal (μ k) ((M : ℝ) • x)
    rw [map_smul, smul_eq_mul, Int.cast_mul]
    exact mul_le_mul_of_nonneg_left (hx k hk) hMR.le
  · intro hz
    refine ⟨(M : ℝ)⁻¹ • z, ?_, ?_⟩
    · intro k hk
      have hbound := hz k hk
      change ((M * cut k : ℤ) : ℝ) ≤ latticeNormal (μ k) z at hbound
      rw [Int.cast_mul] at hbound
      change (cut k : ℝ) ≤ latticeNormal (μ k) ((M : ℝ)⁻¹ • z)
      rw [map_smul, smul_eq_mul, ← div_eq_inv_mul]
      apply (le_div_iff₀ hMR).mpr
      nlinarith
    · change (M : ℝ) • ((M : ℝ)⁻¹ • z) = z
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hMR), one_smul]

-- every buffered intermediate relaxation is the inverse dilation of an actual same-fan integer polygon.
theorem exists_actual_scaled_facet_relaxation {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (hlen : ∀ k, Q.edgeLength k ≤ P.edgeLength k) (i : ZMod n) (j : ℤ)
    (hj₀ : 0 ≤ j) (hjm : j ≤ cyclicFacetRelaxationScale e i)
    (hbuffer : Q.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1 ≤ P.edgeLength i) :
    ∃ A : Finset Site, LatticeConvex A ∧ ∃ R : OrderedCyclicLatticePolygon e A,
      R.vertex = scaledFacetRelaxationVertex e F P i j ∧
      R.edgeLength = scaledFacetRelaxationLength e F P i j ∧
      latticeHull A = (fun x : RealPlane => (cyclicFacetRelaxationScale e i : ℝ) • x) ''
        cyclicFacetRelaxedRegion e F P i j := by
  have hM := cyclic_facet_relaxation_scale_positive e horder i
  have hdom := scaled_facet_relaxation_lengths_dominate e horder Z F Q P hlen i j hj₀ hjm hbuffer
  have hpos : ∀ k, 0 < scaledFacetRelaxationLength e F P i j k :=
    fun k => lt_of_lt_of_le (mul_pos hM (Q.length_pos k)) (hdom k)
  obtain ⟨A, hA, R, hv, hr⟩ := exists_saturated_positive_cyclic_walk e
    (scaledFacetRelaxationVertex e F P i j) (scaledFacetRelaxationLength e F P i j) hpos
    (scaled_facet_relaxation_edge_equations e horder F P i j)
  refine ⟨A, hA, R, hv, hr, ?_⟩
  rw [R.hull_eq, ordered_cyclic_walk_facet_presentation e horder R.vertex R.edgeLength R.length_pos R.edge_eq, hv]
  unfold cyclicFacetRelaxedRegion
  rw [finite_inward_region_positive_dilation _ _ _ _ hM]
  ext z
  constructor
  · intro hz k _hk
    have hbound := hz k
    rw [scaled_facet_relaxation_support_levels e horder F P i j k] at hbound
    exact hbound
  · intro hz k
    have hbound := hz k (Finset.mem_univ k)
    rw [scaled_facet_relaxation_support_levels e horder F P i j k]
    exact hbound

end KumarNivat
